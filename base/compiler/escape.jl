module EscapeAnalysis

export find_escapes!

import Core:
    SimpleVector, GotoNode, GotoIfNot, Argument, IntrinsicFunction, Const, sizeof

import ..Compiler:
    Vector, IdDict, MethodInstance, IRCode, SSAValue, PiNode, PhiNode, OptimizationState,
    PhiCNode, UpsilonNode, ReturnNode, IR_FLAG_EFFECT_FREE, BitSet,
    ==, !, !==, !=, ≠, :, ≤, &, |, +, -, *, <, <<, ∪, ∩, ⊆,
    isbitstype, ismutabletype, widenconst, argextype, argtype_to_function, isexpr,
    is_meta_expr_head, copy, zip, empty!, length, get, first, isassigned, push!, isempty,
    @assert, @nospecialize

isnothing(x) = x === nothing

# analysis
# ========

"""
    x::EscapeLattice

A lattice for escape information, which holds the following properties:
- `x.Analyzed::Bool`: not formally part of the lattice, indicates this statement has not been analyzed at all
- `x.ReturnEscape::BitSet`: keeps SSA numbers of return statements where it can be returned to the caller
  * `isempty(x.ReturnEscape)` means it never escapes to the caller
  * otherwise it indicates it will escape to the caller via return (possibly as a field),
    where `0 ∈ x.ReturnEscape` has the special meaning that it's visible to the caller
    simply because it's passed as call argument
- `x.ThrownEscape::Bool`: indicates it may escape to somewhere through an exception (possibly as a field)
- `x.GlobalEscape::Bool`: indicates it may escape to a global space an exception (possibly as a field)
- `x.ArgEscape::Int` (not implemented yet): indicates it will escape to the caller through `setfield!` on argument(s)
  * `-1` : no escape
  * `0` : unknown or multiple
  * `n` : through argument N

These attributes can be combined to create a partial lattice that has a finite height, given
that input program has a finite number of statements, which is assured by Julia's semantics.

There are utility constructors to create common `EscapeLattice`s, e.g.,
- `NoEscape()`: the bottom element of this lattice, meaning it won't escape to anywhere
- `AllEscape()`: the topmost element of this lattice, meaning it will escape to everywhere

The escape analysis will transition these elements from the bottom to the top,
in the same direction as Julia's native type inference routine.
An abstract state will be initialized with the bottom(-like) elements:
- the call arguments are initialized as `ArgumentReturnEscape()`, because they're visible from a caller immediately
- the other states are initialized as `NotAnalyzed()`, which is a special lattice element that
  is slightly lower than `NoEscape`, but at the same time doesn't represent any meaning
  other than it's not analyzed yet (thus it's not formally part of the lattice).
"""
struct EscapeLattice
    Analyzed::Bool
    ReturnEscape::BitSet
    ThrownEscape::Bool
    GlobalEscape::Bool
    # TODO: ArgEscape::Int
end

function ==(x::EscapeLattice, y::EscapeLattice)
    return x.Analyzed === y.Analyzed &&
           x.ReturnEscape == y.ReturnEscape &&
           x.ThrownEscape === y.ThrownEscape &&
           x.GlobalEscape === y.GlobalEscape
end

# lattice constructors
# precompute default values in order to eliminate computations at callsites
const NO_RETURN = BitSet()
const ARGUMENT_RETURN = BitSet(0)
NotAnalyzed() = EscapeLattice(false, NO_RETURN, false, false) # not formally part of the lattice
NoEscape() = EscapeLattice(true, NO_RETURN, false, false)
ReturnEscape(returns::BitSet) = EscapeLattice(true, returns, false, false)
ReturnEscape(pc::Int) = ReturnEscape(BitSet(pc))
ArgumentReturnEscape() = ReturnEscape(ARGUMENT_RETURN)
ThrownEscape() = EscapeLattice(true, NO_RETURN, true, false)
GlobalEscape() = EscapeLattice(true, NO_RETURN, false, true)
let
    all_return = BitSet(0:1000000)
    global AllReturnEscape() = ReturnEscape(all_return) # used for `show`
    global AllEscape() = EscapeLattice(true, all_return, true, true)
end

# Convenience names for some ⊑ queries
export
    has_not_analyzed,
    has_no_escape,
    has_return_escape,
    has_thrown_escape,
    has_global_escape,
    has_all_escape,
    can_elide_finalizer
has_not_analyzed(x::EscapeLattice) = x == NotAnalyzed()
has_no_escape(x::EscapeLattice) = x ⊑ NoEscape()
has_return_escape(x::EscapeLattice) = !isempty(x.ReturnEscape)
has_return_escape(x::EscapeLattice, pc::Int) = pc in x.ReturnEscape
has_thrown_escape(x::EscapeLattice) = x.ThrownEscape
has_global_escape(x::EscapeLattice) = x.GlobalEscape
has_all_escape(x::EscapeLattice) = AllEscape() == x


"""
    can_elide_finalizer(x::EscapeLattice, pc::Int) -> Bool

Queries the validity of the finalizer elision optimization at the `return` site of statement `pc`,
which inserts `finalize` call when the lifetime of interested object ends.
Note that we don't need to take `x.ThrownEscape` into account because it would have never
been thrown when the program execution reaches the `return` site.
"""
function can_elide_finalizer(x::EscapeLattice, pc::Int)
    x.GlobalEscape && return false
    0 in x.ReturnEscape && return false
    return pc ∉ x.ReturnEscape
end

"""
    can_allocate_on_stack(x::EscapeLattice) -> Bool

Queries the validity of heap-to-stack optimization, which allocates `mutable` object that
`x` represents on stack rather than heap.
The condition is almost same as `has_no_escape(x)`, but additionally we can ignore
`ThrownEscape` if it's handled within analysis frame.
"""
function can_allocate_on_stack(x::EscapeLattice)
    return x.Analyzed &&
           !has_return_escape(x) &&
           !has_unhandled_thrown_escape(x) &&
           !x.GlobalEscape
end

function ⊑(x::EscapeLattice, y::EscapeLattice)
    if x.Analyzed ≤ y.Analyzed &&
       x.ReturnEscape ⊆ y.ReturnEscape &&
       x.ThrownEscape ≤ y.ThrownEscape &&
       x.GlobalEscape ≤ y.GlobalEscape
       return true
    end
    return false
end
⋤(x::EscapeLattice, y::EscapeLattice) = ⊑(x, y) && !⊑(y, x)

function ⊔(x::EscapeLattice, y::EscapeLattice)
    return EscapeLattice(
        x.Analyzed | y.Analyzed,
        x.ReturnEscape ∪ y.ReturnEscape,
        x.ThrownEscape | y.ThrownEscape,
        x.GlobalEscape | y.GlobalEscape,
        )
end

function ⊓(x::EscapeLattice, y::EscapeLattice)
    return EscapeLattice(
        x.Analyzed & y.Analyzed,
        x.ReturnEscape ∩ y.ReturnEscape,
        x.ThrownEscape & y.ThrownEscape,
        x.GlobalEscape & y.GlobalEscape,
        )
end

"""
    state::EscapeState

Extended lattice that maps arguments and SSA values to escape information represented as `EscapeLattice`:
- `state.arguments::Vector{EscapeLattice}`: escape information about "arguments" – note that
  "argument" can include both call arguments and slots appearing in analysis frame
- `ssavalues::Vector{EscapeLattice}`: escape information about each SSA value
"""
struct EscapeState
    arguments::Vector{EscapeLattice}
    ssavalues::Vector{EscapeLattice}
end
function EscapeState(nslots::Int, nargs::Int, nstmts::Int)
    arguments = EscapeLattice[
        1 ≤ i ≤ nargs ? ArgumentReturnEscape() : NotAnalyzed() for i in 1:nslots]
    ssavalues = EscapeLattice[NotAnalyzed() for _ in 1:nstmts]
    return EscapeState(arguments, ssavalues)
end

const GLOBAL_ESCAPE_CACHE = IdDict{MethodInstance,EscapeState}()
__clear_escape_cache!() = empty!(GLOBAL_ESCAPE_CACHE)

const Changes = Vector{Tuple{Any,EscapeLattice}}
"""
    find_escapes(ir::IRCode, nargs::Int) -> EscapeState

Escape analysis implementation is based on the data-flow algorithm described in the paper [^MM02].
The analysis works on the lattice of [`EscapeLattice`](@ref) and transitions lattice elements
from the bottom to the top in a _backward_ way, i.e. data flows from usage cites to definitions,
until every lattice gets converged to a fixed point by maintaining a (conceptual) working set
that contains program counters corresponding to remaining SSA statements to be analyzed.
Note that the analysis only manages a single global state, with some flow-sensitivity
encoded as property of `EscapeLattice`.

[^MM02]: A Graph-Free approach to Data-Flow Analysis.
         Markas Mohnen, 2002, April.
         <https://api.semanticscholar.org/CorpusID:28519618>
"""
function find_escapes!(ir::IRCode, nargs::Int, sv::OptimizationState)
    (; stmts, sptypes, argtypes) = ir
    nstmts = length(stmts)

    # only manage a single state, some flow-sensitivity is encoded as `EscapeLattice` properties
    state = EscapeState(length(ir.argtypes), nargs, nstmts)
    changes = Changes() # stashes changes that happen at current statement

    while true
        local anyupdate = false

        for pc in nstmts:-1:1
            stmt = stmts.inst[pc]

            # we escape statements with the `ThrownEscape` property using the effect-freeness
            # information computed by the inliner
            is_effect_free = stmts.flag[pc] & IR_FLAG_EFFECT_FREE ≠ 0

            # collect escape information
            if isa(stmt, Expr)
                head = stmt.head
                if head === :call
                    has_changes = escape_call!(stmt.args, pc, state, ir, changes)
                    if !is_effect_free
                        add_changes!(stmt.args, ir, ThrownEscape(), changes)
                    else
                        has_changes || continue
                    end
                elseif head === :invoke
                    escape_invoke!(stmt.args, pc, state, ir, changes)
                elseif head === :new
                    info = state.ssavalues[pc]
                    info == NotAnalyzed() && (info = NoEscape())
                    for arg in stmt.args[2:end]
                        push!(changes, (arg, info))
                    end
                    push!(changes, (SSAValue(pc), info)) # we will be interested in if this allocation is not escape or not
                elseif head === :splatnew
                    info = state.ssavalues[pc]
                    info == NotAnalyzed() && (info = NoEscape())
                    # splatnew passes field values using a single tuple (args[2])
                    push!(changes, (stmt.args[2], info))
                    push!(changes, (SSAValue(pc), info)) # we will be interested in if this allocation is not escape or not
                elseif head === :(=)
                    lhs, rhs = stmt.args
                    if isa(lhs, GlobalRef) # global store
                        add_change!(rhs, ir, GlobalEscape(), changes)
                    end
                elseif head === :foreigncall
                    # for foreigncall we simply escape every argument (args[6:length(args[3])])
                    # and its name (args[1])
                    # TODO: we can apply a similar strategy like builtin calls to specialize some foreigncalls
                    foreigncall_nargs = length((stmt.args[3])::SimpleVector)
                    name = stmt.args[1]
                    # if normalize(name) === :jl_gc_add_finalizer_th
                    #     continue # XXX assume this finalizer call is valid for finalizer elision
                    # end
                    push!(changes, (name, ThrownEscape()))
                    add_changes!(stmt.args[6:5+foreigncall_nargs], ir, ThrownEscape(), changes)
                elseif head === :throw_undef_if_not # XXX when is this expression inserted ?
                    add_change!(stmt.args[1], ir, ThrownEscape(), changes)
                elseif is_meta_expr_head(head)
                    # meta expressions doesn't account for any usages
                    continue
                elseif head === :static_parameter
                    # :static_parameter refers any of static parameters, but since they exist
                    # statically, we're really not interested in their escapes
                    continue
                elseif head === :copyast
                    # copyast simply copies a surface syntax AST, and should never use any of arguments or SSA values
                    continue
                elseif head === :undefcheck
                    # undefcheck is temporarily inserted by compiler
                    # it will be processd be later pass so it won't change any of escape states
                    continue
                elseif head === :the_exception
                    # we don't propagate escape information on exceptions via this expression, but rather
                    # use a dedicated lattice property `ThrownEscape`
                    continue
                elseif head === :isdefined
                    # just returns `Bool`, nothing accounts for any usages
                    continue
                elseif head === :enter || head === :leave || head === :pop_exception
                    # these exception frame managements doesn't account for any usages
                    # we can just ignore escape information from
                    continue
                elseif head === :gc_preserve_begin || head === :gc_preserve_end
                    # `GC.@preserve` may "use" arbitrary values, but we can just ignore the escape information
                    # imposed on `GC.@preserve` expressions since they're supposed to never be used elsewhere
                    continue
                else
                    add_changes!(stmt.args, ir, AllEscape(), changes)
                end
            elseif isa(stmt, GlobalRef) # global load
                add_change!(SSAValue(pc), ir, GlobalEscape(), changes)
            elseif isa(stmt, PiNode)
                if isdefined(stmt, :val)
                    info = state.ssavalues[pc]
                    push!(changes, (stmt.val, info))
                end
            elseif isa(stmt, PhiNode)
                info = state.ssavalues[pc]
                values = stmt.values
                for i in 1:length(values)
                    if isassigned(values, i)
                        push!(changes, (values[i], info))
                    end
                end
            elseif isa(stmt, PhiCNode)
                info = state.ssavalues[pc]
                values = stmt.values
                for i in 1:length(values)
                    if isassigned(values, i)
                        push!(changes, (values[i], info))
                    end
                end
            elseif isa(stmt, UpsilonNode)
                if isdefined(stmt, :val)
                    info = state.ssavalues[pc]
                    push!(changes, (stmt.val, info))
                end
            elseif isa(stmt, ReturnNode)
                if isdefined(stmt, :val)
                    add_change!(stmt.val, ir, ReturnEscape(pc), changes)
                end
            else
                @assert stmt isa GotoNode || stmt isa GotoIfNot || stmt isa GlobalRef || isnothing(stmt) # TODO remove me
                continue
            end

            isempty(changes) && continue

            anyupdate |= propagate_changes!(state, changes)

            empty!(changes)
        end

        anyupdate || break
    end

    for pc in 1:nstmts
        # heap-to-stack optimization are carried for heap-allocated objects that are not escaped
        if isexpr(stmts.inst[pc], :new) && ismutabletype(widenconst(stmts.type[pc])) && has_no_escape(state.ssavalues[pc])
            stmts.flag[pc] |= IR_FLAG_NO_ESCAPE
        end
    end
    GLOBAL_ESCAPE_CACHE[sv.linfo] = state
    return state
end


# propagate changes, and check convergence
function propagate_changes!(state::EscapeState, changes::Changes)
    local anychanged = false

    for (x, info) in changes
        if isa(x, Argument)
            old = state.arguments[x.n]
            new = old ⊔ info
            if old ≠ new
                state.arguments[x.n] = new
                anychanged |= true
            end
        elseif isa(x, SSAValue)
            old = state.ssavalues[x.id]
            new = old ⊔ info
            if old ≠ new
                state.ssavalues[x.id] = new
                anychanged |= true
            end
        end
    end

    return anychanged
end

function add_changes!(args::Vector{Any}, ir::IRCode, info::EscapeLattice, changes::Changes)
    for x in args
        add_change!(x, ir, info, changes)
    end
end

function add_change!(@nospecialize(x), ir::IRCode, info::EscapeLattice, changes::Changes)
    if !isbitstype(widenconst(argextype(x, ir, ir.sptypes, ir.argtypes)))
        push!(changes, (x, info))
    end
end

function escape_invoke!(args::Vector{Any}, pc::Int,
                        state::EscapeState, ir::IRCode, changes::Changes)
    linfo = first(args)::MethodInstance
    linfostate = get(GLOBAL_ESCAPE_CACHE, linfo, nothing)
    args = args[2:end]
    if isnothing(linfostate)
        add_changes!(args, ir, AllEscape(), changes)
    else
        retinfo = state.ssavalues[pc] # escape information imposed on the call statement
        for i in 1:length(args)
            arg = args[i]
            arginfo = linfostate.arguments[i]
            info = from_interprocedural(arginfo, retinfo)
            push!(changes, (arg, info))
        end
    end
end

# reinterpret the escape information imposed on the callee argument (`arginfo`) in the
# context of the caller frame using the escape information imposed on the return value (`retinfo`)
function from_interprocedural(arginfo::EscapeLattice, retinfo::EscapeLattice)
    ar = arginfo.ReturnEscape
    @assert !isempty(ar) "invalid escape lattice element returned from inter-procedural context"
    newarginfo = EscapeLattice(true, NO_RETURN, arginfo.ThrownEscape, arginfo.GlobalEscape)
    if ar == ARGUMENT_RETURN
        # if this is simply passed as the call argument, we can discard the `ReturnEscape`
        # information and just propagate the other escape information
        return newarginfo
    else
        # if this can be a return value, we have to merge it with the escape information
        return newarginfo ⊔ retinfo
    end
end

function escape_call!(args::Vector{Any}, pc::Int,
                      state::EscapeState, ir::IRCode, changes::Changes)
    ft = argextype(first(args), ir, ir.sptypes, ir.argtypes)
    f = argtype_to_function(ft)
    if isa(f, Core.IntrinsicFunction)
        return false # COMBAK we may break soundness here, e.g. `pointerref`
    else
        ishandled = escape_builtin!(f, args, pc, state, ir, changes)::Union{Nothing,Bool}
    end
    isnothing(ishandled) && return false # nothing to propagate
    if !ishandled
        # if this call hasn't been handled by any of pre-defined handlers,
        # we escape this call conservatively
        add_changes!(args[2:end], ir, AllEscape(), changes)
    end
    return true
end

# TODO implement more builtins, make them more accurate
# TODO use `T_IFUNC`-like logic and don't not abuse the dispatch

escape_builtin!(@nospecialize(f), _...) = return false

escape_builtin!(::typeof(isa), _...) = return nothing
escape_builtin!(::typeof(typeof), _...) = return nothing
escape_builtin!(::typeof(Core.sizeof), _...) = return nothing
escape_builtin!(::typeof(===), _...) = return nothing

function escape_builtin!(::typeof(ifelse), args::Vector{Any}, pc::Int, state::EscapeState, ir::IRCode, changes::Changes)
    length(args) == 4 || return false
    f, cond, th, el = args
    info = state.ssavalues[pc]
    condt = argextype(cond, ir, ir.sptypes, ir.argtypes)
    if isa(condt, Const) && (cond = condt.val; isa(cond, Bool))
        if cond
            push!(changes, (th, info))
        else
            push!(changes, (el, info))
        end
    else
        push!(changes, (th, info))
        push!(changes, (el, info))
    end
    return true
end

function escape_builtin!(::typeof(tuple), args::Vector{Any}, pc::Int, state::EscapeState, ir::IRCode, changes::Changes)
    info = state.ssavalues[pc]
    info == NotAnalyzed() && (info = NoEscape())
    add_changes!(args[2:end], ir, info, changes)
    return true
end

# TODO don't propagate escape information to the 1st argument, but propagate information to aliased field
function escape_builtin!(::typeof(getfield), args::Vector{Any}, pc::Int, state::EscapeState, ir::IRCode, changes::Changes)
    info = state.ssavalues[pc]
    info == NotAnalyzed() && (info = NoEscape())
    # only propagate info when the field itself is non-bitstype
    if !isbitstype(widenconst(ir.stmts.type[pc]))
        add_changes!(args[2:end], ir, info, changes)
    end
    return true
end


end # module EscapeAnalysis
