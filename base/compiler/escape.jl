module EscapeAnalysis

export find_escapes!

import Core:
    SimpleVector, GotoNode, GotoIfNot, Argument, IntrinsicFunction, Const, sizeof

import ..Compiler:
    Vector, IdDict, MethodInstance, IRCode, SSAValue, PiNode, PhiNode,
    PhiCNode, UpsilonNode, ReturnNode, IR_FLAG_EFFECT_FREE,
    ==, !, !==, !=, ≠, :, ≤, &, |, +, -, *, <, <<,
    isbitstype, ismutabletype, widenconst, argextype, argtype_to_function, isexpr,
    is_meta_expr_head, copy, zip, empty!, length, get, first, isassigned, push!, isempty,
    @assert, @nospecialize

isnothing(x) = x === nothing

abstract type EscapeInformation end

struct NoInformation <: EscapeInformation end
struct NoEscape      <: EscapeInformation end
struct ReturnEscape  <: EscapeInformation end
struct Escape        <: EscapeInformation end

==(x::EscapeInformation, y::EscapeInformation) = x === y

⊑(x::EscapeInformation, y::EscapeInformation) = x === y
⊑(::Escape,             ::EscapeInformation)  = true
⊑(::EscapeInformation,  ::NoInformation)      = true
⊑(::Escape,             ::NoInformation)      = true # avoid ambiguity
⊑(::ReturnEscape,       ::NoEscape)           = true

⊔(x::EscapeInformation, y::EscapeInformation) = x⊑y ? y : y⊑x ? x : NoInformation()
⊓(x::EscapeInformation, y::EscapeInformation) = x⊑y ? x : y⊑x ? y : Escape()

# extend lattices of escape information to lattices of mappings of arguments and SSA stmts to escape information
# ⊓ and ⊔ operate pair-wise, and from there we can just rely on the Base implementation for dictionary equality comparison
struct EscapeState
    arguments::Vector{EscapeInformation}
    ssavalues::Vector{EscapeInformation}
end
function EscapeState(nslots::Int, nargs::Int, nstmts::Int)
    arguments = EscapeInformation[
        i ≤ nargs ? ReturnEscape() : NoEscape() for i in 1:nslots]
    ssavalues = EscapeInformation[NoInformation() for _ in 1:nstmts]
    return EscapeState(arguments, ssavalues)
end
copy(s::EscapeState) = EscapeState(copy(s.arguments), copy(s.ssavalues))

⊔(X::EscapeState, Y::EscapeState) = EscapeState(
    EscapeInformation[x ⊔ y for (x, y) in zip(X.arguments, Y.arguments)],
    EscapeInformation[x ⊔ y for (x, y) in zip(X.ssavalues, Y.ssavalues)])
⊓(X::EscapeState, Y::EscapeState) = EscapeState(
    EscapeInformation[x ⊓ y for (x, y) in zip(X.arguments, Y.arguments)],
    EscapeInformation[x ⊓ y for (x, y) in zip(X.ssavalues, Y.ssavalues)])
==(X::EscapeState, Y::EscapeState) = X.arguments == Y.arguments && X.ssavalues == Y.ssavalues

# const GLOBAL_ESCAPE_CACHE = IdDict{MethodInstance,EscapeState}()
# __clear_escape_cache!() = empty!(GLOBAL_ESCAPE_CACHE)

# An escape analysis implementation based on the algorithm described in the paper [MM02].
# The analysis works on the lattice of `EscapeInformation` and transitions lattice elements
# from the top to the bottom in a backward way, i.e. data flows from usage cites to definitions.
#
# [MM02] A Graph-Free approach to Data-Flow Analysis.
#        Markas Mohnen, 2002, April.
#        https://api.semanticscholar.org/CorpusID:28519618

const Changes = Vector{Tuple{Any,EscapeInformation}}
const IR_FLAG_NO_ESCAPE = 0x01 << 5

# TODO
# - implement more builtin handling
# - (related to above) do alias analysis to some extent
# - maybe flow-sensitivity (with sparse analysis state)
function find_escapes!(ir::IRCode, nargs::Int)
    (; stmts, sptypes, argtypes) = ir
    nstmts = length(stmts)
    state = EscapeState(length(ir.argtypes), nargs, nstmts) # flow-insensitive, only manage a single state

    # if length(argtypes) ≠ 0
    #     Core.println("analyzing... ", argtypes[1], " ", length(argtypes), " ", nstmts)
    # end
    while true
        local anyupdate = false
        local changes = Changes()

        for pc in nstmts:-1:1
            stmt = stmts.inst[pc]

            # inliner already computed effect-freeness of this statement (whether it may throw or not)
            # and if it may throw, we conservatively escape all the arguments
            is_effect_free = stmts.flag[pc] & IR_FLAG_EFFECT_FREE ≠ 0

            # collect escape information
            if isa(stmt, Expr)
                head = stmt.head
                if head === :call # TODO implement more builtins, make them more accurate
                    if !is_effect_free
                        # TODO we can have a look at builtins.c and limit the escaped arguments if any of them are not captured in the thrown exception
                        add_changes!(stmt.args[2:end], ir, Escape(), changes)
                    else
                        escape_call!(stmt.args, pc, state, ir, changes) || continue
                    end
                elseif head === :invoke
                    # linfo = first(stmt.args)
                    # escapes_for_call = get(GLOBAL_ESCAPE_CACHE, linfo, nothing)
                    # if isnothing(escapes_for_call)
                    # TODO: (Xuanda) fix call cache
                        add_changes!(stmt.args[3:end], ir, Escape(), changes)
                    # else
                    #     for (arg, info) in zip(stmt.args[2:end], escapes_for_call.arguments)
                    #         if info === ReturnEscape()
                    #             info = NoEscape()
                    #         end
                    #         push!(changes, (arg, info))
                    #     end
                    # end
                # elseif head === :invoke
                #     linfo = first(stmt.args)
                #     escapes_for_call = get(GLOBAL_ESCAPE_CACHE, linfo, nothing)
                #     if isnothing(escapes_for_call)
                #         add_changes!(stmt.args[3:end], ir, Escape(), changes)
                #     else
                #         for (arg, info) in zip(stmt.args[2:end], escapes_for_call.arguments)
                #             if info === ReturnEscape()
                #                 info = NoEscape()
                #             end
                #             push!(changes, (arg, info))
                #         end
                #     end
                elseif head === :new
                    info = state.ssavalues[pc]
                    info === NoInformation() && (info = NoEscape())
                    for arg in stmt.args[2:end]
                        push!(changes, (arg, info))
                    end
                    push!(changes, (SSAValue(pc), info)) # we will be interested in if this allocation is not escape or not
                elseif head === :splatnew
                    info = state.ssavalues[pc]
                    info === NoInformation() && (info = NoEscape())
                    # splatnew passes field values using a single tuple (args[2])
                    push!(changes, (stmt.args[2], info))
                    push!(changes, (SSAValue(pc), info)) # we will be interested in if this allocation is not escape or not
                elseif head === :(=)
                    lhs, rhs = stmt.args
                    if isa(lhs, GlobalRef)
                        add_change!(rhs, ir, Escape(), changes)
                    end
                elseif head === :cfunction
                    # for :cfunction we conservatively escapes all its arguments
                    add_changes!(stmt.args, ir, Escape(), changes)
                elseif head === :foreigncall
                    # for foreigncall we simply escape every argument (args[6:length(args[3])])
                    # and its name (args[1])
                    # TODO: we can apply similar strategy like builtin calls
                    #       to specialize some foreigncalls
                    foreigncall_nargs = length((stmt.args[3])::SimpleVector)
                    push!(changes, (stmt.args[1], Escape()))
                    add_changes!(stmt.args[6:5+foreigncall_nargs], ir, Escape(), changes)
                elseif is_meta_expr_head(head)
                    continue
                elseif head === :static_parameter
                    # static_parameter reference static parameter using index
                    continue
                elseif head === :copyast
                    # copyast simply copies a surface syntax AST
                    continue
                elseif head === :undefcheck
                    # undefcheck is temporarily inserted by compiler
                    # it will be processd be later pass so it won't change any of escape states
                    continue
                elseif head === :throw_undef_if_not
                    # conservatively escapes the val argument (argument[1])
                    add_change!(stmt.args[1], ir, Escape(), changes)
                elseif head === :the_exception
                    continue
                elseif head === :isdefined
                    continue
                elseif head === :enter || head === :leave || head === :pop_exception
                    continue
                elseif head === :gc_preserve_begin || head === :gc_preserve_end
                    continue
                else # TODO: this is too conservative
                    add_changes!(stmt.args, ir, Escape(), changes)
                end
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
                    add_change!(stmt.val, ir, ReturnEscape(), changes)
                end
            else
                @assert stmt isa GotoNode || stmt isa GotoIfNot || stmt isa GlobalRef || isnothing(stmt) # TODO remove me
                continue
            end

            isempty(changes) && continue

            # propagate changes
            new = copy(state)
            for (x, info) in changes
                if isa(x, Argument)
                    new.arguments[x.n] = new.arguments[x.n] ⊓ info
                elseif isa(x, SSAValue)
                    new.ssavalues[x.id] = new.ssavalues[x.id] ⊓ info
                end
            end
            empty!(changes)

            # convergence check and worklist update
            if new ≠ state
                state = new

                anyupdate |= true
            end
        end

        anyupdate || break
    end

    for pc in 1:nstmts
        # heap-to-stack optimization are carried for heap-allocated objects that are not escaped
        if isexpr(stmts.inst[pc], :new) && ismutabletype(widenconst(stmts.type[pc])) && state.ssavalues[pc] === NoEscape()
            stmts.flag[pc] |= IR_FLAG_NO_ESCAPE
        end
    end

    return state
end

function add_changes!(args::Vector{Any}, ir::IRCode, @nospecialize(info::EscapeInformation), changes::Changes)
    for x in args
        add_change!(x, ir, info, changes)
    end
end

function add_change!(@nospecialize(x), ir::IRCode, @nospecialize(info::EscapeInformation), changes::Changes)
    if !isbitstype(widenconst(argextype(x, ir, ir.sptypes, ir.argtypes)))
        push!(changes, (x, info))
    end
end

function escape_call!(args::Vector{Any}, pc::Int, state::EscapeState, ir::IRCode, changes::Changes)
    ft = argextype(first(args), ir, ir.sptypes, ir.argtypes)
    f = argtype_to_function(ft)
    if isa(f, Core.IntrinsicFunction)
        ishandled = nothing # XXX we may break soundness here, e.g. `pointerref`
    else
        ishandled = escape_builtin!(f, args, pc, state, ir, changes)::Union{Nothing,Bool}
    end
    isnothing(ishandled) && return false # nothing to propagate
    if !ishandled
        # if this call hasn't been handled by any of pre-defined handlers,
        # we escape this call conservatively
        add_changes!(args[2:end], ir, Escape(), changes)
    end
    return true
end

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
    if isa(condt, Const) && isa(condt.val, Bool)
        if condt.val
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
    info === NoInformation() && (info = NoEscape())
    # TODO: we may want to remove this check when we implement the alias analysis
    add_changes!(args[2:end], ir, info, changes)
    return true
end

# TODO don't propagate escape information to the 1st argument, but propagate information to aliased field
function escape_builtin!(::typeof(getfield), args::Vector{Any}, pc::Int, state::EscapeState, ir::IRCode, changes::Changes)
    info = state.ssavalues[pc]
    info === NoInformation() && (info = NoEscape())
    rt = widenconst(ir.stmts.type[pc])
    # Only propagate info when the field itself is non-bitstype
    # TODO: we may want to remove this check when we implement the alias analysis
    if !isbitstype(rt)
        add_changes!(args[2:end], ir, info, changes)
    end
    return true
end

end # module EscapeAnalysis
