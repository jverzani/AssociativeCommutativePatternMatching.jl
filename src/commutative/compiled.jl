## ---- compiled patterns -----

#=
A pattern compiled for the commutative matcher. `check_expr_r` examines the
pattern each time it is called: is it a slot, does it have a defslot or a
segment, is its operation commutative, which forms of a power apply, ... A
`CompiledPattern` records the answers once, and `_cm` takes the same steps as
`check_expr_r`, in the same order, so the matches are the same, in the same
order. Steps which are rare in practice (segments among several arguments,
a lone segment argument, rationals) call the functions of rule2a.jl with
the original pattern.
=#

# made by `compile_pattern`
Base.@kwdef struct CompiledPattern
    kind::Symbol            # :real, :sym, :fallback, :opslot, :slot, :fail, :defslot, :onlyseg, :call
    pat::Any                # the pattern
    op::Any = nothing       # operation of a call
    args::Vector{CompiledPattern} = CompiledPattern[] # its arguments, compiled
    argexprs::Vector{Any} = Any[] # and as patterns
    # as checked by `ceoaa`
    allslots::Bool = false  # all arguments wildcards, none an operation
    nseg::Int = 0
    nslot::Int = 0
    anyseg::Bool = false
    anyplus::Bool = false
    # a call
    commutative::Bool = false
    order::Vector{Int} = Int[] # order in which `check_commutative` matches the arguments
    rational::Bool = false  # op is //
    power::Bool = false     # op is ^, sqrt or exp
    neim::Bool = false      # a product with a power: a quotient may match
    rap::Vector{CompiledPattern} = CompiledPattern[] # for op /, `_rule_as_powers`
    raporder::Vector{Int} = Int[]
    divpow::Union{Nothing, CompiledPattern} = nothing # for op /, the rule as a power
    # a slot, or (~F)(...)
    var::Symbol = :_
    istuple::Bool = false   # a segment slot binds a tuple
    haspred::Bool = false
    pred::Any = nothing
    # a defslot
    newr::Union{Nothing, CompiledPattern} = nothing
    rest::Union{Nothing, CompiledPattern} = nothing
    defvar::Symbol = :_
    defval::Any = nothing
end

Base.show(io::IO, c::CompiledPattern) = print(io, "compile_pattern(", c.pat, ")")

"""
    compile_pattern(pat)

A pattern compiled for the commutative matcher: the questions `_ceachmatch`
asks of the pattern at each call are answered once. Use it in place of the
pattern in `_ceachmatch` or `_cmatch`; the matches are the same. A rule made
by [`@rule`](@ref) compiles its pattern.
"""
function compile_pattern end
compile_pattern(c::CompiledPattern) = c
function compile_pattern(pat)
    isa(pat, Real) && return CompiledPattern(kind = :real, pat = pat)
    isa(pat, Symbol) && return CompiledPattern(kind = :sym, pat = pat)
    (isa(pat, Expr) && iscall(pat)) || return CompiledPattern(kind = :fallback, pat = pat)

    opᵣ = operation(pat)
    if is_𝑋(opᵣ) # (~F)(...)
        args = arguments(pat)
        if length(args) == 1
            # `check_expr_r` continues with the argument, after the step for (~F)
            a = only(args)
            (isa(a, Expr) && iscall(a) && !is_𝑋(operation(a))) ||
                return CompiledPattern(kind = :fallback, pat = pat)
        end
        return CompiledPattern(; kind = :opslot, pat, var = varname(opᵣ),
                               _arguments(args)...)
    end
    _compile_rest(pat)
end

# the arguments, and what `ceoaa` checks of them
function _arguments(argexprs)
    argexprs = collect(Any, argexprs)
    (args = CompiledPattern[compile_pattern(a) for a ∈ argexprs],
     argexprs = argexprs,
     allslots = all(is_𝑋, argexprs) && !any(is_op, argexprs),
     nseg = count(is_segment, argexprs),
     nslot = count(is_slot, argexprs),
     anyseg = any(is_segment, argexprs),
     anyplus = any(is_plus, argexprs))
end

_order(argexprs) = sortperm(collect(eachindex(argexprs)); by = i -> _commutative_priority(argexprs[i]))

# the steps of `check_expr_r` after the one for (~F)
function _compile_rest(pat)
    if is_𝑋(pat)
        tuple = is_segment(pat) || is_plus(pat)
        return CompiledPattern(; kind = :slot, pat, var = varname(pat), istuple = tuple,
                               haspred = has_predicate(pat),
                               pred = has_predicate(pat) ? get_predicate(pat) : nothing)
    end

    op, args = operation(pat), arguments(pat)
    i = findfirst(is_defslot, args)
    if i !== nothing # as `has_defslot`
        op ∈ (:^, :/) && i == 1 && return CompiledPattern(kind = :fail, pat = pat)
        ps = copy(args)
        qᵢ = :(~$(ps[i].args[2].args[2]))
        ps[i] = qᵢ
        newr = Expr(:call, op, ps...)
        deleteat!(ps, i)
        return CompiledPattern(; kind = :defslot, pat,
                               newr = compile_pattern(newr),
                               rest = compile_pattern(pterm(op, ps)),
                               defvar = varname(qᵢ),
                               defval = get(defslot_op_map, op, -1))
    end

    if length(args) == 1 && (is_segment(first(args)) || is_plus(first(args)))
        return CompiledPattern(kind = :onlyseg, pat = pat)
    end

    # a quotient is matched in other forms, which need its two parts
    op === :/ && length(args) != 2 && return CompiledPattern(kind = :fallback, pat = pat)

    a = _arguments(args)
    kw = (; kind = :call, pat, op, a...,
          commutative = iscommutative(op), order = _order(a.argexprs),
          rational = op == ://, power = op ∈ (:^, :sqrt, :exp),
          neim = op === :* && any(is_operation(:^), args))
    op === :/ || return CompiledPattern(; kw...)
    rap = collect(Any, _rule_as_powers(pat))
    CompiledPattern(; kw..., rap = CompiledPattern[compile_pattern(r) for r ∈ rap],
                    raporder = _order(rap), divpow = compile_pattern(_div_as_power(pat)))
end

# the rule `a / b` as a power, as in the (/, ^) case of `different_powers`
function _div_as_power(rule)
    a, b = arguments(rule)
    if is_operation(:^)(b) # combine exponents
        u, v = arguments(b)
        if is_operation(:(//))(v)
            n,d = arguments(v)
            v′ = pterm(:(//), (-n, d))
        elseif !isa(u, Integer) && isa(v, Number)
            v′ = -v
        else
            v′ = pterm(:*, (v, -1.0))
        end
        b′ = pterm(:^, (u, v′))
    elseif is_operation(:sqrt)(b) # 1/sqrt(u) is u^(-1//2)
        b′ = pterm(:^, (only(arguments(b)), -1//2))
    else
        b′ = Expr(:call, :^, b, -1)
    end
    (isa(a, Number) && isone(a)) ? b′ : Expr(:call, :*, a, b′)
end

## ---- matching: the steps of `check_expr_r` -----

_ceachmatch(c::CompiledPattern, sub) = _cm(c, sub, [MatchDict()], false)
function _cmatch(c::CompiledPattern, sub)
    σs = _cm(c, sub, [MatchDict()], true)
    isempty(σs) ? nothing : first(σs)
end

function _cm(c::CompiledPattern, @nospecialize(data), σs::𝑀, once::Bool)::𝑀
    k = c.kind
    k === :real && return eq_expr(c.pat, data) ? σs : NO_MATCH
    k === :sym && return eq_expr(data, c.pat) ? σs : NO_MATCH
    k === :fallback && return check_expr_r(data, c.pat, σs, once)
    if k === :opslot
        !iscall(data) && return MatchDict[]
        σs = merge_vectors_of_matches(σs, match_dict(c.var => operation(data)))
        arg_data = arguments(data)
        length(arg_data) > 1 && return _c_ceoaa(c, arg_data, σs, once)
        return _cm_rest(only(c.args), isempty(arg_data) ? arg_data : only(arg_data), σs, once)
    end
    _cm_rest(c, data, σs, once)
end

function _cm_rest(c::CompiledPattern, @nospecialize(data), σs::𝑀, once::Bool)::𝑀
    k = c.kind
    k === :slot && return _c_just_variable(c, data, σs, once)
    k === :fail && return MatchDict[]
    if k === :defslot
        σ′s = _cm(c.newr::CompiledPattern, data, σs, once)
        σ′s != MatchDict[] && return σ′s # had a match
        σs = _cm(c.rest::CompiledPattern, data, σs, false)
        σs == MatchDict[] && return MatchDict[]
        return _merge_single_expr(σs, c.defvar, c.defval)
    end
    k === :onlyseg && return only_argument_is_segment(data, c.pat, σs)

    # a call
    c.rational && _is_rational(data) && return has_rational(data, c.pat, σs)
    !iscall(data) && return NO_MATCH
    opₛ = _opsym(operation(data))
    if c.power || (c.op === :/ && opₛ ∈ (:^, :*, :/))
        return _c_different_powers(c, data, opₛ, σs, once)
    end

    arg_data = arguments(data)
    neim = c.neim && opₛ === :/
    neim && (arg_data = _data_as_powers(data))
    opₛ != c.op && !neim && return NO_MATCH

    c.anyseg && return has_any_segment(opₛ, arg_data, c.op, c.argexprs, σs)
    c.anyplus && return has_any_plus(opₛ, arg_data, c.op, c.argexprs, σs)

    length(arg_data) != length(c.args) && return MatchDict[]
    if c.commutative
        σ′s = _c_check_commutative(c.args, c.order, arg_data, σs, once)
        return isempty(σ′s) ? NO_MATCH : σ′s
    end
    return _c_ceoaa(c, arg_data, σs, once)
end

# as `ceoaa`, with the arguments of `c`
function _c_ceoaa(c::CompiledPattern, arg_data, σs::𝑀, once::Bool)::𝑀
    if c.allslots
        iszero(c.nseg) && c.nslot != length(arg_data) && return NO_MATCH
    end
    σs == NO_MATCH && return NO_MATCH
    c.anyseg && return has_any_segment(nothing, arg_data, nothing, c.argexprs, σs)
    c.anyplus && return has_any_plus(nothing, arg_data, nothing, c.argexprs, σs)
    σ′s = σs
    n = min(length(arg_data), length(c.args))
    for i ∈ 1:n
        σ′s = _cm(c.args[i], arg_data[i], σ′s, once && i == n) # later arguments may reject a match
        σ′s == NO_MATCH && return NO_MATCH
    end
    return σ′s
end

# σ with var => val, for a new var: `match_dict(σ, var => val)` without the
# allocations of its general signature
_bind(σ::MatchDict, var::Symbol, @nospecialize(val)) =
    MatchDict(σ, var, isa(val, Number) ? unwrap_const(val) : val)

# as `just_variable`
function _c_just_variable(c::CompiledPattern, @nospecialize(data), σs::𝑀, once::Bool)::𝑀
    var = c.var
    val = c.istuple ? (data,) : data
    isempty(σs) && return NO_MATCH
    ms = MatchDict[]
    for σ ∈ σs
        if haskey(σ, var) # if the slot has already been matched
            isequal(σ[var], val) && push!(ms, σ)
        else
            c.haspred && !_evalguard(c.pred, val) && continue
            push!(ms, _bind(σ, var, val))
        end
        once && !isempty(ms) && break
    end
    return isempty(ms) ? NO_MATCH : ms
end

# as `check_commutative`
function _c_check_commutative(args::Vector{CompiledPattern}, order, arg_data, σs::𝑀, once::Bool)::𝑀
    length(arg_data) != length(args) && return NO_MATCH
    used = falses(length(arg_data))
    σ′′s = MatchDict[]
    _c_check_commutative!(σ′′s, used, arg_data, args, order, 1, σs, once)
    return isempty(σ′′s) ? NO_MATCH : σ′′s
end

function _c_check_commutative!(out, used, arg_data, args, order, k, σs::𝑀, once::Bool)::𝑀
    σs == NO_MATCH && return out
    k > length(order) && return _append_unique!(out, σs)
    pat = args[order[k]]
    for j ∈ eachindex(arg_data)
        used[j] && continue
        val = arg_data[j]
        # try only the first of equal unused values, as in `_check_commutative!`
        isdup = false
        for jj ∈ 1:(j - 1)
            if !used[jj] && _cheap_isequal(arg_data[jj], val)
                isdup = true
                break
            end
        end
        isdup && continue

        σ′s = _cm(pat, val, σs, once && k == length(order)) # later patterns may reject a match
        σ′s == NO_MATCH && continue
        used[j] = true
        _c_check_commutative!(out, used, arg_data, args, order, k + 1, σ′s, once)
        used[j] = false
        once && !isempty(out) && break
    end
    return out
end

# as `different_powers`
function _c_different_powers(c::CompiledPattern, @nospecialize(data), opₛ, σs::𝑀, once::Bool)::𝑀
    opᵣ = c.op
    arg_data = arguments(data)
    b = first(arg_data)

    if opᵣ === :^
        if (opₛ === :^) # try first normal checks
            σ′s = _c_ceoaa(c, arg_data, σs, once)
            !isempty(σ′s) && return σ′s
        end
        fad = Vector{Any}(undef, 2)
        is1divsmth = (opₛ == :/) && isequal(1, _unwrap_const(first(arg_data)))
        if is1divsmth && _is_operation(^)(arg_data[2]) # 1/(...)^(...)
            m = arg_data[2]
            fad[1] = arguments(m)[1]
            fad[2] = -1*arguments(m)[2]
        elseif is1divsmth && _is_operation(sqrt)(arg_data[2]) # 1/sqrt(...)
            m = arg_data[2]
            fad[1] = arguments(m)[1]
            fad[2] = -1//2
        elseif is1divsmth && _is_operation(exp)(arg_data[2]) # 1/exp(...)
            m = arg_data[2]
            fad[1] = ℯ
            fad[2] = sterm(-, (first(arguments(m)),))
        elseif is1divsmth # 1/(...)
            fad[1] = arg_data[2]
            fad[2] = -1
        elseif (opₛ === :^) && iscall(b) && (_opsym(operation(b)) === :/) && _isone(arguments(b)[1])
            # (1/...)^(...)
            fad[1] = arguments(b)[2]
            fad[2] = -1*arg_data[2]
        elseif opₛ === :exp
            fad[1] = ℯ
            fad[2] = b
        elseif opₛ === :sqrt
            fad[1] = b
            fad[2] = 1//2
        else
            return MatchDict[]
        end
        return _c_ceoaa(c, fad, σs, once)

    elseif opᵣ === :sqrt
        if (opₛ === :sqrt)
            tocheck = arg_data
        # `isequal`, not `∈`: `==` need not return a Bool for a symbolic exponent
        elseif (opₛ === :^) && any(isequal(_unwrap_const(arg_data[2])), (1//2, :(1//2)))
            tocheck = (b,)
        else
            return MatchDict[]
        end
        return _c_ceoaa(c, tocheck, σs, once)

    elseif opᵣ === :exp
        if (opₛ === :exp)
            tocheck = arg_data
        elseif (opₛ === :^) && (_unwrap_const(b) ∈ (ℯ,:ℯ))
            tocheck = (arg_data[2],)
        else
            return MatchDict[]
        end
        return _c_ceoaa(c, tocheck, σs, once)

    elseif (opᵣ, opₛ) == (:/, :*)
        return _c_check_commutative(c.rap, c.raporder, arg_data, σs, once)

    elseif (opᵣ, opₛ) == (:/, :/)
        # both as quotients and as products of powers; see `different_powers`
        σ′s = _c_ceoaa(c, arg_data, σs, once)
        once && !isempty(σ′s) && return σ′s
        σ″s = _c_check_commutative(c.rap, c.raporder, _data_as_powers(data), σs, once)
        return unique!(vcat(σ′s, σ″s))

    elseif (opᵣ, opₛ) == (:/, :^)
        return _cm(c.divpow::CompiledPattern, data, σs, once)
    end
    return NO_MATCH
end
