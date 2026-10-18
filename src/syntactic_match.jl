const ϟ = nothing # match paper notation

# exact syntax tree up to wildcards
# s is subject
# p is pattern; slot variables only/guards allowed/no defslots
# return nothing (ϟ) or a dictionary of all matched wildcard variables
function syntactic_match(s, p, σ = match_dict())
    if !has_𝑋(p)
        return isequal(unwrap_const(s), unwrap_const(p)) ? σ :  ϟ
    elseif is_slot(p)
        var = varname(p)

        if haskey(σ, var)
            return (σ[var] != s) ?  ϟ : σ
        end

        pass_any_guard(p, s) || return ϟ
        return match_dict(σ, var => s)
    else
        σ′ = σ

        opₛ, opₚ = operation(s), operation(p)
        if is_𝑋(opₚ)
            σ′ = match_dict(σ′, varname(opₚ) => opₛ)
        else
            _opsym(opₛ) == opₚ || return ϟ
        end
        ss, ps = arguments(s), arguments(p)
        length(ss) == length(ps) || return ϟ
        for (sᵢ, pᵢ) ∈ zip(ss, ps)
            σ′ = syntactic_match(sᵢ,pᵢ, σ′)
            σ′ == ϟ && return ϟ
        end
        return σ′
    end
    return ϟ
end

### --- other matching
# copy of  CallableExpressions.expression_map_matched(pred, mapping, u)
# if argument, `a`, matches via `is_match` replace with `f(a)`
function map_matched(ex, is_match, f)
    T = symtype(ex)
    map_matched(T, ex, is_match, f)
end

function map_matched(T, ex, is_match, f)
    if !iscall(ex)
        return is_match(ex) ? f(ex) : ex
    else
        is_match(ex) && return f(ex)
        iscall(ex) || return ex
        children = map_matched.(arguments(ex), is_match, f)
        return sterm(T, operation(ex), children)
    end
end

# does predicate match an argument in the expression
## use
function _ismatch(ex, pred)
    if iscall(ex)
        return any(Base.Fix2(_ismatch, pred), arguments(ex))
    elseif isexpr(ex)
        return any(Base.Fix2(_ismatch, pred), children(ex))
    end
    pred(ex)
end

# if expression operation, `op`, matches via `is_match` replace with `f(op)`
function map_matched_head(ex, is_match, f)
    T = symtype(ex)
    map_matched_head(T, ex, is_match, f)
end

function map_matched_head(T, ex, is_match, f)
    !iscall(ex) && return ex
    op = operation(ex)
    is_match(op) && (op = f(op))
    args′ = map_matched_head.(arguments(ex), is_match, f)
    return sterm(T, op, args′)
end

# does predicate match an operation in the expression
function _ismatchhead(ex, pred)
    if iscall(ex)
        pred(operation(ex)) && return true
        return any(Base.Fix2(_ismatchhead, pred), arguments(ex))
    elseif isexpr(ex)
        pred(head(ex)) && return true
        return any(Base.Fix2(_ismatchhead, pred), children(ex))
    end
    pred(ex)
end
