# utils for matching

# These may need extensions to use with other packages; eg cf replace.jl

# if x is a wrapped constant number, unwrap it. Otherwise return x
# Might need call like
# AssociativeCommutativePatternMatching.unwrap_const(x::Basic) = SymEngine.unwrap_const(x)
unwrap_const(x::Any) = _unwrap_const(x)


# cases for expression types
_unwrap_const(x) = x
_unwrap_const(x::Number) = x
function _unwrap_const(x::Symbol)
    x ∈ (:π, :pi) && return MathConstants.pi
    x ∈ (:ℯ, :e, ) && return MathConstants.ℯ
    x ∈ (:φ, :golden) && return MathConstants.golden
    x ∈ (:γ, :eulergamma) && return MathConstants.eulergamma
    x == :catalan && return MathConstants.catalan
    return x
end
_unwrap_const(x::Expr) = _isnumber(x) ? eval(x) : x

# check if value holds a number
_isnumber(::Any) = false
_isnumber(x::Number) = true
_isnumber(x::Symbol) = x ∈ (:π, :pi, :ℯ, :e, :φ, :golden, :γ, :eulergamma, :catalan)
_isnumber(x::Expr) = !(_ismatch(x, !_isnumber))

## ----- substitution mapping stored in a dictionary -----
# A substitution is a collection of pairs 𝑋 -> 𝐺
# an empty dictionary is a match
# when there is no match, `nothing` is used
# an empty container of matches indicates no matches

const ∅ = ()
const MatchDict = Base.ImmutableDict{Symbol, Any}

match_dict() = MatchDict()

function match_dict(kvs::Pair...)
    σ = MatchDict()
    match_dict(σ, kvs...)
end

function match_dict(σ::MatchDict, kvs::Pair...)
    for (k,v) ∈ kvs
        v = isa(v,Number) ? _unwrap_const(v) : v
        if haskey(σ, k)
            σ[k] != v && error("repeated key with different value: $k => $v ($(σ[k]))")
        else
            σ = MatchDict(σ, k, v)
        end
    end
    σ
end

#  σ △ σ′ (\bigtriangleup) for every x in the intersection of the domains has same value
function iscompatible(σ::MatchDict, σ′::MatchDict)
    isempty(σ) && return true
    isempty(σ′) && return true
    for k in keys(σ)
            if haskey(σ′, k) # intersect(keys(σ), keys(σ′)) allocates
            isequal(σ[k], σ′[k]) || return false
        end
    end
    return true
end

# σ ⊔ σ′ (\sqcup) is union of two compatible matches
function merge_match(σ::MatchDict, σ′::MatchDict)
    # assume compatible
    for (k,v) ∈ σ′
        σ = match_dict(σ, k => v)
    end
    σ
end
merge_match(σ::Tuple, σ′::MatchDict) = σ′

function union_merge(θ, σ′::MatchDict)
    (merge_match(σ, σ′) for σ ∈ θ if iscompatible(σ, σ′))
end

function union_merge(θ, θ′)
    (merge_match(σ, σ′) for σ ∈ θ for σ′ ∈ θ′ if iscompatible(σ, σ′))
end

## utils
_isone(x) = isequal(x, 1)
_groupby(pred, t) = (t = filter(pred,t), f=filter(!pred, t))



## Expression related methods
_is_operation(op) = ex -> iscall(ex) && operation(ex) ∈ (op, Symbol(op))

# need to compare x and p when p is from an expression
# trick -- SymEngine.Basic <: Number
# compare Number, Expr, Irrational, Symbol

eq_expr(a::Any, b::Any) = isequal(unwrap_const(a), unwrap_const(b))
eq_expr(a::Expr, b::Expr) = !isnothing(syntactic_match(unwrap_const(a), unwrap_const(b)))


# create a term for a pattern (pterm) or a subject (sterm)
# the former is only for expressions
# the latter might involve a symbolic type
function pterm(op::Union{Expr,Symbol}, args; elide=true)
    if elide && length(args) == 1 && op ∈(:+, :*, :^, :/)
        return only(args)
    else
        return maketerm(Expr, :call, (op, args...), nothing)
        #Expr(:call, op, args...)
    end
end

# symbolic type

# to pass to maketerm (sterm)
# Might want to do something like
# AssociativeCommutativePatternMatching.symtype(::SymEngine.Basic) = SymEngine.Basic
symtype(::Real) = Expr
symtype(::Symbol) = Expr
symtype(::Expr) = Expr
symtype(::T) where T = T

function sterm(op, args)
    S = symtype(first(args))
    sterm(S, op, args)
end

# construct term of abstract type S from op and args
function sterm(S, op, args)
    if S == Expr
        !isa(op, Union{Expr, Symbol}) && (op = nameof(op))
        return pterm(op, args)
    end

    if isa(op, Symbol)
        for M ∈ (@__MODULE__, Main, Base)
            if isdefined(M, op)
                op = getfield(M, op)
                break
            end
        end
        isa(op, Symbol) && (op = Core.eval(Main, op))
    elseif isa(op, Expr)
        for M ∈ (@__MODULE__, Main, Base)
            try
                op = Core.eval(M, op)
                break
            catch err
                # fall through if the expression is not yet resolvable in this module
            end
        end
    end

    maketerm(S, op, args, nothing)
end


# invert an expr to regularize a/b --> a*b^{-1}
function _invert_expr(pat)
    if isa(pat, Integer)
        return pterm(:^, (pat, -1.0))
    elseif is_operation(:(//))(pat)
        u,v = arguments(pat)
        u′ = isa(u, Number) ? -u : pterm(:*, (u,-1))
        return pterm(:(//), (u′, v))
    else
        return pterm(:^, (pat, -1))
    end
end

# --- basic total order, can override for other types
<ₑ(x::Symbol, y::Symbol) = x < y
<ₑ(x::Any, y::Any) = <ₑ(Symbol(x), Symbol(y))


# ----- predicates
_is_rational(x) = isa(_unwrap_const(x), Rational)

# can override, say with :Symbol
iscommutative(op) = op ∈ (:+, :*, +, *)
isassociative(op) = op ∈ (:+, :*, +, *)

isassociative(::typeof(+)) = true
isassociative(::typeof(*)) = true

iscommutative(::typeof(+)) = true
iscommutative(::typeof(*)) = true

# check for wildcard variables
is_𝑋(x::Any) = false
has_𝑋(x::Any) = false
is_slot(x::Any) = false
is_defslot(x::Any) = false
is_segment(x::Any) = false
is_plus(x::Any) = false
is_op(x::Any) = false

# Expr
is_𝑋(x::Expr) = (iscall(x) && operation(x) === :(~))  ||
    ((!iscall(x) && isexpr(x)) && head(x) != :... && is_𝑋(first(x.args)))

function has_𝑋(x::Expr)
    is_𝑋(x) && return true
    !iscall(x) && return false
    is_𝑋(operation(x)) && return true
    any(has_𝑋, arguments(x))
end

function is_slot(x::Expr)
    is_𝑋(x) || return false
    _, x = x.args
    iscall(x) && return false
    return true
end

function is_defslot(x::Expr)

    is_𝑋(x) || return false
    _, arg = x.args
    is_operation(:(!))(arg) && return true

    return false
end

has_defslot(::Any) = false
function has_defslot(x::Expr)
    return is_defslot(x) ||
        (is_operation(:^)(x) && is_defslot(last(arguments(x))))
end

is_slot_or_defslot(x) = is_slot(x) || is_defslot(x)

function is_segment(x::Expr)
    is_𝑋(x) || return false # first is ~
    h,x = x.args
    is_𝑋(h) && return false # an op
    is_𝑋(x) || return false # second is ~
    _, x = x.args
    is_𝑋(x) && return false
    return true
end

# ~~~x (1 or more)
function is_plus(x::Expr)
    is_𝑋(x) || return false
    _,x = x.args
    is_𝑋(x) || return false
    _,x = x.args
    is_𝑋(x) || return false
    return true
end

# (~G)(~x)
function is_op(x::Expr)
    is_𝑋(x) && iscall(x) && is_𝑋(operation(x))
end


## ------
const defslot_op_map = Dict(:+ => 0, :* => 1, :^ => 1, :/ => 1)

# return symbol holding variable name
varname(x::Symbol) = x
function varname(x::Expr)
    iscall(x) && !(x.args[1] ∈ (:~, :!)) && throw(ArgumentError("$x is not a wild card variable"))
    if x.args[1] ∈ (:~, :!)
        varname(x.args[2])
    else
        varname(x.args[1])
    end
end

## -- work with guards
# return true *if* either var has no predicate or
# predicate(data) is true
# use like pass_any_guard(var, data) || return ∅
function pass_any_guard(var, data)
    !has_predicate(var) && return true

    pred = get_predicate(var)
    pred_fn = pred

    if pred isa Symbol
        for M ∈ (@__MODULE__, Main, Base)
            if isdefined(M, pred)
                pred_fn = getfield(M, pred)
                break
            end
        end
    elseif pred isa Expr
        for M ∈ (@__MODULE__, Main, Base)
            try
                pred_fn = Core.eval(M, pred)
                break
            catch err
                # fall through if this expression is not yet resolvable in the current scope
            end
        end
    end

    # Avoid re-evaluating user predicates repeatedly when they are already callables.
    if pred_fn isa Function
        return try
            Base.invokelatest(pred_fn, _unwrap_const(data))
        catch err
            false
        end
    end

    # Fallback for unusual dynamic forms.
    try
        return Base.invokelatest(eval(pred), _unwrap_const(data))
    catch err
        try
            return invokelatest(Main.eval(pred), _unwrap_const(data))
        catch err
            false
        end
    end
end

# Does wildcard have a predicate?
has_predicate(x::Symbol)::Bool = false
function has_predicate(x::Expr)::Bool
    if x.args[1] ∈ (:~, :!)
        has_predicate(x.args[2])
    else
        length(x.args) == 2 && x.head==:(::)
    end
end

# get_predicate. Assumes user has called `has_predicate` and got TRUE
get_predicate(x::Symbol) = :nothing
function get_predicate(x::Expr)
    if x.args[1] ∈ (:~, :!)
        get_predicate(x.args[2])
    else
        x.args[2]
    end
end
