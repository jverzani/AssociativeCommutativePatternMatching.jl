# utils for matching

# These may need extensions to use with other packages; eg cf replace.jl

# if x is a wrapped constant number, unwrap it. Otherwise return x
# Might need call like
# AssociativeCommutativePatternMatching.unwrap_const(x::Basic) = SymEngine.unwrap_const(x)
unwrap_const(x::Any) = x
function unwrap_const(x::Symbol)
    if hasproperty(Base.MathConstants, x)
        return getproperty(Base.MathConstants, x)
    end
    x == :twoπ && return 2π
    x == :fourπ && return      4π
    x == :halfπ && return      π / 2
    x == :quartπ && return     π / 4
    x == :invπ && return       1 / π
    x == :twoinvπ && return    2 / π
    x == :fourinvπ && return   4 / π
    x == :inv2π && return      1 / (2π)
    x == :inv4π && return      1 / (4π)
    x == :sqrt2 && return      √2
    x == :sqrt3 && return      √3
    x == :sqrtπ && return      √π
    x == :sqrt2π && return     √2π
    x == :sqrt4π && return     √4π
    x == :sqrthalfπ && return  √(π / 2)
    x == :invsqrt2 && return   1 / √2
    x == :invsqrtπ && return   1 / √π
    x == :invsqrt2π && return  1 / √2π
    x == :loghalf && return    log(1 / 2)
    x == :logtwo && return     log(2)
    x == :logten && return     log(10)
    x == :logπ && return       log(π)
    x == :log2π && return      log(2π)
    x == :log4π && return      log(4π)
    return x
end

_unwrap_const(x) = unwrap_const(x)

## ----- substitution mapping stored in a dictionary -----
# A substitution is a collection of pairs 𝑋 -> 𝐺
# an empty dictionary is a match
# when there is no match, `nothing` is used
# an empty container of matches indicates no matches

const ∅ = ()
const MatchDict = Base.ImmutableDict{Symbol, Any}

match_dict() = MatchDict()

function match_dict(@nospecialize(kvs::Pair...))::MatchDict
    σ = MatchDict()
    match_dict(σ, kvs...)
end

function match_dict(σ::MatchDict, @nospecialize(kvs::Pair...))::MatchDict
    for (k,v) ∈ kvs
        v = isa(v,Number) ? unwrap_const(v) : v
        if haskey(σ, k)
            σk = σ[k]
            !isequal(σk, v) && error("repeated key with different value: $k => $v ($σk)")
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

eq_expr(a::Any, b::Any) = isequal(_unwrap_const(a), _unwrap_const(b))
eq_expr(a::Expr, b::Expr) = equal_terms(_unwrap_const(a), _unwrap_const(b))

# a symbol in a pattern matches a symbolic variable of the same name
eq_expr(a::Any, b::Symbol) = isequal(_unwrap_const(a), _unwrap_const(b)) ||
    (!iscall(a) && !isa(a, Symbol) && Symbol(string(a)) === b)

# compare head and arguments of two terms
# (not to be confused with `syntactic_match(s, p, σ)` of
# syntactic_match.jl, which matches a subject to a pattern)
function equal_terms(a, b)
    𝑎, 𝑏 = isexpr(a), isexpr(b)
    𝑎 == 𝑏 || return false
    !𝑎 && return isequal(a, b)
    operation(a) ==  operation(b) || return false
    as, bs = arguments(a), arguments(b)
    length(as) == length(bs) || return false
    all(splat(isequal), zip(as, bs))
end


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

# create a term on the subject side
function sterm(op, args)
    # numbers (e.g. 2 in 2x) may not identify the symbolic type
    i = findfirst(a -> !isa(_unwrap_const(a), Real), args)
    S = symtype(args[something(i, firstindex(args))])
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
        return pterm(:^, (pat, -1))
    elseif is_operation(:(//))(pat)
        u,v = arguments(pat)
        return pterm(:(//), (v, u))
    else
        return pterm(:^, (pat, -1))
    end
end

# a subject `u / v` as a product of powers: the factors of `u` (dropping a 1),
# and for each factor of `v` its inverse, `f^-1`, or `b^(-k)` for a power `b^k`
_factors(x) = iscall(x) && Symbol(operation(x)) === :* ? arguments(x) : (x,)
function _invert_data(f)
    # a number, possibly symbolic (SymbolicUtils keeps sqrt(1)), is inverted as a
    # number: a term `c^-1` with an integer `c` would raise a DomainError
    c = _unwrap_const(f)
    isa(c, Number) && return isa(c, Integer) ? 1 // c : inv(c)
    if iscall(f) && Symbol(operation(f)) === :^
        b, k = arguments(f)
        return sterm(^, (b, _negate(k)))
    end
    sterm(^, (f, -1))
end
function _data_as_powers(@nospecialize(data))
    u, v = arguments(data)
    Any[(f for f in _factors(u) if !_isone(_unwrap_const(f)))..., map(_invert_data, _factors(v))...]
end

# -k, as a number when k is one, e.g. :(1//2)
function _negate(k)
    k′ = _constant_value(k)
    isa(k′, Number) ? -k′ : sterm(-, (k,))
end

# --- basic total order, can override for other types
<ₑ(x::Symbol, y::Symbol) = x < y
<ₑ(x::Any, y::Any) = <ₑ(Symbol(x), Symbol(y))


# put arguments of commutative operations in a standard order (<ₑ),
# so terms equal up to commutativity, e.g. sin(a+b) and sin(b+a), compare equal.
# Subjects are fully ordered; for patterns only calls without wildcards are
# reordered and wildcards (with any guard) are left alone.
_canonical(x; pattern=false) = x
function _canonical(ex::Expr; pattern=false)
    pattern && is_𝑋(ex) && return ex
    iscall(ex) || return ex
    op = operation(ex)
    args = [_canonical(a; pattern) for a ∈ arguments(ex)]
    if iscommutative(op) && !(pattern && has_𝑋(ex))
        sort!(args, lt = <ₑ)
    end
    return Expr(:call, op, args...)
end

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

## -- evaluate a guard
#
# A guard is best given as a value -- a function spliced into the pattern,
# as `@pattern` does, or as with `:(~x::$pred)`. Such a guard is called
# directly.
#
# A guard given by name or as an expression in a quoted pattern
# (`:(~x::isfoo)`) is looked up in `Main` and `Base`, not in the module
# which wrote the pattern; use `@pattern` for that. A guard which can not be
# resolved, or which errors, fails the match.

_resolve_predicate(pred) = pred

# a name, as used in a quoted pattern or template, or `nothing`
function _resolve_name(x::Symbol)
    for M ∈ (Main, Base)
        isdefined(M, x) && return getfield(M, x)
    end
    return nothing
end

_resolve_predicate(pred::Symbol) = _resolve_name(pred)

# guards given as expressions (e.g. `!=(-1)`) are evaluated once and cached,
# keyed by the identity of the expression. A failure is not cached, so a
# guard defined later will be found.
const PREDICATE_FN_CACHE = IdDict{Expr, Any}()

function _resolve_predicate(pred::Expr)
    haskey(PREDICATE_FN_CACHE, pred) && return PREDICATE_FN_CACHE[pred]
    pred_fn = try
        Core.eval(Main, pred)
    catch err
        return nothing
    end
    PREDICATE_FN_CACHE[pred] = pred_fn
    return pred_fn
end

function _evalguard(pred, data)
    # look up in the latest world, as the guard may be defined after this
    # code was compiled
    pred_fn = Base.invokelatest(_resolve_predicate, pred)
    pred_fn === nothing && return false
    try
        Base.invokelatest(pred_fn, _unwrap_const(data)) === true
    catch err
        false
    end
end

# return true *if* either var has no predicate or
# predicate(data) is true
# use like pass_any_guard(var, data) || return ∅
pass_any_guard(var, data) = !has_predicate(var) || _evalguard(get_predicate(var), data)

# Does wildcard have a predicate?
has_predicate(::Any)::Bool = false
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
