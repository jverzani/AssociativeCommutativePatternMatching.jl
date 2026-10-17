# For dispatch
### ---- match, eachmatch, replace

# return iterator of each possible match
function _eachmatch(pat::Union{Symbol,Expr}, ex)
    pat, ex = _canonical(pat; pattern=true), _canonical(ex)
    if has_𝑋(pat)
        return match_one_to_one([ex], pat)
    else
        σ = syntactic_match(ex, pat)
        return isnothing(σ) ? () : (σ,)
    end
end

function _match(pat::Union{Symbol, Expr}, sub)
    σs = _eachmatch(pat, sub)
    σ = iterate(σs)
    isnothing(σ) && return nothing
    first(σ)
end

# `_rewrite` is in commutative/rule.jl

## --- walk over expression, but return symtype of T
function walk(T, ex, inner, outer)
    (!is_𝑋(ex) && (iscall(ex) || isexpr(ex))) || return outer(ex)
    if isexpr(ex) && !iscall(ex)
        ex′ = Expr(head(ex), map(inner, children(ex))...)
    elseif isexpr(ex)
        if T == Expr
            ex′ = pterm(operation(ex),  map(inner, arguments(ex)); elide=false)
        else
            ex′ = sterm(T, operation(ex), map(inner, arguments(ex)))
        end
    end
    outer(ex′)
end

postwalk(f, ex, T) = walk(T, ex,    x -> postwalk(f,x, T), f)
prewalk(f, ex, T)  = walk(T, f(ex), x -> prewalk(f, x, T), identity)


"""
    _replace([T], ex, args::Pair...)

Replace parts of an expression with something else.

Returns a symbolic object of same types as `ex`

The replacement is specified using `variable => value`; these are processed left to right.

There are different methods depending on the type of key in the the `key => value` pairs specified:

* A function call can be replaced by passing in a pair `𝐹 => 𝐹`, (e.g. `sin=>cos`)
* a variable, say `a` can be replaced by passing in  a pair like `a => a^2`
* an expression can be replaced similarly.
* For wildcard matching, an expression is used on both sides, as in `:(cos(~x)) => :(sin(~x))`.

The first three are straightforward. First, for function heads:

```@repl replace
julia> using SymEngine

julia> using AssociativeCommutativePatternMatching; import AssociativeCommutativePatternMatching: _replace

julia> @vars x p
(x, p)

julia> _replace(cos(x) - cos(x^2), cos => sin)
sin(x) - sin(x^2)
```

(See below for a hack when the function head is `exp`.)

For symbolic variables, we have:

```@repl replace
julia> ex = cos(x) - x*p
-p*x + cos(x)

julia> _replace(ex, x => 2*one(x))
-2*p + cos(2)

julia> _replace(ex, p => 2*one(x))
-2*x + cos(x)
```

For symbolic expressions, we have:


```@repl replace
julia> ex = cos(x)^2 + cos(x) + 1
1 + cos(x)^2 + cos(x)

julia> _replace(ex, cos(x) => x)
1 + x + x^2
```

Replacements occur only if an entire node in the expression tree is matched:

```@repl replace
julia> u = 1 + x
1 + x

julia> _replace(u + exp(-u), u => x^2)
1 + x + exp(-x^2)
```

(As this addition has three terms, `1+x` is not a subtree in the expression tree.)


The last needs more explanation, as there can be wildcards in the expression.

Wildcards have a naming convention:

* `~x` to match a single part of an expression (possibly all arguments to a function)
* `~!x` like previous, only has a default value when operation is `+`, `*`, or `^`.
* `~~x` match 0, 1, or more variables
* `~~x` match 1 or more variables

```@repl replace
julia> _replace(cos(pi + x^2), :(cos(pi + ~x)) => :(-cos(~x)))
-cos(x^2)

```

```@repl replace
julia> ex = log(sin(x)) + tan(sin(x^2))
log(sin(x)) + tan(sin(x^2))

julia> _replace(ex, :(sin(~x)) => :(tan((~x) / 2)))
log(tan((1/2)*x)) + tan(tan((1/2)*x^2))

julia> _replace(ex, :(sin(~x)) => :(~x))
log(x) + tan(x^2)

julia> _replace(x*p, :((~x) * x) => :(~x))
p
```

## Picture

The `AbstractTrees` package can print this tree-representation of the expression `ex = sin(x + x*log(x) + cos(x + p + x^2))`:

```
julia> print_tree(ex;maxdepth=10)
sin
└─ +
   ├─ x
   ├─ *
   │  ├─ x
   │  └─ log
   │     └─ x
   └─ cos              <--
      └─ +             ...
         ├─ x          <--
         ├─ p          ...
         └─ ^          ...
            ├─ x       ...
            └─ 2       ...
```

In the `_replace` command, the  wildcard expression `:(cos(x + ~x))` looks at the part of the tree that has `cos` as a node, and the lone child is an expression with node `+` and child `x`. The `~x then matches `p + x^2`.

```@repl replace
julia> _replace(sin(x + x*log(x) + cos(x + p + x^2)), :(cos(x + ~x)) => :(sin(~x)))
sin(x + x*log(x) + sin(p + x^2))

```
"""
function _replace(T, ex, uv::Pair)
    u,v = uv

    # Expr
    isa(u, Expr) && return _replace_arguments(T, ex, u, v)

    # is u function replace head
    isa(u, Function) && return map_matched_head(ex, ==(Symbol(u)), _ -> v)

    # is u variable, replace exact
    return map_matched(ex, ==(u), _ -> v)
end

_replace(ex, uv::Pair) = _replace(symtype(ex), ex, uv::Pair)
#
function _replace_arguments(T, ex, u, v)
    iscall(ex) || return (ex == u ? v : ex)

    postwalk(ex, T) do x
        σ = _match(u, x) # sigma is nothing, (), or a substitution
        isnothing(σ) && return x
        isempty(σ) && return v
        return _rewrite(T, σ, v)
    end

end

# old traverse
function __replace_arguments(T, ex, u, v)
    iscall(ex) || return (ex == u ? v : ex)

    σ = _match(u, ex) # sigma is nothing, (), or a substitution

    if !isnothing(σ)
        σ == () && return v # no substitution
        return _rewrite(T, σ, v)
    end

    # peel off
    op, args = operation(ex), arguments(ex)
    args′ = [_replace_arguments(T, a, u, v) for a ∈ args]
    return sterm(T, op, args′)

end
