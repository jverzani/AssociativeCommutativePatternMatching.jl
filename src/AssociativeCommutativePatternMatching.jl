
"""
AssociativeCommutativePatternMatching

This package provides an implementation of the algorithm of [Non-linear Associative-Commutative Many-to-One Pattern Matching with Sequence Variables](https://arxiv.org/abs/1705.00907) by Manuel Krebber through Chapter 3, referred to as MatchPy.

A match is a dictionary containing a mapping between wildcard values in the *pattern* with values in the *subject*.

Patterns are specified with expressions and within wildcards are specified by:

|Syntax | with predicate | note |
|:------|:---------------|:-----|
|`~x`   | `~x::pred`     | a slot variable to match a single argument |
|`~!x`   | `~!x`         | a default slot variable to match a single argument |
|`~~x`   | `~~x::pred`   | a star variable to match 0, 1 or more arguments |
|`~~~x`   | `~~~x::pred` | a plus variable to match 1 or more arguments |

The variable name is `x` in each of the above; variable names must be unique within a pattern (so one can't have both a `~x` and a `~~x`, though the same variable may appear more than once.

A predicate is a function which is called on a proposed match; unless it returns `true` (or if it throws an error) the match is rejected. In a quoted pattern, a predicate given by name, as in `:(~x::isfoo)`, is looked up in `Main` and `Base`. To use a predicate from another module, write the pattern with `@pattern`, which evaluates the predicate where the macro is called, or interpolate the function, as in `:(~x::\$isfoo)`.

A default slot variable has default values for the enclosing operations of `+` (0), `*` (1),  and `^` (the exponent, also 1).

Matching is against arguments in a function or the function head. Functions may be associative and/or commutative. The MatchPy algorithm allows the separation (as happens with matrix multiplication).

The pattern `f(a, ~x, c)` would match `f(a,b,c)` (with `:x => b`) but not match `f(a,b₁, b₂, c)`. Whereas `f(a, ~~x, c)` would match with `:x => [b₁, b₂]`.

For `AssociativeCommutativePatternMatching`  and associative functions, matches have the function applied to slot variables. So `+(a,~x,c)` matched against `:(+(a, b₁, b₂, c))` would have `:x => :(b₁ + b₂)`.

Before matching, the arguments of commutative functions in the subject (and in parts of the pattern without wildcards) are put in a standard order. So `sin(a + b) + ~x` matches `sin(b + a) + c`, but `sin(a - b) + ~x` does not match `sin(b - a) + c`. As a consequence, matched values have commutative arguments in this standard order, e.g. `(~x)^(~x)` matched against `:((x + p)^(x + p))` has `:x => :(p + x)`.

The primary function is the unexported `_eachmatch(pat, sub`) function which returns an iterator of matches. The `_match(pat, sub)` function returns the first value. There are also `_rewrite` and `_replace` functions.
## Example

```
julia> @time AssociativeCommutativePatternMatching._eachmatch(:(~x + ~y), :(a + b + c));
  0.000071 seconds (60 allocations: 3.000 KiB)

julia> @time AssociativeCommutativePatternMatching._eachmatch(:(~x + ~y), :(a + b)) |> collect
  0.000203 seconds (527 allocations: 26.219 KiB)
2-element Vector{Base.ImmutableDict{Symbol, Any}}:
 Base.ImmutableDict(:x => :a, :y => :b)
 Base.ImmutableDict(:x => :b, :y => :a)

julia> @time AssociativeCommutativePatternMatching._eachmatch(:(~x + ~y), :(a + b + c)) |> collect
  0.000233 seconds (1.46 k allocations: 70.125 KiB)
6-element Vector{Base.ImmutableDict{Symbol, Any}}:
 Base.ImmutableDict(:x => :a, :y => :(b + c))
 Base.ImmutableDict(:x => :b, :y => :(a + c))
 Base.ImmutableDict(:x => :(a + b), :y => :c)
 Base.ImmutableDict(:x => :c, :y => :(a + b))
 Base.ImmutableDict(:x => :(a + c), :y => :b)
 Base.ImmutableDict(:x => :(b + c), :y => :a)

 ```

The reduced number of allocations in the first call, is due to the values being returned as a generator. There are additional allocations when iterated by `collect`. The second example shows commutativity being employed, as `+` is assumed to be commutative. As well, `+` is assumed to be associative, so there are 6 matches in the last example, the first of which matches `:(a + (b+c))`.

## Commutative matching

The package also has a matcher which takes commutativity, but not associativity, into account. It is derived from the matcher used for the rule-based methods of [SymbolicIntegration](https://github.com/JuliaSymbolics/SymbolicIntegration.jl). The function `_ceachmatch(pat, sub)` returns a vector of the matches and `_cmatch(pat, sub)` the first match or `nothing`. The macros `@pattern` and `@rule` create patterns and rewriting rules whose guards and right-hand sides are resolved in the calling module; `@acrule` creates a rule which matches with `_match` instead. As with everything else here, they are not exported (SymbolicUtils has macros of these names), so use, e.g., `using AssociativeCommutativePatternMatching: @rule`. The function `_rewrite` rewrites a template using a match.

```
julia> AssociativeCommutativePatternMatching._ceachmatch(:(~x + ~y), :(a + b + c))
Base.ImmutableDict{Symbol, Any}[]
```

"""
module AssociativeCommutativePatternMatching

using TermInterface
import Combinatorics: permutations, multiset_combinations, multiexponents, powerset, combinations


include("utils.jl")
include("syntactic_match.jl")
include("match_py.jl")
include("replace.jl")

# commutative matching
include("commutative/utils.jl")
include("commutative/rule2a.jl")
include("commutative/pattern.jl")
include("commutative/rule.jl")

"""
    _ceachmatch(pat, sub)

Return a vector of the matches of the pattern `pat` to the subject `sub`,
each a dictionary from wildcard names to their values. The vector is
empty if there is no match.

Unlike `_eachmatch`, only commutativity of `+` and `*` is used, not
associativity.
"""
function _ceachmatch(pat, sub)
    check_expr_r(sub, pat)
end

"""
    _cmatch(pat, sub)

Return the first match of the pattern `pat` to the subject `sub`, or
`nothing` if there is no match. See [`_ceachmatch`](@ref).
"""
function _cmatch(pat, sub)
    σs = _ceachmatch(pat, sub)
    isempty(σs) && return nothing
    first(σs)
end

end
