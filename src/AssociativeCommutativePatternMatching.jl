
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

A predicate is a function, which can be evaluated on a proposed match in the scope of this package, that if `false` will prevent a match.

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

"""
module AssociativeCommutativePatternMatching

using TermInterface
import Combinatorics: permutations, multiset_combinations, multiexponents, powerset

include("utils.jl")
include("syntactic_match.jl")
include("match_py.jl")
include("replace.jl")
include("simplify.jl")
end
