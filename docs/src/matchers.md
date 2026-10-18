```@meta
CurrentModule = AssociativeCommutativePatternMatching
DocTestSetup = quote
    using AssociativeCommutativePatternMatching
    const ACPM = AssociativeCommutativePatternMatching
end
```

# The two matchers

The two matchers share the pattern language, guards, rules and rewriting described in [AssociativeCommutativePatternMatching.jl](@ref). This page describes what is particular to each. In short though the main difference is with segment variables where the associative/commutative matcher (`_eachmatch`) takes longer but is thorough, whereas `_ceachmatch` is content with finding a quicker match.

## The associative-commutative matcher

`_eachmatch` and `_match` implement the algorithm of [Non-linear Associative-Commutative Many-to-One Pattern Matching with Sequence Variables](https://arxiv.org/abs/1705.00907) by Manuel Krebber through Chapter 3 (only the one-to-one matching), referred to as MatchPy. Operations may be associative and/or commutative; the algorithm allows for these to be separate (as happens with matrix multiplication).

The matches are returned as a lazy iterator, which allocates little until it is iterated, e.g. with `collect` or `first`.

### Associativity

In an associative operation a slot may match several arguments, combined with the operation, and segments may split the arguments in every way. This can give a combinatorially large number of matches. In a sum there are eight ways to divide three terms between two segments, while for an operation `f` which is neither associative nor commutative the segments must take consecutive arguments, giving four:

```jldoctest matchers
julia> length(collect(ACPM._eachmatch(:(~~x + ~~y), :(a + b + c))))
8

julia> ACPM._eachmatch(:(f(~~x, ~~y)), :(f(a, b, c))) |> collect
4-element Vector{Base.ImmutableDict{Symbol, Any}}:
 Base.ImmutableDict(:y => Any[], :x => Any[:a, :b, :c])
 Base.ImmutableDict(:y => Any[:c], :x => Any[:a, :b])
 Base.ImmutableDict(:y => Any[:b, :c], :x => Any[:a])
 Base.ImmutableDict(:y => Any[:a, :b, :c], :x => Any[])
```

Associativity and commutativity of an operation can be specified with the unexport `isassociative` and `iscommutative` methods.


### Standard order

Before matching, the arguments of commutative operations in the subject, and in the parts of the pattern without wildcards, are put in a standard order. So `sin(a + b) + ~x` matches `sin(b + a) + c`, but `sin(a - b) + ~x` does not match `sin(b - a) + c`. As a consequence, matched values have commutative arguments in this order:

```jldoctest matchers
julia> ACPM._match(:((~x)^(~x)), :((x + p)^(x + p)))
Base.ImmutableDict{Symbol, Any} with 1 entry:
  :x => :(p + x)
```

When the wildcards are slots, substituting a match into the pattern, with [`_rewrite`](@ref), gives back the subject, up to this order.

## The commutative matcher

`_ceachmatch` and `_cmatch` extend the pattern matcher used for the rule-based methods of [SymbolicIntegration](https://github.com/JuliaSymbolics/SymbolicIntegration.jl). They were written to see if more rule-based integration patterns could be matched (cf. [RUBISymbolicIntegration](https://github.com/jverzani/RUBISymbolicIntegration.jl)), so the matching is suited to such rules: commutativity is used, associativity is not, and there are several ways of writing a power. The matches are returned in a vector, and the subject is matched as it is stored, with no reordering.

```jldoctest matchers
julia> ACPM._cmatch(:((~x)^(~x)), :((x + p)^(x + p)))
Base.ImmutableDict{Symbol, Any} with 1 entry:
  :x => :(x + p)
```

### Segments

When several segments share the arguments of an operation, only one way of dividing the arguments among them is found, rather than every way:

```jldoctest matchers
julia> ACPM._ceachmatch(:(f(~~x, ~~y)), :(f(a, b, c)))
1-element Vector{Base.ImmutableDict{Symbol, Any}}:
 Base.ImmutableDict(:y => (), :x => (:a, :b, :c))
```

### Powers written differently

A power may be written in several ways, and a symbolic package may store one way as another, e.g. `1/x` as `x^-1`. A pattern for a power also matches `sqrt(u)` as `u^(1//2)`, `exp(u)` as `ℯ^u`, `1/u` as `u^-1`, and a quotient as a product with a negative power:

```jldoctest matchers
julia> ACPM._cmatch(:((~u)^(~m)), :(1 / sqrt(x)))
Base.ImmutableDict{Symbol, Any} with 2 entries:
  :m => -1//2
  :u => :x

julia> ACPM._cmatch(:((~u)^(~m) * ~v), :(a / b))
Base.ImmutableDict{Symbol, Any} with 3 entries:
  :v => :a
  :m => -1
  :u => :b
```

The associative-commutative matcher matches these in the same way:

```jldoctest matchers
julia> ACPM._match(:((~u)^(~m)), :(1 / sqrt(x)))
Base.ImmutableDict{Symbol, Any} with 2 entries:
  :m => -1//2
  :u => :x
```
