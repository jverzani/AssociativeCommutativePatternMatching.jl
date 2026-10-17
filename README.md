# AssociativeCommutativePatternMatching

[![Build Status](https://github.com/jverzani/AssociativeCommutativePatternMatching.jl/actions/workflows/CI.yml/badge.svg?branch=main)](https://github.com/jverzani/AssociativeCommutativePatternMatching.jl/actions/workflows/CI.yml?query=branch%3Amain)

This package provides two pattern matching algorithm.

The firsa an implementation of the algorithm of [Non-linear Associative-Commutative Many-to-One Pattern Matching with Sequence Variables](https://arxiv.org/abs/1705.00907) by Manuel Krebber through Chapter 3,

This algorithm finds all matches of a pattern employing wildcards against a subject. The patterns are specified with Julia expressions. The AssociativeCommutativePatternMatching algorithm can separately match associatively *and* commutatively.

Example:

```{julia}
julia> AssociativeCommutativePatternMatching._match(:(~!a*~x + ~!b*~y), :(2x + y)) |> collect
4-element Vector{Pair{Symbol, Any}}:
 :y => :y
 :b => 1
 :x => 2
 :a => :x
```

There are 4 possible matches here:

```
julia> AssociativeCommutativePatternMatching._eachmatch(:(~!a*~x + ~!b*~y), :(2x + y)) |> collect
4-element Vector{Base.ImmutableDict{Symbol, Any}}:
 Base.ImmutableDict(:y => :y, :b => 1, :x => 2, :a => :x)
 Base.ImmutableDict(:y => :y, :b => 1, :x => :x, :a => 2)
 Base.ImmutableDict(:y => 2, :b => :x, :x => :y, :a => 1)
 Base.ImmutableDict(:y => :x, :b => 2, :x => :y, :a => 1)
```

The second algorithm is an extension from a pattern matching function used for the rule-based methods of [SymbolicIntegration](https://github.com/JuliaSymbolics/SymbolicIntegration.jl). It was originally implemented to see if more rule-based integration patterns could be matched (cf. [RUBISymbolicIntegration](https://github.com/jverzani/RUBISymbolicIntegration.jl)).
