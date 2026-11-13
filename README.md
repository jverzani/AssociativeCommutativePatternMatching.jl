# AssociativeCommutativePatternMatching

[![Build Status](https://github.com/jverzani/AssociativeCommutativePatternMatching.jl/actions/workflows/CI.yml/badge.svg?branch=main)](https://github.com/jverzani/AssociativeCommutativePatternMatching.jl/actions/workflows/CI.yml?query=branch%3Amain)
[![Pattern matching, cases matched of 62: ACPM 54, SymbolicUtils 46](https://img.shields.io/badge/pattern%20matching%2C%20matched%20of%2062-ACPM%2054%20%C2%B7%20SymbolicUtils%2046-2f8a4c)](https://rawcdn.githack.com/jverzani/AssociativeCommutativePatternMatching.jl/7c41935f0d02fcb2acea22ba1ea4aa6df2ed596d/benchmark/matching/results/matching_comparison.html)

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

## Comparison

The matching badge compares `_eachmatch` with the matcher of SymbolicUtils' `@rule`,
both on SymbolicUtils terms. It counts how many of the 62 cases of
`benchmark/matching/cases.jl` each one matches; every match found is checked by
substituting it back into the pattern. The cases cover slots, commutativity,
associativity, segments, default values, guards, powers written differently, nested
patterns and operation slots. Most of the difference is associativity: only
`_eachmatch` (and SymJ) let a slot take several terms of a sum or product.

The [comparison](https://rawcdn.githack.com/jverzani/AssociativeCommutativePatternMatching.jl/7c41935f0d02fcb2acea22ba1ea4aa6df2ed596d/benchmark/matching/results/matching_comparison.html)
also has `_ceachmatch`, both matchers with their patterns compiled, the matcher in
`rule2.jl` of SymbolicIntegration, [MatchMaker](https://github.com/JuliaSymbolics/MatchMaker.jl)
and [SymJ](https://github.com/jverzani/SymJ.jl), with the times of each. See
`benchmark/matching/README.md` to rerun it.
