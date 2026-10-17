```@meta
CurrentModule = AssociativeCommutativePatternMatching
DocTestSetup = quote
    using AssociativeCommutativePatternMatching
    using AssociativeCommutativePatternMatching: @pattern, @rule, @acrule
    const ACPM = AssociativeCommutativePatternMatching
end
```

# AssociativeCommutativePatternMatching.jl

This package matches *patterns*, expressions with wildcards such as `~x`, against *subjects*. A subject may be a Julia `Expr` or a term of a symbolic package implementing [TermInterface](https://github.com/JuliaSymbolics/TermInterface.jl), such as SymEngine, SymbolicUtils or SimpleExpressions. The package depends only on the lightweight `TermInterface` and `Combinatorics` packages.

A match, or substitution, `σ` maps the names of the wildcards to parts of the subject, so that substituting `σ` into the pattern gives back the subject.

There are two matchers, which share the pattern language, the rules, and the rewriting described on this page:

|                         | `_eachmatch`, `_match`                    | `_ceachmatch`, `_cmatch`                   |
|:------------------------|:------------------------------------------|:-------------------------------------------|
| `+` and `*` are         | associative and commutative               | commutative                                |
| `~x + ~y` and `a + b + c` | match, e.g. `x => a + b`, `y => c`      | do not match                               |
| all the matches are     | an iterator (a lazy generator)            | a vector                                   |
| a segment `~~x` binds   | a vector                                  | a tuple                                    |
| rules                   | [`@acrule`](@ref)                         | [`@rule`](@ref)                            |
| algorithm               | Krebber's [associative-commutative matching](https://arxiv.org/abs/1705.00907) | that of [SymbolicIntegration](https://github.com/JuliaSymbolics/SymbolicIntegration.jl)'s rules |

What is particular to each is described in [The two matchers](@ref).

Nothing is exported, as SymbolicUtils has macros of the same names, so qualify the functions, and import the macros you use:

```julia
import AssociativeCommutativePatternMatching as ACPM
using AssociativeCommutativePatternMatching: @pattern, @rule, @acrule
```

## Matching

`_match(pattern, subject)` returns the first match, or `nothing` if there is none; `_eachmatch(pattern, subject)` returns all of them. Likewise `_cmatch` and `_ceachmatch`. A match is a `Base.ImmutableDict` from the names of the wildcards to their values.

```jldoctest index
julia> ACPM._match(:(sin(~x)), :(sin(a + b)))
Base.ImmutableDict{Symbol, Any} with 1 entry:
  :x => :(a + b)

julia> ACPM._cmatch(:(sin(~x)), :(sin(a + b)))
Base.ImmutableDict{Symbol, Any} with 1 entry:
  :x => :(a + b)

julia> ACPM._cmatch(:(sin(~x)), :(cos(a))) === nothing
true
```

As `+` and `*` are commutative, the arguments of a sum or a product may match in any order:

```jldoctest index
julia> ACPM._ceachmatch(:(~x + ~y), :(a + b))
2-element Vector{Base.ImmutableDict{Symbol, Any}}:
 Base.ImmutableDict(:y => :b, :x => :a)
 Base.ImmutableDict(:y => :a, :x => :b)

julia> ACPM._eachmatch(:(~x + ~y), :(a + b)) |> collect
2-element Vector{Base.ImmutableDict{Symbol, Any}}:
 Base.ImmutableDict(:y => :a, :x => :b)
 Base.ImmutableDict(:y => :b, :x => :a)
```

With associativity, `a + b + c` may also be grouped as `(a + b) + c`, so `~x + ~y` matches it, in six ways; without, there are three terms for two slots, and no match:

```jldoctest index
julia> ACPM._eachmatch(:(~x + ~y), :(a + b + c)) |> collect
6-element Vector{Base.ImmutableDict{Symbol, Any}}:
 Base.ImmutableDict(:y => :a, :x => :(b + c))
 Base.ImmutableDict(:y => :b, :x => :(a + c))
 Base.ImmutableDict(:y => :(a + b), :x => :c)
 Base.ImmutableDict(:y => :c, :x => :(a + b))
 Base.ImmutableDict(:y => :(a + c), :x => :b)
 Base.ImmutableDict(:y => :(b + c), :x => :a)

julia> isempty(ACPM._ceachmatch(:(~x + ~y), :(a + b + c)))
true
```

A symbolic subject is matched in the same way:

```julia
julia> using SymEngine

julia> @vars x y;

julia> ACPM._cmatch(:(sin(~x)), sin(x + y))
Base.ImmutableDict{Symbol, Any} with 1 entry:
  :x => x + y
```

A symbolic package may store a number as a symbolic term. So that a number in a pattern equals one in the subject, extend `unwrap_const` to return the Julia number, e.g. `ACPM.unwrap_const(x::SymbolicUtils.BasicSymbolic) = SymbolicUtils.unwrap_const(x)`.

## Wildcards

| wildcard | matches                                               |
|:---------|:------------------------------------------------------|
| `~x`     | one argument (a *slot*)                               |
| `~!x`    | one argument, or a default value when there is none   |
| `~~x`    | zero or more arguments (a *segment*)                  |
| `~~~x`   | one or more arguments                                 |
| `(~F)(~x)` | the operation of a call, as well as its arguments   |

A pattern can have only one wildcard of a given name, so `~x + ~~x` is not allowed. A name may be repeated, though, in which case each occurrence must match the same value. Anything else in a pattern, such as a function name or a number, must appear in the subject as written.

### Slots

The slot `~x` matches a single argument, which may itself be an expression:

```jldoctest index
julia> ACPM._cmatch(:(~x + ~y), :(a + sin(b)))
Base.ImmutableDict{Symbol, Any} with 2 entries:
  :y => :(sin(b))
  :x => :a

julia> ACPM._cmatch(:(~x + ~x), :(a + a))
Base.ImmutableDict{Symbol, Any} with 1 entry:
  :x => :a

julia> ACPM._cmatch(:(~x + ~x), :(a + b)) === nothing
true
```

With `_match`, a slot in an associative operation may match several arguments, combined with the operation, as `:x => :(a + b)` above.

### Default slots

The default slot `~!x` matches as `~x` does, but when there is no argument to match it binds a default value: `0` within a sum, and `1` within a product, or as an exponent or a denominator.

```jldoctest index
julia> ACPM._cmatch(:(~x + ~!y), :a)
Base.ImmutableDict{Symbol, Any} with 2 entries:
  :y => 0
  :x => :a

julia> ACPM._match(:((~x)^(~!n)), :a)
Base.ImmutableDict{Symbol, Any} with 2 entries:
  :x => :a
  :n => 1

julia> ACPM._eachmatch(:(~!a * sin(~!b * ~x + ~!c)^(~!m)), :(sin(2x))) |> collect
2-element Vector{Any}:
 Base.ImmutableDict{Symbol, Any}(:b => 2, :x => :x, :c => 0, :m => 1, :a => 1)
 Base.ImmutableDict{Symbol, Any}(:b => :x, :x => 2, :c => 0, :m => 1, :a => 1)
```

(As `2x` is a commutative product, `~!b * ~x` matches it both ways.)

### Segments

The segment `~~x` matches any number of arguments, including none; `~~~x` must match at least one. `_match` binds the arguments as a vector, `_cmatch` as a tuple:

```jldoctest index
julia> ACPM._match(:(~x + ~~y), :(a + b + c))
Base.ImmutableDict{Symbol, Any} with 2 entries:
  :x => :a
  :y => Any[:b, :c]

julia> ACPM._ceachmatch(:(~x + ~~~y), :(a + b + c))
3-element Vector{Base.ImmutableDict{Symbol, Any}}:
 Base.ImmutableDict(:y => (:b, :c), :x => :a)
 Base.ImmutableDict(:y => (:a, :c), :x => :b)
 Base.ImmutableDict(:y => (:a, :b), :x => :c)
```

In an operation that is not commutative, a segment matches a run of consecutive arguments:

```jldoctest index
julia> ACPM._cmatch(:(f(~x, ~~y)), :(f(a)))
Base.ImmutableDict{Symbol, Any} with 2 entries:
  :y => ()
  :x => :a

julia> ACPM._cmatch(:(f(~x, ~~~y)), :(f(a))) === nothing
true
```

### Operation slots

A slot in the position of an operation matches the operation of the subject:

```jldoctest index
julia> ACPM._cmatch(:((~F)(~x)), :(sin(a)))
Base.ImmutableDict{Symbol, Any} with 2 entries:
  :x => :a
  :F => :sin
```

## Guards

A wildcard may have a guard, a predicate its value must satisfy, written `~x::pred`. The match is made only when `pred(value)` returns `true`; a guard which returns anything else, or throws an error, rejects the match.

```jldoctest index
julia> ACPM._cmatch(:((~x)^(~n::isinteger)), :(x^2))
Base.ImmutableDict{Symbol, Any} with 2 entries:
  :n => 2
  :x => :x

julia> ACPM._match(:((~x)^(~n::isinteger)), :(x^y)) === nothing
true
```

A guard may be the name of a function, or an expression which evaluates to one, such as an anonymous function or a partially applied function. As `y > 1` throws an error for the symbol `y`, the first guard below rejects `x^y`:

```jldoctest index
julia> ACPM._cmatch(:((~x)^(~n::(n -> n > 1))), :(x^y)) === nothing
true

julia> ACPM._match(:((~x)^(~n::!=(-1))), :(x^3))
Base.ImmutableDict{Symbol, Any} with 2 entries:
  :n => 3
  :x => :x
```

A guard on a segment is passed all of its values, as a vector or tuple:

```jldoctest index
julia> ACPM._cmatch(:(~x + ~~y::(u -> length(u) == 2)), :(a + b + c))
Base.ImmutableDict{Symbol, Any} with 2 entries:
  :y => (:b, :c)
  :x => :a

julia> ACPM._eachmatch(:(~x + ~~y::(!isempty)), :(a + b)) |> collect
2-element Vector{Base.ImmutableDict{Symbol, Any}}:
 Base.ImmutableDict(:x => :a, :y => Any[:b])
 Base.ImmutableDict(:x => :b, :y => Any[:a])
```

### Where a guard is found

In a quoted pattern, a guard given by name, or an expression for a guard, is evaluated in `Main` (with names looked up in `Main`, then `Base`) when the pattern is first matched. A predicate defined in a package or another module will not be found there, and the match fails. To use such a predicate, write the pattern with [`@pattern`](@ref) (or the left-hand side of a rule), which evaluates each guard where the macro is called, or interpolate the function into the pattern, as in `:(~x::$ispos)`:

```jldoctest index
julia> module M
           import AssociativeCommutativePatternMatching as ACPM
           using AssociativeCommutativePatternMatching: @pattern
           ispos(x) = x > 0
           quoted = ACPM._match(:(f(~x::ispos)), :(f(2)))
           macroed = ACPM._match(@pattern(f(~x::ispos)), :(f(2)))
           interpolated = ACPM._cmatch(:(f(~x::$ispos)), :(f(2)))
       end;

julia> M.quoted === nothing # `ispos` is not found in `Main`
true

julia> M.macroed
Base.ImmutableDict{Symbol, Any} with 1 entry:
  :x => 2

julia> M.interpolated
Base.ImmutableDict{Symbol, Any} with 1 entry:
  :x => 2
```

## The `@pattern` macro

A pattern may be written as a quoted expression, as above, or with the [`@pattern`](@ref) macro, which differs only in how guards are found (see [Where a guard is found](@ref)). Values may be interpolated into a pattern with `$`:

```jldoctest index
julia> n = 3;

julia> pat = @pattern (~x)^$n
:((~x) ^ 3)

julia> ACPM._cmatch(pat, :(y^3))
Base.ImmutableDict{Symbol, Any} with 1 entry:
  :x => :y
```

## Rules

### `@rule` and `@acrule`

The [`@rule`](@ref) macro creates a rule, `lhs => rhs`, matched with `_cmatch`; [`@acrule`](@ref) creates one matched with `_match`. The left-hand side is a pattern, as for `@pattern`. Calling a rule on a subject returns `rhs`, with each wildcard replaced by its value in the first match, or `nothing` when the subject does not match.

```jldoctest index
julia> r = @rule sin(2 * ~x) => 2 * sin(~x) * cos(~x)
@rule sin(2 * ~x) => 2 * sin(~x) * cos(~x)

julia> r(:(sin(2t)))
:(2 * sin(t) * cos(t))

julia> r(:(cos(2t))) === nothing
true

julia> r = @acrule ~x + ~y => (~x) * (~y);

julia> r(:(a + b + c))
:((b + c) * a)

julia> (@rule ~x + ~y => (~x) * (~y))(:(a + b + c)) === nothing
true
```

For an `Expr` subject, as above, the values are substituted into `rhs` and an `Expr` is returned. For a symbolic subject, `rhs` is Julia code that is run, so the result is computed:

```julia
julia> using SymEngine

julia> @vars x y;

julia> r = @rule (~x)^(~n::isinteger) => (~x)^(~n + 1) / (~n + 1);

julia> r(x^2)
(1/3)*x^3

julia> r(x^y) === nothing
true
```

The right-hand side is compiled where the macro is called, so it may use the functions and variables of the calling module. A segment is replaced by its values, which may be splatted into a call:

```julia
julia> r = @rule ~x + ~~y => +(~~y...);

julia> r(x + y + 2) # drops one term of the sum
x + y
```

As this substitutes a tuple into an `Expr` for an `Expr` subject, a segment on the right-hand side is best used with symbolic subjects.

### Rewriting with a match

[`_rewrite(σ, rhs)`](@ref _rewrite) replaces the wildcards in the template `rhs` with their values in the match `σ`. The type of the subject may be given, as `_rewrite(σ, rhs, T)` or `_rewrite(T, σ, rhs)`; otherwise it is found from the values in `σ`. For an `Expr` subject the result is an expression; for a symbolic one each call is evaluated, with the names in `rhs` looked up in `Main`, `Base` and then this package.

```jldoctest index
julia> σ = ACPM._match(:(~x * tanh(exp(~x))), :(a^2 * tanh(exp(a^2))))
Base.ImmutableDict{Symbol, Any} with 1 entry:
  :x => :(a ^ 2)

julia> ACPM._rewrite(σ, :(~x * tanh(exp(~x))))
:(a ^ 2 * tanh(exp(a ^ 2)))

julia> ACPM._rewrite(Expr, σ, :(sqrt(~x)))
:(sqrt(a ^ 2))
```

### Replacing

`_replace(ex, pat => rhs)` walks through an expression, replacing each part matching `pat` (with `_match`) by `rhs`. The left-hand side may also be a function, to replace an operation, or a variable or expression to replace exactly.

```jldoctest index
julia> ACPM._replace(:(cos(2x)^2 + sin(2x)^2), :(sin(~x)^2 + cos(~x)^2) => 1)
1

julia> ACPM._replace(:(2cos(2x)^2 + 2sin(2x)^2), :(~!a * sin(~x)^2 + ~!a * cos(~x)^2) => :(~!a))
2
```

## Commutative and associative operations

Whether an operation is commutative or associative is decided by the functions `iscommutative` and `isassociative`, which are passed the operation of the subject. By default only `+` and `*` (as functions or symbols) are commutative and associative. They may be extended for other operations; `_cmatch` uses only `iscommutative`.

```jldoctest index
julia> ACPM.iscommutative(x::Symbol) = x ∈ (:+, :*, :fₘ)

julia> length(ACPM._ceachmatch(:(fₘ(~x, ~y)), :(fₘ(a, b))))
2

julia> length(ACPM._ceachmatch(:(f(~x, ~y)), :(f(a, b))))
1
```

## Differences from SymbolicUtils

The wildcards `~x`, `~!x` and `~~x`, guards written `~x::pred`, and the forms `@rule lhs => rhs` and `@acrule lhs => rhs` are as in SymbolicUtils. Compared with SymbolicUtils (v4.51), this package differs in that:

* A subject may be an `Expr`, as well as a symbolic term from any package implementing TermInterface.
* `_eachmatch` and `_ceachmatch` return every match of a pattern, not just the first.
* A segment `~~x` binds to a vector (`_match`) or a tuple (`_cmatch`), rather than to a view of the arguments, and a guard on a segment is passed these.
* There is a segment `~~~x` which matches one or more arguments.
* A default slot `~!x` may be used in a denominator, defaulting to `1`, as well as in `+`, `*` and an exponent.
* A guard which returns anything but `true`, or which throws an error, rejects the match. In SymbolicUtils, the rule throws an error.
* A guard in a quoted pattern is looked up in `Main` (see [Where a guard is found](@ref)). Guards in `@pattern`, `@rule` and `@acrule` are evaluated in the calling module, as with SymbolicUtils' `@rule`.

Some features of SymbolicUtils' rules are not supported:

* a predicate over the whole rule, `@rule lhs => rhs where pred`. For a symbolic subject, the same effect comes from a right-hand side such as `pred ? rhs : nothing`, as a rule returns whatever `rhs` evaluates to;
* `~` alone on the right-hand side, to return the match;
* contextual predicates, and the macro `@capture`.
