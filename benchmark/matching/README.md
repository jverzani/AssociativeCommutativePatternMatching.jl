# Matching comparison

62 patterns, each matched against a SymbolicUtils term by five matchers, one also with its pattern compiled:

| Key | Matcher | Package |
|---|---|---|
| `ac` | `_eachmatch`, associative-commutative (MatchPy) | AssociativeCommutativePatternMatching (this checkout) |
| `c` | `_ceachmatch`, commutative | AssociativeCommutativePatternMatching |
| `cc` | `_ceachmatch` with the pattern compiled once by `compile_pattern`, as `@rule` does | AssociativeCommutativePatternMatching |
| `su` | the matcher of `@rule` | [SymbolicUtils](https://github.com/JuliaSymbolics/SymbolicUtils.jl) |
| `si` | `check_expr_r` in `src/methods/rule_based/rule2.jl` | [SymbolicIntegration](https://github.com/JuliaSymbolics/SymbolicIntegration.jl) |
| `mm` | `match`/`matchall`, the pattern rewritten with MatchMaker's markers and compiled once | [MatchMaker](https://github.com/JuliaSymbolics/MatchMaker.jl) |

The result is a page, `results/matching_comparison.html`, with a summary,
the findings, and a table with one row per case. Selecting a case shows each
matcher's first match, every match, and the times.

## Running it

```sh
cd benchmark/matching
julia --project=env -e 'using Pkg; Pkg.instantiate()'   # once
julia --project=env run.jl     # about 30 s, most of it loading SymbolicIntegration
julia build.jl
julia --project=env matchmaker_corpus.jl   # MatchMaker's test suites, about 2 min
```

`env` takes this package from the checkout (`../../..`), MatchMaker from its
GitHub repository (it is not registered yet), and the others from the registry.

## How it works

| File | Role |
|---|---|
| `cases.jl` | the cases, `(group, pattern, subject, note)`; subjects are built with SymbolicUtils `@syms x y z a b c t` |
| `run.jl` | runs the four matchers on each case and writes `results/matching.json` |
| `build.jl`, `template.html` | turn the results into the page |
| `matchmaker_corpus.jl` | runs MatchMaker's ported test suites (MatchPy, SymbolicUtils, SymPy, Metatheory) through `_eachmatch` and `_ceachmatch`, and writes `results/matchmaker_corpus.txt` |

For each case and matcher, `run.jl` records:

- **First match**: what a rule would use: `_match`, `_cmatch`, the matcher of
  the `@rule` with a continuation returning the first bindings, and
  `check_expr_r`.
- **Every match**: `_eachmatch` (collected, at most 5000), `_ceachmatch`, and for
  SymbolicUtils a continuation that records the bindings and returns
  `nothing`, so the matcher backtracks. SymbolicUtils limits commutative
  backtracking with a work budget (`COMM_BACKTRACK_BUDGET`) that `(r::Rule)(term)`
  resets on each call; `run.jl` resets it too, since it calls the matcher
  directly. rule2 returns one match only.
- **Distinct**: the number of different matches among them.
- **Check**: each match (up to 200 per case) is substituted into the pattern
  and compared numerically with the subject; a mismatch would count as wrong.
- **Times**: microseconds per call, warm, the best of three batches of at least
  2 ms. Compare them only within one run.

Guards use functions from Base (`iseven`, `isodd`, `isinteger`), which all four
matchers can find: rule2 evaluates a guard in the SymbolicIntegration module.

## Updating the page

`build.jl` fills in the numbers, table and versions. The "What stands out"
section is written by hand in `template.html`; check it against new results.

## MatchMaker's test suites

`matchmaker_corpus.jl` includes MatchMaker's `test/matchpy/one_to_one.jl`,
`test/su/rewrite.jl`, `test/sympy/match.jl` and `test/metatheory/reductions.jl`,
intercepting their helpers (`mp`, `mpc`, `sm`) to record each case: the
pattern, the subject, the expected matches (or count) and the variable specs.
Each pattern is translated to this package's syntax (`slot` as `~x`, a segment
with minimum 0 or 1 as `~~x` or `~~~x`, `optional` as `~!x` when its default
is the identity of its head, a predicate as a guard), and each subject to an
`Expr`. A head declared associative or commutative in MatchMaker gets the
suffix `ₐ` or `ₘ`, which `isassociative`/`iscommutative` methods recognize.
Distinct matches are then compared with the expected ones, segments as lists
of arguments, sorted under commutative heads. As a check on this translation,
MatchMaker's own matches go through the same comparison, and all agree.
Cases with cross-variable constraints, or defaults other than the identity,
are not translated.
