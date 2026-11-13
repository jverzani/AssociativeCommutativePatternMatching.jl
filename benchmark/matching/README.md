# Matching comparison

62 patterns, each matched against a SymbolicUtils term by five matchers, and against the same term built with SymJ by SymJ's matcher; both of this package's matchers also run with their pattern compiled:

| Key | Matcher | Package |
|---|---|---|
| `ac` | `_eachmatch`, associative-commutative (MatchPy) | AssociativeCommutativePatternMatching (this checkout) |
| `acc` | `_eachmatch` with the pattern compiled once by `compile_eachmatch`, as `@acrule` does | AssociativeCommutativePatternMatching |
| `c` | `_ceachmatch`, commutative | AssociativeCommutativePatternMatching |
| `cc` | `_ceachmatch` with the pattern compiled once by `compile_pattern`, as `@rule` does | AssociativeCommutativePatternMatching |
| `su` | the matcher of `@rule` | [SymbolicUtils](https://github.com/JuliaSymbolics/SymbolicUtils.jl) |
| `si` | `check_expr_r` in `src/methods/rule_based/rule2.jl` | [SymbolicIntegration](https://github.com/JuliaSymbolics/SymbolicIntegration.jl) |
| `mm` | `match`/`matchall`, the pattern rewritten with MatchMaker's markers and compiled once | [MatchMaker](https://github.com/JuliaSymbolics/MatchMaker.jl) |
| `sj` | `match`/`eachmatch` with `SymJ.pattern(p)`, compiled once; the subject is built with SymJ from the same expression | [SymJ](https://github.com/jverzani/SymJ.jl) |

The result is a page, `results/matching_comparison.html`, laid out like
GruntzLimit's limits comparison: a summary (counts by outcome, with a bar,
and first- and all-match times), a grid with one row per matcher and one
column per case, colored by outcome (matched and checked, matched but not
checked, wrong, no match, error) and showing the number of matches when
there are several, filters (matchers differ, counts differ, matched by one
or by none, wrong, errors), and below it the selected case: the pattern, the
subject, and each matcher's first match, every match and times. Then the
findings and how it was run.

## Running it

```sh
cd benchmark/matching
julia --project=env -e 'using Pkg; Pkg.instantiate()'   # once
julia --project=env run.jl     # about 1 min, much of it loading SymbolicIntegration and SymJ
julia build.jl
julia --project=env matchmaker_corpus.jl   # MatchMaker's test suites, about 2 min
```

`env` takes this package from the checkout (`../../..`), MatchMaker and SymJ
from their GitHub repositories (they are not registered), and the others from
the registry.

## How it works

| File | Role |
|---|---|
| `cases.jl` | the cases, `(group, pattern, subject, note)`; subjects are built with SymbolicUtils `@syms x y z a b c t` |
| `run.jl` | runs the matchers on each case and writes `results/matching.json` |
| `build.jl`, `template.html` | turn the results into the page |
| `matchmaker_corpus.jl` | runs MatchMaker's ported test suites (MatchPy, SymbolicUtils, SymPy, Metatheory) through `_eachmatch` and `_ceachmatch`, and writes `results/matchmaker_corpus.txt` |

For each case and matcher, `run.jl` records:

- **First match**: what a rule would use: `_match`, `_cmatch`, the matcher of
  the `@rule` with a continuation returning the first bindings, and
  `check_expr_r`.
- **Every match**: `_eachmatch` (collected, at most 5000), `_ceachmatch`, and for
  SymbolicUtils a continuation that records the bindings and returns
  `nothing`, so the matcher backtracks. SymJ's `eachmatch` returns the
  distinct matches. SymbolicUtils limits commutative
  backtracking with a work budget (`COMM_BACKTRACK_BUDGET`) that `(r::Rule)(term)`
  resets on each call; `run.jl` resets it too, since it calls the matcher
  directly. rule2 returns one match only.
- **Distinct**: the number of different matches among them.
- **Check**: each match (up to 200 per case) is substituted into the pattern
  and compared numerically with the subject; a mismatch would count as wrong.
- **Times**: microseconds per call, warm, the best of three batches of at least
  2 ms. Compare them only within one run.

Guards use functions from Base (`iseven`, `isodd`, `isinteger`), which all the
matchers can find: rule2 evaluates a guard in the SymbolicIntegration module.

## Updating the page

`build.jl` fills in the numbers, grid, times and versions, including the
numbers quoted in the findings (spans such as `med-sj`, `t11-cc`, `t40ac`).
The "What stands out" section is otherwise written by hand in
`template.html`; check it against new results.

## Results so far

Cases matched (of 62) and the first-match median in µs. Times are on one
machine and only comparable within a run; the second run was on a busier
machine (SymbolicUtils' own median went from 0.93 to 1.79 µs).

| Date | ACPM | SymbolicUtils | `ac` | `acc` | `c` | `cc` | `su` | `si` | `mm` | `sj` |
|---|---|---|---|---|---|---|---|---|---|---|
| 2026-10-18 | `63eb9eb` + changes | 4.51.0 | 54, 13.1 | | 49, 1.81 | 49, 0.45 | 46, 0.93 | 42, 0.44 | | |
| 2026-11-13 | `5a19296` | 4.56.1 | 54, 8.42 | 54, 8.00 | 49, 2.81 | 49, 0.79 | 46, 1.79 | 42, 0.70 | 36, 2.45 | 56, 0.78 |

Notes:

- The second run adds MatchMaker 1.0.0 and SymJ 0.1.0 (`main`), and
  `_eachmatch` with its pattern compiled. Between the runs `_eachmatch`'s
  internals were made typed and lazy where it matters: relative to
  SymbolicUtils in the same run, its first-match median went from 14× to
  4.7×, and the two-binomial product (case 55) from 628 to 160 µs.
- With SymbolicUtils 4.56, `isinteger(x)` throws a `MethodError`, about
  30 µs; `_eachmatch` tries `a => x` first for `~a::isinteger * ~x`, so
  case 40 takes about 400 µs (old and new code alike).

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
