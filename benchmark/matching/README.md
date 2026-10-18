# Matching comparison

62 patterns, each matched against a SymbolicUtils term by four matchers:

| Key | Matcher | Package |
|---|---|---|
| `ac` | `_eachmatch`, associative-commutative (MatchPy) | AssociativeCommutativePatternMatching (this checkout) |
| `c` | `_ceachmatch`, commutative | AssociativeCommutativePatternMatching |
| `su` | the matcher of `@rule` | [SymbolicUtils](https://github.com/JuliaSymbolics/SymbolicUtils.jl) |
| `si` | `check_expr_r` in `src/methods/rule_based/rule2.jl` | [SymbolicIntegration](https://github.com/JuliaSymbolics/SymbolicIntegration.jl) |

The result is a page, `results/matching_comparison.html`, with a summary,
the findings, and a table with one row per case. Selecting a case shows each
matcher's first match, every match, and the times.

## Running it

```sh
cd benchmark/matching
julia --project=env -e 'using Pkg; Pkg.instantiate()'   # once
julia --project=env run.jl     # about 30 s, most of it loading SymbolicIntegration
julia build.jl
```

`env` takes this package from the checkout (`../../..`) and the others from
the registry.

## How it works

| File | Role |
|---|---|
| `cases.jl` | the cases, `(group, pattern, subject, note)`; subjects are built with SymbolicUtils `@syms x y z a b c t` |
| `run.jl` | runs the four matchers on each case and writes `results/matching.json` |
| `build.jl`, `template.html` | turn the results into the page |

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
