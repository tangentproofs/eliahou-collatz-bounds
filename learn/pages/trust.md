# Trust: what has and hasn't been checked

This site **explains** the Lean proof. It does not re-check it.

## Lean checking

| | `main` @ 24c01e9 (Lean files unchanged since db804ce) |
|---|---|
| Built by this site | **no**. By the owner's choice, no Lean was built on our servers for this site. |
| Built publicly (CI) | **no Lean CI** in the repository. The only workflow deploys the Pages site. |
| Build claims | `README.md` and `ARISTOTLE_SUMMARY.md` say every paper-facing theorem is proved with no `sorry` and standard axioms only. |
| `#print axioms` | **not run by this site.** No output is recorded in the repository. Expected: `propext`, `Classical.choice`, `Quot.sound`. |
| `sorry`, `admit`, `axiom` | none found by grep in `Collatz/`, `Results.lean`, `Main.lean` |
| `native_decide`, `decide := true` kernel bypass, `implemented_by`, `extern` | none found by grep. `native_decide` was removed in db804ce; the big power comparisons use `norm_num` with `set_option exponentiation.threshold 100000000` |
| Small `decide` | `collatzComp_one`, `collatzComp_two`, `farey_14_15` (`decide +revert`) use ordinary kernel `decide`, which adds no axiom |
| Dependencies | Mathlib only |

**Build risks worth checking first** (from the Claude audit): the three real-number inequalities on the main path (`conv14_lt_logb_three`, `conv16_lt_logb_three`, `logb_three_plus_lt_conv13`) end in `norm_num` goals that compare powers with exponents in the tens of millions. Two `grind` calls in `rational_approx_bound` carry real arithmetic. All are mathematically true; whether the tactics close them at this size is something only a build shows.

Kernel-checked arithmetic on numbers with millions of digits (for example 2^85137581 against 3^53715833 in `conv16_lt_logb_three`) relies on Lean's GMP-accelerated `Nat` operations. It is ordinary kernel checking, but it is the part most worth rebuilding.

## What the Lean does *not* contain

- **The computer verification up to 2⁴⁰.** The headlines assume `2 ^ 40 < c.minElem`. "Every nontrivial cycle has at least 17,087,915 elements" needs, in addition, the 1990s computer check that every n ≤ 2⁴⁰ reaches 1. That is cited in a docstring (ContinuedFractions.lean lines 199-204) and not formalized. [`CollatzCycle.isNontrivial`](#/node/CollatzCycle.isNontrivial) is defined but unused.
- **Going round once.** The cardinality headlines assume injectivity. Shrinking a cycle that repeats itself to one that doesn't is easy on paper but not in the Lean.

## This site's own data

- **Declarations were read from the source text, not a Lean build.** `learn/tools/scan_decls.py` finds every top-level declaration (77) with its exact lines and text. Every declaration carries `"extracted": false`. "Mentions" and "proof uses" edges are matched by name, including `x.method` calls resolved from binder types, and may miss or misattribute a few uses.
- **Identifier links on the source pages** come from the same name matching (`data/xref.json` is marked `"heuristic": true`). Names in Mathlib's main namespaces (`Finset.`, `Real.`, `Nat.`, …) link to the Mathlib docs search.
- **"Unused" lemmas** (`three_pow_lt_two_pow_15`, `log_bound_at_2_40`, …) are unused according to that scan.
- **Audit.** The four headline statements were audited by a second model (Claude), reading the source only; see [the review](#/review) and `learn/CLAUDE_AUDIT.md`.
- **Explanations** are drafts by Grok Bot (`review: draft`), not yet checked by a human.

## To upgrade this page

Build on a capable machine (`lake exe cache get && lake build`), run `#print axioms` for each headline, replace `scan_decls.py` with `ExtractDecls.lean` + `build_xref.py` as on the other tangentproofs sites, and replace the "no" entries above.
