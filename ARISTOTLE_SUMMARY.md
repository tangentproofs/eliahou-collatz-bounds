# Summary of changes for run ffc37045-0f36-4039-93f8-d4fb3d553900

I have formalized Eliahou's 1993 paper "The 3x+1 problem: new lower bounds on nontrivial cycle lengths" in Lean 4 with Mathlib.

> **Update (main @ db804ce and later):** Pre-audit follow-ups are in. There is **no** `native_decide` and **no** remaining `sorry` on the paper-facing theorems. Large power / Farey facts use `norm_num` (with a raised `exponentiation.threshold`). Full Theorem 1.1 linear form is proved in `Collatz/LinearForm.lean`; paper-facing aliases live in `Results.lean`. Layout is `Collatz/` at the repo root (not `RequestProject/Collatz/`).

## Main Result (Fully Proved)

**`eliahou_bound`**: Any cycle of the compressed Collatz map with minimum element > 2^40 has at least **17,087,915** elements. Proved with standard axioms only (no sorry).

**`eliahou_theorem_1_1` / `rational_linear_form`**: For an exact (injective) cycle with `min > 2^40`,

`Card Ω = 301994·a + 17087915·b + 85137581·c`

for some `a, b, c ≥ 0` with `b > 0` and `a·c = 0`. Fully proved (no sorry).

## File Structure (`Collatz/`)

1. **`Defs.lean`** — Compressed Collatz map, cycles, `numOdd_pos`, `ExactCollatzCycle` / injectivity → `Card Ω` glue (sorry-free)

2. **`ProductFormula.lean`** — Lemma 2.2: ∏(3 + 1/n) = 2^L over odd cycle elements (sorry-free)

3. **`Sandwich.lean`** — Theorem 2.1 sandwich inequality and L/k₁ > log₂(3) (sorry-free)

4. **`ContinuedFractions.lean`** — Farey pair bound (Lemma 3.1), convergent numerical facts (including `3^10781274 < 2^17087915` via **`norm_num`**, not `native_decide`), `rational_approx_bound`, and **`eliahou_bound`** (sorry-free)

5. **`LinearForm.lean`** — Full Theorem 1.1 linear form and paper-facing wrappers that discharge `hk` via `numOdd_pos` (sorry-free)

6. **`Results.lean`** (repo root) — Thin comparator surface re-exporting paper-facing statements

## Summary

The formalization follows the paper's structure. Lemma 2.2, Theorem 2.1, the main lower bound, and the full linear form of Theorem 1.1 are all fully proved. See `README.md` and `Collatz/README.md` for current scope.
