# Formalization of Eliahou's Bound on Collatz Cycle Lengths

This directory contains a Lean 4 / Mathlib formalization of the main results from:

> Eliahou, S. (1993). "The 3x+1 problem: new lower bounds on nontrivial cycle lengths."
> Discrete Mathematics, 118(1-3), 45-56.

## Main Result

**Theorem** (`eliahou_bound`): Any cycle of the compressed Collatz map
with minimum element > 2^40 has at least **17,087,915** elements.

This is **fully proved** with no sorry, using only standard axioms.

## File Structure

### `Defs.lean` — Basic Definitions
- `collatzComp`: The compressed Collatz function T(n) = n/2 if even, (3n+1)/2 if odd
- `CollatzCycle`: Structure representing a cycle of length L
- `numOdd`, `numEven`, `minElem`, `maxElem`: Cycle statistics
- `trivialCycle`: The trivial cycle {1, 2}

### `ProductFormula.lean` — Lemma 2.2
- `eliahou_product_formula`: ∏_{i odd} (3·xᵢ + 1) = 2^L · ∏_{i odd} xᵢ
- `eliahou_product_formula_real`: ∏_{i odd} (3 + 1/xᵢ) = 2^L
- Helper lemmas about reindexing products over cycles

### `Sandwich.lean` — Theorem 2.1
- `eliahou_sandwich`: log₂(3 + 1/M) ≤ L/k₁ ≤ log₂(3 + 1/m)
- `log2_three_lt_ratio`: log₂(3) < L/k₁ (every cycle has ratio above log₂(3))

### `ContinuedFractions.lean` — Main Bound (Theorem 1.1)
- `farey_pair_bound`: Lemma 3.1 on Farey pairs
- Verified numerical facts about convergents of log₂(3):
  - `three_pow_lt_two_pow_15`: 3^10781274 < 2^17087915
  - `two_pow_lt_three_pow_14`: 2^16785921 < 3^10590737
  - `log_bound_at_2_40`: (3·2⁴⁰+1)^190537 < 2^7923474
  - `farey_13_15`, `farey_14_15`: Farey pair identities
- `rational_approx_bound`: Any L/k₁ in (log₂3, log₂(3+1/m)) with m > 2^40 has L ≥ 17087915
- **`eliahou_bound`**: The main theorem (**fully proved**)
- `eliahou_precise`: The more precise linear combination form (sorry — requires semi-convergent analysis)

## Proof Overview

The proof follows Eliahou's paper closely:

1. **Product Formula** (Lemma 2.2): For a Collatz cycle, the product ∏(3+1/n) over
   odd elements equals 2^L. This follows from the observation that ∏T(xᵢ) = ∏xᵢ
   (reindexing a cycle) combined with the multiplicative structure of T.

2. **Sandwich Inequality** (Theorem 2.1): Taking bounds on each factor using the
   min and max of the cycle gives log₂(3+1/M) ≤ L/k₁ ≤ log₂(3+1/m).

3. **Farey Pair Analysis** (Sections 3-4): The fraction L/k₁ must lie in the narrow
   interval (log₂(3), log₂(3+1/m)). Using the continued fraction expansion of log₂(3)
   and verified numerical bounds, we show any such fraction has L ≥ 17,087,915.
