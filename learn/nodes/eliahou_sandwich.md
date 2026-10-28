---
id: eliahou_sandwich
title: 'Theorem 2.1, non-strict form: the sandwich on L/k₁'
summary: '**The surprise:** the ratio of a cycle''s length to its number of odd steps is squeezed between log₂(3
  + 1/max) and log₂(3 + 1/min). For a cycle of huge numbers that is a window of width about 1/min around log₂ 3.'
review: draft
authors:
- grok-bot
caveats:
- 'Weaker than the paper''s Theorem 2.1 in two ways: the paper''s *left* inequality is strict (because the largest
  element of a cycle is even), and the paper also proves a sharper right-hand bound log₂(3 + μ) with μ the mean
  of 1/n over the odd elements. Neither is formalized. The later argument only needs log₂ 3 < L/k₁ ≤ log₂(3 + 1/m),
  which the Lean has.'
- The header comment of Sandwich.lean (lines 13-16) advertises strict inequalities that no theorem in the file proves;
  the theorem's own docstring is accurate.
- The docstring calls this the 'full sandwich inequality'; the Claude audit flags 'full' as inaccurate.
widgets:
- type: walkthrough
  title: How Sandwich.lean proves it (Sandwich.lean, lines 34-101)
  config:
    steps:
    - text: Each odd factor 3 + 1/x is at most 3 + 1/m, so the product is at most (3 + 1/m)^k₁
      lean: '(3 + 1 / (c.minElem : ℝ)) ^ c.numOdd := by'
      link: prod_le_pow_min
    - text: …and at least (3 + 1/M)^k₁
      lean: '∏ i ∈ c.oddIndices, (3 + 1 / (c.seq i : ℝ)) := by'
      link: pow_max_le_prod
    - text: The product is 2^L (product formula)
      lean: rw [← eliahou_product_formula_real c]
      uses:
      - eliahou_product_formula_real
    - text: 'Take log₂ and divide by k₁: upper bound'
      lean: theorem ratio_le_log
      link: ratio_le_log
    - text: …and lower bound
      lean: theorem log_le_ratio
      link: log_le_ratio
    - text: Pair them up
      lean: ⟨log_le_ratio c hk, ratio_le_log c hk⟩
quiz:
- q: Which element of the cycle controls the *upper* end of the sandwich?
  type: choice
  choices:
  - the largest, M
  - the smallest, m
  - the first, x₀
  answer: 1
  explain: 'The upper bound is `Real.logb 2 (3 + 1 / (c.minElem : ℝ))`: small elements make 1/x big.'
- q: The paper states strict inequalities. What does the Lean state?
  type: choice
  choices:
  - strict < on both sides
  - ≤ on both sides
  - < on the left only
  answer: 1
  explain: Both conjuncts use ≤. The strict lower bound against log₂ 3 itself is a separate lemma, `log2_three_lt_ratio`.
- q: What extra hypothesis does `eliahou_sandwich` take?
  type: choice
  choices:
  - min > 2⁴⁰
  - 0 < c.numOdd
  - injectivity
  answer: 1
  explain: '`(hk : 0 < c.numOdd)`, which `CollatzCycle.numOdd_pos` always supplies.'
---
## Plain English

**Theorem (`eliahou_sandwich`).** Let `c` be a cycle of length L with k₁ = [`numOdd`](#/node/CollatzCycle.numOdd) odd elements, smallest element m ([`minElem`](#/node/CollatzCycle.minElem)) and largest M ([`maxElem`](#/node/CollatzCycle.maxElem)). If k₁ > 0, then

> log₂(3 + 1/M) ≤ L/k₁ ≤ log₂(3 + 1/m).

### Why

By the [product formula](#/node/eliahou_product_formula), the product of (3 + 1/x) over the k₁ odd elements is exactly 2^L. Each factor lies between 3 + 1/M and 3 + 1/m, so (3 + 1/M)^k₁ ≤ 2^L ≤ (3 + 1/m)^k₁. Taking log₂ and dividing by k₁ gives the sandwich.

Since 1/M > 0, the left end is already above log₂ 3, so L/k₁ > log₂ 3 ([`log2_three_lt_ratio`](#/node/log2_three_lt_ratio)). With m > 2⁴⁰, the right end is below log₂(3 + 2⁻⁴⁰). The rest of the proof is about fractions in that window.

The hypothesis `0 < c.numOdd` is always true ([`numOdd_pos`](#/node/CollatzCycle.numOdd_pos)); the version in Results.lean discharges it.
