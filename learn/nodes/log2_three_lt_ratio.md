---
id: log2_three_lt_ratio
title: L/k₁ is strictly above log₂ 3
summary: '**The surprise:** going round any Collatz cycle, odd steps must be *rarer* than log₂ 3 predicts would
  balance: L/k₁ > log₂ 3 for every cycle, even 1 → 2 → 1.'
review: draft
authors:
- grok-bot
quiz:
- q: For the trivial cycle, L/k₁ is
  type: choice
  choices:
  - '2'
  - '1.585'
  - '1'
  answer: 0
  explain: L = 2, k₁ = 1.
- q: Is the inequality strict?
  type: choice
  choices:
  - 'Yes'
  - 'No'
  answer: 0
  explain: '`Real.logb 2 3 < (L : ℝ) / c.numOdd`.'
- q: Which element's size is used?
  type: choice
  choices:
  - the maximum (only its positivity)
  - the minimum, which must exceed 2⁴⁰
  answer: 0
  explain: The proof uses `log_le_ratio` and that maxElem is positive.
---
## Plain English

**Theorem (`log2_three_lt_ratio`).** For every cycle with k₁ > 0, log₂ 3 < L/k₁.

From the lower half of the [sandwich](#/node/eliahou_sandwich): L/k₁ ≥ log₂(3 + 1/M), and 3 + 1/M > 3 because M is positive. For 1 → 2 → 1, L/k₁ = 2 > 1.585.
