---
id: CollatzCycle.maxElem
title: The largest number in the cycle
summary: '**The surprise:** the largest element is only used to show L/k₁ is *strictly* above log₂ 3; any positive
  number would do.'
review: draft
authors:
- grok-bot
quiz:
- q: Which side of the sandwich uses maxElem?
  type: choice
  choices:
  - lower
  - upper
  answer: 0
  explain: '`Real.logb 2 (3 + 1 / (c.maxElem : ℝ)) ≤ (L : ℝ) / c.numOdd`.'
- q: Do the headline theorems put any hypothesis on maxElem?
  type: choice
  choices:
  - Yes, it must be below 2⁴⁰
  - 'No'
  answer: 1
  explain: Only minElem appears in the hypotheses.
- q: What does it contribute to the final bound?
  type: choice
  choices:
  - The strict inequality log₂ 3 < L/k₁
  - The number 17087915 directly
  - Nothing
  answer: 0
  explain: '`log2_three_lt_ratio` uses `log_le_ratio` and 1/M > 0.'
---
## Plain English

**Definition (`c.maxElem`).** The maximum of the set of values {x₀, …, x_{L−1}}, via `Finset.max'`.

It gives the lower end of the [sandwich](#/node/eliahou_sandwich), log₂(3 + 1/M) ≤ L/k₁, and since 1/M > 0 this is strictly bigger than log₂ 3 ([`log2_three_lt_ratio`](#/node/log2_three_lt_ratio)).
