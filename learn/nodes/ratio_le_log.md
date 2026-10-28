---
id: ratio_le_log
title: L/k₁ ≤ log₂(3 + 1/min)
summary: '**The surprise:** the bigger the cycle''s smallest number, the closer L/k₁ is forced to log₂ 3, and that
  closeness is the entire source of the 17-million bound.'
review: draft
authors:
- grok-bot
quiz:
- q: If m > 2⁴⁰, L/k₁ is at most about
  type: choice
  choices:
  - log₂ 3 + 2⁻⁴⁰/(3 ln 2)
  - log₂ 3 + 1
  - '2'
  answer: 0
  explain: log₂(3 + ε) ≈ log₂ 3 + ε/(3 ln 2) for small ε = 1/m.
- q: Which inequality on the product does it use?
  type: choice
  choices:
  - ∏(3 + 1/x) ≤ (3 + 1/m)^k₁
  - ∏(3 + 1/x) ≥ (3 + 1/M)^k₁
  answer: 0
  explain: Each factor is at most 3 + 1/m.
- q: Is it strict?
  type: choice
  choices:
  - No, ≤
  - Yes, <
  answer: 0
  explain: '`(L : ℝ) / c.numOdd ≤ Real.logb 2 (3 + 1 / (c.minElem : ℝ))`.'
---
## Plain English

**Theorem (`ratio_le_log`).** For a cycle with k₁ > 0 and minimum m, L/k₁ ≤ log₂(3 + 1/m).

Proof: by the product formula, 2^L = ∏(3 + 1/x) ≤ (3 + 1/m)^k₁ ([`two_pow_le_bound_min`](#/node/two_pow_le_bound_min)); take logarithms. This is the upper half of the [sandwich](#/node/eliahou_sandwich).
