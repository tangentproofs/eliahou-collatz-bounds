---
id: rational_approx_bound
title: Fractions in the window have numerator ≥ 17,087,915
summary: '**The surprise:** the simplest fraction squeezed between log₂ 3 and log₂(3 + 2⁻⁴⁰) already has numerator
  17,087,915.'
review: draft
authors:
- grok-bot
quiz:
- q: Which convergent of log₂ 3 sets the bound?
  type: choice
  choices:
  - 17087915/10781274
  - 301994/190537
  - 3/2
  answer: 0
  explain: Its numerator is the bound.
- q: Above the middle convergent, how big must L be?
  type: choice
  choices:
  - at least 17087915 + 301994
  - at least 301994
  - at least 2⁴⁰
  answer: 0
  explain: Farey bound with the pair (17087915/10781274, 301994/190537).
- q: Does it mention cycles?
  type: choice
  choices:
  - 'No'
  - 'Yes'
  answer: 0
  explain: It is about natural numbers and logarithms only.
---
## Plain English

**Theorem (`rational_approx_bound`).** For natural numbers k₁ > 0, L and m > 2⁴⁰, if log₂ 3 < L/k₁ ≤ log₂(3 + 1/m), then L ≥ 17087915.

Proof (ContinuedFractions.lean lines 172-197): the window lies inside (16785921/10590737, 301994/190537). Splitting at 17087915/10781274, the [Farey bound](#/node/farey_pair_bound) gives L ≥ 17087915 + 301994 above it, L ≥ 16785921 + 17087915 below it, and coprimality gives a multiple of 17087915 at it.

[`rational_linear_form`](#/node/rational_linear_form) is the sharper version used for Theorem 1.1.
