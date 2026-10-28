---
id: collatzMul
title: '2·T(n): 3n+1 if odd, n if even'
summary: '**The surprise:** doubling T removes every division, which turns the cycle condition into a statement
  about products of whole numbers.'
review: draft
authors:
- grok-bot
quiz:
- q: collatzMul(5) =
  type: choice
  choices:
  - '16'
  - '8'
  - '5'
  answer: 0
  explain: '5 is odd: 3·5 + 1 = 16 = 2·T(5) = 2·8.'
- q: collatzMul(6) =
  type: choice
  choices:
  - '6'
  - '3'
  - '19'
  answer: 0
  explain: 6 is even.
- q: How does it relate to T?
  type: choice
  choices:
  - collatzMul n = 2 · T n
  - collatzMul n = T n + 1
  answer: 0
  explain: '`collatzMul_eq_two_mul_collatzComp`.'
---
## Plain English

**Definition (`collatzMul`).** collatzMul(n) = 3n + 1 if n is odd, n if n is even. It equals 2·T(n) (`collatzMul_eq_two_mul_collatzComp`).

Multiplying over a cycle: ∏ collatzMul(xᵢ) = 2^L ∏ T(xᵢ) = 2^L ∏ xᵢ ([`prod_collatzMul_eq`](#/node/prod_collatzMul_eq)).
