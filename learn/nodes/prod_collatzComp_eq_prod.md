---
id: prod_collatzComp_eq_prod
title: 'Going round the loop: ∏ T(xᵢ) = ∏ xᵢ'
summary: '**The surprise:** applying T to every element of a cycle just rotates the list, so the product does not
  change.'
review: draft
authors:
- grok-bot
quiz:
- q: Why are the two products equal?
  type: choice
  choices:
  - T shifts the list by one position, a reordering
  - T is the identity
  answer: 0
  explain: Reindex with `Equiv.ofBijective`.
- q: Does it need injectivity?
  type: choice
  choices:
  - 'No'
  - 'Yes'
  answer: 0
  explain: Only the cycle structure.
- q: Over which positions?
  type: choice
  choices:
  - all of Fin L
  - odd positions only
  answer: 0
  explain: '`∏ i : Fin L`.'
---
## Plain English

**Theorem (`prod_collatzComp_eq_prod`).** For every cycle, the product of T(xᵢ) over all positions equals the product of the xᵢ.

Since T(xᵢ) = x_{i+1 mod L} and i ↦ i+1 mod L is a bijection ([`succMod_bijective`](#/node/succMod_bijective)), it is the same product in a different order. First step of the [product formula](#/node/eliahou_product_formula).
