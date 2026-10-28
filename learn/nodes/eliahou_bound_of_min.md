---
id: eliahou_bound_of_min
title: L ≥ 17,087,915 (bounds the length, not the distinct values)
summary: '**The surprise:** this bound is on L, the length of the indexing, which for a repeated loop can be bigger
  than the number of distinct values, so on its own it is weaker than it looks.'
review: draft
authors:
- grok-bot
quiz:
- q: Does `eliahou_bound_of_min` assume the cycle has no repeated values?
  type: choice
  choices:
  - 'Yes'
  - 'No'
  answer: 1
  explain: 'Its only hypothesis besides the cycle is `hmin : 2 ^ 40 < cyc.minElem`.'
- q: Then what exactly is bounded?
  type: choice
  choices:
  - the number of distinct values
  - the length parameter L
  - the minimum
  answer: 1
  explain: The conclusion is `17087915 ≤ L`.
- q: Which theorem turns this into a bound on distinct values?
  type: choice
  choices:
  - eliahou_bound_card
  - eliahou_product_formula
  - farey_pair_bound
  answer: 0
  explain: '`eliahou_bound_card` rewrites with `card_eq_of_injective`.'
---
## Plain English

**Theorem (`eliahou_bound_of_min`).** For every [`CollatzCycle`](#/node/CollatzCycle) `cyc` of length L whose smallest element is above 2⁴⁰, L ≥ 17,087,915.

It is [`eliahou_bound`](#/node/eliahou_bound) with the "some element is odd" hypothesis filled in by [`numOdd_pos`](#/node/CollatzCycle.numOdd_pos).

Because a `CollatzCycle` may go round a shorter loop several times, L here is "a" period. If the shortest loop had period p and you went round it twice, L = 2p, and the theorem only says 2p ≥ 17087915. (Applied to the once-round cycle it gives p ≥ 17087915 too, but that step is not in the Lean.) [`eliahou_bound_card`](#/node/eliahou_bound_card) adds injectivity to talk about distinct values.
