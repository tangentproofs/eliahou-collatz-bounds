---
id: CollatzCycle.minElem
title: The smallest number in the cycle
summary: '**The surprise:** this one number decides everything: the theorems need nothing about the cycle except
  that its minimum exceeds 2⁴⁰.'
review: draft
authors:
- grok-bot
quiz:
- q: What does `2 ^ 40 < c.minElem` say?
  type: choice
  choices:
  - Some element exceeds 2⁴⁰
  - Every element exceeds 2⁴⁰
  - The cycle has length above 2⁴⁰
  answer: 1
  explain: If the minimum is above 2⁴⁰, every element is.
- q: Why does `minElem` need L > 0?
  type: choice
  choices:
  - The minimum of an empty set is undefined
  - To make it computable
  - It does not
  answer: 0
  explain: '`Finset.min''` takes a non-emptiness proof, built from `c.hL`.'
- q: For the trivial cycle 1, 2, what is minElem?
  type: choice
  choices:
  - '1'
  - '2'
  - '0'
  answer: 0
  explain: The values are 1 and 2.
---
## Plain English

**Definition (`c.minElem`).** The minimum of the set of values {x₀, …, x_{L−1}}. Lean's `Finset.min'` needs a proof that the set is non-empty, which comes from L > 0.

It enters the [sandwich](#/node/eliahou_sandwich) through the upper bound log₂(3 + 1/m), and the headline theorems assume `2 ^ 40 < c.minElem`.
