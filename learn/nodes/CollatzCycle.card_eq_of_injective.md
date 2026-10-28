---
id: CollatzCycle.card_eq_of_injective
title: Injective ⇒ L distinct values
summary: '**The surprise:** this two-line lemma is the entire bridge from Lean''s indexed cycle to the paper''s
  set Ω.'
review: draft
authors:
- grok-bot
quiz:
- q: What is concluded?
  type: choice
  choices:
  - (image of seq).card = L
  - L > 0
  answer: 0
  explain: '`(Finset.univ.image c.seq).card = L`.'
- q: Which Mathlib fact proves it?
  type: choice
  choices:
  - Finset.card_image_of_injective
  - Nat.mod_lt
  answer: 0
  explain: Plus `Finset.card_fin`.
- q: Without injectivity, how do card and L compare?
  type: choice
  choices:
  - card ≤ L
  - card ≥ L
  answer: 0
  explain: An image is never bigger than the domain.
---
## Plain English

**Theorem (`card_eq_of_injective`).** If a cycle's `seq` is injective, then the set of its values has exactly L elements.

Used as the first step of [Theorem 1.1](#/node/eliahou_theorem_1_1) and [`eliahou_bound_card`](#/node/eliahou_bound_card).
