---
id: ExactCollatzCycle
title: A cycle with no repeated values
summary: '**The surprise:** the paper''s Card Ω and Lean''s L only agree once you add this one field: injectivity.'
review: draft
authors:
- grok-bot
quiz:
- q: Is 1, 2, 1, 2 an ExactCollatzCycle 4?
  type: choice
  choices:
  - No, 1 repeats
  - 'Yes'
  answer: 0
  explain: Injectivity fails.
- q: What does injectivity buy?
  type: choice
  choices:
  - L = number of distinct values
  - min > 2⁴⁰
  answer: 0
  explain: '`card_eq_length`.'
- q: Is it a new kind of cycle or a cycle plus a property?
  type: choice
  choices:
  - a CollatzCycle plus a proof
  - something unrelated
  answer: 0
  explain: '`extends CollatzCycle L`.'
---
## Plain English

**Structure (`ExactCollatzCycle L`).** A [`CollatzCycle L`](#/node/CollatzCycle) together with a proof that `seq` is injective: no value appears at two positions. For such a cycle the number of distinct values is exactly L (`ExactCollatzCycle.card_eq_length`).

The headline theorems are also restated for this wrapper (`ExactCollatzCycle.eliahou_theorem_1_1`, `ExactCollatzCycle.eliahou_bound_card`).
