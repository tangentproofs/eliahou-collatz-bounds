---
id: CollatzCycle.oddIndices
title: Positions holding odd numbers
summary: '**The surprise:** the cycle''s "odd elements" are tracked as *positions*, not values, so a repeated value
  is counted once per visit.'
review: draft
authors:
- grok-bot
quiz:
- q: For the cycle 1, 2 (positions 0 and 1), what is `oddIndices`?
  type: choice
  choices:
  - '{0}'
  - '{1}'
  - '{0, 1}'
  - ∅
  answer: 0
  explain: Position 0 holds 1, which is odd; position 1 holds 2.
- q: Is it a set of numbers or of positions?
  type: choice
  choices:
  - numbers
  - positions (elements of Fin L)
  answer: 1
  explain: Its type is `Finset (Fin L)`.
- q: What is its size called elsewhere?
  type: choice
  choices:
  - numOdd (k₁)
  - minElem
  - L
  answer: 0
  explain: '`numOdd c := c.oddIndices.card`.'
---
## Plain English

**Definition (`c.oddIndices`).** The set of positions i in {0, …, L−1} where the number xᵢ is odd. Its size is [`numOdd`](#/node/CollatzCycle.numOdd), the k₁ of the paper. `evenIndices` is the complementary set.

Products such as ∏_{i ∈ oddIndices} (3xᵢ + 1) in the [product formula](#/node/eliahou_product_formula) range over these positions.
