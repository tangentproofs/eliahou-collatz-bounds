---
id: trivialCycle
title: The known cycle 1 → 2 → 1
summary: '**The surprise:** the only known positive Collatz cycle is a perfectly good `CollatzCycle 2`; the theorems
  exclude it only through the hypothesis min > 2⁴⁰.'
review: draft
authors:
- grok-bot
quiz:
- q: Its length L is
  type: choice
  choices:
  - '2'
  - '3'
  - '1'
  answer: 0
  explain: Two positions.
- q: Do the headline theorems apply to it?
  type: choice
  choices:
  - No, its minimum is 1
  - 'Yes'
  answer: 0
  explain: They assume min > 2⁴⁰.
- q: In the usual 3x+1 map this cycle is
  type: choice
  choices:
  - 1 → 4 → 2 → 1 (length 3)
  - 1 → 2 → 1 (length 2)
  answer: 0
  explain: The compressed map skips 4.
---
## Plain English

**Definition (`trivialCycle`).** The cycle of length 2 with x₀ = 1, x₁ = 2: T(1) = 2 and T(2) = 1.

Its minimum is 1, so none of the headline theorems applies to it. It does satisfy the [product formula](#/node/eliahou_product_formula): 3·1 + 1 = 4 = 2².
