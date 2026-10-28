---
id: CollatzCycle.numOdd
title: 'k₁: the number of odd steps'
summary: '**The surprise:** the whole proof is about the single ratio L/k₁. Cycle length over number of odd steps
  must be almost exactly log₂ 3.'
review: draft
authors:
- grok-bot
quiz:
- q: For the trivial cycle 1, 2, what are L and k₁?
  type: choice
  choices:
  - L = 2, k₁ = 1
  - L = 2, k₁ = 2
  - L = 1, k₁ = 1
  answer: 0
  explain: Two positions, one of which (holding 1) is odd.
- q: Roughly what must L/k₁ be for a cycle of large numbers?
  type: choice
  choices:
  - '2'
  - log₂ 3 ≈ 1.585
  - 3/2
  - '1'
  answer: 1
  explain: The sandwich puts it between log₂(3 + 1/M) and log₂(3 + 1/m).
- q: Why is it marked `noncomputable`?
  type: choice
  choices:
  - It uses classical reasoning (Finset filtering under `open Classical`-style instances); it does not affect the
    theorems
  - It is undefined
  - It uses an axiom beyond the standard three
  answer: 0
  explain: Lean marks definitions noncomputable when it cannot compile them to code; the logic is unaffected.
---
## Plain English

**Definition (`c.numOdd`).** The number of positions in the cycle holding an odd number, the size of [`oddIndices`](#/node/CollatzCycle.oddIndices). Eliahou calls it k₁.

Each odd step multiplies (roughly) by 3/2 and each even step by 1/2. To come back to the start you need 3^k₁ ≈ 2^L, so L/k₁ ≈ log₂ 3 ≈ 1.58496. The [sandwich](#/node/eliahou_sandwich) makes "≈" precise. It is always at least 1 ([`numOdd_pos`](#/node/CollatzCycle.numOdd_pos)).
