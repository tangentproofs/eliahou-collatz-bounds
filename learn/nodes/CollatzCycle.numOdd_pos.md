---
id: CollatzCycle.numOdd_pos
title: Every cycle has an odd element
summary: '**The surprise:** an all-even cycle is impossible for a one-line reason: halving its smallest element
  would give a smaller element of the cycle.'
review: draft
authors:
- grok-bot
quiz:
- q: Why does the proof look at the *smallest* element?
  type: choice
  choices:
  - Because T of it, m/2, would be an even smaller element of the cycle
  - Because it is odd
  - Because it is 1
  answer: 0
  explain: '`hge : c.minElem ≤ c.minElem / 2` and `hlt : c.minElem / 2 < c.minElem`.'
- q: Where is positivity used?
  type: choice
  choices:
  - to show m/2 < m
  - nowhere
  answer: 0
  explain: '`Nat.div_lt_self (c.pos i) …` needs m > 0.'
- q: Does it need min > 2⁴⁰?
  type: choice
  choices:
  - 'Yes'
  - No, it holds for every CollatzCycle
  answer: 1
  explain: No hypothesis beyond the cycle itself.
---
## Plain English

**Theorem (`c.numOdd_pos`).** Every [`CollatzCycle`](#/node/CollatzCycle) has at least one odd element: 0 < [`numOdd`](#/node/CollatzCycle.numOdd).

Proof (Defs.lean lines 133-155): suppose every element is even. Take a position holding the minimum m. The next element is T(m) = m/2, which is in the cycle, so m ≤ m/2. But m is positive, so m/2 < m. Contradiction.

This is what lets the paper-facing theorems drop the hypothesis `0 < c.numOdd`.
