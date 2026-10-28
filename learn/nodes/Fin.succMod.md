---
id: Fin.succMod
title: Wrap-around successor on positions 0…L−1
summary: '**The surprise:** to say "the list closes up into a loop" Lean needs an explicit wrap-around: position
  L−1 is followed by position 0.'
review: draft
authors:
- grok-bot
quiz:
- q: With L = 5, what is the successor of position 4?
  type: choice
  choices:
  - '5'
  - '0'
  - '4'
  - undefined
  answer: 1
  explain: '(4 + 1) mod 5 = 0: the loop closes.'
- q: 'Why does it take the argument `hL : 0 < L`?'
  type: choice
  choices:
  - To prove the result is less than L (mod by zero would be meaningless)
  - It is unused
  - To make L even
  answer: 0
  explain: '`Nat.mod_lt _ hL` proves (i+1) % L < L, which needs L > 0.'
- q: Is `Fin.succMod` from Mathlib?
  type: choice
  choices:
  - 'Yes'
  - 'No: this project defines it (in Defs.lean)'
  answer: 1
  explain: It is defined in Collatz/Defs.lean lines 37-38, in the `Fin` namespace.
---
## Plain English

**Definition (`Fin.succMod`).** For a position i in {0, 1, …, L−1} (a `Fin L`) and a proof that L > 0, `i.succMod hL` is the position (i + 1) mod L. So 0 → 1 → … → L−1 → 0.

It is used in [`CollatzCycle`](#/node/CollatzCycle) to say that T sends the number at position i to the number at the next position, going round the loop. The proof that it is a bijection ([`succMod_bijective`](#/node/succMod_bijective)) is what lets the product formula reindex a product around the cycle.
