---
id: collatzComp
title: The compressed Collatz map T
summary: '**The surprise:** T(0) = 0, so 0 is a fixed point of this Lean function. That is why a Collatz cycle in
  this project must consist of *positive* numbers.'
review: draft
authors:
- grok-bot
quiz:
- q: What is T(7)?
  type: choice
  choices:
  - '22'
  - '11'
  - '3'
  - '21'
  answer: 1
  explain: 7 is odd, so T(7) = (3·7 + 1)/2 = 22/2 = 11.
- q: What is T(0)?
  type: choice
  choices:
  - '0'
  - '1'
  - undefined
  answer: 0
  explain: 0 is even, so T(0) = 0/2 = 0. The docstring notes 0 is outside the domain of interest.
- q: How does T relate to the usual 3x+1 map?
  type: choice
  choices:
  - It is the same map
  - It combines the odd step 3n+1 with the halving that always follows it
  - It only applies to odd numbers
  answer: 1
  explain: 'For odd n, T(n) = (3n+1)/2: the usual map''s two steps n → 3n+1 → (3n+1)/2 in one.'
---
## Plain English

**Definition (`collatzComp`).** For a natural number n,

> T(n) = n/2 if n is even, and (3n + 1)/2 if n is odd.

This is the "compressed" or "accelerated" 3x+1 map used by Eliahou: when n is odd, 3n+1 is even, so the usual map would halve it next anyway; T does both steps at once. Every cycle of the usual map gives a cycle of T and vice versa, but the lengths differ (T skips the even number 3n+1).

Lean's natural-number division rounds down, but here it never has to: n/2 is only used for even n, and 3n+1 is even when n is odd. On n = 0 the definition gives 0, which is why [`CollatzCycle`](#/node/CollatzCycle) requires all its numbers to be positive.
