---
id: CollatzCycle
title: A Collatz cycle of length L
summary: '**The surprise:** nothing forces the L positions to hold *different* numbers, so 1, 2, 1, 2 is a `CollatzCycle
  4`. That is why the cardinality theorems also assume injectivity.'
review: draft
authors:
- grok-bot
caveats:
- L counts positions, with repeats. Eliahou's Card Ω is the number of distinct elements; the Lean bridges the two
  with injectivity.
quiz:
- q: Is the list 1, 2, 1, 2 a `CollatzCycle 4`?
  type: choice
  choices:
  - 'Yes'
  - No, values must be distinct
  - No, L must be even
  answer: 0
  explain: T(1) = 2, T(2) = 1, and all are positive, so `step` and `pos` hold. Nothing requires distinct values.
- q: Why must every element be positive?
  type: choice
  choices:
  - Because T(0) = 0 would allow the silly cycle 0, 0, …
  - Because Lean has no negative numbers
  - It is not required
  answer: 0
  explain: '`pos : ∀ i, 0 < seq i`. Without it, the constant list 0 would be a cycle of every length.'
- q: Which map must the cycle follow?
  type: choice
  choices:
  - n ↦ 3n + 1 or n/2
  - 'the compressed map T: n/2 or (3n+1)/2'
  - n ↦ n + 1
  answer: 1
  explain: '`step : ∀ i, collatzComp (seq i) = seq (i.succMod hL)`.'
---
## Plain English

**Structure (`CollatzCycle L`).** A cycle of length L is:

* `hL`: a proof that L > 0;
* `seq`: a list of L natural numbers x₀, …, x_{L−1} (a function from `Fin L`);
* `pos`: every xᵢ is positive;
* `step`: T(xᵢ) = x_{i+1}, with indices taken mod L ([`collatzComp`](#/node/collatzComp), [`Fin.succMod`](#/node/Fin.succMod)).

So it is an orbit of the compressed map that comes back to where it started after L steps.

Two things the structure does **not** require:

1. **Distinct values.** Going round the loop 1 → 2 → 1 twice is a `CollatzCycle 4`. L is therefore "a period", not necessarily the smallest one. Theorems that talk about the number of distinct values add `Function.Injective c.seq` (or use [`ExactCollatzCycle`](#/node/ExactCollatzCycle)).
2. **Nontriviality.** The trivial cycle 1, 2 is a `CollatzCycle 2` ([`trivialCycle`](#/node/trivialCycle)). The headline theorems exclude it by assuming the smallest element is above 2⁴⁰.
