---
id: eliahou_bound_card
title: A Collatz cycle above 2⁴⁰ has at least 17,087,915 distinct numbers
summary: '**The surprise:** a cycle that stays above 2⁴⁰ would have to contain at least 17,087,915 *different* numbers,
  a bound proved with no search at all, from the continued fraction of log₂ 3.'
review: draft
authors:
- grok-bot
caveats:
- min > 2⁴⁰ is a hypothesis; the computer check that justifies it for 'every nontrivial cycle' is not formalized.
- Counts elements of a cycle of the compressed map T, as in the paper.
widgets:
- type: walkthrough
  title: How the bound is proved (LinearForm.lean, lines 94-105)
  config:
    steps:
    - text: Distinct values = L, by injectivity
      lean: rw [cyc.card_eq_of_injective hinj]
      uses:
      - CollatzCycle.card_eq_of_injective
    - text: L ≥ 17087915 for any cycle above 2⁴⁰
      lean: exact eliahou_bound_of_min cyc hmin
      link: eliahou_bound_of_min
    - text: …which discharges the 'some element is odd' hypothesis
      lean: eliahou_bound cyc hmin cyc.numOdd_pos
      note: eliahou_bound in ContinuedFractions.lean takes 0 < numOdd as an extra hypothesis; numOdd_pos proves
        it.
      uses:
      - eliahou_bound
      - CollatzCycle.numOdd_pos
quiz:
- q: What is bounded below by 17,087,915?
  type: choice
  choices:
  - the largest element of the cycle
  - the number of distinct values in the cycle
  - the number of odd elements
  - 2⁴⁰
  answer: 1
  explain: 'The conclusion is `17087915 ≤ (Finset.univ.image cyc.seq).card`: the size of the set of values.'
- q: Why is injectivity assumed here?
  type: choice
  choices:
  - Without it the cycle could repeat a shorter loop, and L would not count distinct values
  - Because Lean cannot handle repeated numbers
  - It is not assumed
  answer: 0
  explain: '`hinj : Function.Injective cyc.seq` is used to rewrite the cardinality as L (`card_eq_of_injective`).'
- q: Does the proof check any numbers by computer search?
  type: choice
  choices:
  - Yes, all numbers up to 2⁴⁰
  - 'No: it compares powers like 3^10590737 and 2^16785921 symbolically with norm_num'
  - Yes, it enumerates cycles
  answer: 1
  explain: No cycle search appears. The heavy computation is comparing huge powers of 2 and 3, done by `norm_num`
    in ContinuedFractions.lean.
---
## Plain English

**Theorem (`eliahou_bound_card`).** If `cyc` is a cycle of the compressed Collatz map ([`CollatzCycle`](#/node/CollatzCycle)) in which no value repeats, and its smallest element ([`minElem`](#/node/CollatzCycle.minElem)) is greater than 2⁴⁰, then the set of its values has at least **17,087,915** elements.

This is the headline consequence of [Theorem 1.1](#/node/eliahou_theorem_1_1), but in Lean it is proved by a slightly different route: through [`eliahou_bound_of_min`](#/node/eliahou_bound_of_min) and [`rational_approx_bound`](#/node/rational_approx_bound), which only needs the window (16785921/10590737, 301994/190537) and the Farey bound, not the full linear form.

### Where the number comes from

L/k₁ (cycle length over number of odd steps) must lie strictly above log₂ 3 and at most log₂(3 + 2⁻⁴⁰). Every fraction in that window is "complicated": the simplest one is the convergent 17087915/10781274. Any fraction strictly between two Farey neighbours has numerator at least the sum of theirs ([`farey_pair_bound`](#/node/farey_pair_bound)), and that pins L ≥ 17087915.
