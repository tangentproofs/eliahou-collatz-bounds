---
id: eliahou_theorem_1_1
title: 'Eliahou''s Theorem 1.1: the length of a high Collatz cycle'
summary: '**The surprise:** the possible lengths of a hypothetical Collatz cycle above 2⁴⁰ are not just large, they
  have a rigid shape: 301994·a + 17087915·b + 85137581·c with b > 0 and a·c = 0, all because of three fractions
  close to log₂ 3.'
review: draft
authors:
- grok-bot
caveats:
- The Lean theorem is about the **compressed** map T(n) = n/2 or (3n+1)/2. In the original 3x+1 map the same cycle
  also visits each 3n+1, so it is longer (L plus the number of odd steps). Eliahou's paper also counts T-cycles.
- The hypothesis is min > 2⁴⁰, not 'nontrivial'. Reading it as 'every cycle other than 1 → 2 → 1' needs the computer
  check that all n ≤ 2⁴⁰ reach 1, which is outside the Lean.
- Injectivity is a hypothesis. Every cycle can be shrunk to an injective one (go round once), but that step is not
  formalized; without it see [eliahou_bound_of_min](#/node/eliahou_bound_of_min), which bounds L rather than the
  number of distinct values.
- This site did not build the Lean; see the Trust page.
widgets:
- type: walkthrough
  title: How LinearForm.lean proves it (LinearForm.lean, lines 125-179)
  config:
    steps:
    - text: The length is the number of distinct values (injectivity)
      lean: rw [cyc.card_eq_of_injective hinj]
      note: Rewrite the cardinality of the set of values as L. From here on everything is about L.
      uses:
      - CollatzCycle.card_eq_of_injective
    - text: The cycle has at least one odd element, so k₁ = numOdd > 0
      lean: exact rational_linear_form cyc.numOdd_pos hmin
      note: 'numOdd_pos is proved in Defs.lean: an all-even cycle would contain half its smallest element.'
      link: rational_linear_form
      uses:
      - CollatzCycle.numOdd_pos
    - text: 'Sandwich: log₂ 3 < L/k₁ ≤ log₂(3 + 1/m)'
      lean: (log2_three_lt_ratio cyc cyc.numOdd_pos) (ratio_le_log cyc cyc.numOdd_pos)
      note: These come from the product formula ∏(3 + 1/n) = 2^L over the odd elements.
      link: eliahou_sandwich
      uses:
      - log2_three_lt_ratio
      - ratio_le_log
    - text: 'Trap L/k₁ between two convergents: 85137581/53715833 < L/k₁ < 301994/190537'
      lean: 'have h_low : (85137581 : ℚ) / 53715833 < (L : ℚ) / k₁ :='
      note: The lower end uses conv16_lt_logb_three (2^85137581 < 3^53715833); the upper end uses m > 2⁴⁰ (logb_three_plus_lt_conv13).
      uses:
      - conv16_lt_logb_three
      - logb_three_plus_lt_conv13
      hard: true
    - text: 'Case L/k₁ < 17087915/10781274: L = b·17087915 + c·85137581 with b, c > 0'
      lean: farey_intermediate_coeffs
      note: The two convergents are Farey neighbours (farey_15_16), and a fraction strictly between Farey neighbours
        is a positive combination of them.
      uses:
      - farey_intermediate_coeffs
      - farey_15_16
    - text: 'Case L/k₁ = 17087915/10781274: L is a multiple of 17087915'
      lean: exact coprime_15.dvd_of_dvd_mul_left this
      note: 17087915 and 10781274 are coprime, so the numerator divides L.
      uses:
      - coprime_15
    - text: 'Case L/k₁ > 17087915/10781274: L = a·301994 + b·17087915 with a, b > 0'
      lean: farey_13_15 hgt h_high
      note: Same Farey argument with the other neighbour pair (301994/190537, 17087915/10781274).
      uses:
      - farey_13_15
      - farey_intermediate_coeffs
quiz:
- q: What does the theorem assume about the numbers in the cycle?
  type: choice
  choices:
  - that they are all odd
  - that the smallest is greater than 2⁴⁰ and no value repeats
  - that the Collatz conjecture is true
  - 'nothing: it is about every cycle'
  answer: 1
  explain: 'The hypotheses are `hinj : Function.Injective cyc.seq` and `hmin : 2 ^ 40 < cyc.minElem`.'
- q: Which coefficient is guaranteed to be positive?
  type: choice
  choices:
  - a (the coefficient of 301994)
  - b (the coefficient of 17087915)
  - c (the coefficient of 85137581)
  - none of them
  answer: 1
  explain: The conclusion is `∃ a b cCoeff, 0 < b ∧ a * cCoeff = 0 ∧ …`. So b ≥ 1, and the length is at least 17087915.
- q: Does this theorem say that a nontrivial Collatz cycle exists?
  type: choice
  choices:
  - Yes, it constructs one
  - 'No: it only says what length one would have to have'
  answer: 1
  explain: It is a statement about every cycle satisfying the hypotheses; there may be none. The known cycle 1 →
    2 → 1 is excluded by min > 2⁴⁰.
- q: Where does the number 2⁴⁰ come from in the classical argument?
  type: choice
  choices:
  - It is the largest number the Lean kernel can handle
  - A computer verification that all numbers below 2⁴⁰ reach 1, so other cycles must lie above it
  - It is the length of the trivial cycle
  answer: 1
  explain: Eliahou took 2⁴⁰ from the computer checks of the day. In Lean it is simply the hypothesis `hmin`; the
    computer check is not formalized.
---
## Plain English

**Theorem (`eliahou_theorem_1_1`).** Take a cycle of the compressed Collatz map ([`collatzComp`](#/node/collatzComp)), written as a list of L positive numbers going round a loop ([`CollatzCycle`](#/node/CollatzCycle)). Suppose

1. no number appears twice in the list (`Function.Injective cyc.seq`), and
2. the smallest number in it ([`minElem`](#/node/CollatzCycle.minElem)) is bigger than 2⁴⁰.

Then the number of distinct values in the cycle can be written as

> 301994·a + 17087915·b + 85137581·c

for some natural numbers a, b, c with **b > 0** and **a·c = 0** (at most one of a and c is non-zero).

Since b ≥ 1, the length is at least 17,087,915. That corollary is [`eliahou_bound_card`](#/node/eliahou_bound_card).

The three numbers are numerators of convergents of the continued fraction of log₂ 3:
301994/190537, 17087915/10781274 and 85137581/53715833. The proof never looks for cycles. It shows that L divided by the number of odd steps must land in a very narrow window just above log₂ 3, and then asks which fractions fit in that window.

### Why the hypotheses are there

* **min > 2⁴⁰.** This is exactly the hypothesis of the paper's Theorem 1.1. The window above log₂ 3 has width set by the smallest element m: it is (log₂ 3, log₂(3 + 1/m)]. Eliahou used the 1990s computer check that every number below 2⁴⁰ reaches 1, so any *other* cycle lives above 2⁴⁰. That computer check is **not** in the Lean: the theorem simply assumes min > 2⁴⁰.
* **Injective.** A [`CollatzCycle`](#/node/CollatzCycle) of length L may go round a shorter loop several times. Injectivity makes L the number of different values (`CollatzCycle.card_eq_of_injective`).
