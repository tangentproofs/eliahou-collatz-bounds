---
id: rational_linear_form
title: 'Pure number theory: fractions in the window'
summary: '**The surprise:** this is the heart of Theorem 1.1, and it never mentions Collatz. Any fraction L/k₁ just
  above log₂ 3 (within log₂(3 + 2⁻⁴⁰)) has numerator 301994a + 17087915b + 85137581c.'
review: draft
authors:
- grok-bot
widgets:
- type: walkthrough
  title: The three cases (LinearForm.lean, lines 125-166)
  config:
    steps:
    - text: 'Lower end: 85137581/53715833 < log₂ 3 < L/k₁'
      lean: rat_of_real_div_lt (by norm_num) hk₁ (conv16_lt_logb_three.trans hlower)
      uses:
      - conv16_lt_logb_three
    - text: 'Upper end: L/k₁ ≤ log₂(3 + 1/m) < 301994/190537 (uses m > 2⁴⁰)'
      lean: (lt_of_le_of_lt hupper (logb_three_plus_lt_conv13 m hm))
      uses:
      - logb_three_plus_lt_conv13
      hard: true
    - text: Compare with the middle convergent 17087915/10781274
      lean: 'rcases lt_trichotomy ((L : ℚ) / k₁) ((17087915 : ℚ) / 10781274) with hlt | heq | hgt'
    - text: 'Below: Farey pair (p₁₆/q₁₆, p₁₅/q₁₅) gives L = b·p₁₅ + c·p₁₆'
      lean: farey_15_16 h_low hlt
      uses:
      - farey_intermediate_coeffs
      - farey_15_16
    - text: 'Equal: coprimality gives L = 17087915·b'
      lean: exact coprime_15.dvd_of_dvd_mul_left this
      uses:
      - coprime_15
    - text: 'Above: Farey pair (p₁₅/q₁₅, p₁₃/q₁₃) gives L = a·p₁₃ + b·p₁₅'
      lean: farey_13_15 hgt h_high
      uses:
      - farey_13_15
quiz:
- q: Does this theorem mention Collatz cycles?
  type: choice
  choices:
  - 'Yes'
  - No, only natural numbers L, k₁, m and logarithms
  answer: 1
  explain: Its hypotheses are `0 < k₁`, `2 ^ 40 < m` and the two log inequalities.
- q: What makes two fractions p/q < p'/q' 'Farey neighbours' here?
  type: choice
  choices:
  - p'·q − p·q' = 1
  - p + p' = q + q'
  - they have equal denominators
  answer: 0
  explain: '`hfarey : p'' * q - p * q'' = 1` in `farey_intermediate_coeffs`.'
- q: If L/k₁ equals 17087915/10781274 exactly, what are a and c?
  type: choice
  choices:
  - both 0
  - a = 1, c = 0
  - a = 0, c = 1
  answer: 0
  explain: 'The proof returns `⟨0, b, 0, …⟩`: L = 17087915·b.'
---
## Plain English

**Theorem (`rational_linear_form`).** Let k₁ > 0, L be natural numbers and m > 2⁴⁰. If

> log₂ 3 < L/k₁ ≤ log₂(3 + 1/m),

then L = 301994·a + 17087915·b + 85137581·c for some a, b, c ≥ 0 with b > 0 and a·c = 0.

### Proof idea

The window is inside (85137581/53715833, 301994/190537), two convergents of log₂ 3 on either side of the middle convergent 17087915/10781274. Neighbouring pairs among these three fractions are *Farey neighbours* (cross-differences equal 1: [`farey_15_16`](#/node/farey_15_16), [`farey_13_15`](#/node/farey_13_15)). Any fraction strictly between Farey neighbours p/q < p'/q' is (a·p + b·p')/(a·q + b·q') with a, b ≥ 1 ([`farey_intermediate_coeffs`](#/node/farey_intermediate_coeffs)). So:

* below the middle convergent: L = b·17087915 + c·85137581;
* equal to it: L is a multiple of 17087915 (they are coprime, [`coprime_15`](#/node/coprime_15));
* above it: L = a·301994 + b·17087915.

In every case b > 0 and one of a, c is zero.
