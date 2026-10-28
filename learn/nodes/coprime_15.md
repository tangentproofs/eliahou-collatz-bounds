---
id: coprime_15
title: 17087915 and 10781274 are coprime
summary: '**The surprise:** this is what handles the case where L/k₁ hits the convergent exactly: then L must be
  a multiple of 17,087,915.'
review: draft
authors:
- grok-bot
quiz:
- q: If L/k₁ = 17087915/10781274, then
  type: choice
  choices:
  - 17087915 divides L
  - L = 10781274
  - k₁ = 1
  answer: 0
  explain: '`coprime_15.dvd_of_dvd_mul_left`.'
- q: Are consecutive convergent numerators and denominators always coprime?
  type: choice
  choices:
  - 'Yes'
  - 'No'
  answer: 0
  explain: Convergents are in lowest terms.
- q: Tactic?
  type: choice
  choices:
  - norm_num
  - decide
  answer: 0
  explain: As written.
---
## Plain English

**Theorem (`coprime_15`).** gcd(17087915, 10781274) = 1.

If L/k₁ = 17087915/10781274 then 10781274·L = 17087915·k₁, and coprimality forces 17087915 to divide L.
