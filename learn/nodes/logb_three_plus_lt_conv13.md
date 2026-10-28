---
id: logb_three_plus_lt_conv13
title: 'Where 2⁴⁰ enters: log₂(3 + 1/m) < 301994/190537'
summary: '**The surprise:** with 2³⁹ instead of 2⁴⁰ this step fails and the bound collapses from 17,087,915 to 301,994
  (Eliahou, p. 55). One bit of verification is worth a factor of 56.'
review: draft
authors:
- grok-bot
caveats:
- The big-number comparisons are checked by norm_num and Lean's kernel; this site has not rebuilt them.
quiz:
- q: What does m > 2⁴⁰ buy?
  type: choice
  choices:
  - The window's upper end is below 301994/190537
  - It makes L even
  - Nothing
  answer: 0
  explain: That is the conclusion.
- q: Roughly how many binary digits does 2^7923474 have?
  type: choice
  choices:
  - 7,923,475
  - 301,994
  - '40'
  answer: 0
  explain: 2^n has n+1 binary digits.
- q: Is the related standalone lemma `log_bound_at_2_40` used by the main proof?
  type: choice
  choices:
  - No, it is proved but unused; this lemma redoes the check inside its own proof
  - 'Yes'
  answer: 0
  explain: In our source scan nothing refers to `log_bound_at_2_40`.
---
## Plain English

**Theorem (`logb_three_plus_lt_conv13`).** For every natural number m > 2⁴⁰, log₂(3 + 1/m) < 301994/190537.

Equivalently (3 + 1/m)^190537 < 2^301994. Since 1/m < 2⁻⁴⁰ it is enough to check (3·2⁴⁰ + 1)^190537 < 2^(301994 + 40·190537) = 2^7923474, a comparison of numbers with millions of digits, done by `norm_num` inside the proof.

The margin is thin, about 10%: log₂(3 + 2⁻⁴⁰) − log₂ 3 ≈ 4.4·10⁻¹³, against ≈ 4.9·10⁻¹³ for the gap up to 301994/190537. Eliahou remarks (p. 55) that had the conjecture been verified only up to 2³⁹, this step would fail and the best bound he could claim would be **301,994**. One more bit of computer verification multiplied the bound by more than 56.
