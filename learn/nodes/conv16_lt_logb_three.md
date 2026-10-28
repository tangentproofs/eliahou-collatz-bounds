---
id: conv16_lt_logb_three
title: 85137581/53715833 is just below log₂ 3
summary: '**The surprise:** proving one fraction is below log₂ 3 here means comparing 2^85137581 with 3^53715833,
  numbers with about 25.6 million decimal digits each.'
review: draft
authors:
- grok-bot
quiz:
- q: Which integer inequality is equivalent?
  type: choice
  choices:
  - 2^85137581 < 3^53715833
  - 3^85137581 < 2^53715833
  answer: 0
  explain: a/b < log₂ 3 ⇔ 2^a < 3^b.
- q: Which tactic does the heavy lifting?
  type: choice
  choices:
  - norm_num
  - native_decide
  - sorry
  answer: 0
  explain: The README says no native_decide remains; norm_num with a raised exponentiation threshold.
- q: Is 85137581/53715833 above or below log₂ 3?
  type: choice
  choices:
  - below
  - above
  answer: 0
  explain: As stated.
---
## Plain English

**Theorem (`conv16_lt_logb_three`).** 85137581/53715833 < log₂ 3.

Equivalently 2^85137581 < 3^53715833. The proof rewrites the real logarithm inequality into this integer comparison and settles it with `norm_num` (LinearForm.lean lines 84-89). It is the lower edge of the window in [`rational_linear_form`](#/node/rational_linear_form).
