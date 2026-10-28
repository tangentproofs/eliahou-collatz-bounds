---
id: farey_15_16
title: 17087915/10781274 and 85137581/53715833 are Farey neighbours
summary: '**The surprise:** the next convergent, 85137581/53715833, is also a Farey neighbour, and that is what
  produces the third coefficient c in Theorem 1.1.'
review: draft
authors:
- grok-bot
quiz:
- q: Which is larger?
  type: choice
  choices:
  - 17087915/10781274
  - 85137581/53715833
  answer: 0
  explain: p'/q' = 17087915/10781274.
- q: Which coefficient of Theorem 1.1 does this pair produce?
  type: choice
  choices:
  - c (85137581)
  - a (301994)
  answer: 0
  explain: Below the middle, L = b·17087915 + c·85137581.
- q: How is it proved?
  type: choice
  choices:
  - norm_num
  - a long induction
  answer: 0
  explain: One line, `norm_num`.
---
## Plain English

**Theorem (`farey_15_16`).** 17087915 · 53715833 − 85137581 · 10781274 = 1.

So 85137581/53715833 < 17087915/10781274 are Farey neighbours, used for the "below the middle" case in [`rational_linear_form`](#/node/rational_linear_form).
