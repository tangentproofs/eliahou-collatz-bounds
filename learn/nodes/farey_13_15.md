---
id: farey_13_15
title: 301994/190537 and 17087915/10781274 are Farey neighbours
summary: '**The surprise:** two convergents of log₂ 3 found by continued fractions satisfy a cross-multiplication
  identity that equals exactly 1.'
review: draft
authors:
- grok-bot
quiz:
- q: What is the value of the expression?
  type: choice
  choices:
  - '1'
  - '0'
  - −1
  answer: 0
  explain: As stated.
- q: Which fraction is larger?
  type: choice
  choices:
  - 301994/190537
  - 17087915/10781274
  answer: 0
  explain: p'q − pq' = 1 > 0 with p'/q' = 301994/190537.
- q: What does the identity allow?
  type: choice
  choices:
  - Applying the Farey bound and coefficient lemmas
  - Nothing
  answer: 0
  explain: It is the `hfarey` hypothesis.
---
## Plain English

**Theorem (`farey_13_15`).** 301994 · 10781274 − 17087915 · 190537 = 1.

So 17087915/10781274 < 301994/190537 are Farey neighbours, the pair used for the "above the middle" case in [`rational_linear_form`](#/node/rational_linear_form). Checked by `norm_num`.
