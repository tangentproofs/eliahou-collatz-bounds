---
id: farey_pair_bound
title: 'Lemma 3.1: between Farey neighbours, numerators add'
summary: '**The surprise:** between p/q and p''/q'' with p''q − pq'' = 1, the simplest fraction is the mediant (p+p'')/(q+q'').
  Nothing in between has a smaller numerator or denominator.'
review: draft
authors:
- grok-bot
quiz:
- q: Between 1/2 and 1/1, what is the smallest possible denominator?
  type: choice
  choices:
  - '2'
  - '3'
  - '4'
  answer: 1
  explain: q + q' = 2 + 1 = 3, e.g. 2/3.
- q: Which condition makes p/q and p'/q' Farey neighbours?
  type: choice
  choices:
  - p'q − pq' = 1
  - p = p'
  - q = q'
  answer: 0
  explain: '`hfarey : p'' * q - p * q'' = 1`.'
- q: Is subtraction here natural-number subtraction?
  type: choice
  choices:
  - Yes; with p/q < p'/q' it is the true difference
  - No, it is over ℤ
  answer: 0
  explain: All variables are ℕ; the strict order makes p'q > pq', so truncation does not occur.
---
## Plain English

**Theorem (`farey_pair_bound`).** Let p/q < p'/q' with q, q' > 0 and p'q − pq' = 1. If x/y lies strictly between them (y > 0), then x ≥ p + p' and y ≥ q + q'.

Example: between 1/2 and 1/1 (1·2 − 1·1 = 1) every fraction has numerator ≥ 2 and denominator ≥ 3, and 2/3 is the simplest one.

This is the classical fact behind continued-fraction best approximations. The project proves it directly with `nlinarith`.
