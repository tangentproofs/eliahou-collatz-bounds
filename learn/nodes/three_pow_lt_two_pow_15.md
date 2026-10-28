---
id: three_pow_lt_two_pow_15
title: 3^10781274 < 2^17087915 (proved, unused)
summary: '**The surprise:** a comparison of numbers with over five million digits is proved here, but our scan finds
  nothing that uses it. The main proof does its big comparisons inside other lemmas.'
review: draft
authors:
- grok-bot
caveats:
- '''Unused'' comes from scanning the source text for the name, not from a Lean build.'
quiz:
- q: 2^17087915 has about how many decimal digits?
  type: choice
  choices:
  - 5.1 million
  - 17 thousand
  - '40'
  answer: 0
  explain: 17087915 · log₁₀ 2 ≈ 5.14 million.
- q: Is this lemma on the main proof path?
  type: choice
  choices:
  - No (according to the source scan)
  - 'Yes'
  answer: 0
  explain: It is unused.
- q: It is equivalent to
  type: choice
  choices:
  - log₂ 3 < 17087915/10781274
  - log₂ 3 > 17087915/10781274
  answer: 0
  explain: Take log₂.
---
## Plain English

**Theorem (`three_pow_lt_two_pow_15`).** 3^10781274 < 2^17087915, i.e. log₂ 3 < 17087915/10781274.

Proved by `norm_num`. In our source scan no other declaration refers to it (nor to `two_pow_lt_three_pow_14`, `two_pow_lt_three_pow_16` or `log_bound_at_2_40`). The real-number lemmas used by the main proof repeat equivalent checks inside their own proofs.
