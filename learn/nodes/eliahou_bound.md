---
id: eliahou_bound
title: L ≥ 17,087,915, given an odd element
summary: '**The surprise:** the docstring calls this Theorem 1.1, but it is only its corollary, and it still carries
  the hypothesis 0 < numOdd, which is always true.'
review: draft
authors:
- grok-bot
caveats:
- The docstring's word 'unconditionally' refers to an informal argument outside Lean.
- The docstring says 'elements'; the statement bounds the length parameter L (see eliahou_bound_of_min).
quiz:
- q: Which extra hypothesis does `eliahou_bound` have compared with `eliahou_bound_of_min`?
  type: choice
  choices:
  - 0 < c.numOdd
  - injectivity
  - c.maxElem < 2⁴⁰
  answer: 0
  explain: '`(hk : 0 < c.numOdd)`, discharged later by `numOdd_pos`.'
- q: Is the computer verification up to 2⁴⁰ part of the Lean proof?
  type: choice
  choices:
  - 'Yes'
  - No, only mentioned in a comment
  answer: 1
  explain: It appears only in the docstring; the theorem assumes `2 ^ 40 < c.minElem`.
- q: Which lemma does the number theory?
  type: choice
  choices:
  - rational_approx_bound
  - eliahou_product_formula
  - collatzComp_pos
  answer: 0
  explain: '`apply rational_approx_bound (by omega) hmin …`.'
---
## Plain English

**Theorem (`eliahou_bound`).** If `c` is a cycle of length L with smallest element above 2⁴⁰ and at least one odd element, then L ≥ 17,087,915.

Proof: the [sandwich](#/node/eliahou_sandwich) puts L/k₁ in the window (log₂ 3, log₂(3 + 1/m)], and [`rational_approx_bound`](#/node/rational_approx_bound) says every fraction there has numerator at least 17087915.

The docstring (ContinuedFractions.lean lines 199-204) says the 2⁴⁰ hypothesis makes this "unconditional" for nontrivial cycles because of computer checks. That remark is about the mathematics, not the Lean: the computer check is not formalized. The docstring (and ARISTOTLE_SUMMARY.md) also says "at least 17,087,915 **elements**", but the theorem bounds L, which for a repeated loop is a multiple of the number of elements; [`eliahou_bound_card`](#/node/eliahou_bound_card) is the version about elements.
