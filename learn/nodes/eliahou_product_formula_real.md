---
id: eliahou_product_formula_real
title: 'Lemma 2.2 in the paper''s form: ∏ (3 + 1/x) = 2^L'
summary: '**The surprise:** a product of numbers like 3.0000001 over the odd elements of a cycle is *exactly* a
  power of two.'
review: draft
authors:
- grok-bot
quiz:
- q: For the trivial cycle 1, 2, what is ∏(3 + 1/x) over odd x?
  type: choice
  choices:
  - '4'
  - '3'
  - '2'
  answer: 0
  explain: 'Only x = 1: 3 + 1 = 4 = 2².'
- q: In which number system is this stated?
  type: choice
  choices:
  - ℕ
  - ℝ
  - ℚ
  answer: 1
  explain: 'The factors are `(3 + 1 / (c.seq i : ℝ))`.'
- q: How is it proved?
  type: choice
  choices:
  - Divide the integer product formula by the product of the odd elements
  - By induction on L
  - By norm_num
  answer: 0
  explain: The last step is `exact eliahou_product_formula c`.
---
## Plain English

**Theorem (`eliahou_product_formula_real`).** For every cycle of length L, the real product over odd positions of (3 + 1/xᵢ) equals 2^L.

It is the [integer product formula](#/node/eliahou_product_formula) divided by the product of the odd elements (non-zero since every element is positive). The [sandwich](#/node/eliahou_sandwich) bounds each factor to get its inequalities.
