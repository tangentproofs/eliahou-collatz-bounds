---
id: eliahou_product_formula
title: 'Lemma 2.2: the odd elements multiply out to a power of two'
summary: '**The surprise:** for any Collatz cycle, multiplying 3x+1 over its odd elements gives exactly 2^L times
  the product of those odd elements. Just going round a loop forces an exact identity.'
review: draft
authors:
- grok-bot
caveats:
- Products are over *positions* `i ∈ c.oddIndices`, so if a non-injective cycle repeats a value, the value is counted
  once per position. That is consistent on both sides.
widgets:
- type: walkthrough
  title: How ProductFormula.lean proves it (ProductFormula.lean, lines 57-120)
  config:
    steps:
    - text: 'Going round the cycle: ∏ T(xᵢ) = ∏ xᵢ'
      lean: '∏ i : Fin L, collatzComp (c.seq i) = ∏ i : Fin L, c.seq i'
      note: Reindex the product by i ↦ i+1 mod L, a bijection of Fin L.
      link: prod_collatzComp_eq_prod
      uses:
      - succMod_bijective
    - text: 'Multiply each factor by 2: ∏ collatzMul(xᵢ) = 2^L ∏ xᵢ'
      lean: '∏ i : Fin L, collatzMul (c.seq i) = 2 ^ L * ∏ i : Fin L, c.seq i'
      note: collatzMul x = 2·T(x) is 3x+1 for odd x and x for even x.
      link: prod_collatzMul_eq
      uses:
      - collatzMul
    - text: Split both products into odd and even positions
      lean: CollatzCycle.prod_split_odd_even
      uses:
      - CollatzCycle.prod_split_odd_even
    - text: Cancel the (non-zero) product over the even positions
      lean: exact mul_right_cancel₀
      note: Every element is positive, so the even product is not zero and can be cancelled.
quiz:
- q: Check the formula on the trivial cycle 1 → 2 (L = 2). What is ∏_{x odd}(3x+1)?
  type: choice
  choices:
  - '2'
  - '4'
  - '8'
  - '1'
  answer: 1
  explain: The only odd element is 1, so the product is 3·1 + 1 = 4, and 2^L · 1 = 2² = 4.
- q: Does the theorem need min > 2⁴⁰ or injectivity?
  type: choice
  choices:
  - Yes, both
  - Only injectivity
  - 'Neither: it holds for every CollatzCycle'
  answer: 2
  explain: 'The only hypothesis is `c : CollatzCycle L`.'
- q: What is the key idea of the proof?
  type: choice
  choices:
  - Induction on L
  - The product of T(xᵢ) around a cycle equals the product of the xᵢ, because T shifts the list by one
  - A computer check
  answer: 1
  explain: '`prod_collatzComp_eq_prod` reindexes by the wrap-around successor (`succMod_bijective`).'
---
## Plain English

**Theorem (`eliahou_product_formula`).** For every cycle `c` of length L ([`CollatzCycle`](#/node/CollatzCycle)), the product of (3·x + 1) over the positions holding odd numbers ([`oddIndices`](#/node/CollatzCycle.oddIndices)) equals 2^L times the product of those odd numbers:

> ∏_{x odd} (3x + 1) = 2^L · ∏_{x odd} x.

Dividing through gives the form in the paper, ∏ (3 + 1/x) = 2^L ([`eliahou_product_formula_real`](#/node/eliahou_product_formula_real)).

### Why it is true

Every step of the compressed map multiplies by 1/2 and, if the number was odd, also replaces x by 3x + 1. Going once round the loop returns to the start, so the product of the T(xᵢ) is the product of the xᵢ (they are the same numbers, shifted by one place). Since 2·T(x) is 3x+1 for odd x and x for even x, multiplying everything out and cancelling the even elements gives the identity.

No hypothesis on the size of the numbers is needed, and the trivial cycle satisfies it too: for 1 → 2 → 1, (3·1+1) = 4 = 2² · 1.
