# The review: do the statements say what the names say?

Each headline was read against Eliahou's paper by Grok Bot, then audited independently by Claude from the source and the paper's PDF (no build). The full audit is committed as [`learn/CLAUDE_AUDIT.md`](https://github.com/tangentproofs/eliahou-collatz-bounds/blob/main/learn/CLAUDE_AUDIT.md). Its fixes are applied to the node pages.

| Headline | Classical claim | Verdict |
|---|---|---|
| [`eliahou_theorem_1_1`](#/node/eliahou_theorem_1_1) | Theorem 1.1: Card Ω = 301994a + 17087915b + 85137581c, b > 0, ac = 0, provided min Ω > 2⁴⁰ | **Faithful.** Same hypothesis as the paper (min > 2⁴⁰). Injectivity encodes "L = Card Ω". |
| [`eliahou_bound_card`](#/node/eliahou_bound_card) | "every nontrivial cycle has ≥ 17,087,915 elements" | **Faithful to Theorem 1.1's corollary, not to the abstract's sentence.** It assumes min > 2⁴⁰; "nontrivial" needs the 2⁴⁰ computer check, which is not formalized. |
| [`eliahou_product_formula`](#/node/eliahou_product_formula) | Lemma 2.2: ∏_{n∈Ω₁}(3 + 1/n) = 2^Card Ω | **Faithful**, with no hypotheses. Slightly more general: products are over positions, which matches the paper's set when values are distinct. |
| [`eliahou_sandwich`](#/node/eliahou_sandwich) | Theorem 2.1 | **Weaker than named.** It is non-strict on the left (the paper's is strict), and the paper's sharper bound log₂(3 + μ) is missing. Neither matters for Theorem 1.1. |

## What a careful reader should know

1. **"Nontrivial" vs "min > 2⁴⁰".** The Lean, like the paper's Theorem 1.1, assumes every element of the cycle exceeds 2⁴⁰. The famous sentence "any nontrivial cycle has at least 17,087,915 elements" also needs Yoneda's computer verification that all n < 2⁴⁰ reach 1. That is cited in a docstring and not formalized. Today's verification limits are far higher, but this proof uses 2⁴⁰.
2. **The compressed map.** Lengths count elements of a cycle of T(n) = n/2 or (3n+1)/2. A cycle of the usual 3x+1 map also visits each 3n+1, so its length is different.
3. **Length vs elements.** A `CollatzCycle L` may go round a shorter loop several times. `eliahou_bound_of_min` and `eliahou_bound` bound L. Their docstrings and ARISTOTLE_SUMMARY.md say "elements", which overstates them. `eliahou_bound_card` and Theorem 1.1 bound the number of distinct elements, assuming injectivity.
4. **Unused pieces.** `isNontrivial` and four big-power lemmas (`three_pow_lt_two_pow_15`, `two_pow_lt_three_pow_14`, `two_pow_lt_three_pow_16`, `log_bound_at_2_40`) are proved or defined but not used, according to a source scan.
5. **Nothing checked by a build.** There is no Lean CI in the repository, and this site did not build it. See [Trust](#/trust).

## Smuggled hypotheses?

None found. `hmin` constrains the *size* of the elements, `hinj` their repetition, and `0 < numOdd` is proved (`numOdd_pos`), not assumed, in the paper-facing versions. Getting a *length* bound from an *element-size* bound is the mathematical content.
