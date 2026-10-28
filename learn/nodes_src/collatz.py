# Explainer nodes for the Eliahou Collatz formalization. Written as Python data so the YAML is always
# valid; tools/write_nodes.py turns each entry into learn/nodes/<id>.md. Lead every summary with the surprise.
NODES = []
def node(id, title, summary, body, quiz, caveats=(), widgets=None):
    NODES.append(dict(id=id, title=title, summary=summary, body=body, quiz=quiz, caveats=list(caveats), widgets=widgets))
def q(text, choices, answer, explain):
    return {"q": text, "type": "choice", "choices": choices, "answer": answer, "explain": explain}
def wt(title, steps):
    return [{"type": "walkthrough", "title": title, "config": {"steps": steps}}]
def st(text, lean=None, note=None, link=None, uses=None, hard=False):
    s = {"text": text}
    if lean: s["lean"] = lean
    if note: s["note"] = note
    if link: s["link"] = link
    if uses: s["uses"] = uses
    if hard: s["hard"] = True
    return s

# ---------------------------------------------------------------- headlines
node("eliahou_theorem_1_1", "Eliahou's Theorem 1.1: the length of a high Collatz cycle",
 "**The surprise:** the possible lengths of a hypothetical Collatz cycle above 2⁴⁰ are not just large, they have a rigid shape: 301994·a + 17087915·b + 85137581·c with b > 0 and a·c = 0, all because of three fractions close to log₂ 3.",
 r"""
## Plain English

**Theorem (`eliahou_theorem_1_1`).** Take a cycle of the compressed Collatz map ([`collatzComp`](#/node/collatzComp)), written as a list of L positive numbers going round a loop ([`CollatzCycle`](#/node/CollatzCycle)). Suppose

1. no number appears twice in the list (`Function.Injective cyc.seq`), and
2. the smallest number in it ([`minElem`](#/node/CollatzCycle.minElem)) is bigger than 2⁴⁰.

Then the number of distinct values in the cycle can be written as

> 301994·a + 17087915·b + 85137581·c

for some natural numbers a, b, c with **b > 0** and **a·c = 0** (at most one of a and c is non-zero).

Since b ≥ 1, the length is at least 17,087,915. That corollary is [`eliahou_bound_card`](#/node/eliahou_bound_card).

The three numbers are numerators of convergents of the continued fraction of log₂ 3:
301994/190537, 17087915/10781274 and 85137581/53715833. The proof never looks for cycles. It shows that L divided by the number of odd steps must land in a very narrow window just above log₂ 3, and then asks which fractions fit in that window.

### Why the hypotheses are there

* **min > 2⁴⁰.** This is exactly the hypothesis of the paper's Theorem 1.1. The window above log₂ 3 has width set by the smallest element m: it is (log₂ 3, log₂(3 + 1/m)]. Eliahou used the 1990s computer check that every number below 2⁴⁰ reaches 1, so any *other* cycle lives above 2⁴⁰. That computer check is **not** in the Lean: the theorem simply assumes min > 2⁴⁰.
* **Injective.** A [`CollatzCycle`](#/node/CollatzCycle) of length L may go round a shorter loop several times. Injectivity makes L the number of different values (`CollatzCycle.card_eq_of_injective`).
""",
 [q("What does the theorem assume about the numbers in the cycle?",
    ["that they are all odd", "that the smallest is greater than 2⁴⁰ and no value repeats", "that the Collatz conjecture is true", "nothing: it is about every cycle"], 1,
    "The hypotheses are `hinj : Function.Injective cyc.seq` and `hmin : 2 ^ 40 < cyc.minElem`."),
  q("Which coefficient is guaranteed to be positive?",
    ["a (the coefficient of 301994)", "b (the coefficient of 17087915)", "c (the coefficient of 85137581)", "none of them"], 1,
    "The conclusion is `∃ a b cCoeff, 0 < b ∧ a * cCoeff = 0 ∧ …`. So b ≥ 1, and the length is at least 17087915."),
  q("Does this theorem say that a nontrivial Collatz cycle exists?",
    ["Yes, it constructs one", "No: it only says what length one would have to have"], 1,
    "It is a statement about every cycle satisfying the hypotheses; there may be none. The known cycle 1 → 2 → 1 is excluded by min > 2⁴⁰."),
  q("Where does the number 2⁴⁰ come from in the classical argument?",
    ["It is the largest number the Lean kernel can handle", "A computer verification that all numbers below 2⁴⁰ reach 1, so other cycles must lie above it", "It is the length of the trivial cycle"], 1,
    "Eliahou took 2⁴⁰ from the computer checks of the day. In Lean it is simply the hypothesis `hmin`; the computer check is not formalized.")],
 caveats=[
  "The Lean theorem is about the **compressed** map T(n) = n/2 or (3n+1)/2. In the original 3x+1 map the same cycle also visits each 3n+1, so it is longer (L plus the number of odd steps). Eliahou's paper also counts T-cycles.",
  "The hypothesis is min > 2⁴⁰, not 'nontrivial'. Reading it as 'every cycle other than 1 → 2 → 1' needs the computer check that all n ≤ 2⁴⁰ reach 1, which is outside the Lean.",
  "Injectivity is a hypothesis. Every cycle can be shrunk to an injective one (go round once), but that step is not formalized; without it see [eliahou_bound_of_min](#/node/eliahou_bound_of_min), which bounds L rather than the number of distinct values.",
  "This site did not build the Lean; see the Trust page."],
 widgets=wt("How LinearForm.lean proves it (LinearForm.lean, lines 125-179)", [
   st("The length is the number of distinct values (injectivity)", "rw [cyc.card_eq_of_injective hinj]",
      "Rewrite the cardinality of the set of values as L. From here on everything is about L.", uses=["CollatzCycle.card_eq_of_injective"]),
   st("The cycle has at least one odd element, so k₁ = numOdd > 0", "exact rational_linear_form cyc.numOdd_pos hmin",
      "numOdd_pos is proved in Defs.lean: an all-even cycle would contain half its smallest element.", uses=["CollatzCycle.numOdd_pos"], link="rational_linear_form"),
   st("Sandwich: log₂ 3 < L/k₁ ≤ log₂(3 + 1/m)", "(log2_three_lt_ratio cyc cyc.numOdd_pos) (ratio_le_log cyc cyc.numOdd_pos)",
      "These come from the product formula ∏(3 + 1/n) = 2^L over the odd elements.", uses=["log2_three_lt_ratio", "ratio_le_log"], link="eliahou_sandwich"),
   st("Trap L/k₁ between two convergents: 85137581/53715833 < L/k₁ < 301994/190537", "have h_low : (85137581 : ℚ) / 53715833 < (L : ℚ) / k₁ :=",
      "The lower end uses conv16_lt_logb_three (2^85137581 < 3^53715833); the upper end uses m > 2⁴⁰ (logb_three_plus_lt_conv13).", uses=["conv16_lt_logb_three", "logb_three_plus_lt_conv13"], hard=True),
   st("Case L/k₁ < 17087915/10781274: L = b·17087915 + c·85137581 with b, c > 0", "farey_intermediate_coeffs",
      "The two convergents are Farey neighbours (farey_15_16), and a fraction strictly between Farey neighbours is a positive combination of them.", uses=["farey_intermediate_coeffs", "farey_15_16"]),
   st("Case L/k₁ = 17087915/10781274: L is a multiple of 17087915", "exact coprime_15.dvd_of_dvd_mul_left this",
      "17087915 and 10781274 are coprime, so the numerator divides L.", uses=["coprime_15"]),
   st("Case L/k₁ > 17087915/10781274: L = a·301994 + b·17087915 with a, b > 0", "farey_13_15 hgt h_high",
      "Same Farey argument with the other neighbour pair (301994/190537, 17087915/10781274).", uses=["farey_13_15", "farey_intermediate_coeffs"])]))

node("eliahou_bound_card", "A Collatz cycle above 2⁴⁰ has at least 17,087,915 distinct numbers",
 "**The surprise:** a cycle that stays above 2⁴⁰ would have to contain at least 17,087,915 *different* numbers, a bound proved with no search at all, from the continued fraction of log₂ 3.",
 r"""
## Plain English

**Theorem (`eliahou_bound_card`).** If `cyc` is a cycle of the compressed Collatz map ([`CollatzCycle`](#/node/CollatzCycle)) in which no value repeats, and its smallest element ([`minElem`](#/node/CollatzCycle.minElem)) is greater than 2⁴⁰, then the set of its values has at least **17,087,915** elements.

This is the headline consequence of [Theorem 1.1](#/node/eliahou_theorem_1_1), but in Lean it is proved by a slightly different route: through [`eliahou_bound_of_min`](#/node/eliahou_bound_of_min) and [`rational_approx_bound`](#/node/rational_approx_bound), which only needs the window (16785921/10590737, 301994/190537) and the Farey bound, not the full linear form.

### Where the number comes from

L/k₁ (cycle length over number of odd steps) must lie strictly above log₂ 3 and at most log₂(3 + 2⁻⁴⁰). Every fraction in that window is "complicated": the simplest one is the convergent 17087915/10781274. Any fraction strictly between two Farey neighbours has numerator at least the sum of theirs ([`farey_pair_bound`](#/node/farey_pair_bound)), and that pins L ≥ 17087915.
""",
 [q("What is bounded below by 17,087,915?",
    ["the largest element of the cycle", "the number of distinct values in the cycle", "the number of odd elements", "2⁴⁰"], 1,
    "The conclusion is `17087915 ≤ (Finset.univ.image cyc.seq).card`: the size of the set of values."),
  q("Why is injectivity assumed here?",
    ["Without it the cycle could repeat a shorter loop, and L would not count distinct values", "Because Lean cannot handle repeated numbers", "It is not assumed"], 0,
    "`hinj : Function.Injective cyc.seq` is used to rewrite the cardinality as L (`card_eq_of_injective`)."),
  q("Does the proof check any numbers by computer search?",
    ["Yes, all numbers up to 2⁴⁰", "No: it compares powers like 3^10590737 and 2^16785921 symbolically with norm_num", "Yes, it enumerates cycles"], 1,
    "No cycle search appears. The heavy computation is comparing huge powers of 2 and 3, done by `norm_num` in ContinuedFractions.lean.")],
 caveats=[
  "min > 2⁴⁰ is a hypothesis; the computer check that justifies it for 'every nontrivial cycle' is not formalized.",
  "Counts elements of a cycle of the compressed map T, as in the paper."],
 widgets=wt("How the bound is proved (LinearForm.lean, lines 94-105)", [
   st("Distinct values = L, by injectivity", "rw [cyc.card_eq_of_injective hinj]", uses=["CollatzCycle.card_eq_of_injective"]),
   st("L ≥ 17087915 for any cycle above 2⁴⁰", "exact eliahou_bound_of_min cyc hmin", link="eliahou_bound_of_min"),
   st("…which discharges the 'some element is odd' hypothesis", "eliahou_bound cyc hmin cyc.numOdd_pos",
      "eliahou_bound in ContinuedFractions.lean takes 0 < numOdd as an extra hypothesis; numOdd_pos proves it.", uses=["eliahou_bound", "CollatzCycle.numOdd_pos"])]))

node("eliahou_product_formula", "Lemma 2.2: the odd elements multiply out to a power of two",
 "**The surprise:** for any Collatz cycle, multiplying 3x+1 over its odd elements gives exactly 2^L times the product of those odd elements. Just going round a loop forces an exact identity.",
 r"""
## Plain English

**Theorem (`eliahou_product_formula`).** For every cycle `c` of length L ([`CollatzCycle`](#/node/CollatzCycle)), the product of (3·x + 1) over the positions holding odd numbers ([`oddIndices`](#/node/CollatzCycle.oddIndices)) equals 2^L times the product of those odd numbers:

> ∏_{x odd} (3x + 1) = 2^L · ∏_{x odd} x.

Dividing through gives the form in the paper, ∏ (3 + 1/x) = 2^L ([`eliahou_product_formula_real`](#/node/eliahou_product_formula_real)).

### Why it is true

Every step of the compressed map multiplies by 1/2 and, if the number was odd, also replaces x by 3x + 1. Going once round the loop returns to the start, so the product of the T(xᵢ) is the product of the xᵢ (they are the same numbers, shifted by one place). Since 2·T(x) is 3x+1 for odd x and x for even x, multiplying everything out and cancelling the even elements gives the identity.

No hypothesis on the size of the numbers is needed, and the trivial cycle satisfies it too: for 1 → 2 → 1, (3·1+1) = 4 = 2² · 1.
""",
 [q("Check the formula on the trivial cycle 1 → 2 (L = 2). What is ∏_{x odd}(3x+1)?",
    ["2", "4", "8", "1"], 1,
    "The only odd element is 1, so the product is 3·1 + 1 = 4, and 2^L · 1 = 2² = 4."),
  q("Does the theorem need min > 2⁴⁰ or injectivity?",
    ["Yes, both", "Only injectivity", "Neither: it holds for every CollatzCycle"], 2,
    "The only hypothesis is `c : CollatzCycle L`."),
  q("What is the key idea of the proof?",
    ["Induction on L", "The product of T(xᵢ) around a cycle equals the product of the xᵢ, because T shifts the list by one", "A computer check"], 1,
    "`prod_collatzComp_eq_prod` reindexes by the wrap-around successor (`succMod_bijective`).")],
 caveats=["Products are over *positions* `i ∈ c.oddIndices`, so if a non-injective cycle repeats a value, the value is counted once per position. That is consistent on both sides."],
 widgets=wt("How ProductFormula.lean proves it (ProductFormula.lean, lines 57-120)", [
   st("Going round the cycle: ∏ T(xᵢ) = ∏ xᵢ", "∏ i : Fin L, collatzComp (c.seq i) = ∏ i : Fin L, c.seq i",
      "Reindex the product by i ↦ i+1 mod L, a bijection of Fin L.", link="prod_collatzComp_eq_prod", uses=["succMod_bijective"]),
   st("Multiply each factor by 2: ∏ collatzMul(xᵢ) = 2^L ∏ xᵢ", "∏ i : Fin L, collatzMul (c.seq i) = 2 ^ L * ∏ i : Fin L, c.seq i",
      "collatzMul x = 2·T(x) is 3x+1 for odd x and x for even x.", link="prod_collatzMul_eq", uses=["collatzMul"]),
   st("Split both products into odd and even positions", "CollatzCycle.prod_split_odd_even", uses=["CollatzCycle.prod_split_odd_even"]),
   st("Cancel the (non-zero) product over the even positions", "exact mul_right_cancel₀",
      "Every element is positive, so the even product is not zero and can be cancelled.")]))

node("eliahou_sandwich", "Theorem 2.1, non-strict form: the sandwich on L/k₁",
 "**The surprise:** the ratio of a cycle's length to its number of odd steps is squeezed between log₂(3 + 1/max) and log₂(3 + 1/min). For a cycle of huge numbers that is a window of width about 1/min around log₂ 3.",
 r"""
## Plain English

**Theorem (`eliahou_sandwich`).** Let `c` be a cycle of length L with k₁ = [`numOdd`](#/node/CollatzCycle.numOdd) odd elements, smallest element m ([`minElem`](#/node/CollatzCycle.minElem)) and largest M ([`maxElem`](#/node/CollatzCycle.maxElem)). If k₁ > 0, then

> log₂(3 + 1/M) ≤ L/k₁ ≤ log₂(3 + 1/m).

### Why

By the [product formula](#/node/eliahou_product_formula), the product of (3 + 1/x) over the k₁ odd elements is exactly 2^L. Each factor lies between 3 + 1/M and 3 + 1/m, so (3 + 1/M)^k₁ ≤ 2^L ≤ (3 + 1/m)^k₁. Taking log₂ and dividing by k₁ gives the sandwich.

Since 1/M > 0, the left end is already above log₂ 3, so L/k₁ > log₂ 3 ([`log2_three_lt_ratio`](#/node/log2_three_lt_ratio)). With m > 2⁴⁰, the right end is below log₂(3 + 2⁻⁴⁰). The rest of the proof is about fractions in that window.

The hypothesis `0 < c.numOdd` is always true ([`numOdd_pos`](#/node/CollatzCycle.numOdd_pos)); the version in Results.lean discharges it.
""",
 [q("Which element of the cycle controls the *upper* end of the sandwich?",
    ["the largest, M", "the smallest, m", "the first, x₀"], 1,
    "The upper bound is `Real.logb 2 (3 + 1 / (c.minElem : ℝ))`: small elements make 1/x big."),
  q("The paper states strict inequalities. What does the Lean state?",
    ["strict < on both sides", "≤ on both sides", "< on the left only"], 1,
    "Both conjuncts use ≤. The strict lower bound against log₂ 3 itself is a separate lemma, `log2_three_lt_ratio`."),
  q("What extra hypothesis does `eliahou_sandwich` take?",
    ["min > 2⁴⁰", "0 < c.numOdd", "injectivity"], 1,
    "`(hk : 0 < c.numOdd)`, which `CollatzCycle.numOdd_pos` always supplies.")],
 caveats=["Weaker than the paper's Theorem 2.1 in two ways: the paper's *left* inequality is strict (because the largest element of a cycle is even), and the paper also proves a sharper right-hand bound log₂(3 + μ) with μ the mean of 1/n over the odd elements. Neither is formalized. The later argument only needs log₂ 3 < L/k₁ ≤ log₂(3 + 1/m), which the Lean has.",
  "The header comment of Sandwich.lean (lines 13-16) advertises strict inequalities that no theorem in the file proves; the theorem's own docstring is accurate.",
  "The docstring calls this the 'full sandwich inequality'; the Claude audit flags 'full' as inaccurate."],
 widgets=wt("How Sandwich.lean proves it (Sandwich.lean, lines 34-101)", [
   st("Each odd factor 3 + 1/x is at most 3 + 1/m, so the product is at most (3 + 1/m)^k₁", "(3 + 1 / (c.minElem : ℝ)) ^ c.numOdd := by", link="prod_le_pow_min"),
   st("…and at least (3 + 1/M)^k₁", "∏ i ∈ c.oddIndices, (3 + 1 / (c.seq i : ℝ)) := by", link="pow_max_le_prod"),
   st("The product is 2^L (product formula)", "rw [← eliahou_product_formula_real c]", uses=["eliahou_product_formula_real"]),
   st("Take log₂ and divide by k₁: upper bound", "theorem ratio_le_log", link="ratio_le_log"),
   st("…and lower bound", "theorem log_le_ratio", link="log_le_ratio"),
   st("Pair them up", "⟨log_le_ratio c hk, ratio_le_log c hk⟩")]))

# ---------------------------------------------------------------- statement set
node("collatzComp", "The compressed Collatz map T",
 "**The surprise:** T(0) = 0, so 0 is a fixed point of this Lean function. That is why a Collatz cycle in this project must consist of *positive* numbers.",
 r"""
## Plain English

**Definition (`collatzComp`).** For a natural number n,

> T(n) = n/2 if n is even, and (3n + 1)/2 if n is odd.

This is the "compressed" or "accelerated" 3x+1 map used by Eliahou: when n is odd, 3n+1 is even, so the usual map would halve it next anyway; T does both steps at once. Every cycle of the usual map gives a cycle of T and vice versa, but the lengths differ (T skips the even number 3n+1).

Lean's natural-number division rounds down, but here it never has to: n/2 is only used for even n, and 3n+1 is even when n is odd. On n = 0 the definition gives 0, which is why [`CollatzCycle`](#/node/CollatzCycle) requires all its numbers to be positive.
""",
 [q("What is T(7)?", ["22", "11", "3", "21"], 1, "7 is odd, so T(7) = (3·7 + 1)/2 = 22/2 = 11."),
  q("What is T(0)?", ["0", "1", "undefined"], 0, "0 is even, so T(0) = 0/2 = 0. The docstring notes 0 is outside the domain of interest."),
  q("How does T relate to the usual 3x+1 map?", ["It is the same map", "It combines the odd step 3n+1 with the halving that always follows it", "It only applies to odd numbers"], 1,
    "For odd n, T(n) = (3n+1)/2: the usual map's two steps n → 3n+1 → (3n+1)/2 in one.")])

node("Fin.succMod", "Wrap-around successor on positions 0…L−1",
 "**The surprise:** to say \"the list closes up into a loop\" Lean needs an explicit wrap-around: position L−1 is followed by position 0.",
 r"""
## Plain English

**Definition (`Fin.succMod`).** For a position i in {0, 1, …, L−1} (a `Fin L`) and a proof that L > 0, `i.succMod hL` is the position (i + 1) mod L. So 0 → 1 → … → L−1 → 0.

It is used in [`CollatzCycle`](#/node/CollatzCycle) to say that T sends the number at position i to the number at the next position, going round the loop. The proof that it is a bijection ([`succMod_bijective`](#/node/succMod_bijective)) is what lets the product formula reindex a product around the cycle.
""",
 [q("With L = 5, what is the successor of position 4?", ["5", "0", "4", "undefined"], 1, "(4 + 1) mod 5 = 0: the loop closes."),
  q("Why does it take the argument `hL : 0 < L`?", ["To prove the result is less than L (mod by zero would be meaningless)", "It is unused", "To make L even"], 0,
    "`Nat.mod_lt _ hL` proves (i+1) % L < L, which needs L > 0."),
  q("Is `Fin.succMod` from Mathlib?", ["Yes", "No: this project defines it (in Defs.lean)"], 1, "It is defined in Collatz/Defs.lean lines 37-38, in the `Fin` namespace.")])

node("CollatzCycle", "A Collatz cycle of length L",
 "**The surprise:** nothing forces the L positions to hold *different* numbers, so 1, 2, 1, 2 is a `CollatzCycle 4`. That is why the cardinality theorems also assume injectivity.",
 r"""
## Plain English

**Structure (`CollatzCycle L`).** A cycle of length L is:

* `hL`: a proof that L > 0;
* `seq`: a list of L natural numbers x₀, …, x_{L−1} (a function from `Fin L`);
* `pos`: every xᵢ is positive;
* `step`: T(xᵢ) = x_{i+1}, with indices taken mod L ([`collatzComp`](#/node/collatzComp), [`Fin.succMod`](#/node/Fin.succMod)).

So it is an orbit of the compressed map that comes back to where it started after L steps.

Two things the structure does **not** require:

1. **Distinct values.** Going round the loop 1 → 2 → 1 twice is a `CollatzCycle 4`. L is therefore "a period", not necessarily the smallest one. Theorems that talk about the number of distinct values add `Function.Injective c.seq` (or use [`ExactCollatzCycle`](#/node/ExactCollatzCycle)).
2. **Nontriviality.** The trivial cycle 1, 2 is a `CollatzCycle 2` ([`trivialCycle`](#/node/trivialCycle)). The headline theorems exclude it by assuming the smallest element is above 2⁴⁰.
""",
 [q("Is the list 1, 2, 1, 2 a `CollatzCycle 4`?", ["Yes", "No, values must be distinct", "No, L must be even"], 0,
    "T(1) = 2, T(2) = 1, and all are positive, so `step` and `pos` hold. Nothing requires distinct values."),
  q("Why must every element be positive?", ["Because T(0) = 0 would allow the silly cycle 0, 0, …", "Because Lean has no negative numbers", "It is not required"], 0,
    "`pos : ∀ i, 0 < seq i`. Without it, the constant list 0 would be a cycle of every length."),
  q("Which map must the cycle follow?", ["n ↦ 3n + 1 or n/2", "the compressed map T: n/2 or (3n+1)/2", "n ↦ n + 1"], 1, "`step : ∀ i, collatzComp (seq i) = seq (i.succMod hL)`.")],
 caveats=["L counts positions, with repeats. Eliahou's Card Ω is the number of distinct elements; the Lean bridges the two with injectivity."])

node("CollatzCycle.oddIndices", "Positions holding odd numbers",
 "**The surprise:** the cycle's \"odd elements\" are tracked as *positions*, not values, so a repeated value is counted once per visit.",
 r"""
## Plain English

**Definition (`c.oddIndices`).** The set of positions i in {0, …, L−1} where the number xᵢ is odd. Its size is [`numOdd`](#/node/CollatzCycle.numOdd), the k₁ of the paper. `evenIndices` is the complementary set.

Products such as ∏_{i ∈ oddIndices} (3xᵢ + 1) in the [product formula](#/node/eliahou_product_formula) range over these positions.
""",
 [q("For the cycle 1, 2 (positions 0 and 1), what is `oddIndices`?", ["{0}", "{1}", "{0, 1}", "∅"], 0, "Position 0 holds 1, which is odd; position 1 holds 2."),
  q("Is it a set of numbers or of positions?", ["numbers", "positions (elements of Fin L)"], 1, "Its type is `Finset (Fin L)`."),
  q("What is its size called elsewhere?", ["numOdd (k₁)", "minElem", "L"], 0, "`numOdd c := c.oddIndices.card`.")])

node("CollatzCycle.numOdd", "k₁: the number of odd steps",
 "**The surprise:** the whole proof is about the single ratio L/k₁. Cycle length over number of odd steps must be almost exactly log₂ 3.",
 r"""
## Plain English

**Definition (`c.numOdd`).** The number of positions in the cycle holding an odd number, the size of [`oddIndices`](#/node/CollatzCycle.oddIndices). Eliahou calls it k₁.

Each odd step multiplies (roughly) by 3/2 and each even step by 1/2. To come back to the start you need 3^k₁ ≈ 2^L, so L/k₁ ≈ log₂ 3 ≈ 1.58496. The [sandwich](#/node/eliahou_sandwich) makes "≈" precise. It is always at least 1 ([`numOdd_pos`](#/node/CollatzCycle.numOdd_pos)).
""",
 [q("For the trivial cycle 1, 2, what are L and k₁?", ["L = 2, k₁ = 1", "L = 2, k₁ = 2", "L = 1, k₁ = 1"], 0, "Two positions, one of which (holding 1) is odd."),
  q("Roughly what must L/k₁ be for a cycle of large numbers?", ["2", "log₂ 3 ≈ 1.585", "3/2", "1"], 1, "The sandwich puts it between log₂(3 + 1/M) and log₂(3 + 1/m)."),
  q("Why is it marked `noncomputable`?", ["It uses classical reasoning (Finset filtering under `open Classical`-style instances); it does not affect the theorems", "It is undefined", "It uses an axiom beyond the standard three"], 0,
    "Lean marks definitions noncomputable when it cannot compile them to code; the logic is unaffected.")])

node("CollatzCycle.minElem", "The smallest number in the cycle",
 "**The surprise:** this one number decides everything: the theorems need nothing about the cycle except that its minimum exceeds 2⁴⁰.",
 r"""
## Plain English

**Definition (`c.minElem`).** The minimum of the set of values {x₀, …, x_{L−1}}. Lean's `Finset.min'` needs a proof that the set is non-empty, which comes from L > 0.

It enters the [sandwich](#/node/eliahou_sandwich) through the upper bound log₂(3 + 1/m), and the headline theorems assume `2 ^ 40 < c.minElem`.
""",
 [q("What does `2 ^ 40 < c.minElem` say?", ["Some element exceeds 2⁴⁰", "Every element exceeds 2⁴⁰", "The cycle has length above 2⁴⁰"], 1, "If the minimum is above 2⁴⁰, every element is."),
  q("Why does `minElem` need L > 0?", ["The minimum of an empty set is undefined", "To make it computable", "It does not"], 0, "`Finset.min'` takes a non-emptiness proof, built from `c.hL`."),
  q("For the trivial cycle 1, 2, what is minElem?", ["1", "2", "0"], 0, "The values are 1 and 2.")])

node("CollatzCycle.maxElem", "The largest number in the cycle",
 "**The surprise:** the largest element is only used to show L/k₁ is *strictly* above log₂ 3; any positive number would do.",
 r"""
## Plain English

**Definition (`c.maxElem`).** The maximum of the set of values {x₀, …, x_{L−1}}, via `Finset.max'`.

It gives the lower end of the [sandwich](#/node/eliahou_sandwich), log₂(3 + 1/M) ≤ L/k₁, and since 1/M > 0 this is strictly bigger than log₂ 3 ([`log2_three_lt_ratio`](#/node/log2_three_lt_ratio)).
""",
 [q("Which side of the sandwich uses maxElem?", ["lower", "upper"], 0, "`Real.logb 2 (3 + 1 / (c.maxElem : ℝ)) ≤ (L : ℝ) / c.numOdd`."),
  q("Do the headline theorems put any hypothesis on maxElem?", ["Yes, it must be below 2⁴⁰", "No"], 1, "Only minElem appears in the hypotheses."),
  q("What does it contribute to the final bound?", ["The strict inequality log₂ 3 < L/k₁", "The number 17087915 directly", "Nothing"], 0, "`log2_three_lt_ratio` uses `log_le_ratio` and 1/M > 0.")])

# ---------------------------------------------------------------- the proof path
node("eliahou_bound_of_min", "L ≥ 17,087,915 (bounds the length, not the distinct values)",
 "**The surprise:** this bound is on L, the length of the indexing, which for a repeated loop can be bigger than the number of distinct values, so on its own it is weaker than it looks.",
 r"""
## Plain English

**Theorem (`eliahou_bound_of_min`).** For every [`CollatzCycle`](#/node/CollatzCycle) `cyc` of length L whose smallest element is above 2⁴⁰, L ≥ 17,087,915.

It is [`eliahou_bound`](#/node/eliahou_bound) with the "some element is odd" hypothesis filled in by [`numOdd_pos`](#/node/CollatzCycle.numOdd_pos).

Because a `CollatzCycle` may go round a shorter loop several times, L here is "a" period. If the shortest loop had period p and you went round it twice, L = 2p, and the theorem only says 2p ≥ 17087915. (Applied to the once-round cycle it gives p ≥ 17087915 too, but that step is not in the Lean.) [`eliahou_bound_card`](#/node/eliahou_bound_card) adds injectivity to talk about distinct values.
""",
 [q("Does `eliahou_bound_of_min` assume the cycle has no repeated values?", ["Yes", "No"], 1, "Its only hypothesis besides the cycle is `hmin : 2 ^ 40 < cyc.minElem`."),
  q("Then what exactly is bounded?", ["the number of distinct values", "the length parameter L", "the minimum"], 1, "The conclusion is `17087915 ≤ L`."),
  q("Which theorem turns this into a bound on distinct values?", ["eliahou_bound_card", "eliahou_product_formula", "farey_pair_bound"], 0, "`eliahou_bound_card` rewrites with `card_eq_of_injective`.")])

node("eliahou_bound", "L ≥ 17,087,915, given an odd element",
 "**The surprise:** the docstring calls this Theorem 1.1, but it is only its corollary, and it still carries the hypothesis 0 < numOdd, which is always true.",
 r"""
## Plain English

**Theorem (`eliahou_bound`).** If `c` is a cycle of length L with smallest element above 2⁴⁰ and at least one odd element, then L ≥ 17,087,915.

Proof: the [sandwich](#/node/eliahou_sandwich) puts L/k₁ in the window (log₂ 3, log₂(3 + 1/m)], and [`rational_approx_bound`](#/node/rational_approx_bound) says every fraction there has numerator at least 17087915.

The docstring (ContinuedFractions.lean lines 199-204) says the 2⁴⁰ hypothesis makes this "unconditional" for nontrivial cycles because of computer checks. That remark is about the mathematics, not the Lean: the computer check is not formalized. The docstring (and ARISTOTLE_SUMMARY.md) also says "at least 17,087,915 **elements**", but the theorem bounds L, which for a repeated loop is a multiple of the number of elements; [`eliahou_bound_card`](#/node/eliahou_bound_card) is the version about elements.
""",
 [q("Which extra hypothesis does `eliahou_bound` have compared with `eliahou_bound_of_min`?", ["0 < c.numOdd", "injectivity", "c.maxElem < 2⁴⁰"], 0, "`(hk : 0 < c.numOdd)`, discharged later by `numOdd_pos`."),
  q("Is the computer verification up to 2⁴⁰ part of the Lean proof?", ["Yes", "No, only mentioned in a comment"], 1, "It appears only in the docstring; the theorem assumes `2 ^ 40 < c.minElem`."),
  q("Which lemma does the number theory?", ["rational_approx_bound", "eliahou_product_formula", "collatzComp_pos"], 0, "`apply rational_approx_bound (by omega) hmin …`.")],
 caveats=["The docstring's word 'unconditionally' refers to an informal argument outside Lean.", "The docstring says 'elements'; the statement bounds the length parameter L (see eliahou_bound_of_min)."])

node("eliahou_product_formula_real", "Lemma 2.2 in the paper's form: ∏ (3 + 1/x) = 2^L",
 "**The surprise:** a product of numbers like 3.0000001 over the odd elements of a cycle is *exactly* a power of two.",
 r"""
## Plain English

**Theorem (`eliahou_product_formula_real`).** For every cycle of length L, the real product over odd positions of (3 + 1/xᵢ) equals 2^L.

It is the [integer product formula](#/node/eliahou_product_formula) divided by the product of the odd elements (non-zero since every element is positive). The [sandwich](#/node/eliahou_sandwich) bounds each factor to get its inequalities.
""",
 [q("For the trivial cycle 1, 2, what is ∏(3 + 1/x) over odd x?", ["4", "3", "2"], 0, "Only x = 1: 3 + 1 = 4 = 2²."),
  q("In which number system is this stated?", ["ℕ", "ℝ", "ℚ"], 1, "The factors are `(3 + 1 / (c.seq i : ℝ))`."),
  q("How is it proved?", ["Divide the integer product formula by the product of the odd elements", "By induction on L", "By norm_num"], 0, "The last step is `exact eliahou_product_formula c`.")])

node("CollatzCycle.numOdd_pos", "Every cycle has an odd element",
 "**The surprise:** an all-even cycle is impossible for a one-line reason: halving its smallest element would give a smaller element of the cycle.",
 r"""
## Plain English

**Theorem (`c.numOdd_pos`).** Every [`CollatzCycle`](#/node/CollatzCycle) has at least one odd element: 0 < [`numOdd`](#/node/CollatzCycle.numOdd).

Proof (Defs.lean lines 133-155): suppose every element is even. Take a position holding the minimum m. The next element is T(m) = m/2, which is in the cycle, so m ≤ m/2. But m is positive, so m/2 < m. Contradiction.

This is what lets the paper-facing theorems drop the hypothesis `0 < c.numOdd`.
""",
 [q("Why does the proof look at the *smallest* element?", ["Because T of it, m/2, would be an even smaller element of the cycle", "Because it is odd", "Because it is 1"], 0, "`hge : c.minElem ≤ c.minElem / 2` and `hlt : c.minElem / 2 < c.minElem`."),
  q("Where is positivity used?", ["to show m/2 < m", "nowhere"], 0, "`Nat.div_lt_self (c.pos i) …` needs m > 0."),
  q("Does it need min > 2⁴⁰?", ["Yes", "No, it holds for every CollatzCycle"], 1, "No hypothesis beyond the cycle itself.")])

node("log2_three_lt_ratio", "L/k₁ is strictly above log₂ 3",
 "**The surprise:** going round any Collatz cycle, odd steps must be *rarer* than log₂ 3 predicts would balance: L/k₁ > log₂ 3 for every cycle, even 1 → 2 → 1.",
 r"""
## Plain English

**Theorem (`log2_three_lt_ratio`).** For every cycle with k₁ > 0, log₂ 3 < L/k₁.

From the lower half of the [sandwich](#/node/eliahou_sandwich): L/k₁ ≥ log₂(3 + 1/M), and 3 + 1/M > 3 because M is positive. For 1 → 2 → 1, L/k₁ = 2 > 1.585.
""",
 [q("For the trivial cycle, L/k₁ is", ["2", "1.585", "1"], 0, "L = 2, k₁ = 1."),
  q("Is the inequality strict?", ["Yes", "No"], 0, "`Real.logb 2 3 < (L : ℝ) / c.numOdd`."),
  q("Which element's size is used?", ["the maximum (only its positivity)", "the minimum, which must exceed 2⁴⁰"], 0, "The proof uses `log_le_ratio` and that maxElem is positive.")])

node("ratio_le_log", "L/k₁ ≤ log₂(3 + 1/min)",
 "**The surprise:** the bigger the cycle's smallest number, the closer L/k₁ is forced to log₂ 3, and that closeness is the entire source of the 17-million bound.",
 r"""
## Plain English

**Theorem (`ratio_le_log`).** For a cycle with k₁ > 0 and minimum m, L/k₁ ≤ log₂(3 + 1/m).

Proof: by the product formula, 2^L = ∏(3 + 1/x) ≤ (3 + 1/m)^k₁ ([`two_pow_le_bound_min`](#/node/two_pow_le_bound_min)); take logarithms. This is the upper half of the [sandwich](#/node/eliahou_sandwich).
""",
 [q("If m > 2⁴⁰, L/k₁ is at most about", ["log₂ 3 + 2⁻⁴⁰/(3 ln 2)", "log₂ 3 + 1", "2"], 0, "log₂(3 + ε) ≈ log₂ 3 + ε/(3 ln 2) for small ε = 1/m."),
  q("Which inequality on the product does it use?", ["∏(3 + 1/x) ≤ (3 + 1/m)^k₁", "∏(3 + 1/x) ≥ (3 + 1/M)^k₁"], 0, "Each factor is at most 3 + 1/m."),
  q("Is it strict?", ["No, ≤", "Yes, <"], 0, "`(L : ℝ) / c.numOdd ≤ Real.logb 2 (3 + 1 / (c.minElem : ℝ))`.")])

node("rational_linear_form", "Pure number theory: fractions in the window",
 "**The surprise:** this is the heart of Theorem 1.1, and it never mentions Collatz. Any fraction L/k₁ just above log₂ 3 (within log₂(3 + 2⁻⁴⁰)) has numerator 301994a + 17087915b + 85137581c.",
 r"""
## Plain English

**Theorem (`rational_linear_form`).** Let k₁ > 0, L be natural numbers and m > 2⁴⁰. If

> log₂ 3 < L/k₁ ≤ log₂(3 + 1/m),

then L = 301994·a + 17087915·b + 85137581·c for some a, b, c ≥ 0 with b > 0 and a·c = 0.

### Proof idea

The window is inside (85137581/53715833, 301994/190537), two convergents of log₂ 3 on either side of the middle convergent 17087915/10781274. Neighbouring pairs among these three fractions are *Farey neighbours* (cross-differences equal 1: [`farey_15_16`](#/node/farey_15_16), [`farey_13_15`](#/node/farey_13_15)). Any fraction strictly between Farey neighbours p/q < p'/q' is (a·p + b·p')/(a·q + b·q') with a, b ≥ 1 ([`farey_intermediate_coeffs`](#/node/farey_intermediate_coeffs)). So:

* below the middle convergent: L = b·17087915 + c·85137581;
* equal to it: L is a multiple of 17087915 (they are coprime, [`coprime_15`](#/node/coprime_15));
* above it: L = a·301994 + b·17087915.

In every case b > 0 and one of a, c is zero.
""",
 [q("Does this theorem mention Collatz cycles?", ["Yes", "No, only natural numbers L, k₁, m and logarithms"], 1, "Its hypotheses are `0 < k₁`, `2 ^ 40 < m` and the two log inequalities."),
  q("What makes two fractions p/q < p'/q' 'Farey neighbours' here?", ["p'·q − p·q' = 1", "p + p' = q + q'", "they have equal denominators"], 0, "`hfarey : p' * q - p * q' = 1` in `farey_intermediate_coeffs`."),
  q("If L/k₁ equals 17087915/10781274 exactly, what are a and c?", ["both 0", "a = 1, c = 0", "a = 0, c = 1"], 0, "The proof returns `⟨0, b, 0, …⟩`: L = 17087915·b.")],
 widgets=wt("The three cases (LinearForm.lean, lines 125-166)", [
   st("Lower end: 85137581/53715833 < log₂ 3 < L/k₁", "rat_of_real_div_lt (by norm_num) hk₁ (conv16_lt_logb_three.trans hlower)", uses=["conv16_lt_logb_three"]),
   st("Upper end: L/k₁ ≤ log₂(3 + 1/m) < 301994/190537 (uses m > 2⁴⁰)", "(lt_of_le_of_lt hupper (logb_three_plus_lt_conv13 m hm))", uses=["logb_three_plus_lt_conv13"], hard=True),
   st("Compare with the middle convergent 17087915/10781274", "rcases lt_trichotomy ((L : ℚ) / k₁) ((17087915 : ℚ) / 10781274) with hlt | heq | hgt"),
   st("Below: Farey pair (p₁₆/q₁₆, p₁₅/q₁₅) gives L = b·p₁₅ + c·p₁₆", "farey_15_16 h_low hlt", uses=["farey_intermediate_coeffs", "farey_15_16"]),
   st("Equal: coprimality gives L = 17087915·b", "exact coprime_15.dvd_of_dvd_mul_left this", uses=["coprime_15"]),
   st("Above: Farey pair (p₁₅/q₁₅, p₁₃/q₁₃) gives L = a·p₁₃ + b·p₁₅", "farey_13_15 hgt h_high", uses=["farey_13_15"])]))

node("rational_approx_bound", "Fractions in the window have numerator ≥ 17,087,915",
 "**The surprise:** the simplest fraction squeezed between log₂ 3 and log₂(3 + 2⁻⁴⁰) already has numerator 17,087,915.",
 r"""
## Plain English

**Theorem (`rational_approx_bound`).** For natural numbers k₁ > 0, L and m > 2⁴⁰, if log₂ 3 < L/k₁ ≤ log₂(3 + 1/m), then L ≥ 17087915.

Proof (ContinuedFractions.lean lines 172-197): the window lies inside (16785921/10590737, 301994/190537). Splitting at 17087915/10781274, the [Farey bound](#/node/farey_pair_bound) gives L ≥ 17087915 + 301994 above it, L ≥ 16785921 + 17087915 below it, and coprimality gives a multiple of 17087915 at it.

[`rational_linear_form`](#/node/rational_linear_form) is the sharper version used for Theorem 1.1.
""",
 [q("Which convergent of log₂ 3 sets the bound?", ["17087915/10781274", "301994/190537", "3/2"], 0, "Its numerator is the bound."),
  q("Above the middle convergent, how big must L be?", ["at least 17087915 + 301994", "at least 301994", "at least 2⁴⁰"], 0, "Farey bound with the pair (17087915/10781274, 301994/190537)."),
  q("Does it mention cycles?", ["No", "Yes"], 0, "It is about natural numbers and logarithms only.")])

node("farey_pair_bound", "Lemma 3.1: between Farey neighbours, numerators add",
 "**The surprise:** between p/q and p'/q' with p'q − pq' = 1, the simplest fraction is the mediant (p+p')/(q+q'). Nothing in between has a smaller numerator or denominator.",
 r"""
## Plain English

**Theorem (`farey_pair_bound`).** Let p/q < p'/q' with q, q' > 0 and p'q − pq' = 1. If x/y lies strictly between them (y > 0), then x ≥ p + p' and y ≥ q + q'.

Example: between 1/2 and 1/1 (1·2 − 1·1 = 1) every fraction has numerator ≥ 2 and denominator ≥ 3, and 2/3 is the simplest one.

This is the classical fact behind continued-fraction best approximations. The project proves it directly with `nlinarith`.
""",
 [q("Between 1/2 and 1/1, what is the smallest possible denominator?", ["2", "3", "4"], 1, "q + q' = 2 + 1 = 3, e.g. 2/3."),
  q("Which condition makes p/q and p'/q' Farey neighbours?", ["p'q − pq' = 1", "p = p'", "q = q'"], 0, "`hfarey : p' * q - p * q' = 1`."),
  q("Is subtraction here natural-number subtraction?", ["Yes; with p/q < p'/q' it is the true difference", "No, it is over ℤ"], 0, "All variables are ℕ; the strict order makes p'q > pq', so truncation does not occur.")])

node("farey_intermediate_coeffs", "Between Farey neighbours: a positive combination",
 "**The surprise:** every fraction strictly between Farey neighbours is literally built from them: x = a·p + b·p' and y = a·q + b·q' with a, b ≥ 1.",
 r"""
## Plain English

**Theorem (`farey_intermediate_coeffs`).** Under the hypotheses of [`farey_pair_bound`](#/node/farey_pair_bound), there are positive a, b with x = a·p + b·p' and y = a·q + b·q'.

The proof gives them explicitly: a = p'y − q'x and b = qx − py, and checks the identities using p'q − pq' = 1. This sharper form is what gives the *linear form* in [Theorem 1.1](#/node/eliahou_theorem_1_1).
""",
 [q("Write 2/3 between 1/2 and 1/1 as a combination", ["a = 1, b = 1", "a = 2, b = 1", "a = 1, b = 2"], 0, "2 = 1·1 + 1·1 and 3 = 1·2 + 1·1."),
  q("Are a and b allowed to be 0?", ["No, both are positive", "Yes"], 0, "The conclusion has `0 < a ∧ 0 < b`."),
  q("How are a and b found?", ["Explicit formulas p'y − q'x and qx − py", "By search", "By choice"], 0, "`refine ⟨p' * y - q' * x, q * x - p * y, …⟩`.")])

node("logb_three_plus_lt_conv13", "Where 2⁴⁰ enters: log₂(3 + 1/m) < 301994/190537",
 "**The surprise:** with 2³⁹ instead of 2⁴⁰ this step fails and the bound collapses from 17,087,915 to 301,994 (Eliahou, p. 55). One bit of verification is worth a factor of 56.",
 r"""
## Plain English

**Theorem (`logb_three_plus_lt_conv13`).** For every natural number m > 2⁴⁰, log₂(3 + 1/m) < 301994/190537.

Equivalently (3 + 1/m)^190537 < 2^301994. Since 1/m < 2⁻⁴⁰ it is enough to check (3·2⁴⁰ + 1)^190537 < 2^(301994 + 40·190537) = 2^7923474, a comparison of numbers with millions of digits, done by `norm_num` inside the proof.

The margin is thin, about 10%: log₂(3 + 2⁻⁴⁰) − log₂ 3 ≈ 4.4·10⁻¹³, against ≈ 4.9·10⁻¹³ for the gap up to 301994/190537. Eliahou remarks (p. 55) that had the conjecture been verified only up to 2³⁹, this step would fail and the best bound he could claim would be **301,994**. One more bit of computer verification multiplied the bound by more than 56.
""",
 [q("What does m > 2⁴⁰ buy?", ["The window's upper end is below 301994/190537", "It makes L even", "Nothing"], 0, "That is the conclusion."),
  q("Roughly how many binary digits does 2^7923474 have?", ["7,923,475", "301,994", "40"], 0, "2^n has n+1 binary digits."),
  q("Is the related standalone lemma `log_bound_at_2_40` used by the main proof?", ["No, it is proved but unused; this lemma redoes the check inside its own proof", "Yes"], 0, "In our source scan nothing refers to `log_bound_at_2_40`.")],
 caveats=["The big-number comparisons are checked by norm_num and Lean's kernel; this site has not rebuilt them."])

node("conv16_lt_logb_three", "85137581/53715833 is just below log₂ 3",
 "**The surprise:** proving one fraction is below log₂ 3 here means comparing 2^85137581 with 3^53715833, numbers with about 25.6 million decimal digits each.",
 r"""
## Plain English

**Theorem (`conv16_lt_logb_three`).** 85137581/53715833 < log₂ 3.

Equivalently 2^85137581 < 3^53715833. The proof rewrites the real logarithm inequality into this integer comparison and settles it with `norm_num` (LinearForm.lean lines 84-89). It is the lower edge of the window in [`rational_linear_form`](#/node/rational_linear_form).
""",
 [q("Which integer inequality is equivalent?", ["2^85137581 < 3^53715833", "3^85137581 < 2^53715833"], 0, "a/b < log₂ 3 ⇔ 2^a < 3^b."),
  q("Which tactic does the heavy lifting?", ["norm_num", "native_decide", "sorry"], 0, "The README says no native_decide remains; norm_num with a raised exponentiation threshold."),
  q("Is 85137581/53715833 above or below log₂ 3?", ["below", "above"], 0, "As stated.")])

node("farey_13_15", "301994/190537 and 17087915/10781274 are Farey neighbours",
 "**The surprise:** two convergents of log₂ 3 found by continued fractions satisfy a cross-multiplication identity that equals exactly 1.",
 r"""
## Plain English

**Theorem (`farey_13_15`).** 301994 · 10781274 − 17087915 · 190537 = 1.

So 17087915/10781274 < 301994/190537 are Farey neighbours, the pair used for the "above the middle" case in [`rational_linear_form`](#/node/rational_linear_form). Checked by `norm_num`.
""",
 [q("What is the value of the expression?", ["1", "0", "−1"], 0, "As stated."),
  q("Which fraction is larger?", ["301994/190537", "17087915/10781274"], 0, "p'q − pq' = 1 > 0 with p'/q' = 301994/190537."),
  q("What does the identity allow?", ["Applying the Farey bound and coefficient lemmas", "Nothing"], 0, "It is the `hfarey` hypothesis.")])

node("farey_15_16", "17087915/10781274 and 85137581/53715833 are Farey neighbours",
 "**The surprise:** the next convergent, 85137581/53715833, is also a Farey neighbour, and that is what produces the third coefficient c in Theorem 1.1.",
 r"""
## Plain English

**Theorem (`farey_15_16`).** 17087915 · 53715833 − 85137581 · 10781274 = 1.

So 85137581/53715833 < 17087915/10781274 are Farey neighbours, used for the "below the middle" case in [`rational_linear_form`](#/node/rational_linear_form).
""",
 [q("Which is larger?", ["17087915/10781274", "85137581/53715833"], 0, "p'/q' = 17087915/10781274."),
  q("Which coefficient of Theorem 1.1 does this pair produce?", ["c (85137581)", "a (301994)"], 0, "Below the middle, L = b·17087915 + c·85137581."),
  q("How is it proved?", ["norm_num", "a long induction"], 0, "One line, `norm_num`.")])

node("coprime_15", "17087915 and 10781274 are coprime",
 "**The surprise:** this is what handles the case where L/k₁ hits the convergent exactly: then L must be a multiple of 17,087,915.",
 r"""
## Plain English

**Theorem (`coprime_15`).** gcd(17087915, 10781274) = 1.

If L/k₁ = 17087915/10781274 then 10781274·L = 17087915·k₁, and coprimality forces 17087915 to divide L.
""",
 [q("If L/k₁ = 17087915/10781274, then", ["17087915 divides L", "L = 10781274", "k₁ = 1"], 0, "`coprime_15.dvd_of_dvd_mul_left`."),
  q("Are consecutive convergent numerators and denominators always coprime?", ["Yes", "No"], 0, "Convergents are in lowest terms."),
  q("Tactic?", ["norm_num", "decide"], 0, "As written.")])

node("prod_collatzComp_eq_prod", "Going round the loop: ∏ T(xᵢ) = ∏ xᵢ",
 "**The surprise:** applying T to every element of a cycle just rotates the list, so the product does not change.",
 r"""
## Plain English

**Theorem (`prod_collatzComp_eq_prod`).** For every cycle, the product of T(xᵢ) over all positions equals the product of the xᵢ.

Since T(xᵢ) = x_{i+1 mod L} and i ↦ i+1 mod L is a bijection ([`succMod_bijective`](#/node/succMod_bijective)), it is the same product in a different order. First step of the [product formula](#/node/eliahou_product_formula).
""",
 [q("Why are the two products equal?", ["T shifts the list by one position, a reordering", "T is the identity"], 0, "Reindex with `Equiv.ofBijective`."),
  q("Does it need injectivity?", ["No", "Yes"], 0, "Only the cycle structure."),
  q("Over which positions?", ["all of Fin L", "odd positions only"], 0, "`∏ i : Fin L`.")])

node("collatzMul", "2·T(n): 3n+1 if odd, n if even",
 "**The surprise:** doubling T removes every division, which turns the cycle condition into a statement about products of whole numbers.",
 r"""
## Plain English

**Definition (`collatzMul`).** collatzMul(n) = 3n + 1 if n is odd, n if n is even. It equals 2·T(n) (`collatzMul_eq_two_mul_collatzComp`).

Multiplying over a cycle: ∏ collatzMul(xᵢ) = 2^L ∏ T(xᵢ) = 2^L ∏ xᵢ ([`prod_collatzMul_eq`](#/node/prod_collatzMul_eq)).
""",
 [q("collatzMul(5) =", ["16", "8", "5"], 0, "5 is odd: 3·5 + 1 = 16 = 2·T(5) = 2·8."),
  q("collatzMul(6) =", ["6", "3", "19"], 0, "6 is even."),
  q("How does it relate to T?", ["collatzMul n = 2 · T n", "collatzMul n = T n + 1"], 0, "`collatzMul_eq_two_mul_collatzComp`.")])

node("ExactCollatzCycle", "A cycle with no repeated values",
 "**The surprise:** the paper's Card Ω and Lean's L only agree once you add this one field: injectivity.",
 r"""
## Plain English

**Structure (`ExactCollatzCycle L`).** A [`CollatzCycle L`](#/node/CollatzCycle) together with a proof that `seq` is injective: no value appears at two positions. For such a cycle the number of distinct values is exactly L (`ExactCollatzCycle.card_eq_length`).

The headline theorems are also restated for this wrapper (`ExactCollatzCycle.eliahou_theorem_1_1`, `ExactCollatzCycle.eliahou_bound_card`).
""",
 [q("Is 1, 2, 1, 2 an ExactCollatzCycle 4?", ["No, 1 repeats", "Yes"], 0, "Injectivity fails."),
  q("What does injectivity buy?", ["L = number of distinct values", "min > 2⁴⁰"], 0, "`card_eq_length`."),
  q("Is it a new kind of cycle or a cycle plus a property?", ["a CollatzCycle plus a proof", "something unrelated"], 0, "`extends CollatzCycle L`.")])

node("CollatzCycle.card_eq_of_injective", "Injective ⇒ L distinct values",
 "**The surprise:** this two-line lemma is the entire bridge from Lean's indexed cycle to the paper's set Ω.",
 r"""
## Plain English

**Theorem (`card_eq_of_injective`).** If a cycle's `seq` is injective, then the set of its values has exactly L elements.

Used as the first step of [Theorem 1.1](#/node/eliahou_theorem_1_1) and [`eliahou_bound_card`](#/node/eliahou_bound_card).
""",
 [q("What is concluded?", ["(image of seq).card = L", "L > 0"], 0, "`(Finset.univ.image c.seq).card = L`."),
  q("Which Mathlib fact proves it?", ["Finset.card_image_of_injective", "Nat.mod_lt"], 0, "Plus `Finset.card_fin`."),
  q("Without injectivity, how do card and L compare?", ["card ≤ L", "card ≥ L"], 0, "An image is never bigger than the domain.")])

node("trivialCycle", "The known cycle 1 → 2 → 1",
 "**The surprise:** the only known positive Collatz cycle is a perfectly good `CollatzCycle 2`; the theorems exclude it only through the hypothesis min > 2⁴⁰.",
 r"""
## Plain English

**Definition (`trivialCycle`).** The cycle of length 2 with x₀ = 1, x₁ = 2: T(1) = 2 and T(2) = 1.

Its minimum is 1, so none of the headline theorems applies to it. It does satisfy the [product formula](#/node/eliahou_product_formula): 3·1 + 1 = 4 = 2².
""",
 [q("Its length L is", ["2", "3", "1"], 0, "Two positions."),
  q("Do the headline theorems apply to it?", ["No, its minimum is 1", "Yes"], 0, "They assume min > 2⁴⁰."),
  q("In the usual 3x+1 map this cycle is", ["1 → 4 → 2 → 1 (length 3)", "1 → 2 → 1 (length 2)"], 0, "The compressed map skips 4.")])

node("CollatzCycle.isNontrivial", "\"Nontrivial\": defined but never used",
 "**The surprise:** the project defines \"nontrivial\" as min > 2, but no theorem uses it. The headlines assume min > 2⁴⁰ instead.",
 r"""
## Plain English

**Definition (`c.isNontrivial`).** 2 < c.minElem.

Our source scan finds no declaration that mentions it. The headline theorems use the much stronger, explicit hypothesis `2 ^ 40 < c.minElem`, and the step from "nontrivial" to "min > 2⁴⁰" (computer verification of the conjecture up to 2⁴⁰) is not formalized. Its docstring says as much.
""",
 [q("Do any theorems use `isNontrivial`?", ["No", "Yes, all headlines"], 0, "It is unused."),
  q("What would be needed to go from isNontrivial to min > 2⁴⁰?", ["A (formalized) check that all n ≤ 2⁴⁰ reach 1", "Nothing"], 0, "That check is not in the Lean."),
  q("isNontrivial means", ["min > 2", "min > 2⁴⁰"], 0, "As defined.")])

node("results_eliahou_theorem_1_1", "Results.lean: the paper-facing statement of Theorem 1.1",
 "**The surprise:** Results.lean, the file meant for checking, restates each theorem by hand and proves it by citing the real one, so a reader can audit the statements in 64 lines.",
 r"""
## Plain English

**Theorem (`results_eliahou_theorem_1_1`).** The same statement as [`eliahou_theorem_1_1`](#/node/eliahou_theorem_1_1), restated in Results.lean (lines 50-56) and proved by applying it.

Results.lean is a thin "comparator surface": ten theorems, each a restatement of a result in `Collatz/`, so the statements can be read without the proofs.
""",
 [q("Is the Results.lean statement identical to the one in LinearForm.lean?", ["Yes, up to names", "No, it is weaker"], 0, "Same hypotheses and conclusion."),
  q("How is it proved?", ["By citing eliahou_theorem_1_1", "From scratch"], 0, "`:= eliahou_theorem_1_1 c hinj hmin`."),
  q("Why have such a file?", ["To audit statements without reading proofs", "For speed"], 0, "That is its role.")])

node("three_pow_lt_two_pow_15", "3^10781274 < 2^17087915 (proved, unused)",
 "**The surprise:** a comparison of numbers with over five million digits is proved here, but our scan finds nothing that uses it. The main proof does its big comparisons inside other lemmas.",
 r"""
## Plain English

**Theorem (`three_pow_lt_two_pow_15`).** 3^10781274 < 2^17087915, i.e. log₂ 3 < 17087915/10781274.

Proved by `norm_num`. In our source scan no other declaration refers to it (nor to `two_pow_lt_three_pow_14`, `two_pow_lt_three_pow_16` or `log_bound_at_2_40`). The real-number lemmas used by the main proof repeat equivalent checks inside their own proofs.
""",
 [q("2^17087915 has about how many decimal digits?", ["5.1 million", "17 thousand", "40"], 0, "17087915 · log₁₀ 2 ≈ 5.14 million."),
  q("Is this lemma on the main proof path?", ["No (according to the source scan)", "Yes"], 0, "It is unused."),
  q("It is equivalent to", ["log₂ 3 < 17087915/10781274", "log₂ 3 > 17087915/10781274"], 0, "Take log₂.")],
 caveats=["'Unused' comes from scanning the source text for the name, not from a Lean build."])
