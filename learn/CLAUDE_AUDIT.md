# Claude audit of the headline statements

**Repo:** `eliahou-collatz-bounds` @ `learn-site` (24c01e9) · **Source read:** `Collatz/{Defs,ProductFormula,Sandwich,ContinuedFractions,LinearForm}.lean`, `Results.lean`, `README.md`, `Collatz/README.md`, `ARISTOTLE_SUMMARY.md`, and the paper itself (`eliahou-collatz.pdf`, Discrete Math 118 (1993) 45–56, pp. 45–48 and 52–56).
**Not done (per instructions):** no files edited, no `lake build`, no `#print axioms`. Everything below is a source-level audit.

---

## 0. The classical statements, quoted from the PDF

So the comparison is against the actual text, not memory:

- **Theorem 1.1** (p. 46): "Let Ω be a nontrivial cycle of *T*. **Provided min Ω > 2⁴⁰**, we have Card Ω = 301994*a* + 17087915*b* + 85137581*c*, where *a,b,c* are nonnegative integers, *b* > 0, and *ac* = 0. In particular, the smallest admissible values for Card Ω are 17087915, 17389909, 17691903, and so on."
- **Theorem 2.1** (p. 46): "Let Ω be a cycle of *T*, and let Ω₁ ⊂ Ω denote the subset of its odd elements. Then log₂(3 + M⁻¹) **<** CardΩ/CardΩ₁ **≤** log₂(3 + m⁻¹), where M = max Ω, m = min Ω. **In fact, a sharper right inequality holds:** CardΩ/CardΩ₁ ≤ log₂(3 + μ), where μ = (1/CardΩ₁)(∑_{n∈Ω₁} n⁻¹)."
- **Lemma 2.2** (p. 46): "Let Ω, Ω₁ be as above, and let *k* = Card Ω. Then ∏_{n∈Ω₁}(3 + n⁻¹) = 2^k."
- **Abstract** (p. 45): "any nontrivial cyclic orbit under iteration of *T* must contain at least 17 087 915 elements." The bridge from Theorem 1.1's `min Ω > 2⁴⁰` to this unconditional sentence is **Yoneda's computer verification** up to 2⁴⁰ ≈ 1.1·10¹², cited on p. 45 and invoked again on p. 55.
- *T* throughout the paper is the **compressed** map `T(n) = n/2` (n even), `(3n+1)/2` (n odd), and "cycle of length k" means `T^(k)(x) = x` for all x ∈ Ω with **k = Card Ω** (p. 45).

---

## 1. `eliahou_theorem_1_1` vs Theorem 1.1

```lean
-- Collatz/LinearForm.lean:171-176
theorem eliahou_theorem_1_1 {L : ℕ} (cyc : CollatzCycle L)
    (hinj : Function.Injective cyc.seq)
    (hmin : (2 : ℕ) ^ 40 < cyc.minElem) :
    ∃ (a b cCoeff : ℕ), 0 < b ∧ a * cCoeff = 0 ∧
      (Finset.univ.image cyc.seq).card =
        301994 * a + 17087915 * b + 85137581 * cCoeff
```
(plus the wrapper `ExactCollatzCycle.eliahou_theorem_1_1`, `LinearForm.lean:182`, and the alias `results_eliahou_theorem_1_1`, `Results.lean:50`.)

**Does it say what the name says? Yes.** This is the closest match of the four.

| Paper | Lean | Comment |
|---|---|---|
| Ω a cycle of *T* | `CollatzCycle L` with `collatzComp` | faithful (§5) |
| Card Ω | `(Finset.univ.image cyc.seq).card` | the cardinality of the **orbit set**, not the index count — correct |
| min Ω > 2⁴⁰ | `hmin : 2^40 < cyc.minElem` | **identical to the paper's own hypothesis**, not an extra one |
| "nontrivial" | *dropped* | harmless: `min Ω > 2⁴⁰` ⟹ nontrivial, so Lean assumes **less** here |
| *a,b,c* nonneg integers | `a b cCoeff : ℕ` | faithful |
| *b* > 0 | `0 < b` | faithful |
| *ac* = 0 | `a * cCoeff = 0` | faithful (over ℕ this is exactly `a = 0 ∨ c = 0`) |
| — | `hinj : Function.Injective cyc.seq` | **extra hypothesis**, but see below |

**On `hinj`.** `CollatzCycle L` is an *indexed loop* `Fin L → ℕ` closed under `succMod`, so `L` is only guaranteed to be a multiple of the true period: a period-*p* orbit also inhabits `CollatzCycle (t·p)` for every *t*. The paper's `k = Card Ω` is the number of **distinct** elements. `hinj` is exactly the statement "this presentation has no repeats", i.e. it is the encoding of `L = Card Ω`, not a mathematical strengthening of the hypotheses. The conclusion is then stated in terms of `card (image seq)`, so the statement is about Card Ω either way. This is the right way to do it, and `ExactCollatzCycle` (`Defs.lean:159`) + `card_eq_of_injective` (`Defs.lean:168`) make the bridge explicit. Mild caveat: **nothing in the development proves that a minimal-period presentation exists or that `hinj` is satisfiable alongside `hmin`** — the user must supply it.

**Does any hypothesis smuggle in the conclusion?** No. `hmin` constrains the *size of the elements*, never the *length*; `hinj` is a statement about repetition. Deriving a length bound from an element-size bound is precisely the mathematical content.

**Proof-shape check (statement-level, no build).** `rational_linear_form` (`LinearForm.lean:125`) reproduces Eliahou's p. 56 argument case-for-case: trichotomy of `L/k₁` against `p₁₅/q₁₅`, with the Farey pairs (p₁₆/q₁₆, p₁₅/q₁₅) and (p₁₅/q₁₅, p₁₃/q₁₃). I checked the constants against Table 1 (p. 53) and by hand:
- p₁₃/q₁₃ = 301994/190537, p₁₄/q₁₄ = 16785921/10590737, p₁₅/q₁₅ = 17087915/10781274, p₁₆/q₁₆ = 85137581/53715833 — all match Table 1 exactly, and the recurrence checks out (a₁₆ = 4: 4·17087915 + 16785921 = 85137581; 4·10781274 + 10590737 = 53715833).
- `farey_13_15`: 301994·10781274 − 17087915·190537 = 3255880060356 − 3255880060355 = **1** ✓
- `farey_15_16`: 17087915·53715833 − 85137581·10781274 = 917891588458195 − 917891588458194 = **1** ✓
- `farey_14_15`: 17087915·10590737 − 16785921·10781274 = 180973613643355 − 180973613643354 = **1** ✓
- `farey_intermediate_coeffs` (`LinearForm.lean:25`) is the correct unimodular inverse: with a = p′y − q′x, b = qx − py one gets ap + bp′ = x(p′q − pq′) = x and aq + bq′ = y. Correct, and the ℕ-subtraction is discharged through ℤ casts.
- Argument/variable binding in each of the three `farey_intermediate_coeffs` calls is correct (I traced which numeral lands in `p`, `q`, `p'`, `q'` in each branch); the resulting `⟨0, b, c⟩` / `⟨0, b, 0⟩` / `⟨a, b, 0⟩` triples all satisfy `b > 0 ∧ ac = 0`.

**Verdict: FAITHFUL WITH CAVEATS** — the only caveats are (i) `hinj` must be supplied by the user as the encoding of `L = Card Ω`, and (ii) the whole thing is unverified at the kernel level (§6).

**Allowed wording:** *"Formalizes Eliahou's Theorem 1.1 exactly as stated in the paper: if Ω is a cycle of the compressed map T whose elements are all distinct and whose minimum exceeds 2⁴⁰, then Card Ω = 301994a + 17087915b + 85137581c for nonnegative integers a, b, c with b ≥ 1 and ac = 0."* Do **not** write "unconditionally" or drop the 2⁴⁰.

---

## 2. `eliahou_bound_card` / `eliahou_bound_of_min` vs "every nontrivial cycle has ≥ 17,087,915 elements"

```lean
-- Collatz/LinearForm.lean:94-97
theorem eliahou_bound_of_min {L : ℕ} (cyc : CollatzCycle L)
    (hmin : (2 : ℕ) ^ 40 < cyc.minElem) :
    17087915 ≤ L

-- Collatz/LinearForm.lean:100-105
theorem eliahou_bound_card {L : ℕ} (cyc : CollatzCycle L)
    (hinj : Function.Injective cyc.seq)
    (hmin : (2 : ℕ) ^ 40 < cyc.minElem) :
    17087915 ≤ (Finset.univ.image cyc.seq).card
```
(both route through `eliahou_bound`, `ContinuedFractions.lean:205`, which additionally takes `hk : 0 < c.numOdd`; the two wrappers discharge `hk` via `CollatzCycle.numOdd_pos`, `Defs.lean:133` — a genuine proof, not an assumption. Good.)

**Gaps against the headline sentence:**

1. **`min > 2⁴⁰` is not "nontrivial".** The repo *defines* nontriviality correctly — `CollatzCycle.isNontrivial := 2 < c.minElem` (`Defs.lean:92`) — but **no headline theorem uses it**; `isNontrivial` is dead code. The step from "nontrivial" to "min > 2⁴⁰" is Yoneda's computation, which is **not formalized and not formalizable by this method**. It is correctly cited in the docstring (`ContinuedFractions.lean:201-204`) but is an unformalized external input. Note this matches the paper's Theorem 1.1 hypothesis exactly; it does *not* match the paper's abstract.
2. **`eliahou_bound_of_min` bounds `L`, not the number of elements.** For a non-injective presentation `L = t · Card Ω`, so `17087915 ≤ L` does **not** imply `17087915 ≤ Card Ω`. `ARISTOTLE_SUMMARY.md:9` and `ContinuedFractions.lean:201` both say "has at least 17,087,915 **elements**" for `eliahou_bound` — that is an overstatement of what that particular theorem says. `eliahou_bound_card` is the one that actually delivers the headline, and it needs `hinj`.
3. **"Collatz cycle" means the compressed map T.** 17,087,915 counts T-orbit elements. A cycle of the raw `3x+1` map has the same odd elements but additional intermediate `3n+1` values, so the number is not interchangeable with "length of a 3x+1 cycle". The paper is explicit about this (p. 45, p. 48 Remark); the repo is consistent with the paper but a reader could easily mis-transfer the number.
4. Nothing smuggles in the conclusion: `hmin` bounds element size, `hinj` bounds repetition, `hk` is proved not assumed.
5. The arithmetic is right: the minimum of `301994a + 17087915b + 85137581c` subject to `b ≥ 1, ac = 0` is 17087915 (and the next values 17389909, 17691903 match p. 46). The three-case proof in `rational_approx_bound` (`ContinuedFractions.lean:172`) bottoms out at `p₁₄+p₁₅ = 33873836`, `17087915`, `p₁₅+p₁₃ = 17389909` respectively — all ≥ 17087915 ✓. The tightness of the 2⁴⁰ step is real but correct: log₂(3+2⁻⁴⁰) − log₂3 ≈ 4.37·10⁻¹³ against p₁₃/q₁₃ − log₂3 = 1/(q₁₃q₁₅) + (p₁₅/q₁₅ − log₂3) ≈ 4.87·10⁻¹³, i.e. roughly a 10% margin — exactly why the paper notes that at 2³⁹ the bound would collapse to 301994 (p. 55).

**Verdict: `eliahou_bound_card` — FAITHFUL WITH CAVEATS. `eliahou_bound_of_min` / `eliahou_bound` — FAITHFUL WITH CAVEATS as a statement about `L`, NOT FAITHFUL as currently *described* ("at least 17,087,915 elements").**

**Allowed wording:** *"Any cycle of the compressed Collatz map T whose minimum element exceeds 2⁴⁰ has at least 17,087,915 distinct elements (the distinctness-counting form requires the injectivity hypothesis). The unconditional reading — 'every nontrivial cycle' — additionally requires Yoneda's computer verification of the conjecture below 2⁴⁰, which is cited but not formalized here."* Not allowed: *"Lean proof that every nontrivial Collatz cycle has ≥ 17,087,915 elements."*

---

## 3. `eliahou_product_formula` / `_real` vs Lemma 2.2

```lean
-- Collatz/ProductFormula.lean:109-111
theorem eliahou_product_formula {L : ℕ} (c : CollatzCycle L) :
    ∏ i ∈ c.oddIndices, (3 * c.seq i + 1) =
    2 ^ L * ∏ i ∈ c.oddIndices, c.seq i

-- Collatz/ProductFormula.lean:127-128
theorem eliahou_product_formula_real {L : ℕ} (c : CollatzCycle L) :
    ∏ i ∈ c.oddIndices, (3 + 1 / (c.seq i : ℝ)) = (2 : ℝ) ^ L
```

**Does it say what the name says? Yes**, and this is the cleanest item in the development.

- **No extra hypotheses at all** — matching the paper, where Lemma 2.2 holds for *any* cycle of T. Positivity (needed so `1/n` is meaningful and so the cancellation is legal) comes from the structure field `pos`, not from an ad-hoc assumption. `_real` is well-formed precisely because `pos` rules out `seq i = 0`.
- Exponent is `L`, i.e. `k = Card Ω` including even elements — correct (the paper's `2^k` with `k = Card Ω`, not `Card Ω₁`).
- The integer form is the obvious clearing of denominators of the real form; both are stated, and `_real` is derived from the integer form.
- Proof structure mirrors the paper's p. 46–47 one-liner: `prod_collatzComp_eq_prod` (reindex by the `succMod` bijection, giving ∏T(n) = ∏n) then split odd/even. Faithful.

**The one caveat: index-product vs set-product.** `oddIndices` (`Defs.lean:49`) is a `Finset (Fin L)`, so the product is over odd **indices**, i.e. over the multiset of odd entries, whereas the paper's ∏_{n∈Ω₁} is over the **set** Ω₁. These coincide iff `seq` is injective. The Lean version is the correct *generalization* (a *t*-fold repetition gives (2^p)^t = 2^L), and it implies Lemma 2.2 on the nose when `seq` is injective — so this is a widening, not a weakening. But the statement as written is not literally "∏ over the set of odd elements"; nothing in this file relates `oddIndices.card` to `Card Ω₁`.

**Verdict: FAITHFUL WITH CAVEATS** (the only caveat being multiset-vs-set, which is a generalization).

**Allowed wording:** *"Eliahou's Lemma 2.2, formalized hypothesis-free: for any cycle of the compressed map, ∏(3 + 1/n) over the odd entries equals 2^L, where L is the cycle length. Products are taken over cycle positions, which coincides with the paper's product over the set Ω₁ when the cycle's entries are distinct."*

---

## 4. `eliahou_sandwich` vs Theorem 2.1

```lean
-- Collatz/Sandwich.lean:98-101
theorem eliahou_sandwich {L : ℕ} (c : CollatzCycle L) (hk : 0 < c.numOdd) :
    Real.logb 2 (3 + 1 / (c.maxElem : ℝ)) ≤ (L : ℝ) / c.numOdd ∧
    (L : ℝ) / c.numOdd ≤ Real.logb 2 (3 + 1 / (c.minElem : ℝ))
```

**This is the weakest of the four relative to its name.** Two concrete divergences:

1. **The left inequality is strict in the paper and non-strict in Lean.** Eliahou: `log₂(3 + M⁻¹) < CardΩ/CardΩ₁`, with the proof note (p. 47): *"The strict inequality on the left is due to the fact that M is even and, therefore, larger than max Ω₁."* The development never proves that `max Ω` is even (a two-line argument: an odd maximum M would have T(M) = (3M+1)/2 > M), so it settles for `≤` in `pow_max_le_prod` / `bound_max_le_two_pow` (`Sandwich.lean:49, 65`). The claim is still *true*, just strictly weaker than Theorem 2.1.
   **This is also an internal documentation inconsistency:** the file header at `Sandwich.lean:13,16` advertises `log₂(3 + 1/M) < L/k₁ < log₂(3 + 1/m)` and `(3 + 1/M)^k₁ < 2^L ≤ (3 + 1/m)^k₁` — strict on the left, and strict on *both* sides in the log form — neither of which is what any theorem in the file proves. The theorem's own docstring (`Sandwich.lean:97`) is honest (`≤ … ≤`); the file header is not. `Collatz/README.md` is honest here.
   *Downstream impact: none.* `log2_three_lt_ratio` (`Sandwich.lean:106`) recovers the strict `log₂3 < L/k₁` it needs from `3 < 3 + 1/M` instead, and `rational_approx_bound` / `rational_linear_form` consume exactly `(strict lower, non-strict upper)`, matching p. 48's "For simplicity, we will only use the inequalities log₂(3) < CardΩ/CardΩ₁ ≤ log₂(3 + m⁻¹)". So the weakening is harmless to the main line — but a reader comparing to "Theorem 2.1" is getting less than the paper.
2. **The sharper right-hand bound is missing entirely.** Theorem 2.1's second half, `CardΩ/CardΩ₁ ≤ log₂(3 + μ)` with μ the mean of the reciprocals of Ω₁ (and Bacher's μ ≤ (8/9)m⁻¹ remark, p. 47–48), is not formalized anywhere. Nothing in the repo claims otherwise, but `eliahou_sandwich` is labelled "**Theorem 2.1** (Eliahou): Full sandwich inequality" — "Full" is not accurate.

Everything else lines up: `m` and `M` are the min/max of the whole orbit (not of Ω₁), matching the paper; `L/numOdd` is `CardΩ/CardΩ₁` up to the same multiset-vs-set caveat as §3 (and the *ratio* is invariant under repetition, so this caveat is genuinely inert here); `hk : 0 < numOdd` is not an extra assumption in substance — it is proved in general by `numOdd_pos` and is discharged automatically in `Results.lean:12`; the paper needs it implicitly for `CardΩ₁` to be a legal denominator. No hypothesis smuggles in the conclusion.

**Verdict: FAITHFUL WITH CAVEATS, trending toward NOT FAITHFUL as named** — it proves a strictly weaker proposition than the theorem it is named after, on two separate counts, and its file header describes a strict inequality it does not prove.

**Allowed wording:** *"A non-strict form of Eliahou's Theorem 2.1: log₂(3 + 1/M) ≤ L/k₁ ≤ log₂(3 + 1/m). The paper's strict left inequality (which needs max Ω to be even) and its sharper right-hand bound log₂(3 + μ) are not formalized."* Not allowed: *"the full sandwich inequality of Theorem 2.1"*.

---

## 5. Definitions: faithfulness check

| Definition | Location | Verdict |
|---|---|---|
| `collatzComp n = if n % 2 = 0 then n / 2 else (3*n+1)/2` | `Defs.lean:20` | **Faithful.** Exactly the paper's *T*. ℕ-division is exact in both branches, confirmed by `two_mul_collatzComp` (`Defs.lean:26`). `collatzComp 0 = 0` is harmless since `pos` excludes 0. |
| `Fin.succMod i hL = ⟨(i+1) % L, _⟩` | `Defs.lean:37` | **Faithful.** Correct cyclic successor; `succMod_bijective` (`ProductFormula.lean:45`) confirms it's a bijection, which is what the reindexing needs. |
| `CollatzCycle L` (`hL`, `seq`, `pos`, `step`) | `Defs.lean:42` | **Faithful with one note.** `step` quantifies over *all* `i`, including the wrap-around `i = L-1`, so it genuinely closes the loop; combined with `succMod` it forces `seq i = T^i (seq 0)` and `T^L (seq 0) = seq 0`. It is a real periodic orbit. **The note:** it does not require `L` to be the minimal period, hence the injectivity machinery. The type is non-vacuous (`trivialCycle : CollatzCycle 2`, `Defs.lean:82`, is constructed and the `step` field actually checked) — a useful sanity check that the definition is not accidentally unsatisfiable. |
| `oddIndices`, `numOdd` | `Defs.lean:49, 57` | **Faithful modulo multiset-vs-set** (§3). `numOdd` is the count of odd *positions*, = `Card Ω₁` iff `seq` injective. Nowhere is `numOdd` related to `card (image …)` the way `L` is in `card_eq_of_injective`. |
| `minElem`, `maxElem` | `Defs.lean:65, 72` | **Faithful.** min'/max' over `image seq` = min/max of the orbit **set** — exactly the paper's m, M, and immune to the repetition issue. Supporting lemmas `minElem_pos`, `minElem_le`, `le_maxElem` are correct. |
| `isNontrivial := 2 < minElem` | `Defs.lean:92` | **Faithful as a definition, but dead code.** It is a correct encoding of "Ω ≠ {1,2}" (the only T-cycle containing 1 or 2 is the trivial one). It is referenced by **no** theorem in the repo. |
| `ExactCollatzCycle` | `Defs.lean:159` | **Faithful.** `extends CollatzCycle L` + `injective : Function.Injective seq`, with `card_eq_length` making `L = Card Ω` explicit. This is the right bridge, and the two `ExactCollatzCycle.*` wrappers are the statements I would actually quote. |
| `numOdd_pos` | `Defs.lean:133` | **Correct and load-bearing.** The argument (an all-even cycle would make `T(min) = min/2` a smaller cycle element) is sound, and it's what lets the paper-facing wrappers avoid assuming `k₁ > 0`. |

---

## 6. Grep results and build-dependent risks

**Grep over all `*.lean` (excluding `.lake`, which does not exist) for `sorry | admit | axiom | native_decide | implemented_by | unsafe | partial | Classical.choice | extern | decide +kernel`: _no matches_.** The sources are clean. The only `decide` is `decide +revert` at `ContinuedFractions.lean:90` (`farey_14_15`), and it is on an unused lemma.

**What I cannot verify without a build — and this is the biggest single risk in the audit:**

1. **No CI builds this project.** `.github/workflows/` contains only `pages.yml`, which checks out the repo and uploads `site/` to GitHub Pages. There is **no `lake build` job anywhere**, and no `.lake/` artifacts in the tree. So there is *no automated evidence that any of these theorems compiles*, and the repeated "fully proved / sorry-free" claims in `README.md`, `Collatz/README.md` and `ARISTOTLE_SUMMARY.md` rest on a developer's local run.
2. **Four astronomically large `norm_num` goals.** `maxHeartbeats 8000000`, `maxRecDepth 10000` and `exponentiation.threshold 100000000` are set precisely to permit these:
   - `three_pow_lt_two_pow_15 : 3^10781274 < 2^17087915` (`ContinuedFractions.lean:101`) — ~5.1M-digit integers;
   - `two_pow_lt_three_pow_14 : 2^16785921 < 3^10590737` (`:107`);
   - `log_bound_at_2_40 : (3·2^40+1)^190537 < 2^7923474` (`:119`) — ~2.4M digits;
   - `two_pow_lt_three_pow_16 : 2^85137581 < 3^53715833` (`LinearForm.lean:80`) — ~25.6M digits, i.e. ~10 MB per operand.
   Each must be evaluated by `norm_num` **and then re-checked by the kernel**. These are plausible with GMP-accelerated `Nat.pow`, but they are expensive enough that "does it finish in the available time/memory" is a real open question. **Mitigating fact I verified by grep: all four of these are declared and never used.** Nothing depends on them.
3. **The load-bearing real-number inequalities are the actual risk.** `conv14_lt_logb_three` (`:137`), `conv16_lt_logb_three` (`LinearForm.lean:84`) and `logb_three_plus_lt_conv13` (`:147`) — the three that *are* used — each end in `rw [← Real.log_rpow, ← Real.log_rpow, Real.log_lt_log_iff] <;> norm_num`, leaving `norm_num` to decide a comparison of two **real** `rpow`s with 8-digit exponents (for `conv16`, `2^85137581` vs `3^53715833` again, now in ℝ). If any one of these does not close, **`eliahou_bound`, `eliahou_bound_card` and `eliahou_theorem_1_1` all fail**. I can confirm the mathematics (all three inequalities are true, with the margins computed in §1–§2); I cannot confirm the tactics.
4. **Two `grind` calls carry real content.** In `rational_approx_bound` (`ContinuedFractions.lean:193-196`): one branch asks `grind` to derive `L ≥ 17087915` from `16785921·k₁ < 10590737·L` and `10781274·L < 17087915·k₁` (sound — it's the positive combination `L = 16785921·(17087915k₁ − 10781274L) + 17087915·(10590737L − 16785921k₁)` using `farey_14_15`); the other asks it to derive `17087915 ∣ L` from `10781274·L = 17087915·k₁` (sound — Presburger-decidable, and `coprime_15` exists, though that branch doesn't visibly cite it). Both are mathematically valid; whether `grind`/`omega` actually discharge them at these coefficient sizes is a build question.
5. **Axiom hygiene is unverified.** Without `#print axioms results_eliahou_theorem_1_1` I cannot confirm the standard-three-axioms claim in `ARISTOTLE_SUMMARY.md:9`. The absence of `native_decide` (which would inject `Lean.ofReduceBool`) and of any `axiom` declaration in the sources is good evidence, but it is not the check itself. **Recommendation: add a `lake build` CI job and a file of `#print axioms` commands over the `Results.lean` surface.**
6. Minor: `Main.lean` sets options and imports Mathlib but is in **no** `lean_lib` target (`defaultTargets = ["Collatz","Results"]`), so `lake build` never compiles it; its `set_option autoImplicit false` etc. do **not** apply to the `Collatz/` files, which rely on Mathlib defaults.

---

## 7. Verdicts

| # | Headline | Verdict |
|---|---|---|
| 1 | `eliahou_theorem_1_1` vs Theorem 1.1 | **FAITHFUL WITH CAVEATS** — matches the paper's statement *and* its `min Ω > 2⁴⁰` hypothesis; `hinj` is the encoding of `Card Ω = L`, not an added assumption; unverified by build. |
| 2 | `eliahou_bound_card` vs "≥ 17,087,915 elements" | **FAITHFUL WITH CAVEATS** — conditional on `min > 2⁴⁰`, which is *not* "nontrivial"; the gap is Yoneda's unformalized computation. |
| 2′ | `eliahou_bound_of_min` / `eliahou_bound` | **FAITHFUL WITH CAVEATS as stated** (`17087915 ≤ L`), but the surrounding prose ("has at least 17,087,915 **elements**") is **NOT FAITHFUL** — without injectivity `L` is only a multiple of Card Ω. |
| 3 | `eliahou_product_formula` / `_real` vs Lemma 2.2 | **FAITHFUL WITH CAVEATS** — hypothesis-free and in fact slightly more general; product is over positions rather than the set Ω₁. |
| 4 | `eliahou_sandwich` vs Theorem 2.1 | **FAITHFUL WITH CAVEATS (weakest of the four)** — left inequality weakened from `<` to `≤`; the sharper `log₂(3 + μ)` half of Theorem 2.1 absent; file header advertises strictness the file does not prove. |

**Three things I would fix before anyone cites this.** (a) Add a CI `lake build` + `#print axioms` job — every "fully proved" claim in the repo is currently unbacked by reproducible evidence. (b) Correct `ARISTOTLE_SUMMARY.md:9` and the `eliahou_bound` docstring to say "length `L`" rather than "elements", or point them at `eliahou_bound_card`. (c) Fix the `Sandwich.lean:13,16` header to match the non-strict theorems, or prove `max Ω` is even and recover the paper's strict left inequality — it's a short argument and would close the one genuine mathematical gap in the four headlines.
