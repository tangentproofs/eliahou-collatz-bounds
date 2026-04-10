import Mathlib
import Collatz.Defs
import Collatz.ProductFormula
import Collatz.Sandwich

/-!
# Continued Fractions and the Eliahou Bound

This file contains the continued fraction machinery and numerical results
needed for Eliahou's main theorem, completing the proof that any nontrivial
Collatz cycle must contain at least 17,087,915 elements.

## Mathematical overview

The argument combines three ingredients:

1. **Sandwich inequality** (Theorem 2.1): For a cycle with k₁ odd elements,
   total length L, and minimum m:  log₂(3) < L/k₁ < log₂(3 + 1/m)

2. **Farey pair bound** (Lemma 3.1): For a Farey pair p/q < p'/q', any
   fraction x/y strictly between them has x ≥ p+p' and y ≥ q+q'.

3. **Numerical bounds** from continued fraction convergents of log₂(3):
   The key convergents are p₁₃/q₁₃ = 301994/190537 and
   p₁₅/q₁₅ = 17087915/10781274, which bracket the interval
   (log₂(3), log₂(3 + 2⁻⁴⁰)).

## References
* Eliahou (1993), Sections 3-4 and Theorem 1.1
-/

open Finset BigOperators Real

set_option maxHeartbeats 4000000

/-! ## Farey pair lemma -/

/-
**Lemma 3.1** (Farey pair property): If p/q < p'/q' form a Farey pair
    (i.e., p'q - pq' = 1), then any fraction x/y strictly between them
    satisfies x ≥ p + p' and y ≥ q + q'.
-/
theorem farey_pair_bound {p q p' q' x y : ℕ} (hq : 0 < q) (hq' : 0 < q')
    (hy : 0 < y)
    (hfarey : p' * q - p * q' = 1)
    (hleft : (p : ℚ) / q < x / y)
    (hright : (x : ℚ) / y < p' / q') :
    p + p' ≤ x ∧ q + q' ≤ y := by
  constructor <;> rw [ div_lt_div_iff₀ ] at hleft hright <;> norm_cast at *;
  · rw [ Nat.sub_eq_iff_eq_add ] at hfarey;
    · nlinarith;
    · exact le_of_lt ( Nat.lt_of_sub_eq_succ hfarey );
  · nlinarith [ Nat.sub_add_cancel ( le_of_lt ( Nat.lt_of_sub_eq_succ hfarey ) ) ]

/-- Corollary: in a Farey pair, for fractions strictly between,
    the numerator is at least p + p'. -/
theorem farey_numerator_bound {p q p' q' x y : ℕ} (hq : 0 < q) (hq' : 0 < q')
    (hy : 0 < y)
    (hfarey : p' * q - p * q' = 1)
    (hleft : (p : ℚ) / q < x / y)
    (hright : (x : ℚ) / y < p' / q') :
    p + p' ≤ x :=
  (farey_pair_bound hq hq' hy hfarey hleft hright).1

/-! ## Numerical facts about convergents of log₂(3)

The continued fraction of log₂(3) = [1; 1, 1, 2, 2, 3, 1, 5, 2, 23, 2, 2, 1, 55, 1, ...]

Key convergents (pₙ/qₙ):
- p₁₃/q₁₃ = 301994/190537   (upper convergent, above log₂(3))
- p₁₄/q₁₄ = 16785921/10590737 (lower convergent, below log₂(3))
- p₁₅/q₁₅ = 17087915/10781274 (upper convergent, above log₂(3))

These satisfy:
  p₁₄/q₁₄ < log₂(3) < p₁₅/q₁₅ < p₁₃/q₁₃

The pairs (p₁₄, p₁₅) and (p₁₅, p₁₃) form Farey pairs.
-/

/-- p₁₃ · q₁₅ - p₁₅ · q₁₃ = 1 (Farey pair identity) -/
theorem farey_13_15 : 301994 * 10781274 - 17087915 * 190537 = 1 := by
  native_decide +revert

/-
p₁₄ · q₁₅ - p₁₅ · q₁₄ = 1 (Farey pair identity for consecutive convergents)
-/
theorem farey_14_15 : 17087915 * 10590737 - 16785921 * 10781274 = 1 := by
  decide +revert

/-
gcd(p₁₅, q₁₅) = 1 (convergents are coprime)
-/
theorem coprime_15 : Nat.Coprime 17087915 10781274 := by
  norm_num

/-
p₁₅/q₁₅ > log₂(3), equivalently 3^q₁₅ < 2^p₁₅
-/
theorem three_pow_lt_two_pow_15 : (3 : ℕ) ^ 10781274 < 2 ^ 17087915 := by
  native_decide +revert

/-
p₁₄/q₁₄ < log₂(3), equivalently 3^q₁₄ > 2^p₁₄
-/
theorem two_pow_lt_three_pow_14 : (2 : ℕ) ^ 16785921 < 3 ^ 10590737 := by
  exact mod_cast by native_decide;

/-
The key inequality: log₂(3 + 2⁻⁴⁰) < p₁₃/q₁₃.
    Equivalently: (3 · 2⁴⁰ + 1)^q₁₃ < 2^(p₁₃ + 40·q₁₃).
    This shows that the interval (log₂(3), log₂(3+2⁻⁴⁰)) lies entirely
    below the convergent 301994/190537.

    This is a verified computational fact; the exponent is
    p₁₃ + 40·q₁₃ = 301994 + 7621480 = 7923474.
-/
theorem log_bound_at_2_40 :
    (3 * 2 ^ 40 + 1 : ℕ) ^ 190537 < 2 ^ 7923474 := by
  native_decide +revert

/-! ## Derived inequalities in ℝ -/

/-
log₂(3) < 17087915/10781274
-/
theorem logb_three_lt_conv15 :
    Real.logb 2 3 < (17087915 : ℝ) / 10781274 := by
  rw [ Real.logb, div_lt_div_iff₀ ] <;> norm_num;
  · rw [ mul_comm, ← Real.log_rpow, ← Real.log_rpow, Real.log_lt_log_iff ] <;> norm_num;
    exact mod_cast by native_decide;
  · positivity

/-
16785921/10590737 < log₂(3)
-/
theorem conv14_lt_logb_three :
    (16785921 : ℝ) / 10590737 < Real.logb 2 3 := by
  rw [ div_lt_iff₀' ] <;> norm_num;
  rw [ Real.logb, mul_div, lt_div_iff₀ ];
  · rw [ ← Real.log_rpow, ← Real.log_rpow, Real.log_lt_log_iff ] <;> norm_num;
    exact mod_cast by native_decide;
  · positivity

/-
log₂(3 + 2⁻⁴⁰) < 301994/190537
-/
theorem logb_three_plus_lt_conv13 (m : ℕ) (hm : 2 ^ 40 < m) :
    Real.logb 2 (3 + 1 / (m : ℝ)) < (301994 : ℝ) / 190537 := by
  -- By combining the results, we conclude the proof.
  have h_log_bound : Real.logb 2 (3 + 1 / (m : ℝ)) < Real.logb 2 ((3 * 2 ^ 40 + 1) / 2 ^ 40) := by
    gcongr <;> norm_num;
    nlinarith [ show ( m : ℝ ) ≥ 2 ^ 40 + 1 by exact_mod_cast hm, inv_mul_cancel₀ ( by positivity : ( m : ℝ ) ≠ 0 ) ];
  refine lt_of_lt_of_le h_log_bound ?_;
  rw [ Real.logb_le_iff_le_rpow ] <;> norm_num;
  rw [ Real.le_rpow_iff_log_le ] <;> norm_num;
  field_simp;
  rw [ mul_comm, ← Real.log_rpow, ← Real.log_rpow, Real.log_le_log_iff ] <;> norm_num;
  rw [ div_pow, div_le_iff₀ ] <;> exact mod_cast by native_decide;

/-! ## The Main Bound -/

/-
Any fraction L/k₁ in the interval (log₂(3), log₂(3 + 1/m)) for m > 2^40
    satisfies L ≥ 17087915.

    **Proof sketch**: By `logb_three_plus_lt_conv13`, the interval is contained
    in (log₂(3), 301994/190537). There are three cases:
    1. L/k₁ ∈ (17087915/10781274, 301994/190537): Farey pair bound gives L ≥ 17389909.
    2. L/k₁ = 17087915/10781274: coprimality gives L = 17087915t ≥ 17087915.
    3. L/k₁ ∈ (log₂(3), 17087915/10781274): Farey pair (p₁₄/q₁₄, p₁₅/q₁₅)
       gives L ≥ 16785921 + 17087915.
-/
theorem rational_approx_bound {k₁ L : ℕ} (hk₁ : 0 < k₁) (hL : 0 < L)
    {m : ℕ} (hm : 2 ^ 40 < m)
    (hlower : Real.logb 2 3 < (L : ℝ) / k₁)
    (hupper : (L : ℝ) / k₁ ≤ Real.logb 2 (3 + 1 / (m : ℝ))) :
    17087915 ≤ L := by
  -- From `hlower` and `hupper`, we get: `16785921 / 10590737 < L / k₁ < 301994 / 190537`.
  have h_bounds : (16785921 : ℚ) / 10590737 < (L : ℚ) / k₁ ∧ (L : ℚ) / k₁ < 301994 / 190537 := by
    apply And.intro;
    · convert conv14_lt_logb_three.trans hlower using 1;
      rw [ div_lt_div_iff₀ ] <;> norm_cast;
      rw [ div_lt_div_iff₀ ] <;> norm_cast;
    · have := logb_three_plus_lt_conv13 m hm;
      convert lt_of_le_of_lt hupper this using 1;
      norm_num [ div_lt_div_iff₀, hk₁, hL ];
      norm_cast;
  -- By trichotomy, we have either L/k₁ > 17087915/10781274 or L/k₁ < 17087915/10781274 or L/k₁ = 17087915/10781274.
  by_cases h_trichotomy : (L : ℚ) / k₁ > (17087915 : ℚ) / 10781274 ∨ (L : ℚ) / k₁ < (17087915 : ℚ) / 10781274 ∨ (L : ℚ) / k₁ = (17087915 : ℚ) / 10781274;
  · rcases h_trichotomy with h | h | h <;> norm_num at *;
    · -- By farey_pair_bound, we have L ≥ 17087915 + 301994.
      have := farey_pair_bound (by norm_num : 0 < 10781274) (by norm_num : 0 < 190537) (by linarith : 0 < k₁) (farey_13_15) h h_bounds.right
      linarith;
    · rw [ div_lt_div_iff₀ ] at * <;> norm_cast at *;
      grind;
    · rw [ div_eq_div_iff ] at h <;> norm_cast at * <;> try linarith;
      grind;
  · grind

/-- **Theorem 1.1** (Eliahou, 1993): Any cycle of the compressed Collatz map
    with minimum element > 2^40 has at least 17,087,915 elements.

    The verification that the Collatz conjecture holds for all n ≤ 2^40
    (done computationally by Yoneda, and later extended by others) means this
    bound applies unconditionally to any nontrivial cycle. -/
theorem eliahou_bound {L : ℕ} (c : CollatzCycle L)
    (hmin : (2 : ℕ) ^ 40 < c.minElem)
    (hk : 0 < c.numOdd) :
    17087915 ≤ L := by
  apply rational_approx_bound (by omega) c.hL hmin
    (log2_three_lt_ratio c hk) (ratio_le_log c hk)

/-- More precise form (Theorem 1.1): the cycle length L is expressible as
    301994a + 17087915b + 85137581c with a,b,c ≥ 0, b > 0, ac = 0.

    This requires a more detailed analysis of the semi-convergent structure
    of the continued fraction of log₂(3), specifically showing that the
    three Farey pairs between consecutive upper semi-convergents
    p₁₃ = 301994, p₁₅ = 17087915, p₁₇ = 85137581 completely partition
    the admissible fractions. The proof is left as an exercise in
    continued fraction theory. -/
theorem eliahou_precise {L : ℕ} (c : CollatzCycle L)
    (hmin : (2 : ℕ) ^ 40 < c.minElem)
    (hk : 0 < c.numOdd) :
    ∃ a b cval : ℕ, 0 < b ∧ a * cval = 0 ∧
    L = 301994 * a + 17087915 * b + 85137581 * cval := by
  sorry
