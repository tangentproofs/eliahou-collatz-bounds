import Collatz.ContinuedFractions

/-!
# Full linear form of Eliahou Theorem 1.1

This file formalises the precise statement

  Card Ω = 301994·a + 17087915·b + 85137581·c

with `a, b, c ≥ 0`, `b > 0`, and `a·c = 0`, for any exact compressed Collatz
cycle with minimum element `> 2^40`.
-/

open Real

set_option maxHeartbeats 8000000
set_option exponentiation.threshold 100000000
set_option maxRecDepth 10000

/-! ## Stronger Farey lemma -/

/-- If `p/q < x/y < p'/q'` is strictly between a Farey pair (`p'q - pq' = 1`),
then there exist positive integers `a, b` with
`x = a·p + b·p'` and `y = a·q + b·q'`. -/
theorem farey_intermediate_coeffs {p q p' q' x y : ℕ}
    (hq : 0 < q) (hq' : 0 < q') (hy : 0 < y)
    (hfarey : p' * q - p * q' = 1)
    (hleft : (p : ℚ) / q < x / y)
    (hright : (x : ℚ) / y < p' / q') :
    ∃ (a b : ℕ), 0 < a ∧ 0 < b ∧
      x = a * p + b * p' ∧ y = a * q + b * q' := by
  have hleftN : p * y < q * x := by
    have := (div_lt_div_iff₀ (Nat.cast_pos.mpr hq) (Nat.cast_pos.mpr hy)).mp hleft
    have : (p : ℚ) * y < q * x := by
      convert this using 1; ring
    exact_mod_cast this
  have hrightN : q' * x < p' * y := by
    have := (div_lt_div_iff₀ (Nat.cast_pos.mpr hy) (Nat.cast_pos.mpr hq')).mp hright
    have : (q' : ℚ) * x < p' * y := by
      convert this using 1; ring
    exact_mod_cast this
  refine ⟨p' * y - q' * x, q * x - p * y, Nat.sub_pos_of_lt hrightN,
    Nat.sub_pos_of_lt hleftN, ?_, ?_⟩
  · refine Int.natCast_inj.mp ?_
    have ha : ((p' * y - q' * x : ℕ) : ℤ) = (p' : ℤ) * y - (q' : ℤ) * x :=
      Int.natCast_sub (Nat.le_of_lt hrightN)
    have hb : ((q * x - p * y : ℕ) : ℤ) = (q : ℤ) * x - (p : ℤ) * y :=
      Int.natCast_sub (Nat.le_of_lt hleftN)
    rw [Nat.cast_add, Nat.cast_mul, Nat.cast_mul, ha, hb]
    have hf : (p' : ℤ) * q - (p : ℤ) * q' = 1 := by
      have hle : p * q' ≤ p' * q := Nat.le_of_lt (Nat.lt_of_sub_eq_succ hfarey)
      calc
        (p' : ℤ) * q - (p : ℤ) * q' = ↑(p' * q - p * q') := by
          rw [← Nat.cast_mul, ← Nat.cast_mul, ← Nat.cast_sub hle]
        _ = ↑(1 : ℕ) := by rw [hfarey]
        _ = 1 := by norm_num
    nlinarith [hf]
  · refine Int.natCast_inj.mp ?_
    have ha : ((p' * y - q' * x : ℕ) : ℤ) = (p' : ℤ) * y - (q' : ℤ) * x :=
      Int.natCast_sub (Nat.le_of_lt hrightN)
    have hb : ((q * x - p * y : ℕ) : ℤ) = (q : ℤ) * x - (p : ℤ) * y :=
      Int.natCast_sub (Nat.le_of_lt hleftN)
    rw [Nat.cast_add, Nat.cast_mul, Nat.cast_mul, ha, hb]
    have hf : (p' : ℤ) * q - (p : ℤ) * q' = 1 := by
      have hle : p * q' ≤ p' * q := Nat.le_of_lt (Nat.lt_of_sub_eq_succ hfarey)
      calc
        (p' : ℤ) * q - (p : ℤ) * q' = ↑(p' * q - p * q') := by
          rw [← Nat.cast_mul, ← Nat.cast_mul, ← Nat.cast_sub hle]
        _ = ↑(1 : ℕ) := by rw [hfarey]
        _ = 1 := by norm_num
    nlinarith [hf]

/-! ## Convergents involving p₁₆ / q₁₆ = 85137581 / 53715833 -/

/-- Oriented Farey identity for `p₁₆/q₁₆ < p₁₅/q₁₅`. -/
theorem farey_15_16 : 17087915 * 53715833 - 85137581 * 10781274 = 1 := by
  norm_num

/-- p₁₆/q₁₆ < log₂(3), equivalently `2^p₁₆ < 3^q₁₆`. -/
theorem two_pow_lt_three_pow_16 : (2 : ℕ) ^ 85137581 < 3 ^ 53715833 := by
  norm_num

/-- 85137581/53715833 < log₂(3) -/
theorem conv16_lt_logb_three :
    (85137581 : ℝ) / 53715833 < Real.logb 2 3 := by
  rw [div_lt_iff₀'] <;> norm_num
  rw [Real.logb, mul_div, lt_div_iff₀]
  · rw [← Real.log_rpow, ← Real.log_rpow, Real.log_lt_log_iff] <;> norm_num
  · positivity

/-! ## Paper-facing lower bound (discharges `hk`) -/

/-- Paper-facing lower bound: discharges `numOdd_pos` automatically. -/
theorem eliahou_bound_of_min {L : ℕ} (cyc : CollatzCycle L)
    (hmin : (2 : ℕ) ^ 40 < cyc.minElem) :
    17087915 ≤ L :=
  eliahou_bound cyc hmin cyc.numOdd_pos

/-- Paper-facing bound in terms of orbit cardinality when `seq` is injective. -/
theorem eliahou_bound_card {L : ℕ} (cyc : CollatzCycle L)
    (hinj : Function.Injective cyc.seq)
    (hmin : (2 : ℕ) ^ 40 < cyc.minElem) :
    17087915 ≤ (Finset.univ.image cyc.seq).card := by
  rw [cyc.card_eq_of_injective hinj]
  exact eliahou_bound_of_min cyc hmin

/-- Same bound for the `ExactCollatzCycle` wrapper. -/
theorem ExactCollatzCycle.eliahou_bound_card {L : ℕ} (cyc : ExactCollatzCycle L)
    (hmin : (2 : ℕ) ^ 40 < cyc.minElem) :
    17087915 ≤ (Finset.univ.image cyc.seq).card :=
  _root_.eliahou_bound_card cyc.toCollatzCycle cyc.injective hmin

/-! ## Full linear form (Eliahou Theorem 1.1) -/

private theorem rat_of_real_div_lt {a b c d : ℕ}
    (_hb : 0 < b) (_hd : 0 < d)
    (h : (a : ℝ) / b < (c : ℝ) / d) :
    (a : ℚ) / b < (c : ℚ) / d := by
  have : ((a : ℚ) / b : ℝ) < ((c : ℚ) / d : ℝ) := by
    simpa using h
  exact_mod_cast this

/-- Any fraction `L/k₁` in `(log₂ 3, log₂(3 + 1/m)]` for `m > 2^40` has the form
`L = 301994·a + 17087915·b + 85137581·c` with `b > 0` and `a·c = 0`. -/
theorem rational_linear_form {k₁ L : ℕ} (hk₁ : 0 < k₁)
    {m : ℕ} (hm : 2 ^ 40 < m)
    (hlower : Real.logb 2 3 < (L : ℝ) / k₁)
    (hupper : (L : ℝ) / k₁ ≤ Real.logb 2 (3 + 1 / (m : ℝ))) :
    ∃ (a b c : ℕ), 0 < b ∧ a * c = 0 ∧
      L = 301994 * a + 17087915 * b + 85137581 * c := by
  have h_low : (85137581 : ℚ) / 53715833 < (L : ℚ) / k₁ :=
    rat_of_real_div_lt (by norm_num) hk₁ (conv16_lt_logb_three.trans hlower)
  have h_high : (L : ℚ) / k₁ < (301994 : ℚ) / 190537 :=
    rat_of_real_div_lt hk₁ (by norm_num)
      (lt_of_le_of_lt hupper (logb_three_plus_lt_conv13 m hm))
  rcases lt_trichotomy ((L : ℚ) / k₁) ((17087915 : ℚ) / 10781274) with hlt | heq | hgt
  · -- p₁₆/q₁₆ < L/k₁ < p₁₅/q₁₅  ⇒  L = b·p₁₅ + c·p₁₆
    obtain ⟨cCoeff, bCoeff, hc, hb, hL, _⟩ :=
      farey_intermediate_coeffs
        (by norm_num : 0 < 53715833) (by norm_num : 0 < 10781274) hk₁
        farey_15_16 h_low hlt
    refine ⟨0, bCoeff, cCoeff, hb, by simp, ?_⟩
    linarith [hL]
  · -- L/k₁ = p₁₅/q₁₅  ⇒  L = b·p₁₅
    have heqN : L * 10781274 = 17087915 * k₁ := by
      have h := (div_eq_div_iff (by exact_mod_cast hk₁.ne' : (k₁ : ℚ) ≠ 0)
        (by norm_num : (10781274 : ℚ) ≠ 0)).mp heq
      exact_mod_cast h
    have hdiv : 17087915 ∣ L := by
      have : 17087915 ∣ 10781274 * L := ⟨k₁, by linarith [heqN]⟩
      exact coprime_15.dvd_of_dvd_mul_left this
    obtain ⟨b, rfl⟩ := hdiv
    have hbpos : 0 < b := by
      have hlogpos : (0 : ℝ) < Real.logb 2 3 :=
        Real.logb_pos (by norm_num) (by norm_num)
      have hpos : 0 < ((17087915 * b : ℕ) : ℝ) / k₁ := lt_trans hlogpos hlower
      exact Nat.pos_of_ne_zero fun h0 => by simp [h0] at hpos
    exact ⟨0, b, 0, hbpos, by simp, by ring⟩
  · -- p₁₅/q₁₅ < L/k₁ < p₁₃/q₁₃  ⇒  L = a·p₁₃ + b·p₁₅
    obtain ⟨aF, bF, haF, hbF, hL, _⟩ :=
      farey_intermediate_coeffs
        (by norm_num : 0 < 10781274) (by norm_num : 0 < 190537) hk₁
        farey_13_15 hgt h_high
    -- x = aF * p15 + bF * p13; paper wants p13*a + p15*b, so a=bF, b=aF
    refine ⟨bF, aF, 0, haF, by simp, ?_⟩
    linarith [hL]

/-- **Eliahou Theorem 1.1** (full linear form): for an injective compressed Collatz
cycle with minimum `> 2^40`,
`Card Ω = 301994·a + 17087915·b + 85137581·c` with `b > 0` and `a·c = 0`. -/
theorem eliahou_theorem_1_1 {L : ℕ} (cyc : CollatzCycle L)
    (hinj : Function.Injective cyc.seq)
    (hmin : (2 : ℕ) ^ 40 < cyc.minElem) :
    ∃ (a b cCoeff : ℕ), 0 < b ∧ a * cCoeff = 0 ∧
      (Finset.univ.image cyc.seq).card =
        301994 * a + 17087915 * b + 85137581 * cCoeff := by
  rw [cyc.card_eq_of_injective hinj]
  exact rational_linear_form cyc.numOdd_pos hmin
    (log2_three_lt_ratio cyc cyc.numOdd_pos) (ratio_le_log cyc cyc.numOdd_pos)

/-- Theorem 1.1 for the `ExactCollatzCycle` wrapper. -/
theorem ExactCollatzCycle.eliahou_theorem_1_1 {L : ℕ} (cyc : ExactCollatzCycle L)
    (hmin : (2 : ℕ) ^ 40 < cyc.minElem) :
    ∃ (a b cCoeff : ℕ), 0 < b ∧ a * cCoeff = 0 ∧
      (Finset.univ.image cyc.seq).card =
        301994 * a + 17087915 * b + 85137581 * cCoeff :=
  _root_.eliahou_theorem_1_1 cyc.toCollatzCycle cyc.injective hmin
