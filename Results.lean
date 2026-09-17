import Collatz.LinearForm

theorem results_eliahou_product_formula {L : ℕ} (c : CollatzCycle L) :
    ∏ i ∈ c.oddIndices, (3 * c.seq i + 1) =
    2 ^ L * ∏ i ∈ c.oddIndices, c.seq i :=
  eliahou_product_formula c

theorem results_eliahou_product_formula_real {L : ℕ} (c : CollatzCycle L) :
    ∏ i ∈ c.oddIndices, (3 + 1 / (c.seq i : ℝ)) = (2 : ℝ) ^ L :=
  eliahou_product_formula_real c

theorem results_eliahou_sandwich {L : ℕ} (c : CollatzCycle L) :
    Real.logb 2 (3 + 1 / (c.maxElem : ℝ)) ≤ (L : ℝ) / c.numOdd ∧
    (L : ℝ) / c.numOdd ≤ Real.logb 2 (3 + 1 / (c.minElem : ℝ)) :=
  eliahou_sandwich c c.numOdd_pos

theorem results_log2_three_lt_ratio {L : ℕ} (c : CollatzCycle L) :
    Real.logb 2 3 < (L : ℝ) / c.numOdd :=
  log2_three_lt_ratio c c.numOdd_pos

theorem results_farey_pair_bound {p q p' q' x y : ℕ} (hq : 0 < q) (hq' : 0 < q')
    (hy : 0 < y)
    (hfarey : p' * q - p * q' = 1)
    (hleft : (p : ℚ) / q < x / y)
    (hright : (x : ℚ) / y < p' / q') :
    p + p' ≤ x ∧ q + q' ≤ y :=
  farey_pair_bound hq hq' hy hfarey hleft hright

theorem results_rational_approx_bound {k₁ L : ℕ} (hk₁ : 0 < k₁)
    {m : ℕ} (hm : 2 ^ 40 < m)
    (hlower : Real.logb 2 3 < (L : ℝ) / k₁)
    (hupper : (L : ℝ) / k₁ ≤ Real.logb 2 (3 + 1 / (m : ℝ))) :
    17087915 ≤ L :=
  rational_approx_bound hk₁ hm hlower hupper

/-- Paper-facing lower-bound consequence of Theorem 1.1 (discharges `numOdd_pos`). -/
theorem results_eliahou_bound {L : ℕ} (c : CollatzCycle L)
    (hmin : (2 : ℕ) ^ 40 < c.minElem) :
    17087915 ≤ L :=
  eliahou_bound_of_min c hmin

/-- Paper-facing bound on orbit cardinality under injectivity. -/
theorem results_eliahou_bound_card {L : ℕ} (c : CollatzCycle L)
    (hinj : Function.Injective c.seq)
    (hmin : (2 : ℕ) ^ 40 < c.minElem) :
    17087915 ≤ (Finset.univ.image c.seq).card :=
  eliahou_bound_card c hinj hmin

/-- Full Eliahou Theorem 1.1 linear form. -/
theorem results_eliahou_theorem_1_1 {L : ℕ} (c : CollatzCycle L)
    (hinj : Function.Injective c.seq)
    (hmin : (2 : ℕ) ^ 40 < c.minElem) :
    ∃ (a b cCoeff : ℕ), 0 < b ∧ a * cCoeff = 0 ∧
      (Finset.univ.image c.seq).card =
        301994 * a + 17087915 * b + 85137581 * cCoeff :=
  eliahou_theorem_1_1 c hinj hmin

theorem results_rational_linear_form {k₁ L : ℕ} (hk₁ : 0 < k₁)
    {m : ℕ} (hm : 2 ^ 40 < m)
    (hlower : Real.logb 2 3 < (L : ℝ) / k₁)
    (hupper : (L : ℝ) / k₁ ≤ Real.logb 2 (3 + 1 / (m : ℝ))) :
    ∃ (a b c : ℕ), 0 < b ∧ a * c = 0 ∧
      L = 301994 * a + 17087915 * b + 85137581 * c :=
  rational_linear_form hk₁ hm hlower hupper
