import Collatz.ContinuedFractions

theorem results_eliahou_product_formula {L : ℕ} (c : CollatzCycle L) :
    ∏ i ∈ c.oddIndices, (3 * c.seq i + 1) =
    2 ^ L * ∏ i ∈ c.oddIndices, c.seq i :=
  eliahou_product_formula c

theorem results_eliahou_product_formula_real {L : ℕ} (c : CollatzCycle L) :
    ∏ i ∈ c.oddIndices, (3 + 1 / (c.seq i : ℝ)) = (2 : ℝ) ^ L :=
  eliahou_product_formula_real c

theorem results_eliahou_sandwich {L : ℕ} (c : CollatzCycle L) (hk : 0 < c.numOdd) :
    Real.logb 2 (3 + 1 / (c.maxElem : ℝ)) ≤ (L : ℝ) / c.numOdd ∧
    (L : ℝ) / c.numOdd ≤ Real.logb 2 (3 + 1 / (c.minElem : ℝ)) :=
  eliahou_sandwich c hk

theorem results_log2_three_lt_ratio {L : ℕ} (c : CollatzCycle L) (hk : 0 < c.numOdd) :
    Real.logb 2 3 < (L : ℝ) / c.numOdd :=
  log2_three_lt_ratio c hk

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

theorem results_eliahou_bound {L : ℕ} (c : CollatzCycle L)
    (hmin : (2 : ℕ) ^ 40 < c.minElem)
    (hk : 0 < c.numOdd) :
    17087915 ≤ L :=
  eliahou_bound c hmin hk
