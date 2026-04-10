import Mathlib
import Collatz.Defs
import Collatz.ProductFormula

/-!
# The Sandwich Inequality (Theorem 2.1)

This file proves Theorem 2.1 from Eliahou (1993):

For a cycle Ω of the compressed Collatz map with k₁ odd elements,
L total elements, min element m, and max element M:

  log₂(3 + 1/M) < L/k₁ < log₂(3 + 1/m)

More precisely, we prove:
  (3 + 1/M)^k₁ < 2^L ≤ (3 + 1/m)^k₁

which follows from the product formula ∏_{n ∈ Ω₁} (3 + 1/n) = 2^L
and the fact that m ≤ n ≤ M for all n in the cycle.

## References
* Eliahou (1993), Theorem 2.1
-/

open Finset BigOperators Real

set_option maxHeartbeats 800000

/-! ## Upper bound: 2^L ≤ (3 + 1/m)^k₁ -/

/-
The product ∏ (3 + 1/xᵢ) ≤ (3 + 1/m)^k₁ where m is the minimum
-/
theorem prod_le_pow_min {L : ℕ} (c : CollatzCycle L) :
    ∏ i ∈ c.oddIndices, (3 + 1 / (c.seq i : ℝ)) ≤
    (3 + 1 / (c.minElem : ℝ)) ^ c.numOdd := by
  convert Finset.prod_le_prod ?_ fun i hi => ?_;
  rw [ Finset.prod_const, CollatzCycle.numOdd ];
  · infer_instance;
  · infer_instance;
  · exact fun i hi => by positivity;
  · gcongr;
    · exact_mod_cast CollatzCycle.minElem_pos c;
    · exact CollatzCycle.minElem_le c i

/-
The product ∏ (3 + 1/xᵢ) ≥ (3 + 1/M)^k₁ where M is the maximum
-/
theorem pow_max_le_prod {L : ℕ} (c : CollatzCycle L) :
    (3 + 1 / (c.maxElem : ℝ)) ^ c.numOdd ≤
    ∏ i ∈ c.oddIndices, (3 + 1 / (c.seq i : ℝ)) := by
  have h_prod_ge : ∀ i ∈ c.oddIndices, (3 + 1 / (c.maxElem : ℝ)) ≤ 3 + 1 / (c.seq i : ℝ) := by
    intros i hi; gcongr;
    · exact_mod_cast c.pos i;
    · exact c.le_maxElem i;
  convert Finset.prod_le_prod ( fun _ _ => by positivity ) h_prod_ge ; aesop

/-- **Theorem 2.1 (upper bound part)**: 2^L ≤ (3 + 1/m)^k₁ -/
theorem two_pow_le_bound_min {L : ℕ} (c : CollatzCycle L) :
    (2 : ℝ) ^ L ≤ (3 + 1 / (c.minElem : ℝ)) ^ c.numOdd := by
  rw [← eliahou_product_formula_real c]
  exact prod_le_pow_min c

/-- **Theorem 2.1 (lower bound part)**: (3 + 1/M)^k₁ ≤ 2^L -/
theorem bound_max_le_two_pow {L : ℕ} (c : CollatzCycle L) :
    (3 + 1 / (c.maxElem : ℝ)) ^ c.numOdd ≤ (2 : ℝ) ^ L := by
  rw [← eliahou_product_formula_real c]
  exact pow_max_le_prod c

/-! ## Logarithmic form of the sandwich inequality -/

/-
The ratio L/k₁ is at most log₂(3 + 1/m)
-/
theorem ratio_le_log {L : ℕ} (c : CollatzCycle L) (hk : 0 < c.numOdd) :
    (L : ℝ) / c.numOdd ≤ Real.logb 2 (3 + 1 / (c.minElem : ℝ)) := by
  rw [ div_le_iff₀' ( by positivity ), logb ];
  rw [ mul_div, le_div_iff₀ ( Real.log_pos ( by norm_num ) ) ];
  convert Real.log_le_log ?_ ( two_pow_le_bound_min c ) using 1;
  · norm_num;
  · rw [ Real.log_pow ];
  · positivity

/-
The ratio L/k₁ is at least log₂(3 + 1/M)
-/
theorem log_le_ratio {L : ℕ} (c : CollatzCycle L) (hk : 0 < c.numOdd) :
    Real.logb 2 (3 + 1 / (c.maxElem : ℝ)) ≤ (L : ℝ) / c.numOdd := by
  rw [ le_div_iff₀ ( by positivity ), mul_comm ];
  rw [ ← Real.logb_pow, Real.logb_le_iff_le_rpow ] <;> norm_cast;
  · convert bound_max_le_two_pow c using 1;
    norm_cast;
  · positivity

/-- **Theorem 2.1** (Eliahou): Full sandwich inequality.
    For a cycle Ω with k₁ = numOdd odd elements:
    log₂(3 + 1/M) ≤ L/k₁ ≤ log₂(3 + 1/m) -/
theorem eliahou_sandwich {L : ℕ} (c : CollatzCycle L) (hk : 0 < c.numOdd) :
    Real.logb 2 (3 + 1 / (c.maxElem : ℝ)) ≤ (L : ℝ) / c.numOdd ∧
    (L : ℝ) / c.numOdd ≤ Real.logb 2 (3 + 1 / (c.minElem : ℝ)) :=
  ⟨log_le_ratio c hk, ratio_le_log c hk⟩

/-
Since log₂(3) < log₂(3 + 1/n) for all n > 0, the ratio L/k₁ > log₂(3)
-/
theorem log2_three_lt_ratio {L : ℕ} (c : CollatzCycle L) (hk : 0 < c.numOdd) :
    Real.logb 2 3 < (L : ℝ) / c.numOdd := by
  -- From log_le_ratio: log₂(3 + 1/M) ≤ L/k₁.
  have h_log_le : Real.logb 2 (3 + 1 / (c.maxElem : ℝ)) ≤ (L : ℝ) / c.numOdd := by
    exact log_le_ratio c hk;
  refine' lt_of_lt_of_le _ h_log_le;
  gcongr <;> norm_num;
  exact lt_of_lt_of_le ( c.pos ⟨ 0, by linarith [ c.hL ] ⟩ ) ( CollatzCycle.le_maxElem c ⟨ 0, by linarith [ c.hL ] ⟩ )
