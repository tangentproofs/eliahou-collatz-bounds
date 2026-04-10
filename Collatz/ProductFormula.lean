import Mathlib
import Collatz.Defs

/-!
# The Product Formula for Collatz Cycles (Lemma 2.2)

This file proves Eliahou's key lemma: for a cycle Ω of the compressed Collatz
map with L elements, if Ω₁ is the subset of odd elements, then

  ∏_{n ∈ Ω₁} (3 + 1/n) = 2^L

or equivalently in integer form:

  ∏_{n ∈ Ω₁} (3n + 1) = 2^L · ∏_{n ∈ Ω₁} n

## References
* Eliahou (1993), Lemma 2.2
-/

open Finset BigOperators

set_option maxHeartbeats 800000

/-- For any n, the "multiplied" Collatz value:
    if n is odd then 3n+1, if n is even then n -/
def collatzMul (n : ℕ) : ℕ :=
  if n % 2 = 1 then 3 * n + 1 else n

/-- collatzMul relates to collatzComp by: collatzMul n = 2 * collatzComp n -/
theorem collatzMul_eq_two_mul_collatzComp {n : ℕ} :
    collatzMul n = 2 * collatzComp n := by
  unfold collatzMul
  rw [two_mul_collatzComp]

/-
collatzMul preserves positivity
-/
theorem collatzMul_pos {n : ℕ} (hn : 0 < n) : 0 < collatzMul n := by
  unfold collatzMul;
  grind

/-
Reindexing: the successor-mod map is a bijection on Fin L
-/
theorem succMod_bijective (L : ℕ) (hL : 0 < L) :
    Function.Bijective (fun i : Fin L => i.succMod hL) := by
  constructor;
  · intro i j; simp +decide [ Fin.succMod ] ;
    exact fun h => Fin.ext <| Nat.mod_eq_of_lt i.2 ▸ Nat.mod_eq_of_lt j.2 ▸ by simpa [ ← ZMod.natCast_eq_natCast_iff' ] using h;
  · intro i;
    use ⟨ ( i + L - 1 ) % L, Nat.mod_lt _ hL ⟩ ; simp +decide [ Fin.ext_iff, Fin.succMod ];
    rw [ Nat.sub_add_cancel ( by linarith [ Fin.is_lt i ] ) ] ; simp +decide [ Nat.mod_eq_of_lt ]

/-
Key step: ∏ T(seq i) = ∏ seq i, by reindexing
-/
theorem prod_collatzComp_eq_prod {L : ℕ} (c : CollatzCycle L) :
    ∏ i : Fin L, collatzComp (c.seq i) = ∏ i : Fin L, c.seq i := by
  obtain ⟨hL, seq, hpos, hstep⟩ := c;
  convert Equiv.prod_comp ( Equiv.ofBijective _ <| succMod_bijective _ _ ) _;
  exacts [ hstep _, hL ]

/-
Key step: ∏ collatzMul(seq i) = 2^L * ∏ seq i
-/
theorem prod_collatzMul_eq {L : ℕ} (c : CollatzCycle L) :
    ∏ i : Fin L, collatzMul (c.seq i) = 2 ^ L * ∏ i : Fin L, c.seq i := by
  rw [ Finset.prod_congr rfl fun i hi => collatzMul_eq_two_mul_collatzComp, Finset.prod_mul_distrib, Finset.prod_const, Finset.card_fin, prod_collatzComp_eq_prod ]

/-- For even n, collatzMul n = n -/
@[simp]
theorem collatzMul_even {n : ℕ} (hn : n % 2 = 0) : collatzMul n = n := by
  simp [collatzMul, hn]

/-- For odd n, collatzMul n = 3n + 1 -/
@[simp]
theorem collatzMul_odd {n : ℕ} (hn : n % 2 = 1) : collatzMul n = 3 * n + 1 := by
  simp [collatzMul, hn]

/-
The complement of odd indices is even indices
-/
theorem CollatzCycle.oddIndices_compl {L : ℕ} (c : CollatzCycle L) :
    c.oddIndicesᶜ = c.evenIndices := by
  ext i
  simp [CollatzCycle.oddIndices, CollatzCycle.evenIndices]

/-
Product over univ splits into product over odd and even indices
-/
theorem CollatzCycle.prod_split_odd_even {L : ℕ} (c : CollatzCycle L)
    (f : Fin L → ℕ) :
    ∏ i : Fin L, f i =
    (∏ i ∈ c.oddIndices, f i) * (∏ i ∈ c.evenIndices, f i) := by
  rw [ ← Finset.prod_union ];
  · rw [ show c.oddIndices ∪ c.evenIndices = Finset.univ from ?_ ];
    ext i
    simp [CollatzCycle.oddIndices, CollatzCycle.evenIndices];
    exact Nat.mod_two_eq_zero_or_one _ |> Or.symm;
  · exact Finset.disjoint_filter.mpr fun _ _ _ _ => by linarith;

/-! ## Lemma 2.2: The Product Formula (Integer Form) -/

/-
**Lemma 2.2** (Eliahou): For a Collatz cycle of length L,
    ∏_{i odd} (3 · xᵢ + 1) = 2^L · ∏_{i odd} xᵢ.
    Equivalently, ∏_{n ∈ Ω₁} (3 + 1/n) = 2^L.
-/
theorem eliahou_product_formula {L : ℕ} (c : CollatzCycle L) :
    ∏ i ∈ c.oddIndices, (3 * c.seq i + 1) =
    2 ^ L * ∏ i ∈ c.oddIndices, c.seq i := by
  -- From 1 and 5: (∏ odd i, (3*seq i + 1)) * (∏ even i, seq i) = 2^L * (∏ odd i, seq i) * (∏ even i, seq i)
  have h_even_eq : (∏ i : Fin L, collatzMul (c.seq i)) = (∏ i ∈ c.oddIndices, (3 * c.seq i + 1)) * (∏ i ∈ c.evenIndices, c.seq i) := by
    convert CollatzCycle.prod_split_odd_even c ( fun i => collatzMul ( c.seq i ) ) using 1;
    congr! 2;
    · unfold CollatzCycle.oddIndices at *; aesop;
    · unfold CollatzCycle.evenIndices at *; aesop
  have h_even_eq' : (∏ i : Fin L, c.seq i) = (∏ i ∈ c.oddIndices, c.seq i) * (∏ i ∈ c.evenIndices, c.seq i) := by
    convert CollatzCycle.prod_split_odd_even c _;
  exact mul_right_cancel₀ ( show ∏ i ∈ c.evenIndices, c.seq i ≠ 0 from Finset.prod_ne_zero_iff.mpr fun i hi => Nat.ne_of_gt <| c.pos i ) <| by nlinarith [ pow_pos ( zero_lt_two' ℤ ) L, prod_collatzMul_eq c ] ;

/-! ## The Product Formula in ℝ -/

/-
The product formula in ℝ: ∏_{i ∈ odd} (3 + 1/xᵢ) = 2^L
-/
theorem eliahou_product_formula_real {L : ℕ} (c : CollatzCycle L) :
    ∏ i ∈ c.oddIndices, (3 + 1 / (c.seq i : ℝ)) = (2 : ℝ) ^ L := by
  convert congr_arg ( fun x : ℕ => x / ∏ i ∈ c.oddIndices, ( c.seq i : ℝ ) ) ( show ( ∏ i ∈ c.oddIndices, ( 3 * c.seq i + 1 ) : ℕ ) = 2 ^ L * ∏ i ∈ c.oddIndices, ( c.seq i : ℕ ) from ?_ ) using 1;
  · norm_num [ add_div' ];
    rw [ ← Finset.prod_div_distrib, Finset.prod_congr rfl ] ; intros ; rw [ inv_eq_one_div, add_div, mul_div_cancel_right₀ _ ( Nat.cast_ne_zero.mpr <| ne_of_gt <| c.pos _ ) ];
  · rw [ eq_div_iff ] <;> norm_cast ; simp +decide [ Finset.prod_eq_zero_iff, ne_of_gt ( c.pos _ ) ];
  · exact eliahou_product_formula c
