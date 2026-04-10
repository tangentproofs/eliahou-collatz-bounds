import Mathlib

/-!
# Collatz Function and Cycle Definitions

This file contains the basic definitions for the compressed Collatz function
and the notion of a Collatz cycle, following Eliahou (1993).

## References
* Eliahou, S. (1993). "The 3x+1 problem: new lower bounds on nontrivial cycle lengths."
  Discrete Mathematics, 118(1-3), 45-56.
-/

open Finset BigOperators

set_option maxHeartbeats 400000

/-- The compressed Collatz function: n/2 if even, (3n+1)/2 if odd.
    Returns 0 on input 0 (which is outside the domain of interest). -/
def collatzComp (n : ℕ) : ℕ :=
  if n % 2 = 0 then n / 2 else (3 * n + 1) / 2

/-
Key property: 2 * collatzComp(n) equals 3n+1 if n is odd, n if n is even
-/
theorem two_mul_collatzComp {n : ℕ} (hn : 0 < n) :
    2 * collatzComp n = if n % 2 = 1 then 3 * n + 1 else n := by
  unfold collatzComp; split_ifs <;> omega;

/-
collatzComp preserves positivity
-/
theorem collatzComp_pos {n : ℕ} (hn : 0 < n) : 0 < collatzComp n := by
  unfold collatzComp; split_ifs <;> omega;

/-- The successor modulo L, wrapping around: i ↦ (i+1) mod L -/
def Fin.succMod {L : ℕ} (i : Fin L) (hL : 0 < L) : Fin L :=
  ⟨(i.val + 1) % L, Nat.mod_lt _ hL⟩

/-- A cycle of the compressed Collatz map of length L.
    This represents a periodic orbit x₀, x₁, ..., x_{L-1} where T(xᵢ) = x_{(i+1) mod L}. -/
structure CollatzCycle (L : ℕ) where
  hL : 0 < L
  seq : Fin L → ℕ
  pos : ∀ i, 0 < seq i
  step : ∀ i : Fin L, collatzComp (seq i) = seq (i.succMod hL)

/-- The set of indices of odd elements -/
def CollatzCycle.oddIndices {L : ℕ} (c : CollatzCycle L) : Finset (Fin L) :=
  Finset.univ.filter (fun i => (c.seq i) % 2 = 1)

/-- The set of indices of even elements -/
def CollatzCycle.evenIndices {L : ℕ} (c : CollatzCycle L) : Finset (Fin L) :=
  Finset.univ.filter (fun i => (c.seq i) % 2 = 0)

/-- The number of odd elements in a cycle -/
noncomputable def CollatzCycle.numOdd {L : ℕ} (c : CollatzCycle L) : ℕ :=
  c.oddIndices.card

/-- The number of even elements in a cycle -/
noncomputable def CollatzCycle.numEven {L : ℕ} (c : CollatzCycle L) : ℕ :=
  c.evenIndices.card

/-- The minimum element of a cycle -/
noncomputable def CollatzCycle.minElem {L : ℕ} (c : CollatzCycle L) : ℕ :=
  haveI : Nonempty (Fin L) := ⟨⟨0, c.hL⟩⟩
  (Finset.univ.image c.seq).min' (by
    rw [Finset.image_nonempty]
    exact Finset.univ_nonempty)

/-- The maximum element of a cycle -/
noncomputable def CollatzCycle.maxElem {L : ℕ} (c : CollatzCycle L) : ℕ :=
  haveI : Nonempty (Fin L) := ⟨⟨0, c.hL⟩⟩
  (Finset.univ.image c.seq).max' (by
    rw [Finset.image_nonempty]
    exact Finset.univ_nonempty)

@[simp] theorem collatzComp_one : collatzComp 1 = 2 := by decide
@[simp] theorem collatzComp_two : collatzComp 2 = 1 := by decide

/-- The trivial cycle {1, 2} -/
def trivialCycle : CollatzCycle 2 where
  hL := by omega
  seq := ![1, 2]
  pos := by intro i; fin_cases i <;> simp
  step := by
    intro i; fin_cases i <;> simp [Fin.succMod, collatzComp]

/-- A cycle is non-trivial if its minimum element is > 2 (equivalently,
    it does not contain 1 or 2). The only cycle containing 1 is {1,2}
    (assuming the Collatz conjecture for small values, which has been verified). -/
def CollatzCycle.isNontrivial {L : ℕ} (c : CollatzCycle L) : Prop :=
  2 < c.minElem

/-
numOdd + numEven = L
-/
theorem CollatzCycle.numOdd_add_numEven {L : ℕ} (c : CollatzCycle L) :
    c.numOdd + c.numEven = L := by
  unfold CollatzCycle.numOdd CollatzCycle.numEven;
  convert Finset.card_add_card_compl ( Finset.filter ( fun i => ( c.seq i ) % 2 = 1 ) Finset.univ ) using 1;
  · unfold CollatzCycle.oddIndices CollatzCycle.evenIndices; simp +decide [ Finset.filter_not, Finset.card_sdiff ] ;
  · norm_num

/-
The minimum element is positive
-/
theorem CollatzCycle.minElem_pos {L : ℕ} (c : CollatzCycle L) :
    0 < c.minElem := by
  unfold CollatzCycle.minElem;
  simp_all +decide [ Finset.min' ];
  exact c.pos

/-
The minimum element is at most any cycle element
-/
theorem CollatzCycle.minElem_le {L : ℕ} (c : CollatzCycle L) (i : Fin L) :
    c.minElem ≤ c.seq i := by
  exact Finset.min'_le _ _ ( Finset.mem_image_of_mem _ ( Finset.mem_univ _ ) )

/-
The maximum element is at least any cycle element
-/
theorem CollatzCycle.le_maxElem {L : ℕ} (c : CollatzCycle L) (i : Fin L) :
    c.seq i ≤ c.maxElem := by
  exact Finset.le_max' ( Finset.univ.image c.seq ) _ ( Finset.mem_image_of_mem _ ( Finset.mem_univ _ ) )