import CoefficientOne.Sampling.Model
import Mathlib

/-! # Continuous dummy-coordinate lift in Corollary 2(ii) -/

open scoped BigOperators
open Set

namespace CoefficientOne.Sampling

noncomputable section

/-- Zero-based version of `min(1,max(0,σ-j+1))` in the manuscript. -/
def dummyCoordinate (σ : ℝ) (j : ℕ) : ℝ := min 1 (max 0 (σ - j))

theorem dummyCoordinate_nonneg (σ : ℝ) (j : ℕ) : 0 ≤ dummyCoordinate σ j :=
  le_min (by norm_num) (le_max_left _ _)

theorem dummyCoordinate_le_one (σ : ℝ) (j : ℕ) : dummyCoordinate σ j ≤ 1 :=
  min_le_left _ _

theorem dummyCoordinate_mono (j : ℕ) : Monotone (fun σ => dummyCoordinate σ j) := by
  intro σ τ h
  exact min_le_min_left _ (max_le_max_left _ (sub_le_sub_right h _))

theorem continuous_dummyCoordinate (j : ℕ) : Continuous (fun σ => dummyCoordinate σ j) := by
  unfold dummyCoordinate
  fun_prop

theorem dummyCoordinate_telescope (σ : ℝ) (j : ℕ) :
    dummyCoordinate σ j = max 0 (σ - j) - max 0 (σ - (j + 1 : ℕ)) := by
  unfold dummyCoordinate
  push_cast
  by_cases h0 : σ ≤ j
  · rw [max_eq_left (by linarith), max_eq_left (by linarith), min_eq_right (by norm_num)]
    ring
  · by_cases h1 : σ ≤ j + 1
    · rw [max_eq_right (by linarith), max_eq_left (by linarith), min_eq_right (by linarith)]
      ring
    · rw [max_eq_right (by linarith), max_eq_right (by linarith), min_eq_left (by linarith)]
      ring

theorem sum_dummyCoordinate_range (σ : ℝ) (k : ℕ) :
    ∑ j ∈ Finset.range k, dummyCoordinate σ j = max 0 σ - max 0 (σ - k) := by
  induction k with
  | zero => simp
  | succ k ih =>
    rw [Finset.sum_range_succ, ih, dummyCoordinate_telescope]
    ring

theorem sum_dummyCoordinate (k : ℕ) {σ : ℝ} (hσ : 0 ≤ σ) (hσk : σ ≤ k) :
    ∑ j : Fin k, dummyCoordinate σ j.val = σ := by
  rw [Fin.sum_univ_eq_sum_range, sum_dummyCoordinate_range,
    max_eq_right hσ, max_eq_left (sub_nonpos.mpr hσk), sub_zero]

theorem dummyCoordinate_l1 (k : ℕ) {σ τ : ℝ}
    (hσ : 0 ≤ σ) (hσk : σ ≤ k) (hτ : 0 ≤ τ) (hτk : τ ≤ k) :
    ∑ j : Fin k, |dummyCoordinate σ j.val - dummyCoordinate τ j.val| = |σ - τ| := by
  by_cases h : σ ≤ τ
  · simp_rw [abs_of_nonpos (sub_nonpos.mpr (dummyCoordinate_mono _ h)), neg_sub]
    rw [Finset.sum_sub_distrib, sum_dummyCoordinate k hτ hτk, sum_dummyCoordinate k hσ hσk,
      abs_of_nonpos (sub_nonpos.mpr h)]
    ring
  · have h' : τ ≤ σ := le_of_not_ge h
    simp_rw [abs_of_nonneg (sub_nonneg.mpr (dummyCoordinate_mono _ h'))]
    rw [Finset.sum_sub_distrib, sum_dummyCoordinate k hσ hσk, sum_dummyCoordinate k hτ hτk,
      abs_of_nonneg (sub_nonneg.mpr h')]

theorem dummyCoordinate_pos_iff (σ : ℝ) (j : ℕ) :
    0 < dummyCoordinate σ j ↔ (j : ℝ) < σ := by
  simp [dummyCoordinate, lt_min_iff, lt_max_iff, sub_pos]

theorem dummyCoordinate_lt_one_iff (σ : ℝ) (j : ℕ) :
    dummyCoordinate σ j < 1 ↔ σ < j + 1 := by
  simp only [dummyCoordinate, min_lt_iff, lt_self_iff_false, false_or, max_lt_iff]
  constructor
  · intro h
    linarith [h.2]
  · intro h
    exact ⟨by norm_num, by linarith⟩

theorem dummyCoordinate_fractional_unique {σ : ℝ} {i j : ℕ}
    (hi0 : 0 < dummyCoordinate σ i) (hi1 : dummyCoordinate σ i < 1)
    (hj0 : 0 < dummyCoordinate σ j) (hj1 : dummyCoordinate σ j < 1) : i = j := by
  have hi := (dummyCoordinate_pos_iff σ i).mp hi0
  have hi' := (dummyCoordinate_lt_one_iff σ i).mp hi1
  have hj := (dummyCoordinate_pos_iff σ j).mp hj0
  have hj' := (dummyCoordinate_lt_one_iff σ j).mp hj1
  rcases lt_trichotomy i j with hij | hij | hji
  · have hcast : (i : ℝ) + 1 ≤ j := by exact_mod_cast Nat.succ_le_of_lt hij
    linarith
  · exact hij
  · have hcast : (j : ℝ) + 1 ≤ i := by exact_mod_cast Nat.succ_le_of_lt hji
    linarith

variable {ι : Type*} [Fintype ι]

def coordinateSum (x : ι → ℝ) : ℝ := ∑ i, x i

def dummyLift (k : ℕ) (x : ι → ℝ) : ι ⊕ Fin k → ℝ :=
  Sum.elim x (fun j => dummyCoordinate ((k : ℝ) - coordinateSum x) j.val)

theorem coordinateSum_nonneg {k : ℕ} {x : ι → ℝ} (hx : x ∈ atMostHypersimplex ι k) :
    0 ≤ coordinateSum x := Finset.sum_nonneg fun i _ => (hx.1 i).1

theorem dummyLift_mem_hypersimplex {k : ℕ} {x : ι → ℝ}
    (hx : x ∈ atMostHypersimplex ι k) : dummyLift k x ∈ hypersimplex (ι ⊕ Fin k) k := by
  refine ⟨?_, ?_⟩
  · intro a
    cases a with
    | inl i => exact hx.1 i
    | inr j => exact ⟨dummyCoordinate_nonneg _ _, dummyCoordinate_le_one _ _⟩
  · rw [Fintype.sum_sum_type]
    change coordinateSum x + (∑ j : Fin k, dummyCoordinate ((k : ℝ) - coordinateSum x) j.val) = k
    have hσ : 0 ≤ (k : ℝ) - coordinateSum x := sub_nonneg.mpr hx.2
    have hσk : (k : ℝ) - coordinateSum x ≤ k := by linarith [coordinateSum_nonneg hx]
    rw [sum_dummyCoordinate k hσ hσk]
    ring

theorem continuous_dummyLift (k : ℕ) : Continuous (dummyLift (ι := ι) k) := by
  apply continuous_pi
  intro a
  cases a with
  | inl i => exact continuous_apply i
  | inr j =>
    change Continuous (fun x : ι → ℝ => dummyCoordinate ((k : ℝ) - coordinateSum x) j.val)
    unfold coordinateSum dummyCoordinate
    fun_prop

theorem coordinateSum_sub_le_l1 (x y : ι → ℝ) :
    |coordinateSum x - coordinateSum y| ≤ vectorL1 (fun i => x i - y i) := by
  unfold coordinateSum vectorL1 EffectiveResistance.l1Norm
  rw [← Finset.sum_sub_distrib]
  exact Finset.abs_sum_le_sum_abs _ _

theorem dummyLift_l1_eq {k : ℕ} {x y : ι → ℝ}
    (hx : x ∈ atMostHypersimplex ι k) (hy : y ∈ atMostHypersimplex ι k) :
    vectorL1 (fun a => dummyLift k x a - dummyLift k y a) =
      vectorL1 (fun i => x i - y i) + |coordinateSum x - coordinateSum y| := by
  unfold vectorL1 EffectiveResistance.l1Norm
  rw [Fintype.sum_sum_type]
  dsimp only [dummyLift, Sum.elim_inl, Sum.elim_inr]
  have hσ : 0 ≤ (k : ℝ) - coordinateSum x := sub_nonneg.mpr hx.2
  have hτ : 0 ≤ (k : ℝ) - coordinateSum y := sub_nonneg.mpr hy.2
  rw [dummyCoordinate_l1 k hσ (by linarith [coordinateSum_nonneg hx])
    hτ (by linarith [coordinateSum_nonneg hy])]
  congr 1
  rw [show (k : ℝ) - coordinateSum x - (k - coordinateSum y) =
    -(coordinateSum x - coordinateSum y) by ring, abs_neg]

theorem dummyLift_l1_le_two {k : ℕ} {x y : ι → ℝ}
    (hx : x ∈ atMostHypersimplex ι k) (hy : y ∈ atMostHypersimplex ι k) :
    vectorL1 (fun a => dummyLift k x a - dummyLift k y a) ≤
      2 * vectorL1 (fun i => x i - y i) := by
  rw [dummyLift_l1_eq hx hy]
  linarith [coordinateSum_sub_le_l1 x y]

end
end CoefficientOne.Sampling
