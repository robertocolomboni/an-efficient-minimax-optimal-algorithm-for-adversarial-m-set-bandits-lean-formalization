import CoefficientOne.RectangleDeletion
import CoefficientOne.SchurStability

/-!
# The actual deletion load and its signed Schur expansion

The load is defined from complete, untruncated partitions. The proof first
uses the manuscript's rectangle deletion formula, then its power-sum
expansion, and finally the alternant cancellation. Zero padding
and vanishing of overlong shapes account for every alphabet size.
-/

noncomputable section

namespace CoefficientOne.ScalarLoad

open Finset RectangleDeterminants RectangleDeletion SchurStability
open AlternantIdentities AlternantCancellation

variable {N : ℕ}

def rectanglePartition (q k : ℕ) (r : ℕ) : ℕ := if r < k then q else 0

theorem rectanglePartition_antitone (q k : ℕ) : Antitone (rectanglePartition q k) := by
  intro r s hrs
  unfold rectanglePartition
  split_ifs <;> omega

theorem rectanglePartition_zero_tail (q k : ℕ) (hk : k ≤ N)
    (r : ℕ) (hr : N ≤ r) : rectanglePartition q k r = 0 := by
  simp only [rectanglePartition, if_neg (show ¬ r < k by omega)]

theorem globalRectangle_eq_rectangleSchur (a : Fin N → ℝ) (q k : ℕ) (hk : k ≤ N) :
    globalSchurValue (rectanglePartition q k) a = rectangleSchur a q k := by
  rw [globalSchurValue_eq_of_fits _ _ (rectanglePartition_zero_tail q k hk)]
  rfl

/-- The manuscript's F_k, with the standard zero convention for overlong shapes. -/
def load (a : Fin N → ℝ) (k : ℕ) : ℝ :=
  ∑ i, a i ^ 2 * globalSchurValue (rectanglePartition 4 k) (Function.update a i 0)

theorem load_eq_rectangleLoad (a : Fin N → ℝ) (k : ℕ) (hk : k ≤ N) :
    load a k = rectangleLoad a 4 k := by
  unfold load rectangleLoad
  simp_rw [globalRectangle_eq_rectangleSchur _ 4 k hk]

theorem initialPartition_eq_deletionShape (k : ℕ) (j : Fin (k + 1)) (i : Fin N) :
    initialPartition k j.val i.val = deletionShape N 4 k j.val i := by
  unfold initialPartition initialPart deletionShape
  have hj := j.isLt
  split_ifs <;> omega

theorem globalInitial_eq_deletionSchur (a : Fin N → ℝ)
    (k : ℕ) (hk : k ≤ N) (j : Fin (k + 1)) :
    globalSchurValue (initialPartition k j.val) a =
      schurValue (deletionShape N 4 k j.val) a := by
  rw [globalSchurValue_eq_of_fits _ _
    (initialPartition_zero _ _ (by omega) (by omega))]
  congr 1
  funext i
  exact initialPartition_eq_deletionShape k j i

theorem load_eq_zero_of_height_gt (a : Fin N → ℝ) (k : ℕ) (hk : N < k) :
    load a k = 0 := by
  unfold load
  apply Finset.sum_eq_zero
  intro i _
  rw [globalSchurValue_eq_zero_of_long _ _ N (le_refl N) (by
    simp [rectanglePartition, hk])]
  ring

theorem globalInitial_eq_zero_of_height_gt (a : Fin N → ℝ)
    (k : ℕ) (hk : N < k) (j : Fin (k + 1)) :
    globalSchurValue (initialPartition k j.val) a = 0 := by
  apply globalSchurValue_eq_zero_of_long _ _ N (le_refl N)
  unfold initialPartition initialPart
  split_ifs <;> omega

/-- The power-sum formula for the actual load, for every alphabet size and k. -/
theorem load_eq_power_sums_fin (a : Fin N → ℝ) (k : ℕ) :
    load a k = ∑ j : Fin (k + 1), (-1 : ℝ) ^ j.val * powerSum a (j.val + 2) *
      globalSchurValue (initialPartition k j.val) a := by
  by_cases hk : k ≤ N
  · rw [load_eq_rectangleLoad a k hk, rectangleLoad_eq_power_sums a 4 k (by decide) hk]
    apply Finset.sum_congr rfl
    intro j _
    rw [globalInitial_eq_deletionSchur a k hk j]
  · rw [load_eq_zero_of_height_gt a k (by omega)]
    symm
    apply Finset.sum_eq_zero
    intro j _
    rw [globalInitial_eq_zero_of_height_gt a k (by omega) j]
    ring

theorem sum_fin_eq_sum_int_Icc (k : ℕ) (f : ℤ → ℝ) :
    (∑ j : Fin (k + 1), f j.val) = ∑ j ∈ Icc 0 (k : ℤ), f j := by
  refine Finset.sum_bij (fun j _ => (j.val : ℤ)) ?_ ?_ ?_ ?_
  · intro j _
    simp only [Finset.mem_Icc]
    have hj := j.isLt
    omega
  · intro i _ j _ heq
    apply Fin.ext
    omega
  · intro j hj
    obtain ⟨hj0, hjk⟩ := Finset.mem_Icc.mp hj
    refine ⟨⟨j.toNat, by omega⟩, Finset.mem_univ _, ?_⟩
    change (j.toNat : ℤ) = j
    omega
  · intro j _
    rfl

theorem load_eq_power_sums (a : Fin N → ℝ) (k : ℕ) :
    load a k = ∑ j ∈ Icc 0 (k : ℤ), (-1 : ℝ) ^ j.toNat *
      powerSum a (j + 2).toNat * globalSchurValue (initialPartition k j) a := by
  rw [load_eq_power_sums_fin]
  have hcast : ∀ j : Fin (k + 1), ((j.val : ℤ) + 2).toNat = j.val + 2 := by
    intro j
    omega
  simpa only [Int.toNat_natCast, hcast] using
    sum_fin_eq_sum_int_Icc k (fun j => (-1 : ℝ) ^ j.toNat *
      powerSum a (j + 2).toNat * globalSchurValue (initialPartition k j) a)

/-- The full signed-load identity, with its left side defined by actual
alphabet deletion. No lower bound on the alphabet size is assumed. -/
theorem load_eq_signed_schur (a : Fin N → ℝ) (k : ℕ) :
    load a k =
      (∑ j ∈ Icc 0 (k : ℤ),
        (globalSchurValue (pPartition k j) a - globalSchurValue (qPartition k j) a)) -
      ∑ j ∈ Icc 0 ((k : ℤ) - 1), globalSchurValue (zPartition k j) a := by
  rw [load_eq_power_sums]
  exact signed_load_value_arbitrary a k (by omega)

end CoefficientOne.ScalarLoad
