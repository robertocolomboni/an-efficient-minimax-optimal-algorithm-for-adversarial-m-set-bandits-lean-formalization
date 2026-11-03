import CoefficientOne.ScalarLoad

/-!
# Rectangle deletion on every finite alphabet

This proves the unrestricted formal-letter statement `lem:rect-deletion`
in `paper/main.tex`. The terminal-row determinant argument is
reused after zero padding. Every Schur shape keeps all its rows, even when
the rectangle height is larger than the original alphabet size.
-/

noncomputable section

namespace CoefficientOne.RectangleDeletionStable

open Finset ScalarLoad SchurStability RectangleDeterminants RectangleDeletion

variable {N M : ℕ}

theorem completeInt_nat_eq_globalRow (a : Fin N → ℝ) (d : ℕ) :
    completeInt a d = globalSchurValue (rectanglePartition d 1) a := by
  by_cases hN : 0 < N
  · rw [globalRectangle_eq_rectangleSchur a d 1 (by omega),
      rectangleSchur_eq_completeDet a d 1 (by omega), Matrix.det_fin_one]
    simp only [toeplitz, Fin.val_zero, Nat.cast_zero, sub_zero, add_zero]
  · have hN0 : N = 0 := by omega
    subst N
    cases d with
    | zero =>
      simp only [Nat.cast_zero]
      rw [completeInt_zero, globalSchurValue_eq_of_fits _ _ (by
        intro r hr
        simp only [rectanglePartition, ite_self])]
      change 1 = rectangleSchur a 0 1
      rw [rectangleSchur_width_zero]
    | succ d =>
      have hc : completeInt a (d + 1 : ℕ) = 0 := by
        have hd : (0 : ℤ) ≤ (d : ℤ) + 1 := by omega
        simp [completeInt, SymmetricFunctions.hsymmExt, hd, CompleteDeletion.eval_hsymm_eq_sum]
      rw [hc, globalSchurValue_eq_zero_of_long _ _ 0 (by omega) (by
        simp only [rectanglePartition, if_pos (show 0 < 1 by omega)]
        omega)]

/-- Complete symmetric functions are stable at every integer degree, including
negative indices and the empty alphabet. -/
theorem completeInt_padded (h : N ≤ M) (a : Fin N → ℝ) (d : ℤ) :
    completeInt (paddedAlphabet (M := M) a) d = completeInt a d := by
  by_cases hd : d < 0
  · rw [completeInt_of_neg _ _ hd, completeInt_of_neg _ _ hd]
  · obtain ⟨r, rfl⟩ := Int.eq_ofNat_of_zero_le (show 0 ≤ d by omega)
    rw [completeInt_nat_eq_globalRow, completeInt_nat_eq_globalRow]
    exact globalSchurValue_padded h a _ (rectanglePartition_antitone r 1)

theorem completeToeplitz_padded (h : N ≤ M) (a : Fin N → ℝ) (q : ℤ) (k : ℕ) :
    toeplitz (completeInt (paddedAlphabet (M := M) a)) q k =
      toeplitz (completeInt a) q k := by
  ext i j
  exact completeInt_padded h a _

theorem deletedRectangle_padded (h : N ≤ M) (a : Fin N → ℝ) (x : ℝ) (q k : ℕ) :
    deletedRectangle (paddedAlphabet (M := M) a) x q k = deletedRectangle a x q k := by
  unfold deletedRectangle
  apply congrArg Matrix.det
  ext i j
  dsimp only [toeplitz]
  rw [completeInt_padded h a _, completeInt_padded h a _]

/-- The full row sequence of the Schur shape in the j-th deletion summand. -/
def deletionPartition (q k j : ℕ) (r : ℕ) : ℕ :=
  if r < k - j then q else if r < k then q - 1 else 0

theorem deletionPartition_antitone (q k j : ℕ) : Antitone (deletionPartition q k j) := by
  intro r s hrs
  unfold deletionPartition
  split_ifs <;> omega

theorem deletionPartition_zero_tail (q k j : ℕ) (hk : k ≤ M) (r : ℕ) (hr : M ≤ r) :
    deletionPartition q k j r = 0 := by
  unfold deletionPartition
  split_ifs <;> omega

theorem deletionShape_padded_eq_global (h : N ≤ M) (a : Fin N → ℝ)
    (q k j : ℕ) (hk : k ≤ M) :
    schurValue (deletionShape M q k j) (paddedAlphabet a) =
      globalSchurValue (deletionPartition q k j) a := by
  exact schurValue_padded_eq_global h a (deletionPartition q k j)
    (deletionPartition_antitone q k j) (deletionPartition_zero_tail q k j hk)

/-- The manuscript's formal-letter deletion identity with no alphabet-size
restriction. Its left side is the actual determinant defining `[a-x]`. -/
theorem rectangle_deletion_stable (a : Fin N → ℝ) (x : ℝ)
    (q k : ℕ) (hq : 1 ≤ q) :
    deletedRectangle a x q k =
      ∑ j : Fin (k + 1), (-x) ^ j.val *
        globalSchurValue (deletionPartition q k j.val) a := by
  let M := max N k
  have hNM : N ≤ M := le_max_left _ _
  have hkM : k ≤ M := le_max_right _ _
  have h := rectangle_deletion (paddedAlphabet (M := M) a) x q k hq hkM
  rw [deletedRectangle_padded hNM a x q k] at h
  rw [h]
  apply Finset.sum_congr rfl
  intro j hj
  rw [deletionShape_padded_eq_global hNM a q k j.val hkM]

/-- Rectangular Jacobi-Trudi with complete row sequences, including k>N. -/
theorem globalRectangle_eq_completeDet (a : Fin N → ℝ) (q k : ℕ) :
    globalSchurValue (rectanglePartition q k) a = (toeplitz (completeInt a) q k).det := by
  let M := max N k
  have hNM : N ≤ M := le_max_left _ _
  have hkM : k ≤ M := le_max_right _ _
  rw [← globalSchurValue_padded hNM a _ (rectanglePartition_antitone q k),
    globalRectangle_eq_rectangleSchur _ q k hkM,
    rectangleSchur_eq_completeDet _ q k hkM, completeToeplitz_padded hNM a q k]

theorem globalRectangle_update_eq_deletedRectangle (a : Fin N → ℝ) (i : Fin N)
    (q k : ℕ) :
    globalSchurValue (rectanglePartition q k) (Function.update a i 0) =
      deletedRectangle a (a i) q k := by
  rw [globalRectangle_eq_completeDet]
  unfold deletedRectangle
  apply congrArg Matrix.det
  ext r l
  exact CompleteDeletion.completeInt_update_zero a i _

/-- Actual-letter deletion at every rectangle height, including q=1 and k>N. -/
theorem rectangle_deletion_actual_stable (a : Fin N → ℝ) (i : Fin N)
    (q k : ℕ) (hq : 1 ≤ q) :
    globalSchurValue (rectanglePartition q k) (Function.update a i 0) =
      ∑ j : Fin (k + 1), (-a i) ^ j.val *
        globalSchurValue (deletionPartition q k j.val) a := by
  rw [globalRectangle_update_eq_deletedRectangle a i q k,
    rectangle_deletion_stable a (a i) q k hq]

end CoefficientOne.RectangleDeletionStable

end
