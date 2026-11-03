import CoefficientOne.ScalarPositivity
import CoefficientOne.ScalarAlphabet

/-!
# Strict scalar positivity by rectangular complementation

This is the final step of the manuscript's scalar lemma: retain the
coefficient-one Schur term of B, multiply by the fifth power of the product
of the letters, and identify its rectangular complement.  Deleting a
letter is transported to the actual smaller positive alphabet.
-/

noncomputable section

namespace CoefficientOne.StrictScalarPositivity

open ScalarReciprocity ScalarPositivity SchurStability ScalarAlphabet

variable {N : ℕ}

/-- The explicit strict Schur lower bound in the scalar lemma. -/
theorem scalarA_ge_strict (a : Fin (N + 1) → ℝ) (ha : ∀ i, 0 < a i)
    (k : ℕ) (hkpos : 1 ≤ k) (hk : k ≤ N) :
    globalSchurValue (strictPartition k) a ≤ scalarA a k := by
  rw [scalarA_reciprocity a ha k hk, ← distinguished_reciprocity a ha k hk hkpos]
  exact mul_le_mul_of_nonneg_left
    (scalarB_ge_distinguished (fun i => (a i)⁻¹) (fun i => (inv_pos.mpr (ha i)).le) (N - k))
    (pow_nonneg (Finset.prod_nonneg (fun i _ => (ha i).le)) 5)

theorem scalarA_pos_succ (a : Fin (N + 1) → ℝ) (ha : ∀ i, 0 < a i)
    (k : ℕ) (hkpos : 1 ≤ k) (hk : k ≤ N) : 0 < scalarA a k :=
  (strictSchurValue_pos a ha k hk).trans_le (scalarA_ge_strict a ha k hkpos hk)

/-- A positive alphabet with at least k+1 letters has strictly positive A_k. -/
theorem scalarA_pos (a : Fin N → ℝ) (ha : ∀ i, 0 < a i)
    (k : ℕ) (hkpos : 1 ≤ k) (hk : k + 1 ≤ N) : 0 < scalarA a k := by
  cases N with
  | zero => omega
  | succ n => exact scalarA_pos_succ a ha k hkpos (by omega)

/-- The deleted alphabet in the matrix certificate still has enough
positive letters. The inserted zero contributes no additional letter. -/
theorem scalarA_update_pos (a : Fin N → ℝ) (ha : ∀ i, 0 < a i)
    (k : ℕ) (hkpos : 1 ≤ k) (hk : k + 2 ≤ N) (i : Fin N) :
    0 < scalarA (Function.update a i 0) k := by
  cases N with
  | zero => exact Fin.elim0 i
  | succ n =>
    rw [scalarA_update_eq_deleted a i k]
    exact scalarA_pos (deletedAlphabet a i) (deletedAlphabet_pos a ha i) k hkpos (by omega)

end CoefficientOne.StrictScalarPositivity
