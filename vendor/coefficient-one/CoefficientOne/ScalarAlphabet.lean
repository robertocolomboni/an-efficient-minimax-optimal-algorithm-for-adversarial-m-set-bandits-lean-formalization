import CoefficientOne.ScalarReciprocity
import CoefficientOne.ElementaryStability
import CoefficientOne.ScalarPadding

/-!
# Symmetry and deletion of the scalar expressions

These are the alphabet-identification steps needed to apply scalar positivity
inside the concrete matrix certificate. Every term is an actual Schur value
or the actual deletion load.
-/

noncomputable section

namespace CoefficientOne.ScalarAlphabet

open Finset ScalarLoad ScalarReciprocity SchurStability ElementaryStability

variable {N : ℕ}

theorem elementaryInt_comp_perm (a : Fin N → ℝ) (e : Equiv.Perm (Fin N)) (d : ℤ) :
    elementaryInt (a ∘ e) d = elementaryInt a d := by
  by_cases hd : d < 0
  · rw [elementaryInt_of_neg _ _ hd, elementaryInt_of_neg _ _ hd]
  · obtain ⟨k, rfl⟩ := Int.eq_ofNat_of_zero_le (show 0 ≤ d by omega)
    rw [elementaryInt_nat_eq_globalColumn, elementaryInt_nat_eq_globalColumn]
    exact globalSchurValue_comp_perm _ (rectanglePartition_antitone 1 k) a e

theorem load_comp_perm (a : Fin N → ℝ) (e : Equiv.Perm (Fin N)) (k : ℕ) :
    load (a ∘ e) k = load a k := by
  rw [load_eq_signed_schur, load_eq_signed_schur]
  apply congrArg₂ (fun x y : ℝ => x - y)
  · apply Finset.sum_congr rfl
    intro j hj
    have hj0 := (Finset.mem_Icc.mp hj).1
    rw [globalSchurValue_comp_perm _ (pPartition_antitone k j hj0),
      globalSchurValue_comp_perm _ (qPartition_antitone k j hj0)]
  · apply Finset.sum_congr rfl
    intro j hj
    have hj0 := (Finset.mem_Icc.mp hj).1
    rw [globalSchurValue_comp_perm _ (zPartition_antitone k j hj0)]

theorem scalarA_comp_perm (a : Fin N → ℝ) (e : Equiv.Perm (Fin N)) (k : ℕ) :
    scalarA (a ∘ e) k = scalarA a k := by
  unfold scalarA
  rw [globalSchurValue_comp_perm _ (rectanglePartition_antitone 2 k),
    globalSchurValue_comp_perm _ (rectanglePartition_antitone 3 (k + 1)),
    elementaryInt_comp_perm, load_comp_perm]

theorem scalarB_comp_perm (a : Fin N → ℝ) (e : Equiv.Perm (Fin N)) (k : ℕ) :
    scalarB (a ∘ e) k = scalarB a k := by
  unfold scalarB
  rw [globalSchurValue_comp_perm _ (rectanglePartition_antitone 3 k),
    globalSchurValue_comp_perm _ (rectanglePartition_antitone 2 (k + 1)),
    elementaryInt_comp_perm, load_comp_perm]

variable {M : ℕ}

theorem scalarA_padded (h : N ≤ M) (a : Fin N → ℝ) (k : ℕ) :
    scalarA (paddedAlphabet (M := M) a) k = scalarA a k := by
  unfold scalarA
  rw [globalSchurValue_padded h a _ (rectanglePartition_antitone 2 k),
    globalSchurValue_padded h a _ (rectanglePartition_antitone 3 (k + 1)),
    elementaryInt_padded h a, ScalarPadding.load_padded h a]

/-- The scalar A evaluated with coordinate i zero is its value on precisely
those N positive letters that remain after removing i. -/
theorem scalarA_update_eq_deleted (a : Fin (N + 1) → ℝ) (i : Fin (N + 1)) (k : ℕ) :
    scalarA (Function.update a i 0) k = scalarA (deletedAlphabet a i) k := by
  rw [← scalarA_comp_perm (Function.update a i 0) (Equiv.swap i (Fin.last N)) k,
    update_comp_swap_eq_padded]
  exact scalarA_padded (Nat.le_succ N) (deletedAlphabet a i) k

theorem scalarB_update_eq_deleted (a : Fin (N + 1) → ℝ) (i : Fin (N + 1)) (k : ℕ) :
    scalarB (Function.update a i 0) k = scalarB (deletedAlphabet a i) k := by
  rw [← scalarB_comp_perm (Function.update a i 0) (Equiv.swap i (Fin.last N)) k,
    update_comp_swap_eq_padded]
  exact ScalarPadding.scalarB_padded (Nat.le_succ N) (deletedAlphabet a i) k

end CoefficientOne.ScalarAlphabet
