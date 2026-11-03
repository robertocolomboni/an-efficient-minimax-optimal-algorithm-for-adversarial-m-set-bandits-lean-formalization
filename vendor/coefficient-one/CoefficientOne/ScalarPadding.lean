import CoefficientOne.ScalarReciprocity
import CoefficientOne.ElementaryStability

/-! Zero-padding stability of the actual deletion load and scalar B. -/

noncomputable section

namespace CoefficientOne.ScalarPadding

open Finset ScalarLoad ScalarReciprocity SchurStability

variable {N M : ℕ}

theorem load_padded (h : N ≤ M) (a : Fin N → ℝ) (k : ℕ) :
    load (paddedAlphabet (M := M) a) k = load a k := by
  rw [load_eq_signed_schur, load_eq_signed_schur]
  congr 1
  · apply Finset.sum_congr rfl
    intro j hj
    have hj0 := (Finset.mem_Icc.mp hj).1
    rw [globalSchurValue_padded h a _ (pPartition_antitone k j hj0),
      globalSchurValue_padded h a _ (qPartition_antitone k j hj0)]
  · apply Finset.sum_congr rfl
    intro j hj
    have hj0 := (Finset.mem_Icc.mp hj).1
    rw [globalSchurValue_padded h a _ (zPartition_antitone k j hj0)]

theorem scalarB_padded (h : N ≤ M) (a : Fin N → ℝ) (k : ℕ) :
    scalarB (paddedAlphabet (M := M) a) k = scalarB a k := by
  unfold scalarB
  rw [globalSchurValue_padded h a _ (rectanglePartition_antitone 3 k),
    globalSchurValue_padded h a _ (rectanglePartition_antitone 2 (k + 1)),
    ElementaryStability.elementaryInt_padded h a k, load_padded h a k]

end CoefficientOne.ScalarPadding

end
