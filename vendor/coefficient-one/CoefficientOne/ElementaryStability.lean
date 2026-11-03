import CoefficientOne.ScalarLoad

/-!
# Elementary symmetric functions under zero padding

The proved elementary-column identity and genuine tableau stability account
for every degree, including degrees above either alphabet size.
-/

noncomputable section

namespace CoefficientOne.ElementaryStability

open ScalarLoad SchurStability RectangleDeterminants

variable {N M : ℕ}

theorem elementaryInt_nat_eq_globalColumn (a : Fin N → ℝ) (k : ℕ) :
    elementaryInt a k = globalSchurValue (rectanglePartition 1 k) a := by
  by_cases hk : k ≤ N
  · rw [globalRectangle_eq_rectangleSchur a 1 k hk, rectangleSchur_width_one a k hk]
  · have hzero : elementaryInt a k = 0 := by
      apply elementaryInt_of_card_lt
      simp only [Fintype.card_fin]
      omega
    rw [hzero]
    symm
    apply globalSchurValue_eq_zero_of_long _ _ N (le_refl N)
    simp only [rectanglePartition, if_pos (show N < k by omega)]
    norm_num

theorem elementaryInt_padded (h : N ≤ M) (a : Fin N → ℝ) (d : ℤ) :
    elementaryInt (paddedAlphabet (M := M) a) d = elementaryInt a d := by
  by_cases hd : d < 0
  · rw [elementaryInt_of_neg _ _ hd, elementaryInt_of_neg _ _ hd]
  · obtain ⟨k, rfl⟩ := Int.eq_ofNat_of_zero_le (show 0 ≤ d by omega)
    rw [elementaryInt_nat_eq_globalColumn, elementaryInt_nat_eq_globalColumn]
    exact globalSchurValue_padded h a (rectanglePartition 1 k) (rectanglePartition_antitone 1 k)

end CoefficientOne.ElementaryStability
