import EffectiveResistance.FiniteLaw
import Mathlib.RingTheory.MvPolynomial.Symmetric.Defs
import Mathlib.Tactic

/-!
# Elementary symmetric functions and the original finite law

The manuscript's elementary symmetric polynomial is the normalizing constant of
the original Lean law. This file proves that identification from the actual sum
over subsets, then implements the manuscript's convention at negative indices.
All identities here are standard finite-sum identities.
-/

noncomputable section

namespace CoefficientOne

open Finset MvPolynomial

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

theorem elementarySum_eq_powersetCard (w : ι → ℝ) (m : ℕ) :
    EffectiveResistance.elementarySum w m =
      ∑ s ∈ (Finset.univ : Finset ι).powersetCard m, ∏ i ∈ s, w i := by
  symm
  apply Finset.sum_subtype
  intro s
  simp only [Finset.mem_powersetCard, Finset.subset_univ, true_and]

theorem eval_esymm_eq_elementarySum (w : ι → ℝ) (m : ℕ) :
    MvPolynomial.eval w (MvPolynomial.esymm ι ℝ m) =
      EffectiveResistance.elementarySum w m := by
  rw [elementarySum_eq_powersetCard]
  simp [MvPolynomial.esymm]

/-- Zero at negative degrees, as in the manuscript. -/
def elementaryInt (w : ι → ℝ) (j : ℤ) : ℝ :=
  if 0 ≤ j then EffectiveResistance.elementarySum w j.toNat else 0

theorem elementaryInt_of_neg (w : ι → ℝ) (j : ℤ) (hj : j < 0) :
    elementaryInt w j = 0 := by
  simp [elementaryInt, not_le.mpr hj]

theorem elementaryInt_nat (w : ι → ℝ) (j : ℕ) :
    elementaryInt w j = EffectiveResistance.elementarySum w j := by
  simp [elementaryInt]

theorem elementarySum_zero (w : ι → ℝ) :
    EffectiveResistance.elementarySum w 0 = 1 := by
  rw [elementarySum_eq_powersetCard]
  simp

theorem elementaryInt_zero (w : ι → ℝ) : elementaryInt w 0 = 1 := by
  simp [elementaryInt, elementarySum_zero]

theorem elementarySum_of_card_lt (w : ι → ℝ) (m : ℕ)
    (hm : Fintype.card ι < m) : EffectiveResistance.elementarySum w m = 0 := by
  rw [elementarySum_eq_powersetCard]
  have hempty : (Finset.univ : Finset ι).powersetCard m = ∅ := by
    apply Finset.eq_empty_iff_forall_notMem.mpr
    intro s hs
    have hc := Finset.card_le_card (Finset.mem_powersetCard.mp hs).1
    have he := (Finset.mem_powersetCard.mp hs).2
    simp only [Finset.card_univ] at hc
    omega
  simp [hempty]

theorem elementaryInt_of_card_lt (w : ι → ℝ) (j : ℤ)
    (hj : (Fintype.card ι : ℤ) < j) : elementaryInt w j = 0 := by
  have hj0 : 0 ≤ j := by omega
  rw [elementaryInt, if_pos hj0]
  apply elementarySum_of_card_lt
  omega

theorem elementaryInt_pos (w : ι → ℝ) (hw : ∀ i, 0 < w i) (j : ℤ)
    (hj0 : 0 ≤ j) (hjcard : j ≤ Fintype.card ι) : 0 < elementaryInt w j := by
  rw [elementaryInt, if_pos hj0]
  exact EffectiveResistance.elementarySum_pos w hw (by omega)

theorem elementarySum_one (w : ι → ℝ) :
    EffectiveResistance.elementarySum w 1 = ∑ i, w i := by
  rw [← eval_esymm_eq_elementarySum]
  simp [MvPolynomial.esymm_one]
end CoefficientOne
