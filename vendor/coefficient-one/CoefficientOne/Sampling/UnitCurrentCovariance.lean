import CoefficientOne.Sampling.UnitCurrent
import CoefficientOne.Sampling.ConditionalGap

/-! # Applying the general unit-current lemma to the actual covariance law -/

open scoped BigOperators
open Matrix EffectiveResistance

namespace CoefficientOne.Sampling
noncomputable section

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

theorem covarianceNetwork_hasConstantKernel
    (w : ι → ℝ) (hw : ∀ i, 0 < w i) (m : ℕ)
    (hmpos : 1 ≤ m) (hmtop : m ≤ Fintype.card ι - 1) :
    HasConstantKernel (externalFieldCovarianceNetwork w hw m hmpos (by simpa using hmtop)) := by
  intro x
  rw [externalFieldCovarianceNetwork_laplacian]
  exact covariance_mulVec_eq_zero_iff_constant w hw m hmpos (by simpa using hmtop) x

theorem covarianceNetwork_hasNormalizedGapOne
    (w : ι → ℝ) (hw : ∀ i, 0 < w i) (m : ℕ)
    (hmpos : 1 ≤ m) (hmtop : m ≤ Fintype.card ι - 1) :
    HasNormalizedGapOne (externalFieldCovarianceNetwork w hw m hmpos (by simpa using hmtop)) := by
  unfold HasNormalizedGapOne
  simp only [externalFieldCovarianceNetwork_laplacian]
  intro i hi
  exact normalized_covariance_gap_fintype w hw m hmpos hmtop i hi

/-- The concrete constant-three conclusion, for the covariance of the actual
positive product-weight law and every nontrivial rank. -/
theorem covariance_unit_current_edgeVariation_le_three
    (w : ι → ℝ) (hw : ∀ i, 0 < w i) (m : ℕ)
    (hmpos : 1 ≤ m) (hmtop : m ≤ Fintype.card ι - 1) (u : ι → ℝ)
    (a b : ι) (hab : a ≠ b) (hsolve : covarianceMatrix w m *ᵥ u = pairDemand a b) :
    (externalFieldCovarianceNetwork w hw m hmpos (by simpa using hmtop)).edgeVariation u ≤ 3 := by
  haveI : Nonempty ι := ⟨a⟩
  apply unit_current_edgeVariation_le_three _
    (externalFieldCovarianceNetwork_degree_pos w hw m hmpos (by simpa using hmtop))
    (covarianceNetwork_hasConstantKernel w hw m hmpos hmtop)
    (covarianceNetwork_hasNormalizedGapOne w hw m hmpos hmtop) u a b hab
  simpa only [externalFieldCovarianceNetwork_laplacian] using hsolve

/-- The static input to the variation bound; its covariance is the original
finite-law covariance, not an assumed graph representation. -/
theorem covariance_edgeVariation_le_three_halves_l1
    (w : ι → ℝ) (hw : ∀ i, 0 < w i) (m : ℕ)
    (hmpos : 1 ≤ m) (hmtop : m ≤ Fintype.card ι - 1) (h : ι → ℝ) :
    (externalFieldCovarianceNetwork w hw m hmpos (by simpa using hmtop)).edgeVariation h ≤
      (3 / 2 : ℝ) * l1Norm (covarianceMatrix w m *ᵥ h) := by
  haveI : Nonempty ι := Fintype.card_pos_iff.mp (by omega)
  have he := edgeVariation_le_three_halves_l1_laplacian _
    (externalFieldCovarianceNetwork_degree_pos w hw m hmpos (by simpa using hmtop))
    (covarianceNetwork_hasConstantKernel w hw m hmpos hmtop)
    (covarianceNetwork_hasNormalizedGapOne w hw m hmpos hmtop) h
  simpa only [externalFieldCovarianceNetwork_laplacian] using he

end
end CoefficientOne.Sampling
