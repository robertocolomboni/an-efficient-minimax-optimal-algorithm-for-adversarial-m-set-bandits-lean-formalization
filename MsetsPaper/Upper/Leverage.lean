import MsetsPaper.External.CesariColomboni
import MsetsPaper.Upper.CovariancePaperSteps
import MsetsPaper.Upper.SymmetricMatrixRange

/-!
# Manuscript Lemmas 1 and 2 on the actual exponential law

All inverse-covariance identities and Moore--Penrose properties are proved.
The coefficient-one estimate of Cesari--Colomboni is imported through the
proved spectral bridge in External/CesariColomboni.lean.
-/

noncomputable section

open Matrix MsetsLower MsetsLower.History
open scoped BigOperators

namespace MsetsPaper.Upper

variable {d m : ℕ}

def leverage (theta : Fin d → ℝ) (a : Action d m) : ℝ :=
  (fun i ↦ selectedIndicator i a) ⬝ᵥ
    ((secondMoment (weightedLaw (m := m) theta))⁻¹ *ᵥ (fun i ↦ selectedIndicator i a))

/-- The kernel clause of the cited spectral result, transported through the
proved equality between the two libraries' actual weighted laws. -/
theorem weighted_covariance_kernel_from_spectral (theta : Fin d → ℝ)
    (hmpos : 1 ≤ m) (hmtop : m ≤ d - 1) (x : Fin d → ℝ) :
    covariance (weightedLaw (m := m) theta) *ᵥ x = 0 ↔ ∀ i j, x i = x j := by
  rw [External.covariance_weightedLaw_eq theta (by omega)]
  exact CoefficientOne.covariance_mulVec_eq_zero_iff_constant
    (fun i ↦ Real.exp (theta i)) (fun i ↦ Real.exp_pos _) m hmpos (by simpa) x

/-- The manuscript's range identity: symmetry identifies the range with the
orthogonal complement of the kernel; the cited spectral kernel clause then
identifies that orthogonal complement with the zero-sum hyperplane. -/
theorem weighted_covariance_range_iff_sum_zero_via_symmetry (theta : Fin d → ℝ)
    (hmpos : 1 ≤ m) (hmtop : m ≤ d - 1) (y : Fin d → ℝ) :
    (∃ z, covariance (weightedLaw (m := m) theta) *ᵥ z = y) ↔ ∑ i, y i = 0 := by
  rw [symmetric_matrix_range_iff_kernel_orthogonal _ (covariance_isSymm _) y]
  constructor
  · intro hy
    have hone := (weighted_covariance_kernel_from_spectral theta hmpos hmtop
      (fun _ ↦ (1 : ℝ))).mpr (fun _ _ ↦ rfl)
    simpa only [dotProduct, one_mul] using hy _ hone
  · intro hy x hx
    have hc := (weighted_covariance_kernel_from_spectral theta hmpos hmtop x).mp hx
    let j : Fin d := ⟨0, by omega⟩
    have hconst : x = fun _ ↦ x j := funext (fun i ↦ hc i j)
    rw [hconst]
    simp only [dotProduct, ← Finset.mul_sum, hy, mul_zero]

/-- The definitive manuscript's difference-of-solutions proof of the
quadratic identity, using the imported spectral kernel clause. -/
theorem weighted_inverse_quadratic_via_spectral_kernel (theta : Fin d → ℝ)
    (hmpos : 1 ≤ m) (hmtop : m ≤ d - 1)
    (y : Fin d → ℝ) (hy : ∑ i, y i = 0) :
    y ⬝ᵥ ((secondMoment (weightedLaw (m := m) theta))⁻¹ *ᵥ y) =
      y ⬝ᵥ (covariancePseudoInverse (weightedLaw (m := m) theta) *ᵥ y) := by
  have hp := weightedLaw_pos theta (show m ≤ d by omega)
  have hs := sum_weightedLaw theta (show m ≤ d by omega)
  have hz := covariance_mulVec_secondMoment_inv_mulVec
    (weightedLaw theta) hp hmpos hmtop y hy
  have hrange := (weighted_covariance_range_iff_sum_zero_via_symmetry
    theta hmpos hmtop y).mpr hy
  have hMP := covariancePseudoInverse_isMoorePenroseInverse
    (weightedLaw theta) hp hs hmpos hmtop
  have hv : covariance (weightedLaw (m := m) theta) *ᵥ
      (covariancePseudoInverse (weightedLaw (m := m) theta) *ᵥ y) = y :=
    hMP.mulVec_eq_self_of_mem_range hrange
  let diff := (secondMoment (weightedLaw (m := m) theta))⁻¹ *ᵥ y -
    covariancePseudoInverse (weightedLaw (m := m) theta) *ᵥ y
  have hdiff : covariance (weightedLaw (m := m) theta) *ᵥ diff = 0 := by
    rw [Matrix.mulVec_sub, hz, hv, sub_self]
  have hc := (weighted_covariance_kernel_from_spectral theta hmpos hmtop diff).mp hdiff
  let j : Fin d := ⟨0, by omega⟩
  have hconst : diff = fun _ ↦ diff j := funext (fun i ↦ hc i j)
  have ho : y ⬝ᵥ diff = 0 := by
    rw [hconst]
    simp only [dotProduct, ← Finset.sum_mul, hy, zero_mul]
  change y ⬝ᵥ (_ - _) = 0 at ho
  rw [dotProduct_sub] at ho
  exact sub_eq_zero.mp ho

/-- Lemma 2, with the actual, uniquely characterized Moore--Penrose inverse. -/
theorem inverse_covariance_identity (theta : Fin d → ℝ)
    (hmpos : 1 ≤ m) (hmtop : m ≤ d - 1) :
    (secondMoment (weightedLaw (m := m) theta)).PosDef ∧
    (∀ y : Fin d → ℝ, (∑ i, y i = 0) →
      y ⬝ᵥ ((secondMoment (weightedLaw (m := m) theta))⁻¹ *ᵥ y) =
        y ⬝ᵥ (covariancePseudoInverse (weightedLaw (m := m) theta) *ᵥ y)) ∧
    (∀ a : Action d m, leverage theta a = 1 +
      ((fun i ↦ selectedIndicator i a) - weightedMarginal (m := m) theta) ⬝ᵥ
        (covariancePseudoInverse (weightedLaw (m := m) theta) *ᵥ
          ((fun i ↦ selectedIndicator i a) - weightedMarginal (m := m) theta))) := by
  have hp := weightedLaw_pos theta (show m ≤ d by omega)
  have hs := sum_weightedLaw theta (show m ≤ d by omega)
  refine ⟨weightedLaw_secondMoment_posDef theta hmpos hmtop, ?_, ?_⟩
  · intro y hy
    exact weighted_inverse_quadratic_via_spectral_kernel theta hmpos hmtop y hy
  · intro a
    change (fun i ↦ selectedIndicator i a) ⬝ᵥ
      ((secondMoment (weightedLaw theta))⁻¹ *ᵥ (fun i ↦ selectedIndicator i a)) = _
    rw [leverage_eq_one_add_centered_inverse_quadratic
      (weightedLaw theta) hp hs hmpos hmtop _ (sum_selectedIndicator a),
      weighted_inverse_quadratic_via_spectral_kernel theta hmpos hmtop _
        (sum_sub_marginal_eq_zero (weightedLaw theta) hs _ (sum_selectedIndicator a))]
    rfl

theorem leverage_le_phi (theta : Fin d → ℝ)
    (hmpos : 1 ≤ m) (hmtop : m ≤ d - 1) (a : Action d m) :
    leverage theta a ≤ phi (weightedMarginal (m := m) theta)
      (fun i ↦ selectedIndicator i a) := by
  have hC := covariancePseudoInverse_isMoorePenroseInverse
    (weightedLaw theta) (weightedLaw_pos theta (by omega))
    (sum_weightedLaw theta (by omega)) hmpos hmtop
  have hy := sum_sub_marginal_eq_zero (weightedLaw theta)
    (sum_weightedLaw theta (by omega)) (fun i ↦ selectedIndicator i a)
    (sum_selectedIndicator a)
  have hCC := External.cesariColomboni theta hmpos hmtop _ hC
    ((fun i ↦ selectedIndicator i a) - weightedMarginal (m := m) theta) hy
  rw [(inverse_covariance_identity theta hmpos hmtop).2.2 a]
  exact add_le_add le_rfl hCC

/-- Every clause of Lemma 1: leverage, affine correction, mean, and range.
The marginal hypotheses below are precisely membership in `P_lam`. -/
theorem linear_majorant (theta : Fin d → ℝ)
    (hmpos : 1 ≤ m) (hmtop : m ≤ d - 1) {lam : ℝ} (hlam : 0 < lam)
    (hlo : ∀ i, lam * ((m : ℝ) / d) ≤ weightedMarginal (m := m) theta i)
    (hhi : ∀ i, weightedMarginal (m := m) theta i ≤ 1 - lam * (1 - (m : ℝ) / d)) :
    (∀ a : Action d m, leverage theta a ≤
      phi (weightedMarginal (m := m) theta) (fun i ↦ selectedIndicator i a)) ∧
    (∀ a : Action d m, ∑ i,
      correction (m : ℝ) (weightedMarginal (m := m) theta) i * selectedIndicator i a =
        4 * phi (weightedMarginal (m := m) theta) (fun i ↦ selectedIndicator i a)) ∧
    ((∑ a : Action d m, weightedLaw theta a *
      phi (weightedMarginal (m := m) theta) (fun i ↦ selectedIndicator i a)) = (d : ℝ) + 1) ∧
    (∀ a : Action d m,
      0 ≤ phi (weightedMarginal (m := m) theta) (fun i ↦ selectedIndicator i a) ∧
      phi (weightedMarginal (m := m) theta) (fun i ↦ selectedIndicator i a) ≤ 1 + 2 * d / lam) :=
  ⟨leverage_le_phi theta hmpos hmtop,
    weightedLaw_correction_dot theta hmpos hmtop,
    weightedLaw_phi_mean theta hmpos hmtop,
    weightedLaw_phi_range theta hmpos hmtop hlam hlo hhi⟩

end MsetsPaper.Upper
