import MsetsPaper.Upper.WeightedLaw

/-!
# The concrete finite-law loss estimator

These are identities for the estimator actually defined by the manuscript's
inverse second moment and scalar action feedback.  They do not assume an
unbiasedness certificate, concentration, or a bound on the loss coordinates.
The stochastic conditional-expectation bridge remains a separate obligation.
-/

noncomputable section

open scoped BigOperators
open Matrix MsetsLower MsetsLower.History

namespace MsetsPaper.Upper

variable {d m : ℕ}

/-- The algorithm's vector estimate, formed from an action and scalar feedback. -/
def estimateVector (theta : Fin d → ℝ) (a : Action d m) (ell : Fin d → ℝ) : Fin d → ℝ :=
  actionLoss a ell • ((secondMoment (weightedLaw (m := m) theta))⁻¹ *ᵥ
    (fun i => selectedIndicator i a))

/-- The estimated loss assigned to the comparator action b after observing a. -/
def estimateScalar (theta : Fin d → ℝ) (a : Action d m) (ell : Fin d → ℝ)
    (b : Action d m) : ℝ :=
  (fun i => selectedIndicator i b) ⬝ᵥ estimateVector theta a ell

private theorem matrix_mulVec_finite_sum {α : Type*} [Fintype α]
    (A : Matrix (Fin d) (Fin d) ℝ) (v : α → Fin d → ℝ) :
    A *ᵥ (∑ a, v a) = ∑ a, A *ᵥ v a := by
  classical
  ext i
  simp only [Matrix.mulVec, dotProduct, Finset.sum_apply, Finset.mul_sum]
  exact Finset.sum_comm

/-- The second moment applied to ell equals the average indicator times feedback. -/
theorem secondMoment_mulVec_observation (p : Action d m → ℝ) (ell : Fin d → ℝ) :
    secondMoment p *ᵥ ell =
      ∑ a : Action d m, (p a * actionLoss a ell) • (fun i => selectedIndicator i a) := by
  classical
  ext i
  simp only [Matrix.mulVec, dotProduct, secondMoment, Finset.sum_mul,
    Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro a _
  rw [← dot_indicator_eq_actionLoss a ell]
  simp only [dotProduct, Finset.mul_sum, Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro j _
  ring

/-- Unbiasedness under the actual normalized exponential sampling law. -/
theorem estimateVector_mean (theta : Fin d → ℝ) (ell : Fin d → ℝ)
    (hmpos : 1 ≤ m) (hmtop : m ≤ d - 1) :
    ∑ a : Action d m, weightedLaw theta a • estimateVector theta a ell = ell := by
  classical
  letI := (weightedLaw_secondMoment_posDef theta hmpos hmtop).isUnit.invertible
  calc
    (∑ a : Action d m, weightedLaw theta a • estimateVector theta a ell) =
        ∑ a : Action d m, (secondMoment (weightedLaw (m := m) theta))⁻¹ *ᵥ
          ((weightedLaw theta a * actionLoss a ell) • (fun i => selectedIndicator i a)) := by
      apply Finset.sum_congr rfl
      intro a _
      rw [Matrix.mulVec_smul]
      simp only [estimateVector, smul_smul]
    _ = (secondMoment (weightedLaw (m := m) theta))⁻¹ *ᵥ
        (∑ a : Action d m,
          (weightedLaw theta a * actionLoss a ell) • (fun i => selectedIndicator i a)) :=
      (matrix_mulVec_finite_sum _ _).symm
    _ = (secondMoment (weightedLaw (m := m) theta))⁻¹ *ᵥ
        (secondMoment (weightedLaw (m := m) theta) *ᵥ ell) := by
      rw [← secondMoment_mulVec_observation]
    _ = ell := by
      rw [Matrix.mulVec_mulVec, Matrix.inv_mul_of_invertible, Matrix.one_mulVec]

/-- The same unbiasedness identity for the estimated loss of any fixed action. -/
theorem estimateScalar_mean (theta : Fin d → ℝ) (ell : Fin d → ℝ)
    (hmpos : 1 ≤ m) (hmtop : m ≤ d - 1) (b : Action d m) :
    ∑ a : Action d m, weightedLaw theta a * estimateScalar theta a ell b =
      actionLoss b ell := by
  classical
  calc
    _ = (fun i => selectedIndicator i b) ⬝ᵥ
        (∑ a : Action d m, weightedLaw theta a • estimateVector theta a ell) := by
      rw [dotProduct_sum]
      simp only [dotProduct_smul, smul_eq_mul, estimateScalar]
    _ = (fun i => selectedIndicator i b) ⬝ᵥ ell := by
      rw [estimateVector_mean theta ell hmpos hmtop]
    _ = actionLoss b ell := by
      rw [dotProduct_comm, dot_indicator_eq_actionLoss]

/-- Averaging actionwise linear estimates is exactly a dot product with the marginal. -/
theorem mean_indicator_dot (p : Action d m → ℝ) (v : Fin d → ℝ) :
    ∑ b : Action d m, p b * ((fun i => selectedIndicator i b) ⬝ᵥ v) =
      marginal p ⬝ᵥ v := by
  classical
  simp only [dotProduct, marginal, Finset.mul_sum, Finset.sum_mul]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro b _
  ring

/-- For each realized action a, averaging its estimates over b gives the
realized scalar loss exactly. This is pathwise, not an expectation over a. -/
theorem estimateScalar_pathwise_mean (theta : Fin d → ℝ) (ell : Fin d → ℝ)
    (hmpos : 1 ≤ m) (hmtop : m ≤ d - 1) (a : Action d m) :
    ∑ b : Action d m, weightedLaw theta b * estimateScalar theta a ell b =
      actionLoss a ell := by
  classical
  have hm : (m : ℝ) ≠ 0 := by exact_mod_cast (show m ≠ 0 by omega)
  have hswap : weightedMarginal (m := m) theta ⬝ᵥ
      ((secondMoment (weightedLaw (m := m) theta))⁻¹ *ᵥ (fun i => selectedIndicator i a)) =
      (fun i => selectedIndicator i a) ⬝ᵥ
        ((secondMoment (weightedLaw (m := m) theta))⁻¹ *ᵥ weightedMarginal (m := m) theta) := by
    simpa only [(secondMoment_isSymm (weightedLaw (m := m) theta)).inv.eq] using
      Matrix.dotProduct_transpose_mulVec (secondMoment (weightedLaw (m := m) theta))⁻¹
        (weightedMarginal (m := m) theta) (fun i => selectedIndicator i a)
  have hunit : weightedMarginal (m := m) theta ⬝ᵥ
      ((secondMoment (weightedLaw (m := m) theta))⁻¹ *ᵥ (fun i => selectedIndicator i a)) = 1 := by
    rw [hswap, weightedLaw_inverse_marginal theta hmpos hmtop]
    simp only [dotProduct, ← Finset.sum_mul, sum_selectedIndicator, mul_inv_cancel₀ hm]
  change (∑ b : Action d m, weightedLaw theta b *
    ((fun i => selectedIndicator i b) ⬝ᵥ estimateVector theta a ell)) = _
  rw [mean_indicator_dot]
  change weightedMarginal (m := m) theta ⬝ᵥ estimateVector theta a ell = _
  rw [estimateVector, dotProduct_smul, hunit]
  simp

end MsetsPaper.Upper
