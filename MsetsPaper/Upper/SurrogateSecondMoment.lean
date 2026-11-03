import MsetsPaper.Upper.KWOneStep

/-!
# T1: the actual pathwise second-order term

These are the calculations in the second-order display of the main proof.
The averaging variable b is a fresh comparator under p_theta; a and its
feedback are fixed. It is not the second moment of the unbiased estimator
over its observation, which is a different calculation in L5.
-/

noncomputable section

open Matrix MsetsLower MsetsLower.History
open scoped BigOperators

namespace MsetsPaper.Upper

variable {d m : ℕ}

theorem estimateScalar_pathwise_secondMoment (theta ell : Fin d → ℝ)
    (hmpos : 1 ≤ m) (hmtop : m ≤ d - 1) (a : Action d m) :
    finiteExpectation (weightedLaw theta) (fun b ↦ (estimateScalar theta a ell b) ^ 2) =
      (actionLoss a ell) ^ 2 * leverage theta a := by
  classical
  letI := (weightedLaw_secondMoment_posDef theta hmpos hmtop).isUnit.invertible
  have hform (b : Action d m) : estimateScalar theta a ell b =
      actionLoss a ell * actionLoss b
        ((secondMoment (weightedLaw (m := m) theta))⁻¹ *ᵥ
          (fun i ↦ selectedIndicator i a)) := by
    rw [estimateScalar, estimateVector, dotProduct_smul]
    rw [dotProduct_comm, dot_indicator_eq_actionLoss]
    rfl
  simp_rw [finiteExpectation, hform, mul_pow]
  calc
    _ = (actionLoss a ell) ^ 2 * ∑ b, weightedLaw theta b *
        (actionLoss b ((secondMoment (weightedLaw (m := m) theta))⁻¹ *ᵥ
          (fun i ↦ selectedIndicator i a))) ^ 2 := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro b _
      ring
    _ = _ := by
      rw [← secondMoment_quadratic, Matrix.mulVec_mulVec,
        Matrix.mul_inv_of_invertible, Matrix.one_mulVec, dotProduct_comm]
      rfl

theorem estimateScalar_pathwise_secondMoment_le_phi (theta ell : Fin d → ℝ)
    (hmpos : 1 ≤ m) (hmtop : m ≤ d - 1) (a : Action d m)
    (hloss : |actionLoss a ell| ≤ 1) :
    finiteExpectation (weightedLaw theta) (fun b ↦ (estimateScalar theta a ell b) ^ 2) ≤
      phi (weightedMarginal (m := m) theta) (fun i ↦ selectedIndicator i a) := by
  have hlev0 : 0 ≤ leverage theta a := by
    simpa only [leverage, star_trivial] using
      (weightedLaw_secondMoment_posDef theta hmpos hmtop).inv.posSemidef.dotProduct_mulVec_nonneg
        (fun i ↦ selectedIndicator i a)
  have hy2 : (actionLoss a ell) ^ 2 ≤ 1 := by
    nlinarith [(abs_le.mp hloss).1, (abs_le.mp hloss).2]
  rw [estimateScalar_pathwise_secondMoment theta ell hmpos hmtop a]
  exact (mul_le_mul_of_nonneg_right hy2 hlev0).trans
    (by simpa using leverage_le_phi theta hmpos hmtop a)

theorem correction_mean (theta : Fin d → ℝ)
    (hmpos : 1 ≤ m) (hmtop : m ≤ d - 1) :
    finiteExpectation (weightedLaw theta)
      (fun b : Action d m ↦ actionLoss b (correction (m : ℝ) (weightedMarginal (m := m) theta))) =
      4 * ((d : ℝ) + 1) := by
  unfold finiteExpectation
  simp_rw [actionLoss_correction theta hmpos hmtop]
  calc
    _ = 4 * ∑ b : Action d m, weightedLaw theta b *
        phi (weightedMarginal (m := m) theta) (fun i ↦ selectedIndicator i b) := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro b _
      ring
    _ = _ := by rw [weightedLaw_phi_mean theta hmpos hmtop]

theorem correction_secondMoment (theta : Fin d → ℝ)
    (hmpos : 1 ≤ m) (hmtop : m ≤ d - 1) {eta : ℝ} (heta : 0 < eta)
    (hlo : ∀ i, (128 * eta * d / 2) * ((m : ℝ) / d) ≤ weightedMarginal (m := m) theta i)
    (hhi : ∀ i, weightedMarginal (m := m) theta i ≤
      1 - (128 * eta * d / 2) * (1 - (m : ℝ) / d)) :
    finiteExpectation (weightedLaw theta)
      (fun b : Action d m ↦ (actionLoss b (correction (m : ℝ) (weightedMarginal (m := m) theta))) ^ 2) ≤
      16 * kwRange d eta * ((d : ℝ) + 1) := by
  have hpoint (b : Action d m) :
      (actionLoss b (correction (m : ℝ) (weightedMarginal (m := m) theta))) ^ 2 ≤
        (4 * kwRange d eta) * actionLoss b
          (correction (m : ℝ) (weightedMarginal (m := m) theta)) := by
    rw [actionLoss_correction theta hmpos hmtop]
    have hb := phi_range_half_parameter theta hmpos hmtop heta hlo hhi b
    change _ ≤ 4 * kwRange d eta * _
    have hmul := mul_le_mul_of_nonneg_right hb.2 hb.1
    change _ ≤ _ at hmul
    dsimp [kwRange]
    nlinarith
  calc
    _ ≤ finiteExpectation (weightedLaw theta)
        (fun b : Action d m ↦ (4 * kwRange d eta) * actionLoss b
          (correction (m : ℝ) (weightedMarginal (m := m) theta))) := by
      apply Finset.sum_le_sum
      intro b _
      exact mul_le_mul_of_nonneg_left (hpoint b) (weightedLaw_pos theta (by omega) b).le
    _ = (4 * kwRange d eta) * finiteExpectation (weightedLaw theta)
        (fun b : Action d m ↦ actionLoss b (correction (m : ℝ) (weightedMarginal (m := m) theta))) := by
      unfold finiteExpectation
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro b _
      ring
    _ = _ := by rw [correction_mean theta hmpos hmtop]; ring

theorem surrogate_secondMoment_le (theta ell : Fin d → ℝ)
    (hmpos : 1 ≤ m) (hmtop : m ≤ d - 1) {eta : ℝ} (heta : 0 < eta)
    (hlo : ∀ i, (128 * eta * d / 2) * ((m : ℝ) / d) ≤ weightedMarginal (m := m) theta i)
    (hhi : ∀ i, weightedMarginal (m := m) theta i ≤
      1 - (128 * eta * d / 2) * (1 - (m : ℝ) / d))
    (a : Action d m) (hloss : |actionLoss a ell| ≤ 1) :
    finiteExpectation (weightedLaw theta) (fun b ↦ (surrogate theta ell eta a b) ^ 2) ≤
      2 * phi (weightedMarginal (m := m) theta) (fun i ↦ selectedIndicator i a) +
        32 * eta ^ 2 * kwRange d eta * ((d : ℝ) + 1) := by
  have hpoint (b : Action d m) : (surrogate theta ell eta a b) ^ 2 ≤
      2 * (estimateScalar theta a ell b) ^ 2 +
        2 * eta ^ 2 * (actionLoss b (correction (m : ℝ) (weightedMarginal (m := m) theta))) ^ 2 := by
    unfold surrogate
    nlinarith [sq_nonneg (estimateScalar theta a ell b +
      eta * actionLoss b (correction (m : ℝ) (weightedMarginal (m := m) theta)))]
  have hsum := Finset.sum_le_sum (fun b (_ : b ∈ (Finset.univ : Finset (Action d m))) ↦
    mul_le_mul_of_nonneg_left (hpoint b) (weightedLaw_pos theta (by omega) b).le)
  have heq : (∑ b : Action d m, weightedLaw theta b *
      (2 * (estimateScalar theta a ell b) ^ 2 + 2 * eta ^ 2 *
        (actionLoss b (correction (m : ℝ) (weightedMarginal (m := m) theta))) ^ 2)) =
      2 * finiteExpectation (weightedLaw theta) (fun b ↦ (estimateScalar theta a ell b) ^ 2) +
        (2 * eta ^ 2) * finiteExpectation (weightedLaw theta)
          (fun b : Action d m ↦ (actionLoss b (correction (m : ℝ) (weightedMarginal (m := m) theta))) ^ 2) := by
    unfold finiteExpectation
    simp only [Finset.mul_sum, ← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro b _
    ring
  rw [heq] at hsum
  have hest := estimateScalar_pathwise_secondMoment_le_phi theta ell hmpos hmtop a hloss
  have hcorr := correction_secondMoment theta hmpos hmtop heta hlo hhi
  have hscaled := mul_le_mul_of_nonneg_left hcorr (show 0 ≤ 2 * eta ^ 2 by positivity)
  change finiteExpectation (weightedLaw theta) (fun b ↦ (surrogate theta ell eta a b) ^ 2) ≤
    2 * finiteExpectation (weightedLaw theta) (fun b ↦ (estimateScalar theta a ell b) ^ 2) +
      (2 * eta ^ 2) * finiteExpectation (weightedLaw theta)
        (fun b : Action d m ↦ (actionLoss b (correction (m : ℝ) (weightedMarginal (m := m) theta))) ^ 2)
    at hsum
  nlinarith

/-- The exact three-line second-order estimate in the proof of T1. -/
theorem scaled_surrogate_secondMoment_le (theta ell : Fin d → ℝ)
    (hmpos : 1 ≤ m) (hmtop : m ≤ d - 1) {eta : ℝ} (heta : 0 < eta)
    (hsmall : eta ≤ 1 / 64)
    (hlo : ∀ i, (128 * eta * d / 2) * ((m : ℝ) / d) ≤ weightedMarginal (m := m) theta i)
    (hhi : ∀ i, weightedMarginal (m := m) theta i ≤
      1 - (128 * eta * d / 2) * (1 - (m : ℝ) / d))
    (a : Action d m) (hloss : |actionLoss a ell| ≤ 1) :
    2 * eta * finiteExpectation (weightedLaw theta) (fun b ↦ (surrogate theta ell eta a b) ^ 2) ≤
      4 * eta * phi (weightedMarginal (m := m) theta) (fun i ↦ selectedIndicator i a) +
        3 * eta ^ 2 * ((d : ℝ) + 1) := by
  have hmoment := surrogate_secondMoment_le theta ell hmpos hmtop heta hlo hhi a hloss
  have hscaled := mul_le_mul_of_nonneg_left hmoment (show 0 ≤ 2 * eta by positivity)
  have hidentity := eta_mul_kwRange (d := d) heta (by omega)
  have hcoef : 64 * eta ^ 3 * kwRange d eta = 2 * eta ^ 2 * (1 + 32 * eta) := by
    nlinarith [congrArg (fun x : ℝ ↦ 64 * eta ^ 2 * x) hidentity]
  have hlast : 2 * eta ^ 2 * (1 + 32 * eta) ≤ 3 * eta ^ 2 := by
    nlinarith [mul_nonneg (sq_nonneg eta) (show 0 ≤ 1 / 64 - eta by linarith)]
  have hlast' := mul_le_mul_of_nonneg_right hlast
    (show 0 ≤ (d : ℝ) + 1 by positivity)
  nlinarith

end MsetsPaper.Upper
