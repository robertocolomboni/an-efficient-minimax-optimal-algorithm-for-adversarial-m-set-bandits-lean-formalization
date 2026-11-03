import MsetsLower.Feedback.MeasureKL

/-! # Algebraic discriminant identities and the literal density derivative

This module is upstream of the derivative bound and KL80. It contains the
printed density and derivative formulas but assumes no sharp derivative bound.
-/

namespace MsetsPaper.Lower.FeedbackSharp
open MsetsLower.Feedback Set MeasureTheory
noncomputable section

/-- The discriminant `D(u,y)` used in the new manuscript. -/
def manuscriptDiscriminant (u y : Real) : Real :=
  1 - 16 * u * y + 16 * u ^ 2

theorem manuscriptDiscriminant_eq_four_discriminant (u y : Real) :
    manuscriptDiscriminant u y = 4 * feedbackDiscriminant u y := by
  unfold manuscriptDiscriminant feedbackDiscriminant
  ring

/-- The discriminant is the square of twice the positive Jacobian. -/
theorem manuscriptDiscriminant_eq_four_jacobian_sq
    {u y : Real} (hu : |u| ≤ 1 / 16)
    (hy : y ∈ Icc (-1 / 2 : Real) (1 / 2 : Real)) :
    manuscriptDiscriminant u y = 4 * feedbackJacobian u y ^ 2 := by
  have hmap := feedbackMap_feedbackInverse hu hy
  unfold feedbackMap shape at hmap
  unfold manuscriptDiscriminant feedbackJacobian feedbackSlope
  linear_combination 16 * u * hmap

theorem manuscriptDiscriminant_mem_Icc
    {u y : Real} (hu : |u| ≤ 1 / 16)
    (hy : y ∈ Icc (-1 / 2 : Real) (1 / 2 : Real)) :
    manuscriptDiscriminant u y ∈ Icc (9 / 16 : Real) (25 / 16 : Real) := by
  have hA := feedbackJacobian_mem_Icc hu hy
  have hA0 : 0 ≤ feedbackJacobian u y := le_trans (by norm_num) hA.1
  have hlo := (sq_le_sq₀ (by norm_num : (0 : Real) ≤ 3 / 8) hA0).2 hA.1
  have hhi := (sq_le_sq₀ hA0 (by norm_num : (0 : Real) ≤ 5 / 8)).2 hA.2
  rw [manuscriptDiscriminant_eq_four_jacobian_sq hu hy]
  constructor <;> nlinarith

theorem manuscriptDiscriminant_pos
    {u y : Real} (hu : |u| ≤ 1 / 16)
    (hy : y ∈ Icc (-1 / 2 : Real) (1 / 2 : Real)) :
    0 < manuscriptDiscriminant u y :=
  lt_of_lt_of_le (by norm_num) (manuscriptDiscriminant_mem_Icc hu hy).1

/-- The formula `p_u(y)=D(u,y)^(-1/2)` on the common support. -/
theorem feedbackDensityCore_eq_inv_sqrt
    {u y : Real} (hu : |u| ≤ 1 / 16)
    (hy : y ∈ Icc (-1 / 2 : Real) (1 / 2 : Real)) :
    feedbackDensityCore u y = 1 / Real.sqrt (manuscriptDiscriminant u y) := by
  have hA := feedbackJacobian_mem_Icc hu hy
  have htwo : 0 < 2 * feedbackJacobian u y := by linarith [hA.1]
  have hD : manuscriptDiscriminant u y = (2 * feedbackJacobian u y) ^ 2 := by
    rw [manuscriptDiscriminant_eq_four_jacobian_sq hu hy]
    ring
  rw [hD, Real.sqrt_sq_eq_abs, abs_of_pos htwo]
  rfl

theorem feedbackDensity_eq_inv_sqrt
    {u y : Real} (hu : |u| ≤ 1 / 16)
    (hy : y ∈ Icc (-1 / 2 : Real) (1 / 2 : Real)) :
    feedbackDensity u y = 1 / Real.sqrt (manuscriptDiscriminant u y) := by
  rw [feedbackDensity_eq_core hy, feedbackDensityCore_eq_inv_sqrt hu hy]

theorem hasDerivAt_manuscriptDiscriminant (u y : Real) :
    HasDerivAt (fun v => manuscriptDiscriminant v y) (-16 * y + 32 * u) u := by
  have h := ((hasDerivAt_const u (1 : Real)).sub
    (((hasDerivAt_id u).const_mul 16).mul_const y)).add
      (((hasDerivAt_id u).pow 2).const_mul 16)
  convert! h using 1
  norm_num
  ring

/-- The exact algebraic identity for the square of the discriminant derivative. -/
theorem discriminantParamDeriv_sq (u y : Real) :
    (-16 * y + 32 * u) ^ 2 =
      64 * (manuscriptDiscriminant u y - 1) + 256 * y ^ 2 := by
  unfold manuscriptDiscriminant
  ring

theorem discriminantParamDeriv_sq_le
    (u : Real) {y : Real}
    (hy : y ∈ Icc (-1 / 2 : Real) (1 / 2 : Real)) :
    (-16 * y + 32 * u) ^ 2 ≤ 64 * manuscriptDiscriminant u y := by
  have hy2 : y ^ 2 ≤ (1 / 4 : Real) := by
    nlinarith [mul_nonneg (sub_nonneg.mpr hy.1) (sub_nonneg.mpr hy.2)]
  rw [discriminantParamDeriv_sq]
  nlinarith

/-- Differentiating the Jacobian identity without changing the existing density. -/
theorem jacobian_mul_paramDeriv
    {u y : Real} (hu : |u| ≤ 1 / 16)
    (hy : y ∈ Icc (-1 / 2 : Real) (1 / 2 : Real)) :
    feedbackJacobian u y * feedbackJacobianParamDeriv u y = 4 * u - 2 * y := by
  have hA := feedbackJacobian_mem_Icc hu hy
  have hAne : feedbackJacobian u y ≠ 0 := ne_of_gt (by linarith [hA.1])
  have hmap := feedbackMap_feedbackInverse hu hy
  unfold feedbackMap shape at hmap
  calc
    feedbackJacobian u y * feedbackJacobianParamDeriv u y =
        -2 * feedbackInverse u y * feedbackJacobian u y +
          2 * u * shape (feedbackInverse u y) := by
      unfold feedbackJacobianParamDeriv
      change feedbackJacobian u y *
        (-2 * feedbackInverse u y -
          2 * u * (-shape (feedbackInverse u y) / feedbackJacobian u y)) = _
      field_simp
      ring
    _ = 4 * u - 2 * y := by
      unfold feedbackJacobian feedbackSlope shape
      linear_combination -2 * hmap

theorem sqrt_manuscriptDiscriminant
    {u y : ℝ} (hu : |u| ≤ 1 / 16)
    (hy : y ∈ Icc (-1 / 2 : ℝ) (1 / 2 : ℝ)) :
    Real.sqrt (manuscriptDiscriminant u y) = 2 * feedbackJacobian u y := by
  have hA := feedbackJacobian_mem_Icc hu hy
  have hD : manuscriptDiscriminant u y = (2 * feedbackJacobian u y) ^ 2 := by
    rw [manuscriptDiscriminant_eq_four_jacobian_sq hu hy]
    ring
  rw [hD, Real.sqrt_sq_eq_abs, abs_of_pos (by linarith [hA.1])]

theorem feedbackDensityParamDeriv_eq_discriminant_formula
    {u y : ℝ} (hu : |u| ≤ 1 / 16)
    (hy : y ∈ Icc (-1 / 2 : ℝ) (1 / 2 : ℝ)) :
    feedbackDensityParamDeriv u y = -(-16 * y + 32 * u) /
      (2 * manuscriptDiscriminant u y * Real.sqrt (manuscriptDiscriminant u y)) := by
  have hA := feedbackJacobian_mem_Icc hu hy
  have hAne : feedbackJacobian u y ≠ 0 := by linarith [hA.1]
  have hAprime : feedbackJacobianParamDeriv u y =
      (4 * u - 2 * y) / feedbackJacobian u y := by
    apply (eq_div_iff hAne).mpr
    nlinarith [jacobian_mul_paramDeriv hu hy]
  rw [feedbackDensityParamDeriv, hAprime, sqrt_manuscriptDiscriminant hu hy,
    manuscriptDiscriminant_eq_four_jacobian_sq hu hy]
  field_simp
  <;> ring

theorem hasDerivAt_feedbackDensityCore_discriminant_formula
    {u y : ℝ} (hu : |u| ≤ 1 / 16)
    (hy : y ∈ Icc (-1 / 2 : ℝ) (1 / 2 : ℝ)) :
    HasDerivAt (fun v ↦ feedbackDensityCore v y)
      (-(-16 * y + 32 * u) /
        (2 * manuscriptDiscriminant u y * Real.sqrt (manuscriptDiscriminant u y))) u := by
  rw [← feedbackDensityParamDeriv_eq_discriminant_formula hu hy]
  exact hasDerivAt_feedbackDensityCore_param hu hy


end
end MsetsPaper.Lower.FeedbackSharp
