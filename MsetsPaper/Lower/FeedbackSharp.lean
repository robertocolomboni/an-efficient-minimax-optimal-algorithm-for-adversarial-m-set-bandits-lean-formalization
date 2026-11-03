import MsetsPaper.Lower.FeedbackDiscriminant

/-!
# Density calculation for the lower-bound construction

This module proves the intermediate bounds in `lem:lower-feedback-density`
of `paper/main.tex`: the explicit discriminant, the derivative bound
`64/9 < 8`, the parameter Lipschitz constant `8`, and chi-square constant
`80`. The density is the same normalized push-forward density already
constructed in `MsetsLower.Feedback`; no new probability law is postulated.
-/

namespace MsetsPaper.Lower.FeedbackSharp

open MsetsLower.Feedback Set MeasureTheory
open scoped Interval

noncomputable section

/-- The discriminant calculation improves the old bound `7/3` to `2`. -/
theorem abs_feedbackJacobianParamDeriv_le_two
    {u y : Real} (hu : |u| ≤ 1 / 16)
    (hy : y ∈ Icc (-1 / 2 : Real) (1 / 2 : Real)) :
    |feedbackJacobianParamDeriv u y| ≤ 2 := by
  have hA := feedbackJacobian_mem_Icc hu hy
  have hApos : 0 < feedbackJacobian u y := by linarith [hA.1]
  have hprod := jacobian_mul_paramDeriv hu hy
  have hprod_sq := congrArg (fun x : Real => x ^ 2) hprod
  simp only [mul_pow] at hprod_sq
  have hD := manuscriptDiscriminant_eq_four_jacobian_sq hu hy
  have hnum := discriminantParamDeriv_sq_le u hy
  have hsq : feedbackJacobianParamDeriv u y ^ 2 ≤ (2 : Real) ^ 2 := by
    by_contra hnot
    have hgt := lt_of_not_ge hnot
    have hpos := mul_pos (sq_pos_of_pos hApos) (sub_pos.mpr hgt)
    nlinarith
  exact (abs_le).2 ⟨by nlinarith, by nlinarith⟩

/-- The new manuscript's pointwise derivative estimate `|∂_u p| ≤ 4/D`. -/
theorem abs_feedbackDensityParamDeriv_le_four_div_discriminant
    {u y : Real} (hu : |u| ≤ 1 / 16)
    (hy : y ∈ Icc (-1 / 2 : Real) (1 / 2 : Real)) :
    |feedbackDensityParamDeriv u y| ≤ 4 / manuscriptDiscriminant u y := by
  have hDpos := manuscriptDiscriminant_pos hu hy
  have hspos : 0 < Real.sqrt (manuscriptDiscriminant u y) := Real.sqrt_pos.mpr hDpos
  have hsq := Real.sq_sqrt hDpos.le
  have hnum : |(-16 * y + 32 * u)| ≤ 8 * Real.sqrt (manuscriptDiscriminant u y) := by
    nlinarith [discriminantParamDeriv_sq_le u hy, sq_abs (-16 * y + 32 * u),
      abs_nonneg (-16 * y + 32 * u)]
  rw [feedbackDensityParamDeriv_eq_discriminant_formula hu hy, abs_div, abs_neg,
    abs_of_pos (show 0 < 2 * manuscriptDiscriminant u y *
      Real.sqrt (manuscriptDiscriminant u y) by positivity)]
  calc
    _ ≤ (8 * Real.sqrt (manuscriptDiscriminant u y)) /
        (2 * manuscriptDiscriminant u y * Real.sqrt (manuscriptDiscriminant u y)) :=
      div_le_div_of_nonneg_right hnum (by positivity)
    _ = _ := by field_simp; ring


theorem abs_feedbackDensityParamDeriv_le_sixtyFour_ninths
    {u y : Real} (hu : |u| ≤ 1 / 16)
    (hy : y ∈ Icc (-1 / 2 : Real) (1 / 2 : Real)) :
    |feedbackDensityParamDeriv u y| ≤ 64 / 9 := by
  have hD := manuscriptDiscriminant_mem_Icc hu hy
  have hDpos := manuscriptDiscriminant_pos hu hy
  calc
    |feedbackDensityParamDeriv u y| ≤ 4 / manuscriptDiscriminant u y :=
      abs_feedbackDensityParamDeriv_le_four_div_discriminant hu hy
    _ ≤ 64 / 9 := by
      rw [div_le_iff₀ hDpos]
      linarith [hD.1]

theorem abs_feedbackDensityParamDeriv_lt_eight
    {u y : Real} (hu : |u| ≤ 1 / 16)
    (hy : y ∈ Icc (-1 / 2 : Real) (1 / 2 : Real)) :
    |feedbackDensityParamDeriv u y| < 8 :=
  lt_of_le_of_lt (abs_feedbackDensityParamDeriv_le_sixtyFour_ninths hu hy)
    (by norm_num)

/-- The parameter derivative of the actual smooth density, not an assumed value. -/
theorem abs_deriv_feedbackDensityCore_param_le
    {u y : Real} (hu : |u| ≤ 1 / 16)
    (hy : y ∈ Icc (-1 / 2 : Real) (1 / 2 : Real)) :
    |deriv (fun v => feedbackDensityCore v y) u| ≤ 64 / 9 := by
  rw [(hasDerivAt_feedbackDensityCore_discriminant_formula hu hy).deriv,
    ← feedbackDensityParamDeriv_eq_discriminant_formula hu hy]
  exact abs_feedbackDensityParamDeriv_le_sixtyFour_ninths hu hy

/-- Mean-value estimate with the new manuscript's constant `8`. -/
theorem abs_feedbackDensityCore_sub_le_eight
    {u v y : Real} (hu : |u| ≤ 1 / 16) (hv : |v| ≤ 1 / 16)
    (hy : y ∈ Icc (-1 / 2 : Real) (1 / 2 : Real)) :
    |feedbackDensityCore u y - feedbackDensityCore v y| ≤ 8 * |u - v| := by
  have huD : u ∈ Icc (-1 / 16 : Real) (1 / 16 : Real) := by
    simpa only [mem_Icc, abs_le, neg_div] using hu
  have hvD : v ∈ Icc (-1 / 16 : Real) (1 / 16 : Real) := by
    simpa only [mem_Icc, abs_le, neg_div] using hv
  have hdiff : ∀ w ∈ Icc (-1 / 16 : Real) (1 / 16 : Real),
      DifferentiableAt Real (fun q => feedbackDensityCore q y) w := by
    intro w hw
    have haw : |w| ≤ (1 / 16 : Real) := by
      simpa only [mem_Icc, abs_le, neg_div] using hw
    exact (hasDerivAt_feedbackDensityCore_discriminant_formula haw hy).differentiableAt
  have hbound : ∀ w ∈ Icc (-1 / 16 : Real) (1 / 16 : Real),
      ‖deriv (fun q => feedbackDensityCore q y) w‖ ≤ (8 : Real) := by
    intro w hw
    have haw : |w| ≤ (1 / 16 : Real) := by
      simpa only [mem_Icc, abs_le, neg_div] using hw
    rw [Real.norm_eq_abs]
    exact (abs_deriv_feedbackDensityCore_param_le haw hy).trans (by norm_num)
  have hmv := Convex.norm_image_sub_le_of_norm_deriv_le
    hdiff hbound (convex_Icc (-1 / 16 : Real) (1 / 16 : Real)) huD hvD
  simpa [Real.norm_eq_abs, abs_sub_comm] using hmv

theorem abs_feedbackDensity_sub_le_eight
    {u v : Real} (hu : |u| ≤ 1 / 16) (hv : |v| ≤ 1 / 16) (y : Real) :
    |feedbackDensity u y - feedbackDensity v y| ≤ 8 * |u - v| := by
  by_cases hy : y ∈ Icc (-1 / 2 : Real) (1 / 2 : Real)
  · rw [feedbackDensity_eq_core hy, feedbackDensity_eq_core hy]
    exact abs_feedbackDensityCore_sub_le_eight hu hv hy
  · rw [feedbackDensity_eq_zero hy, feedbackDensity_eq_zero hy]
    simp only [sub_self, abs_zero]
    positivity

theorem feedbackChiSquaredIntegrand_le_eighty
    {u v y : Real} (hu : |u| ≤ 1 / 16) (hv : |v| ≤ 1 / 16)
    (hy : y ∈ Icc (-1 / 2 : Real) (1 / 2 : Real)) :
    (feedbackDensityCore u y - feedbackDensityCore v y) ^ 2 /
        feedbackDensityCore v y ≤ 80 * (u - v) ^ 2 := by
  have hpv := feedbackDensityCore_mem_Icc hv hy
  have hpvpos : 0 < feedbackDensityCore v y := by linarith [hpv.1]
  have habs := abs_feedbackDensityCore_sub_le_eight hu hv hy
  have hsq : (feedbackDensityCore u y - feedbackDensityCore v y) ^ 2 ≤
      64 * (u - v) ^ 2 := by
    have hsquare : (feedbackDensityCore u y - feedbackDensityCore v y) ^ 2 ≤
        (8 * |u - v|) ^ 2 := by
      rw [sq_le_sq]
      simpa using habs
    nlinarith [sq_abs (u - v)]
  rw [div_le_iff₀ hpvpos]
  calc
    (feedbackDensityCore u y - feedbackDensityCore v y) ^ 2 ≤
        64 * (u - v) ^ 2 := hsq
    _ ≤ (80 * (u - v) ^ 2) * feedbackDensityCore v y := by
      have hcoef : (64 : Real) ≤ 80 * feedbackDensityCore v y := by
        linarith [hpv.1]
      nlinarith [mul_le_mul_of_nonneg_right hcoef (sq_nonneg (u - v))]

/-- The new manuscript's sharpened chi-square integral bound. -/
theorem feedbackChiSquared_le_eighty
    {u v : Real} (hu : |u| ≤ 1 / 16) (hv : |v| ≤ 1 / 16) :
    feedbackChiSquared u v ≤ 80 * (u - v) ^ 2 := by
  unfold feedbackChiSquared
  calc
    (∫ y in (-1 / 2 : Real)..(1 / 2 : Real),
        (feedbackDensityCore u y - feedbackDensityCore v y) ^ 2 /
          feedbackDensityCore v y) ≤
        ∫ _y in (-1 / 2 : Real)..(1 / 2 : Real), 80 * (u - v) ^ 2 := by
      apply intervalIntegral.integral_mono_on (by norm_num)
        (intervalIntegrable_feedbackChiSquaredIntegrand hu hv)
        ((continuous_const : Continuous
          (fun _ : Real => 80 * (u - v) ^ 2)).intervalIntegrable _ _)
      intro y hy
      exact feedbackChiSquaredIntegrand_le_eighty hu hv hy
    _ = 80 * (u - v) ^ 2 := by norm_num

theorem feedbackKL_le_eighty
    {u v : Real} (hu : |u| ≤ 1 / 16) (hv : |v| ≤ 1 / 16) :
    feedbackKL u v ≤ 80 * (u - v) ^ 2 :=
  (feedbackKL_le_chiSquared hu hv).trans (feedbackChiSquared_le_eighty hu hv)

theorem klDiv_feedbackDensityMeasure_le_eighty
    {u v : Real} (hu : |u| ≤ 1 / 16) (hv : |v| ≤ 1 / 16) :
    InformationTheory.klDiv (feedbackDensityMeasure u) (feedbackDensityMeasure v) ≤
      ENNReal.ofReal (80 * (u - v) ^ 2) := by
  rw [klDiv_feedbackDensityMeasure_eq_ofReal hu hv]
  exact ENNReal.ofReal_le_ofReal (feedbackKL_le_eighty hu hv)

/-- The appendix deliberately uses the looser coefficient 128 after invoking
L12. This bridge makes that proof dependency explicit: it uses the definitive
coefficient-80 density calculation rather than the older independent bound. -/
theorem klDiv_feedbackDensityMeasure_le_one_twenty_eight
    {u v : Real} (hu : |u| ≤ 1 / 16) (hv : |v| ≤ 1 / 16) :
    InformationTheory.klDiv (feedbackDensityMeasure u) (feedbackDensityMeasure v) ≤
      ENNReal.ofReal (128 * (u - v) ^ 2) := by
  apply (klDiv_feedbackDensityMeasure_le_eighty hu hv).trans
  exact ENNReal.ofReal_le_ofReal
    (mul_le_mul_of_nonneg_right (by norm_num : (80 : Real) ≤ 128) (sq_nonneg _))

end

end MsetsPaper.Lower.FeedbackSharp
