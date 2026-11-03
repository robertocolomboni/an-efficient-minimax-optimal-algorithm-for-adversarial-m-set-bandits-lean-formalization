import MsetsLower.Feedback.Density
import Mathlib.MeasureTheory.Function.JacobianOneDim

/-!
# The scalar feedback density as a push-forward law

This file upgrades the continuous-test change-of-variables identity in
`Feedback.Density` to literal equality of measures.
-/

namespace MsetsLower.Feedback

open Set MeasureTheory

noncomputable section

/-- Lebesgue-uniform probability measure on `[-1,1]`. -/
def sourceUniformMeasure : Measure Real :=
  (ENNReal.ofReal (1 / 2 : Real)) •
    volume.restrict (Icc (-1 : Real) 1)

/-- The law obtained by pushing the source uniform measure through `F_u`. -/
def feedbackPushforwardMeasure (u : Real) : Measure Real :=
  Measure.map (feedbackMap u) sourceUniformMeasure

/-- The measure represented by the zero-extended density `p_u`. -/
def feedbackDensityMeasure (u : Real) : Measure Real :=
  volume.withDensity (fun y => ENNReal.ofReal (feedbackDensity u y))

private theorem ennreal_jacobian_density_cancel
    {u z : Real} (hu : |u| ≤ 1 / 16)
    (hz : z ∈ Icc (-1 : Real) 1) :
    ENNReal.ofReal |feedbackSlope u z| *
        ENNReal.ofReal (feedbackDensity u (feedbackMap u z)) =
      ENNReal.ofReal (1 / 2 : Real) := by
  have hslope : 0 < feedbackSlope u z := feedbackSlope_pos hu hz
  have hy : feedbackMap u z ∈ Icc (-1 / 2 : Real) (1 / 2 : Real) :=
    (feedbackMap_bijOn hu).mapsTo hz
  rw [abs_of_pos hslope, feedbackDensity_eq_core hy, ← ENNReal.ofReal_mul]
  rw [mul_comm, feedbackDensityCore_map_mul_slope hu hz]
  exact hslope.le

/-- Literal push-forward density identity: if `Z` is uniform on `[-1,1]`,
then `F_u(Z)` has density `feedbackDensity u`. -/
theorem feedbackPushforwardMeasure_eq_densityMeasure
    {u : Real} (hu : |u| ≤ 1 / 16) :
    feedbackPushforwardMeasure u = feedbackDensityMeasure u := by
  apply Measure.ext_of_lintegral
  intro f hf
  have hmap : Measurable (feedbackMap u) := (continuous_feedbackMap u).measurable
  have hden : Measurable (fun y => ENNReal.ofReal (feedbackDensity u y)) :=
    (measurable_feedbackDensity u).ennreal_ofReal
  have hchange := lintegral_image_eq_lintegral_abs_deriv_mul
    (s := Icc (-1 : Real) 1) (f := feedbackMap u) (f' := feedbackSlope u)
    measurableSet_Icc
    (fun z hz => (hasDerivAt_feedbackMap u z).hasDerivWithinAt)
    (feedbackMap_strictMonoOn hu).injOn
    (fun y => ENNReal.ofReal (feedbackDensity u y) * f y)
  rw [feedbackMap_image_Icc hu] at hchange
  unfold feedbackPushforwardMeasure feedbackDensityMeasure sourceUniformMeasure
  rw [lintegral_map hf hmap, lintegral_smul_measure,
    lintegral_withDensity_eq_lintegral_mul volume hden hf]
  have hsupp :
      (∫⁻ y, ((fun q => ENNReal.ofReal (feedbackDensity u q)) * f) y) =
        ∫⁻ y in Icc (-1 / 2 : Real) (1 / 2 : Real),
          ENNReal.ofReal (feedbackDensity u y) * f y := by
    rw [← lintegral_indicator measurableSet_Icc]
    apply lintegral_congr
    intro y
    by_cases hy : y ∈ Icc (-1 / 2 : Real) (1 / 2 : Real)
    · simp only [Pi.mul_apply, indicator_of_mem hy]
    · simp only [Pi.mul_apply, feedbackDensity_eq_zero hy,
        ENNReal.ofReal_zero, zero_mul, indicator_of_notMem hy]
  calc
    ENNReal.ofReal (1 / 2 : Real) •
        (∫⁻ a in Icc (-1 : Real) 1, f (feedbackMap u a)) =
      ∫⁻ a in Icc (-1 : Real) 1,
        ENNReal.ofReal (1 / 2 : Real) * f (feedbackMap u a) := by
      rw [lintegral_const_mul]
      · rfl
      · exact hf.comp hmap
    _ = ∫⁻ a in Icc (-1 : Real) 1,
        ENNReal.ofReal |feedbackSlope u a| *
          (ENNReal.ofReal (feedbackDensity u (feedbackMap u a)) *
            f (feedbackMap u a)) := by
      apply setLIntegral_congr_fun measurableSet_Icc
      intro z hz
      have hcancel := ennreal_jacobian_density_cancel hu hz
      change ENNReal.ofReal (1 / 2 : Real) * f (feedbackMap u z) =
        ENNReal.ofReal |feedbackSlope u z| *
          (ENNReal.ofReal (feedbackDensity u (feedbackMap u z)) *
            f (feedbackMap u z))
      rw [← mul_assoc, hcancel]
    _ = ∫⁻ y in Icc (-1 / 2 : Real) (1 / 2 : Real),
        ENNReal.ofReal (feedbackDensity u y) * f y := hchange.symm
    _ = ∫⁻ y, ((fun q => ENNReal.ofReal (feedbackDensity u q)) * f) y :=
      hsupp.symm

end

end MsetsLower.Feedback

#print axioms MsetsLower.Feedback.feedbackPushforwardMeasure_eq_densityMeasure
