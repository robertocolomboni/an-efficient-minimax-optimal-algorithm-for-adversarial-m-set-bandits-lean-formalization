import MsetsLower.Feedback.Pushforward
import Mathlib.InformationTheory.KullbackLeibler.Basic

/-!
# Measure-theoretic KL for the scalar feedback law

This file identifies the density calculation in `Feedback.Density` with
Mathlib's measure-valued `InformationTheory.klDiv`.  It is the bridge needed
to use the paper's one-step bound inside sequential change-of-measure
arguments.
-/

namespace MsetsLower.Feedback

open Set MeasureTheory InformationTheory
open scoped ENNReal

noncomputable section

/-- The likelihood ratio of the two zero-extended feedback densities. -/
def feedbackDensityRatio (u v y : Real) : ℝ≥0∞ :=
  ENNReal.ofReal (feedbackDensity u y / feedbackDensity v y)

theorem measurable_feedbackDensityRatio (u v : Real) :
    Measurable (feedbackDensityRatio u v) := by
  exact ((measurable_feedbackDensity u).div
    (measurable_feedbackDensity v)).ennreal_ofReal

theorem feedbackDensityRatio_ne_top (u v y : Real) :
    feedbackDensityRatio u v y ≠ ∞ := by
  simp [feedbackDensityRatio]

private theorem feedbackDensity_product_ratio
    {u v y : Real} (hu : |u| ≤ 1 / 16) (hv : |v| ≤ 1 / 16) :
    ENNReal.ofReal (feedbackDensity v y) * feedbackDensityRatio u v y =
      ENNReal.ofReal (feedbackDensity u y) := by
  by_cases hy : y ∈ Icc (-1 / 2 : Real) (1 / 2 : Real)
  · have hpu : 0 ≤ feedbackDensity u y := feedbackDensity_nonneg hu
    have hpv : 0 < feedbackDensity v y := by
      rw [feedbackDensity_eq_core hy]
      exact lt_of_lt_of_le (by norm_num)
        (feedbackDensityCore_mem_Icc hv hy).1
    rw [feedbackDensityRatio, ENNReal.ofReal_div_of_pos hpv]
    exact ENNReal.mul_div_cancel
      (ne_of_gt (ENNReal.ofReal_pos.mpr hpv))
      (ENNReal.ofReal_ne_top)
  · rw [feedbackDensity_eq_zero hy, feedbackDensity_eq_zero hy]
    simp [feedbackDensityRatio]

/-- Reweighting the `v` feedback law by its likelihood ratio gives the
`u` feedback law. -/
theorem feedbackDensityMeasure_withDensity_ratio
    {u v : Real} (hu : |u| ≤ 1 / 16) (hv : |v| ≤ 1 / 16) :
    feedbackDensityMeasure u =
      (feedbackDensityMeasure v).withDensity (feedbackDensityRatio u v) := by
  rw [feedbackDensityMeasure, feedbackDensityMeasure]
  calc
    volume.withDensity (fun y => ENNReal.ofReal (feedbackDensity u y)) =
        volume.withDensity
          ((fun y => ENNReal.ofReal (feedbackDensity v y)) *
            feedbackDensityRatio u v) := by
      congr 1
      funext y
      exact (feedbackDensity_product_ratio hu hv).symm
    _ = (volume.withDensity
          (fun y => ENNReal.ofReal (feedbackDensity v y))).withDensity
            (feedbackDensityRatio u v) :=
      withDensity_mul volume
        (measurable_feedbackDensity v).ennreal_ofReal
        (measurable_feedbackDensityRatio u v)

/-- The feedback laws for two admissible parameters are mutually dominated. -/
theorem feedbackDensityMeasure_absolutelyContinuous
    {u v : Real} (hu : |u| ≤ 1 / 16) (hv : |v| ≤ 1 / 16) :
    feedbackDensityMeasure u ≪ feedbackDensityMeasure v := by
  rw [feedbackDensityMeasure_withDensity_ratio hu hv]
  exact withDensity_absolutelyContinuous _ _

theorem sourceUniformMeasure_apply_univ :
    sourceUniformMeasure Set.univ = 1 := by
  rw [sourceUniformMeasure, Measure.smul_apply,
    Measure.restrict_apply MeasurableSet.univ, Set.univ_inter,
    Real.volume_Icc]
  rw [show (1 / 2 : Real) = (2 : Real)⁻¹ by norm_num,
    ENNReal.ofReal_inv_of_pos (by norm_num : (0 : Real) < 2),
    ENNReal.ofReal_ofNat]
  rw [show ENNReal.ofReal (1 - -1 : Real) = (2 : ℝ≥0∞) by norm_num]
  exact ENNReal.inv_mul_cancel
    (by norm_num : (2 : ℝ≥0∞) ≠ 0)
    (by norm_num : (2 : ℝ≥0∞) ≠ ∞)

theorem feedbackPushforwardMeasure_apply_univ (u : Real) :
    feedbackPushforwardMeasure u Set.univ = 1 := by
  rw [feedbackPushforwardMeasure,
    Measure.map_apply (continuous_feedbackMap u).measurable MeasurableSet.univ]
  simpa using sourceUniformMeasure_apply_univ

theorem feedbackDensityMeasure_apply_univ
    {u : Real} (hu : |u| ≤ 1 / 16) :
    feedbackDensityMeasure u Set.univ = 1 := by
  rw [← feedbackPushforwardMeasure_eq_densityMeasure hu]
  exact feedbackPushforwardMeasure_apply_univ u

/-- Radon--Nikodym derivative of two admissible feedback laws. -/
theorem rnDeriv_feedbackDensityMeasure
    {u v : Real} (hu : |u| ≤ 1 / 16) (hv : |v| ≤ 1 / 16) :
    (feedbackDensityMeasure u).rnDeriv (feedbackDensityMeasure v)
      =ᵐ[feedbackDensityMeasure v] feedbackDensityRatio u v := by
  letI : SigmaFinite (feedbackDensityMeasure v) := by
    rw [feedbackDensityMeasure]
    exact SigmaFinite.withDensity_of_ne_top' fun y => by simp
  rw [feedbackDensityMeasure_withDensity_ratio hu hv]
  exact Measure.rnDeriv_withDensity _ (measurable_feedbackDensityRatio u v)

/-- Mathlib's measure-theoretic divergence is exactly the density integral
`feedbackKL` used in the manuscript. -/
theorem toReal_klDiv_feedbackDensityMeasure_eq
    {u v : Real} (hu : |u| ≤ 1 / 16) (hv : |v| ≤ 1 / 16) :
    (klDiv (feedbackDensityMeasure u) (feedbackDensityMeasure v)).toReal =
      feedbackKL u v := by
  letI : IsFiniteMeasure (feedbackDensityMeasure u) :=
    ⟨by rw [feedbackDensityMeasure_apply_univ hu]; norm_num⟩
  letI : IsFiniteMeasure (feedbackDensityMeasure v) :=
    ⟨by rw [feedbackDensityMeasure_apply_univ hv]; norm_num⟩
  have hac : feedbackDensityMeasure u ≪ feedbackDensityMeasure v :=
    feedbackDensityMeasure_absolutelyContinuous hu hv
  have hmass : feedbackDensityMeasure u Set.univ =
      feedbackDensityMeasure v Set.univ := by
    rw [feedbackDensityMeasure_apply_univ hu,
      feedbackDensityMeasure_apply_univ hv]
  rw [InformationTheory.toReal_klDiv_of_measure_eq hac hmass]
  have hrn := rnDeriv_feedbackDensityMeasure hu hv
  have hrn_u :
      (feedbackDensityMeasure u).rnDeriv (feedbackDensityMeasure v)
        =ᵐ[feedbackDensityMeasure u] feedbackDensityRatio u v :=
    hac.ae_eq hrn
  calc
    (∫ y, llr (feedbackDensityMeasure u) (feedbackDensityMeasure v) y
        ∂feedbackDensityMeasure u) =
        ∫ y, Real.log (feedbackDensityRatio u v y).toReal
          ∂feedbackDensityMeasure u := by
      apply integral_congr_ae
      filter_upwards [hrn_u] with y hy
      rw [llr, hy]
    _ = ∫ y, feedbackDensity u y *
          Real.log (feedbackDensityRatio u v y).toReal ∂volume := by
      rw [feedbackDensityMeasure,
        integral_withDensity_eq_integral_toReal_smul
          (measurable_feedbackDensity u).ennreal_ofReal
          (ae_of_all _ fun y => by simp) ]
      apply integral_congr_ae
      filter_upwards with y
      rw [ENNReal.toReal_ofReal (feedbackDensity_nonneg hu)]
      simp only [smul_eq_mul]
    _ = feedbackKL u v := by
      rw [feedbackKL, intervalIntegral.integral_of_le (by norm_num),
        ← integral_Icc_eq_integral_Ioc]
      rw [← integral_indicator measurableSet_Icc]
      apply integral_congr_ae
      filter_upwards with y
      by_cases hy : y ∈ Icc (-1 / 2 : Real) (1 / 2 : Real)
      · rw [indicator_of_mem hy, feedbackDensity_eq_core hy,
          feedbackDensityRatio, feedbackDensity_eq_core hy,
          feedbackDensity_eq_core hy]
        have hpu : 0 ≤ feedbackDensityCore u y :=
          le_trans (by norm_num) (feedbackDensityCore_mem_Icc hu hy).1
        have hpv : 0 < feedbackDensityCore v y :=
          lt_of_lt_of_le (by norm_num)
            (feedbackDensityCore_mem_Icc hv hy).1
        rw [ENNReal.toReal_ofReal (div_nonneg hpu hpv.le)]
      · rw [indicator_of_notMem hy, feedbackDensity_eq_zero hy]
        simp

theorem integrable_feedbackDensity_mul_log_ratio
    {u v : Real} (hu : |u| ≤ 1 / 16) (hv : |v| ≤ 1 / 16) :
    Integrable
      (fun y => feedbackDensity u y *
        Real.log (feedbackDensityRatio u v y).toReal) volume := by
  have hcore : IntegrableOn
      (fun y => feedbackDensityCore u y *
        Real.log (feedbackDensityCore u y / feedbackDensityCore v y))
      (Icc (-1 / 2 : Real) (1 / 2 : Real)) volume :=
    (continuousOn_feedbackKLIntegrand hu hv).integrableOn_Icc
  have hon : IntegrableOn
      (fun y => feedbackDensity u y *
        Real.log (feedbackDensityRatio u v y).toReal)
      (Icc (-1 / 2 : Real) (1 / 2 : Real)) volume := by
    apply hcore.congr_fun
    · intro y hy
      change feedbackDensityCore u y *
          Real.log (feedbackDensityCore u y / feedbackDensityCore v y) =
        feedbackDensity u y *
          Real.log (feedbackDensityRatio u v y).toReal
      rw [feedbackDensity_eq_core hy, feedbackDensityRatio,
        feedbackDensity_eq_core hy, feedbackDensity_eq_core hy]
      have hpu : 0 ≤ feedbackDensityCore u y :=
        le_trans (by norm_num) (feedbackDensityCore_mem_Icc hu hy).1
      have hpv : 0 < feedbackDensityCore v y :=
        lt_of_lt_of_le (by norm_num)
          (feedbackDensityCore_mem_Icc hv hy).1
      rw [ENNReal.toReal_ofReal (div_nonneg hpu hpv.le)]
    · exact measurableSet_Icc
  exact hon.integrable_of_forall_notMem_eq_zero fun y hy => by
    rw [feedbackDensity_eq_zero hy, zero_mul]

theorem integrable_llr_feedbackDensityMeasure
    {u v : Real} (hu : |u| ≤ 1 / 16) (hv : |v| ≤ 1 / 16) :
    Integrable
      (llr (feedbackDensityMeasure u) (feedbackDensityMeasure v))
      (feedbackDensityMeasure u) := by
  have hweighted := integrable_feedbackDensity_mul_log_ratio hu hv
  have hlog : Integrable
      (fun y => Real.log (feedbackDensityRatio u v y).toReal)
      (feedbackDensityMeasure u) := by
    rw [feedbackDensityMeasure,
      integrable_withDensity_iff_integrable_smul'
        (measurable_feedbackDensity u).ennreal_ofReal
        (ae_of_all _ fun y => by simp)]
    apply hweighted.congr
    filter_upwards with y
    rw [ENNReal.toReal_ofReal (feedbackDensity_nonneg hu)]
    simp only [smul_eq_mul]
  have hac : feedbackDensityMeasure u ≪ feedbackDensityMeasure v :=
    feedbackDensityMeasure_absolutelyContinuous hu hv
  have hrn_u :
      (feedbackDensityMeasure u).rnDeriv (feedbackDensityMeasure v)
        =ᵐ[feedbackDensityMeasure u] feedbackDensityRatio u v :=
    hac.ae_eq (rnDeriv_feedbackDensityMeasure hu hv)
  apply hlog.congr
  filter_upwards [hrn_u] with y hy
  rw [llr, hy]

/-- ENNReal-valued exact identification, suitable for the sequential KL
chain rule. -/
theorem klDiv_feedbackDensityMeasure_eq_ofReal
    {u v : Real} (hu : |u| ≤ 1 / 16) (hv : |v| ≤ 1 / 16) :
    klDiv (feedbackDensityMeasure u) (feedbackDensityMeasure v) =
      ENNReal.ofReal (feedbackKL u v) := by
  letI : IsFiniteMeasure (feedbackDensityMeasure u) :=
    ⟨by rw [feedbackDensityMeasure_apply_univ hu]; norm_num⟩
  letI : IsFiniteMeasure (feedbackDensityMeasure v) :=
    ⟨by rw [feedbackDensityMeasure_apply_univ hv]; norm_num⟩
  have hac := feedbackDensityMeasure_absolutelyContinuous hu hv
  have hne : klDiv (feedbackDensityMeasure u)
      (feedbackDensityMeasure v) ≠ ∞ :=
    InformationTheory.klDiv_ne_top hac
      (integrable_llr_feedbackDensityMeasure hu hv)
  calc
    klDiv (feedbackDensityMeasure u) (feedbackDensityMeasure v) =
        ENNReal.ofReal
          (klDiv (feedbackDensityMeasure u)
            (feedbackDensityMeasure v)).toReal :=
      (ENNReal.ofReal_toReal hne).symm
    _ = ENNReal.ofReal (feedbackKL u v) := by
      rw [toReal_klDiv_feedbackDensityMeasure_eq hu hv]

/-- The manuscript's one-step scalar-feedback bound in Mathlib's native
measure-theoretic KL. -/
theorem klDiv_feedbackDensityMeasure_le
    {u v : Real} (hu : |u| ≤ 1 / 16) (hv : |v| ≤ 1 / 16) :
    klDiv (feedbackDensityMeasure u) (feedbackDensityMeasure v) ≤
      ENNReal.ofReal (128 * (u - v) ^ 2) := by
  rw [klDiv_feedbackDensityMeasure_eq_ofReal hu hv]
  exact ENNReal.ofReal_le_ofReal (feedbackKL_le hu hv)

end

end MsetsLower.Feedback

#print axioms MsetsLower.Feedback.feedbackDensityMeasure_absolutelyContinuous
#print axioms MsetsLower.Feedback.feedbackDensityMeasure_apply_univ
#print axioms MsetsLower.Feedback.rnDeriv_feedbackDensityMeasure
#print axioms MsetsLower.Feedback.toReal_klDiv_feedbackDensityMeasure_eq
#print axioms MsetsLower.Feedback.integrable_llr_feedbackDensityMeasure
#print axioms MsetsLower.Feedback.klDiv_feedbackDensityMeasure_eq_ofReal
#print axioms MsetsLower.Feedback.klDiv_feedbackDensityMeasure_le
