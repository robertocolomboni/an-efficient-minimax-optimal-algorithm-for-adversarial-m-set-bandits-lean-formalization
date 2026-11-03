import MsetsLower.Feedback.MeasureKL
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.Probability.Moments.SubGaussian

/-!
# Moments and Hoeffding input for the confidence noise

This file records the elementary facts about the genuine source variable
`Z ~ Unif[-1,1]` that are needed by the confidence construction.  In
particular, `g(Z)=1-Z^2` has mean `2/3`, and its lower-tail centered version
`2/3-g(Z)` is Hoeffding-subgaussian with parameter `1/4`.
-/

namespace MsetsLower.Feedback

open Set MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal

noncomputable section

instance instIsProbabilityMeasureSourceUniformMeasure :
    IsProbabilityMeasure sourceUniformMeasure :=
  ⟨sourceUniformMeasure_apply_univ⟩

theorem measurable_shape : Measurable shape := by
  unfold shape
  fun_prop

theorem ae_sourceUniformMeasure_mem_Icc :
    ∀ᵐ z ∂sourceUniformMeasure, z ∈ Icc (-1 : Real) 1 := by
  unfold sourceUniformMeasure
  exact Measure.ae_smul_measure (ae_restrict_mem measurableSet_Icc) _

theorem integrable_shape_sourceUniformMeasure :
    Integrable shape sourceUniformMeasure :=
  Integrable.of_mem_Icc 0 1 measurable_shape.aemeasurable <|
    ae_sourceUniformMeasure_mem_Icc.mono fun _ hz => shape_mem_Icc hz

theorem integral_shape_sourceUniformMeasure :
    ∫ z, shape z ∂sourceUniformMeasure = (2 / 3 : Real) := by
  unfold sourceUniformMeasure
  rw [integral_smul_measure]
  simp only [ENNReal.toReal_ofReal (by norm_num : (0 : Real) ≤ 1 / 2),
    smul_eq_mul]
  change (1 / 2 : Real) * (∫ z in Icc (-1 : Real) 1, (1 - z ^ 2)) = 2 / 3
  rw [integral_Icc_eq_integral_Ioc,
    ← intervalIntegral.integral_of_le (by norm_num : (-1 : Real) ≤ 1)]
  have hconst : IntervalIntegrable (fun _ : Real => (1 : Real)) volume (-1) 1 :=
    continuous_const.intervalIntegrable _ _
  have hpow : IntervalIntegrable (fun z : Real => z ^ 2) volume (-1) 1 :=
    (continuous_id.pow 2).intervalIntegrable _ _
  rw [intervalIntegral.integral_sub hconst hpow,
    intervalIntegral.integral_const, integral_pow]
  norm_num

theorem integral_centeredLowerShape_sourceUniformMeasure :
    ∫ z, ((2 / 3 : Real) - shape z) ∂sourceUniformMeasure = 0 := by
  rw [integral_sub (integrable_const _) integrable_shape_sourceUniformMeasure]
  rw [integral_const, integral_shape_sourceUniformMeasure, probReal_univ]
  ring

theorem centeredLowerShape_mem_Icc (z : Real)
    (hz : z ∈ Icc (-1 : Real) 1) :
    (2 / 3 : Real) - shape z ∈ Icc (-1 / 3 : Real) (2 / 3 : Real) := by
  have hg := shape_mem_Icc hz
  constructor <;> norm_num at hg ⊢ <;> linarith

/-- The exact Hoeffding-lemma input used for the manuscript exponent
`exp (-T/18)`. -/
theorem hasSubgaussianMGF_centeredLowerShape_sourceUniformMeasure :
    HasSubgaussianMGF (fun z => (2 / 3 : Real) - shape z) (1 / 4)
      sourceUniformMeasure := by
  have h := hasSubgaussianMGF_of_mem_Icc_of_integral_eq_zero
    (μ := sourceUniformMeasure) (X := fun z => (2 / 3 : Real) - shape z)
    (a := (-1 / 3 : Real)) (b := (2 / 3 : Real))
    (measurable_const.sub measurable_shape |>.aemeasurable)
    (ae_sourceUniformMeasure_mem_Icc.mono fun z hz =>
      centeredLowerShape_mem_Icc z hz)
    integral_centeredLowerShape_sourceUniformMeasure
  convert h using 1
  all_goals norm_num

end

end MsetsLower.Feedback

#print axioms MsetsLower.Feedback.integral_shape_sourceUniformMeasure
#print axioms MsetsLower.Feedback.hasSubgaussianMGF_centeredLowerShape_sourceUniformMeasure
