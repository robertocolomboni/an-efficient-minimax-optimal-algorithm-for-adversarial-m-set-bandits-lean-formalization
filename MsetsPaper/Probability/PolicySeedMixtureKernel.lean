import MsetsPaper.Probability.PolicySeedMixture
import MsetsPaper.Probability.KernelKLMeasurable

namespace MsetsPaper.Probability.PolicySeed
open MsetsLower MeasureTheory ProbabilityTheory Set
open scoped ENNReal ProbabilityTheory
noncomputable section
variable {d m T : ℕ} {Ξ : Type*} [MeasurableSpace Ξ]

instance history_countablyGenerated (d m : ℕ) :
    (t : ℕ) → MeasurableSpace.CountablyGenerated (History d m t)
  | 0 => inferInstanceAs (MeasurableSpace.CountablyGenerated Unit)
  | t + 1 => by
    letI := history_countablyGenerated d m t
    change MeasurableSpace.CountablyGenerated (History d m t × (MSetAction d m × ℝ))
    infer_instance

def fixedPolicyMixtureKernel (P : Policy d m) (hmd : m ≤ d)
    (L : ParametricLossProcess Ξ d m) (μ : Measure Ξ) [SFinite μ] :
    Kernel (Seeds T) (History d m T) where
  toFun r := parametricRunKernel (fixedPolicy P hmd r) L T ∘ₘ μ
  measurable' := by
    apply Measure.measurable_of_measurable_coe
    intro E hE
    have heq (r : Seeds T) :
        (parametricRunKernel (fixedPolicy P hmd r) L T ∘ₘ μ) E =
          μ {x | seedRun P hmd (L.at x) T r ∈ E} := by
      have hm : Measurable (fun x => seedRun P hmd (L.at x) T r) :=
        (measurable_seedRun_parametric P hmd L.at L.measurable_itemLoss).comp
          measurable_prodMk_right
      rw [fixedPolicy_parametric_mixture_eq_map, Measure.map_apply hm hE]
      rfl
    simp_rw [heq]
    exact measurable_measure_prodMk_right
      ((measurable_seedRun_parametric P hmd L.at L.measurable_itemLoss) hE)

@[simp] theorem fixedPolicyMixtureKernel_apply (P : Policy d m) (hmd : m ≤ d)
    (L : ParametricLossProcess Ξ d m) (μ : Measure Ξ) [SFinite μ] (r : Seeds T) :
    fixedPolicyMixtureKernel (T := T) P hmd L μ r =
      parametricRunKernel (fixedPolicy P hmd r) L T ∘ₘ μ := rfl

instance fixedPolicyMixtureKernel_isMarkov (P : Policy d m) (hmd : m ≤ d)
    (L : ParametricLossProcess Ξ d m) (μ : Measure Ξ) [IsProbabilityMeasure μ] :
    IsMarkovKernel (fixedPolicyMixtureKernel (T := T) P hmd L μ) := by
  constructor
  intro r
  change IsProbabilityMeasure (parametricRunKernel (fixedPolicy P hmd r) L T ∘ₘ μ)
  letI := parametricRunKernel_isMarkov (fixedPolicy P hmd r) L T
  infer_instance

theorem measurable_fixedPolicy_mixture_klDiv
    (P : Policy d m) (hmd : m ≤ d) (L₀ L₁ : ParametricLossProcess Ξ d m)
    (μ : Measure Ξ) [IsProbabilityMeasure μ]
    (hac : ∀ r : Seeds T, (parametricRunKernel (fixedPolicy P hmd r) L₀ T ∘ₘ μ) ≪
      (parametricRunKernel (fixedPolicy P hmd r) L₁ T ∘ₘ μ)) :
    Measurable (fun r : Seeds T =>
      InformationTheory.klDiv (parametricRunKernel (fixedPolicy P hmd r) L₀ T ∘ₘ μ)
        (parametricRunKernel (fixedPolicy P hmd r) L₁ T ∘ₘ μ)) :=
  measurable_klDiv_kernel_of_ac (fixedPolicyMixtureKernel P hmd L₀ μ)
    (fixedPolicyMixtureKernel P hmd L₁ μ) hac

end
end MsetsPaper.Probability.PolicySeed
