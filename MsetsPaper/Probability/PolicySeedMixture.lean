import MsetsPaper.Probability.PolicySeedParametric
import MsetsLower.Core.ParametricRun

/-! # Exact averaging of fixed private seeds in a random non-anticipating environment -/

namespace MsetsPaper.Probability.PolicySeed

open MsetsLower MeasureTheory ProbabilityTheory Set
open scoped ENNReal ProbabilityTheory

noncomputable section
variable {d m T : ℕ} {Ξ : Type*} [MeasurableSpace Ξ]

theorem fixedPolicy_parametric_mixture_eq_map
    (P : Policy d m) (hmd : m ≤ d) (r : Seeds T)
    (L : ParametricLossProcess Ξ d m) (μ : Measure Ξ) :
    parametricRunKernel (fixedPolicy P hmd r) L T ∘ₘ μ =
      μ.map (fun x => seedRun P hmd (L.at x) T r) := by
  have hm : Measurable (fun x => seedRun P hmd (L.at x) T r) :=
    (measurable_seedRun_parametric P hmd L.at L.measurable_itemLoss).comp
      measurable_prodMk_right
  have hk : parametricRunKernel (fixedPolicy P hmd r) L T =
      Kernel.deterministic (fun x => seedRun P hmd (L.at x) T r) hm := by
    ext x : 1
    rw [parametricRunKernel_apply, fixedPolicy_runLaw]
    rfl
  rw [hk, Measure.deterministic_comp_eq_map]

theorem fixedPolicy_parametric_event_eq_section
    (P : Policy d m) (hmd : m ≤ d) (r : Seeds T)
    (L : ParametricLossProcess Ξ d m) (μ : Measure Ξ)
    (E : Set (History d m T)) (hE : MeasurableSet E) :
    (parametricRunKernel (fixedPolicy P hmd r) L T ∘ₘ μ).real E =
      μ.real {x | seedRun P hmd (L.at x) T r ∈ E} := by
  have hm : Measurable (fun x => seedRun P hmd (L.at x) T r) :=
    (measurable_seedRun_parametric P hmd L.at L.measurable_itemLoss).comp
      measurable_prodMk_right
  rw [fixedPolicy_parametric_mixture_eq_map, measureReal_def, Measure.map_apply hm hE]
  rfl

theorem measurable_fixedPolicy_parametric_event
    (P : Policy d m) (hmd : m ≤ d)
    (L : ParametricLossProcess Ξ d m) (μ : Measure Ξ) [SFinite μ]
    (E : Set (History d m T)) (hE : MeasurableSet E) :
    Measurable (fun r : Seeds T =>
      (parametricRunKernel (fixedPolicy P hmd r) L T ∘ₘ μ).real E) := by
  simp_rw [fixedPolicy_parametric_event_eq_section P hmd _ L μ E hE]
  exact (measurable_measure_prodMk_right
    ((measurable_seedRun_parametric P hmd L.at L.measurable_itemLoss) hE)).ennreal_toReal

/-- The same policy selector is used in every environment. Thus averaging
the fixed-seed probabilities recovers the original mixture exactly. -/
theorem fixedPolicy_parametric_event_average
    (P : Policy d m) (hmd : m ≤ d)
    (L : ParametricLossProcess Ξ d m) (μ : Measure Ξ) [IsProbabilityMeasure μ]
    (E : Set (History d m T)) (hE : MeasurableSet E) :
    (∫ r : Seeds T, (parametricRunKernel (fixedPolicy P hmd r) L T ∘ₘ μ).real E
      ∂seedMeasure T) = (parametricRunKernel P L T ∘ₘ μ).real E := by
  let S : Set (Ξ × Seeds T) := {x | seedRun P hmd (L.at x.1) T x.2 ∈ E}
  have hS : MeasurableSet S :=
    (measurable_seedRun_parametric P hmd L.at L.measurable_itemLoss) hE
  have hprod : (μ.prod (seedMeasure T)) S =
      (parametricRunKernel P L T ∘ₘ μ) E := by
    rw [Measure.prod_apply hS, Measure.bind_apply hE (Kernel.aemeasurable _)]
    apply lintegral_congr
    intro x
    rw [parametricRunKernel_apply]
    exact seedRun_event_probability P hmd (L.at x) T E hE
  rw [measureReal_def, ← hprod, Measure.prod_apply_symm hS]
  rw [← integral_toReal (measurable_measure_prodMk_right hS).aemeasurable
    (ae_of_all _ fun _ => measure_lt_top _ _)]
  apply integral_congr_ae
  exact ae_of_all _ fun r => fixedPolicy_parametric_event_eq_section P hmd r L μ E hE

end
end MsetsPaper.Probability.PolicySeed
