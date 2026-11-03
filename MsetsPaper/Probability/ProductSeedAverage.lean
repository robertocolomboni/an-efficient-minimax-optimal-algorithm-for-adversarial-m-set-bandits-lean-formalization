import MsetsPaper.Probability.ProductFixingBridge

/-! # Averaging a bounded statistic only after fixing the private seed -/

namespace MsetsPaper.Probability

open MsetsLower MsetsLower.Lower MeasureTheory ProbabilityTheory Set PolicySeed
open scoped ENNReal ProbabilityTheory

noncomputable section

theorem fixedPolicy_joint_map
    {Ξ : Type*} [MeasurableSpace Ξ] {d m T : ℕ}
    (hmd : m ≤ d) (μ : Measure Ξ) (P : Policy d m)
    (L : ParametricLossProcess Ξ d m) (r : Seeds T) :
    parametricRunWithParameterKernel (fixedPolicy P hmd r) L T ∘ₘ μ =
      μ.map (fun ξ => (ξ, seedRun P hmd (L.at ξ) T r)) := by
  have hm : Measurable (fun ξ => (ξ, seedRun P hmd (L.at ξ) T r)) :=
    measurable_id.prodMk ((measurable_seedRun_parametric P hmd L.at L.measurable_itemLoss).comp
      measurable_prodMk_right)
  have hk : parametricRunWithParameterKernel (fixedPolicy P hmd r) L T =
      Kernel.deterministic (fun ξ => (ξ, seedRun P hmd (L.at ξ) T r)) hm := by
    ext ξ : 1
    rw [parametricRunWithParameterKernel_apply, fixedPolicy_runLaw,
      Measure.map_dirac' measurable_prodMk_left]
    rfl
  rw [hk, Measure.deterministic_comp_eq_map]

/-- The inner, seed-fixed expectation is integrable, and averaging it is
exactly the original joint expectation. All parameters remain inside `f`.
This is a bounded signed-statistic Fubini statement, not an event-only law. -/
theorem integral_parametric_fixedSeed_average
    {Ξ : Type*} [MeasurableSpace Ξ] {d m : ℕ}
    (hmd : m ≤ d) (μ : Measure Ξ) [IsProbabilityMeasure μ]
    (P : Policy d m) (L : ParametricLossProcess Ξ d m) (T : ℕ)
    (f : Ξ × History d m T → ℝ) (hf : Measurable f)
    (C : ℝ) (hC : ∀ x, |f x| ≤ C) :
    Integrable (fun r : Seeds T =>
      ∫ x, f x ∂(parametricRunWithParameterKernel (fixedPolicy P hmd r) L T ∘ₘ μ))
      (seedMeasure T) ∧
    (∫ x, f x ∂(parametricRunWithParameterKernel P L T ∘ₘ μ)) =
      ∫ r : Seeds T,
        (∫ x, f x ∂(parametricRunWithParameterKernel (fixedPolicy P hmd r) L T ∘ₘ μ))
        ∂seedMeasure T := by
  let F : Ξ × Seeds T → ℝ := fun x => f (x.1, seedRun P hmd (L.at x.1) T x.2)
  have hmap : Measurable (fun x : Ξ × Seeds T =>
      (x.1, seedRun P hmd (L.at x.1) T x.2)) :=
    measurable_fst.prodMk (measurable_seedRun_parametric P hmd L.at L.measurable_itemLoss)
  have hFi : Integrable F (μ.prod (seedMeasure T)) :=
    Integrable.of_bound (hf.comp hmap).aestronglyMeasurable C
      (ae_of_all _ fun x => by simpa only [Real.norm_eq_abs] using hC (x.1, _))
  have hinner (r : Seeds T) :
      (∫ x, f x ∂(parametricRunWithParameterKernel (fixedPolicy P hmd r) L T ∘ₘ μ)) =
        ∫ ξ, F (ξ, r) ∂μ := by
    rw [fixedPolicy_joint_map]
    exact integral_map
      (measurable_id.prodMk
        ((measurable_seedRun_parametric P hmd L.at L.measurable_itemLoss).comp
          measurable_prodMk_right)).aemeasurable hf.aestronglyMeasurable
  constructor
  · simp_rw [hinner]
    exact hFi.integral_prod_right
  · rw [← seedRun_joint_map_eq_parametricRun hmd μ P L T,
      integral_map hmap.aemeasurable hf.aestronglyMeasurable]
    rw [integral_prod_symm _ hFi]
    exact integral_congr_ae (ae_of_all _ fun r => (hinner r).symm)

end
end MsetsPaper.Probability
