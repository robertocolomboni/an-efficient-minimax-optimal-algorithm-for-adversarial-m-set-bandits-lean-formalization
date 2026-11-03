import MsetsPaper.Probability.PolicySeedParametric
import MsetsPaper.Lower.Foundations
import MsetsLower.Lower.ParametricRegret

/-! # The independent-seed experiment behind parametric kernel fixing

The adversary table and the learner's master seed are independent. The
observable history is their measurable interaction and need not be independent
of either input. We identify the pushforward of that product experiment with
the existing parameter-retaining run kernel, then apply the manuscript's L10
to the product experiment itself.
-/

namespace MsetsPaper.Probability

open MsetsLower MsetsLower.Lower MeasureTheory ProbabilityTheory Set
open PolicySeed
open scoped ENNReal ProbabilityTheory

noncomputable section

/-- Equality of the complete joint laws, retaining the adversary table.
Only the input table and private master seed have a product law. -/
theorem seedRun_joint_map_eq_parametricRun
    {Ξ : Type*} [MeasurableSpace Ξ] {d m : ℕ}
    (hmd : m ≤ d) (μ : Measure Ξ) [IsProbabilityMeasure μ]
    (P : Policy d m) (L : ParametricLossProcess Ξ d m) (T : ℕ) :
    (μ.prod (seedMeasure T)).map
      (fun x : Ξ × Seeds T => (x.1, seedRun P hmd (L.at x.1) T x.2)) =
      parametricRunWithParameterKernel P L T ∘ₘ μ := by
  have hmap : Measurable (fun x : Ξ × Seeds T =>
      (x.1, seedRun P hmd (L.at x.1) T x.2)) :=
    measurable_fst.prodMk
      (measurable_seedRun_parametric P hmd L.at L.measurable_itemLoss)
  ext E hE
  rw [Measure.map_apply hmap hE]
  change (μ.prod (seedMeasure T))
    {x | (x.1, seedRun P hmd (L.at x.1) T x.2) ∈ E} = _
  rw [seedRun_joint_event_probability P hmd L.at L.measurable_itemLoss μ E hE,
    Measure.bind_apply hE (Kernel.aemeasurable _)]
  apply lintegral_congr
  intro ξ
  rw [parametricRunWithParameterKernel_apply,
    Measure.map_apply measurable_prodMk_left hE]

/-- The actual regret is jointly measurable as a function of the two
independent inputs, even for adaptive non-anticipating losses. -/
theorem measurable_seedRun_parametric_regret
    {Ξ : Type*} [MeasurableSpace Ξ] {d m : ℕ}
    (hmd : m ≤ d) (P : Policy d m) (L : ParametricLossProcess Ξ d m) (T : ℕ) :
    Measurable (fun x : Ξ × Seeds T =>
      pathRegret (L.at x.1) T (seedRun P hmd (L.at x.1) T x.2)) := by
  letI : Nonempty (MSetAction d m) := nonempty_MSetAction hmd
  have h := (measurable_parametricPathRegret L T).comp
    (measurable_fst.prodMk
      (measurable_seedRun_parametric P hmd L.at L.measurable_itemLoss))
  simpa only [Function.comp_def, parametricPathRegret_eq_at] using h

/-- Literal application of L10 to independent table and master seed, with
the input and output probabilities identified with the kernel formulation.
The statement matches the existing parametric-regret fixing interface. -/
theorem exists_fixed_parametric_regret_via_product
    {Ξ : Type*} [MeasurableSpace Ξ] {d m : ℕ} (hmd : m ≤ d)
    (μ : Measure Ξ) [IsProbabilityMeasure μ]
    (P : Policy d m) (L : ParametricLossProcess Ξ d m)
    (T : ℕ) (threshold probability : ℝ)
    (haverage : probability ≤
      (parametricRunWithParameterKernel P L T ∘ₘ μ).real
        (parametricRegretEvent L T threshold)) :
    ∃ ξ : Ξ, probability ≤
      (runLaw P (L.at ξ) T).real
        {h | threshold ≤ pathRegret (L.at ξ) T h} := by
  letI : Nonempty (MSetAction d m) := nonempty_MSetAction hmd
  have hmap : Measurable (fun x : Ξ × Seeds T =>
      (x.1, seedRun P hmd (L.at x.1) T x.2)) :=
    measurable_fst.prodMk
      (measurable_seedRun_parametric P hmd L.at L.measurable_itemLoss)
  have hproduct : probability ≤ (μ.prod (seedMeasure T)).real
      {x | threshold ≤ pathRegret (L.at x.1) T (seedRun P hmd (L.at x.1) T x.2)} := by
    rw [← seedRun_joint_map_eq_parametricRun hmd μ P L T,
      measureReal_def, Measure.map_apply hmap
        (measurableSet_parametricRegretEvent L T threshold)] at haverage
    simpa only [parametricRegretEvent, preimage_ofPred_eq,
      parametricPathRegret_eq_at, measureReal_def] using haverage
  obtain ⟨ξ, hξ⟩ := MsetsPaper.Lower.exists_fixed_adversary_seed μ (seedMeasure T)
    (fun x => pathRegret (L.at x.1) T (seedRun P hmd (L.at x.1) T x.2))
    (measurable_seedRun_parametric_regret hmd P L T) hproduct
  refine ⟨ξ, ?_⟩
  have hE : MeasurableSet {h : History d m T | threshold ≤ pathRegret (L.at ξ) T h} :=
    measurableSet_le measurable_const (measurable_pathRegret (L.at ξ) T)
  have hsection := congrArg ENNReal.toReal
    (seedRun_event_probability P hmd (L.at ξ) T _ hE)
  change (seedMeasure T).real
      {r | threshold ≤ pathRegret (L.at ξ) T (seedRun P hmd (L.at ξ) T r)} =
      (runLaw P (L.at ξ) T).real {h | threshold ≤ pathRegret (L.at ξ) T h} at hsection
  exact hξ.trans_eq hsection

end
end MsetsPaper.Probability
