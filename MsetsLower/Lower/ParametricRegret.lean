import MsetsLower.Core.ParametricRun
import MsetsLower.Lower.RegretMeasurability
import MsetsLower.Probability.KernelFixing

/-!
# Jointly measurable regret for table-indexed adversaries

The regret event changes with the deterministic table being fixed.  We retain
the table parameter in the experiment, prove joint measurability of regret,
and apply Tonelli to this genuine parameter-dependent event.
-/

set_option linter.style.header false

namespace MsetsLower.Lower

open MsetsLower MeasureTheory ProbabilityTheory Set
open scoped ENNReal ProbabilityTheory

noncomputable section

/-- Jointly measurable learner cumulative loss for a parametric adversary. -/
def parametricRealizedCumulativeLoss
    {Xi : Type*} [MeasurableSpace Xi] {d m : Nat}
    (L : ParametricLossProcess Xi d m) :
    (t : Nat) → Xi × History d m t → Real
  | 0, _ => 0
  | t + 1, input =>
      parametricRealizedCumulativeLoss L t (input.1, input.2.1) +
        actionLoss input.2.2.1 (L.itemLoss t input.1 input.2.1)

set_option maxHeartbeats 800000 in
-- The nested recursive history type makes elaboration of the joint action-loss
-- map substantially more expensive than the mathematical induction itself.
theorem measurable_parametricRealizedCumulativeLoss
    {Xi : Type*} [MeasurableSpace Xi] {d m : Nat}
    (L : ParametricLossProcess Xi d m) : ∀ t,
    Measurable (parametricRealizedCumulativeLoss L t) := by
  intro t
  induction t with
  | zero => exact measurable_const
  | succ t ih =>
      have hprefix : Measurable
          (fun input : Xi × History d m (t + 1) => (input.1, input.2.1)) :=
        measurable_fst.prodMk (measurable_fst.comp measurable_snd)
      have haction : Measurable
          (fun input : Xi × History d m (t + 1) => input.2.2.1) :=
        measurable_fst.comp (measurable_snd.comp measurable_snd)
      have hpair : Measurable
          (fun input : Xi × History d m (t + 1) =>
            ((input.1, input.2.1), input.2.2.1)) :=
        hprefix.prodMk haction
      exact (ih.comp hprefix).add
        ((measurable_actionLoss_joint (L.measurable_itemLoss t)).comp hpair)

@[simp] theorem parametricRealizedCumulativeLoss_eq_at
    {Xi : Type*} [MeasurableSpace Xi] {d m : Nat}
    (L : ParametricLossProcess Xi d m) : ∀ t (xi : Xi)
      (history : History d m t),
    parametricRealizedCumulativeLoss L t (xi, history) =
      realizedCumulativeLoss (L.at xi) t history := by
  intro t
  induction t with
  | zero => intro xi history; rfl
  | succ t ih =>
      intro xi history
      rw [parametricRealizedCumulativeLoss, realizedCumulativeLoss,
        ih xi history.1]
      rfl

/-- Joint comparator loss for a fixed action. -/
def parametricComparatorCumulativeLoss
    {Xi : Type*} [MeasurableSpace Xi] {d m : Nat}
    (L : ParametricLossProcess Xi d m) (action : MSetAction d m) :
    (t : Nat) → Xi × History d m t → Real
  | 0, _ => 0
  | t + 1, input =>
      parametricComparatorCumulativeLoss L action t (input.1, input.2.1) +
        actionLoss action (L.itemLoss t input.1 input.2.1)

theorem measurable_parametricComparatorCumulativeLoss
    {Xi : Type*} [MeasurableSpace Xi] {d m : Nat}
    (L : ParametricLossProcess Xi d m) (action : MSetAction d m) : ∀ t,
    Measurable (parametricComparatorCumulativeLoss L action t) := by
  intro t
  induction t with
  | zero => exact measurable_const
  | succ t ih =>
      have hprefix : Measurable
          (fun input : Xi × History d m (t + 1) => (input.1, input.2.1)) :=
        measurable_fst.prodMk (measurable_fst.comp measurable_snd)
      exact (ih.comp hprefix).add
        ((measurable_actionLoss action (L.measurable_itemLoss t)).comp hprefix)

@[simp] theorem parametricComparatorCumulativeLoss_eq_at
    {Xi : Type*} [MeasurableSpace Xi] {d m : Nat}
    (L : ParametricLossProcess Xi d m) (action : MSetAction d m) :
    ∀ t (xi : Xi) (history : History d m t),
    parametricComparatorCumulativeLoss L action t (xi, history) =
      comparatorCumulativeLoss (L.at xi) t history action := by
  intro t
  induction t with
  | zero => intro xi history; rfl
  | succ t ih =>
      intro xi history
      rw [parametricComparatorCumulativeLoss, comparatorCumulativeLoss,
        ih xi history.1]
      rfl

/-- Best fixed comparator as the finite pointwise infimum. -/
def parametricBestComparatorCumulativeLoss
    {Xi : Type*} [MeasurableSpace Xi] {d m : Nat}
    (L : ParametricLossProcess Xi d m) (t : Nat) :
    Xi × History d m t → Real :=
  fun input => ⨅ action : MSetAction d m,
    parametricComparatorCumulativeLoss L action t input

theorem measurable_parametricBestComparatorCumulativeLoss
    {Xi : Type*} [MeasurableSpace Xi] {d m : Nat}
    (L : ParametricLossProcess Xi d m) (t : Nat) :
    Measurable (parametricBestComparatorCumulativeLoss L t) := by
  exact Measurable.iInf fun action =>
    measurable_parametricComparatorCumulativeLoss L action t

theorem parametricBestComparatorCumulativeLoss_eq_at
    {Xi : Type*} [MeasurableSpace Xi] {d m : Nat}
    [Nonempty (MSetAction d m)]
    (L : ParametricLossProcess Xi d m) (t : Nat) (xi : Xi)
    (history : History d m t) :
    parametricBestComparatorCumulativeLoss L t (xi, history) =
      bestComparatorCumulativeLoss (L.at xi) t history := by
  unfold parametricBestComparatorCumulativeLoss bestComparatorCumulativeLoss
  change (⨅ action : MSetAction d m,
      parametricComparatorCumulativeLoss L action t (xi, history)) =
    ⨅ action : MSetAction d m,
      comparatorCumulativeLoss (L.at xi) t history action
  congr 1
  funext action
  exact parametricComparatorCumulativeLoss_eq_at L action t xi history

/-- Joint regret of table and observable history. -/
def parametricPathRegret
    {Xi : Type*} [MeasurableSpace Xi] {d m : Nat}
    (L : ParametricLossProcess Xi d m) (t : Nat) :
    Xi × History d m t → Real :=
  fun input => parametricRealizedCumulativeLoss L t input -
    parametricBestComparatorCumulativeLoss L t input

theorem measurable_parametricPathRegret
    {Xi : Type*} [MeasurableSpace Xi] {d m : Nat}
    (L : ParametricLossProcess Xi d m) (t : Nat) :
    Measurable (parametricPathRegret L t) :=
  (measurable_parametricRealizedCumulativeLoss L t).sub
    (measurable_parametricBestComparatorCumulativeLoss L t)

theorem parametricPathRegret_eq_at
    {Xi : Type*} [MeasurableSpace Xi] {d m : Nat}
    [Nonempty (MSetAction d m)]
    (L : ParametricLossProcess Xi d m) (t : Nat) (xi : Xi)
    (history : History d m t) :
    parametricPathRegret L t (xi, history) =
      pathRegret (L.at xi) t history := by
  unfold parametricPathRegret pathRegret
  rw [parametricRealizedCumulativeLoss_eq_at,
    parametricBestComparatorCumulativeLoss_eq_at]

/-- Retain the table parameter alongside the generated observable history. -/
def parametricRunWithParameterKernel
    {Xi : Type*} [MeasurableSpace Xi] {d m : Nat}
    (P : Policy d m) (L : ParametricLossProcess Xi d m) (t : Nat) :
    Kernel Xi (Xi × History d m t) :=
  Kernel.compProd Kernel.id
    (Kernel.prodMkLeft Xi (parametricRunKernel P L t))

instance parametricRunWithParameterKernel.instIsMarkovKernel
    {Xi : Type*} [MeasurableSpace Xi] {d m : Nat}
    (P : Policy d m) (L : ParametricLossProcess Xi d m) (t : Nat) :
    IsMarkovKernel (parametricRunWithParameterKernel P L t) := by
  unfold parametricRunWithParameterKernel
  letI : IsMarkovKernel (parametricRunKernel P L t) :=
    parametricRunKernel_isMarkov P L t
  infer_instance

theorem parametricRunWithParameterKernel_apply
    {Xi : Type*} [MeasurableSpace Xi] {d m : Nat}
    (P : Policy d m) (L : ParametricLossProcess Xi d m)
    (t : Nat) (xi : Xi) :
    parametricRunWithParameterKernel P L t xi =
      (runLaw P (L.at xi) t).map (fun history => (xi, history)) := by
  letI : IsMarkovKernel (parametricRunKernel P L t) :=
    parametricRunKernel_isMarkov P L t
  letI : IsMarkovKernel
      (Kernel.prodMkLeft Xi (parametricRunKernel P L t)) := by
    infer_instance
  ext event hevent
  rw [parametricRunWithParameterKernel, Kernel.compProd_apply hevent,
    Kernel.id_apply]
  simp only [Kernel.prodMkLeft_apply]
  have hsection : Measurable (fun xi' : Xi =>
      parametricRunKernel P L t xi' (Prod.mk xi' ⁻¹' event)) :=
    Kernel.measurable_kernel_prodMk_left
      (κ := parametricRunKernel P L t) hevent
  rw [lintegral_dirac' _ hsection, parametricRunKernel_apply]
  rw [Measure.map_apply measurable_prodMk_left hevent]

/-- Measurable joint regret event used by the fixing argument. -/
def parametricRegretEvent
    {Xi : Type*} [MeasurableSpace Xi] {d m : Nat}
    (L : ParametricLossProcess Xi d m) (t : Nat) (threshold : Real) :
    Set (Xi × History d m t) :=
  {input | threshold ≤ parametricPathRegret L t input}

theorem measurableSet_parametricRegretEvent
    {Xi : Type*} [MeasurableSpace Xi] {d m : Nat}
    (L : ParametricLossProcess Xi d m) (t : Nat) (threshold : Real) :
    MeasurableSet (parametricRegretEvent L t threshold) :=
  measurableSet_le measurable_const (measurable_parametricPathRegret L t)

/-- Exact section formula for the parameter-dependent regret event. -/
theorem parametricRunWithParameterKernel_regretEvent_apply
    {Xi : Type*} [MeasurableSpace Xi] {d m : Nat} (hmd : m ≤ d)
    (P : Policy d m) (L : ParametricLossProcess Xi d m)
    (t : Nat) (threshold : Real) (xi : Xi) :
    parametricRunWithParameterKernel P L t xi
        (parametricRegretEvent L t threshold) =
      runLaw P (L.at xi) t
        {history | threshold ≤ pathRegret (L.at xi) t history} := by
  letI : Nonempty (MSetAction d m) := nonempty_MSetAction hmd
  rw [parametricRunWithParameterKernel_apply,
    Measure.map_apply measurable_prodMk_left
      (measurableSet_parametricRegretEvent L t threshold)]
  congr 1
  ext history
  change (threshold ≤ parametricPathRegret L t (xi, history)) ↔
    threshold ≤ pathRegret (L.at xi) t history
  rw [parametricPathRegret_eq_at]

/-- Fully parameter-dependent fixing-table theorem for regret tails. -/
theorem exists_fixed_parametric_regret
    {Xi : Type*} [MeasurableSpace Xi] {d m : Nat} (hmd : m ≤ d)
    (mu : Measure Xi) [IsProbabilityMeasure mu]
    (P : Policy d m) (L : ParametricLossProcess Xi d m)
    (t : Nat) (threshold probability : Real)
    (haverage : probability ≤
      ((parametricRunWithParameterKernel P L t) ∘ₘ mu).real
        (parametricRegretEvent L t threshold)) :
    ∃ xi : Xi, probability ≤
      (runLaw P (L.at xi) t).real
        {history | threshold ≤ pathRegret (L.at xi) t history} := by
  letI : IsMarkovKernel (parametricRunWithParameterKernel P L t) :=
    parametricRunWithParameterKernel.instIsMarkovKernel P L t
  obtain ⟨xi, hxi⟩ := MsetsLower.Probability.exists_fixed_kernel_real
    mu (parametricRunWithParameterKernel P L t)
      (measurableSet_parametricRegretEvent L t threshold) haverage
  refine ⟨xi, ?_⟩
  change probability ≤ ENNReal.toReal
    (parametricRunWithParameterKernel P L t xi
      (parametricRegretEvent L t threshold)) at hxi
  change probability ≤ ENNReal.toReal
    (runLaw P (L.at xi) t
      {history | threshold ≤ pathRegret (L.at xi) t history})
  rw [parametricRunWithParameterKernel_regretEvent_apply hmd] at hxi
  exact hxi

#print axioms measurable_parametricPathRegret
#print axioms parametricRunWithParameterKernel_regretEvent_apply
#print axioms exists_fixed_parametric_regret

end

end MsetsLower.Lower
