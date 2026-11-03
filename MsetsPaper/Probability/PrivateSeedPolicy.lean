import MsetsPaper.Probability.DeterministicRun
import MsetsPaper.Probability.ExecutionMeasure
import Mathlib.MeasureTheory.Measure.Prod

/-! # A single observable policy for a persistent private seed

The conditioning events inspect only the learner's earlier action choices on
the given history. They do not mention an environment or loss process. Thus
the constructed policy is the SAME policy in every deterministic environment.
Operational equality of the complete run laws is proved separately.
-/

namespace MsetsPaper.Probability.PrivateSeed

open MsetsLower MeasureTheory ProbabilityTheory Set
open scoped ENNReal ProbabilityTheory BigOperators

noncomputable section

variable {Ω : Type*} [MeasurableSpace Ω] {d m : ℕ}

def consistent (choose : (t : ℕ) → Ω → History d m t → MSetAction d m) :
    (t : ℕ) → History d m t → Ω → Prop
  | 0, _, _ => True
  | t + 1, h, r => consistent choose t h.1 r ∧ choose t r h.1 = h.2.1

theorem measurableSet_consistent
    (choose : (t : ℕ) → Ω → History d m t → MSetAction d m)
    (hc : ∀ t, Measurable (Function.uncurry (choose t))) :
    ∀ t, MeasurableSet {x : History d m t × Ω | consistent choose t x.1 x.2} := by
  intro t
  induction t with
  | zero => simp [consistent]
  | succ t ih =>
      have hp : Measurable (fun x : History d m (t + 1) × Ω => (x.1.1, x.2)) :=
        measurable_fst.fst.prodMk measurable_snd
      have hch : Measurable (fun x : History d m (t + 1) × Ω => choose t x.2 x.1.1) :=
        (hc t).comp (measurable_snd.prodMk measurable_fst.fst)
      exact (ih.preimage hp).inter (measurableSet_eq_fun hch measurable_fst.snd.fst)

theorem measurableSet_consistent_next
    (choose : (t : ℕ) → Ω → History d m t → MSetAction d m)
    (hc : ∀ t, Measurable (Function.uncurry (choose t))) (t : ℕ) (a : MSetAction d m) :
    MeasurableSet {x : History d m t × Ω | consistent choose t x.1 x.2 ∧ choose t x.2 x.1 = a} :=
  (measurableSet_consistent choose hc t).inter
    (measurableSet_eq_fun ((hc t).comp measurable_swap) measurable_const)

def prefixMass (ν : Measure Ω)
    (choose : (t : ℕ) → Ω → History d m t → MSetAction d m)
    (t : ℕ) (h : History d m t) : ℝ := ν.real {r | consistent choose t h r}

def nextMass (ν : Measure Ω)
    (choose : (t : ℕ) → Ω → History d m t → MSetAction d m)
    (t : ℕ) (h : History d m t) (a : MSetAction d m) : ℝ :=
  ν.real {r | consistent choose t h r ∧ choose t r h = a}

theorem measurable_prefixMass (ν : Measure Ω) [IsProbabilityMeasure ν]
    (choose : (t : ℕ) → Ω → History d m t → MSetAction d m)
    (hc : ∀ t, Measurable (Function.uncurry (choose t))) (t : ℕ) :
    Measurable (prefixMass ν choose t) :=
  (measurable_measure_prodMk_left (measurableSet_consistent choose hc t)).ennreal_toReal

theorem measurable_nextMass (ν : Measure Ω) [IsProbabilityMeasure ν]
    (choose : (t : ℕ) → Ω → History d m t → MSetAction d m)
    (hc : ∀ t, Measurable (Function.uncurry (choose t))) (t : ℕ) (a : MSetAction d m) :
    Measurable (fun h => nextMass ν choose t h a) :=
  (measurable_measure_prodMk_left (measurableSet_consistent_next choose hc t a)).ennreal_toReal

theorem prefixMass_nonneg (ν : Measure Ω)
    (choose : (t : ℕ) → Ω → History d m t → MSetAction d m) (t : ℕ) (h : History d m t) :
    0 ≤ prefixMass ν choose t h := measureReal_nonneg

theorem nextMass_nonneg (ν : Measure Ω)
    (choose : (t : ℕ) → Ω → History d m t → MSetAction d m)
    (t : ℕ) (h : History d m t) (a : MSetAction d m) :
    0 ≤ nextMass ν choose t h a := measureReal_nonneg

theorem nextMass_le_prefixMass (ν : Measure Ω) [IsProbabilityMeasure ν]
    (choose : (t : ℕ) → Ω → History d m t → MSetAction d m)
    (t : ℕ) (h : History d m t) (a : MSetAction d m) :
    nextMass ν choose t h a ≤ prefixMass ν choose t h :=
  measureReal_mono (fun _ hr => hr.1)

theorem sum_nextMass (ν : Measure Ω) [IsProbabilityMeasure ν]
    (choose : (t : ℕ) → Ω → History d m t → MSetAction d m)
    (hc : ∀ t, Measurable (Function.uncurry (choose t))) (t : ℕ) (h : History d m t) :
    (∑ a, nextMass ν choose t h a) = prefixMass ν choose t h := by
  classical
  let S (a : MSetAction d m) := {r | consistent choose t h r ∧ choose t r h = a}
  have hS (a : MSetAction d m) : MeasurableSet (S a) :=
    (measurableSet_consistent_next choose hc t a).preimage measurable_prodMk_left
  have hdis : Pairwise (fun a b => Disjoint (S a) (S b)) := by
    intro a b hab
    apply Set.disjoint_left.mpr
    intro r hra hrb
    exact hab (hra.2.symm.trans hrb.2)
  have hun : (⋃ a, S a) = {r | consistent choose t h r} := by
    ext r
    simp only [mem_iUnion, mem_setOf_eq, S]
    constructor
    · rintro ⟨a, hr, _⟩; exact hr
    · intro hr; exact ⟨choose t r h, hr, rfl⟩
  change (∑ a, ν.real (S a)) = _
  rw [← measureReal_iUnion_fintype hdis hS, hun]
  rfl

def actionWeight (ν : Measure Ω)
    (choose : (t : ℕ) → Ω → History d m t → MSetAction d m)
    (defaultAction : MSetAction d m) (t : ℕ) (h : History d m t) (a : MSetAction d m) : ℝ := by
  classical
  exact if prefixMass ν choose t h = 0 then (if a = defaultAction then 1 else 0)
    else nextMass ν choose t h a / prefixMass ν choose t h

theorem actionWeight_nonneg (ν : Measure Ω)
    (choose : (t : ℕ) → Ω → History d m t → MSetAction d m)
    (defaultAction : MSetAction d m) (t : ℕ) (h : History d m t) (a : MSetAction d m) :
    0 ≤ actionWeight ν choose defaultAction t h a := by
  unfold actionWeight
  split_ifs <;> try norm_num
  exact div_nonneg (nextMass_nonneg ν choose t h a) (prefixMass_nonneg ν choose t h)

theorem sum_actionWeight (ν : Measure Ω) [IsProbabilityMeasure ν]
    (choose : (t : ℕ) → Ω → History d m t → MSetAction d m)
    (hc : ∀ t, Measurable (Function.uncurry (choose t)))
    (defaultAction : MSetAction d m) (t : ℕ) (h : History d m t) :
    (∑ a, actionWeight ν choose defaultAction t h a) = 1 := by
  classical
  by_cases hz : prefixMass ν choose t h = 0
  · simp [actionWeight, hz]
  · simp only [actionWeight, if_neg hz, ← Finset.sum_div, sum_nextMass ν choose hc, div_self hz]

theorem measurable_actionWeight (ν : Measure Ω) [IsProbabilityMeasure ν]
    (choose : (t : ℕ) → Ω → History d m t → MSetAction d m)
    (hc : ∀ t, Measurable (Function.uncurry (choose t)))
    (defaultAction : MSetAction d m) (t : ℕ) (a : MSetAction d m) :
    Measurable (fun h => actionWeight ν choose defaultAction t h a) := by
  unfold actionWeight
  exact Measurable.ite (measurableSet_eq_fun (measurable_prefixMass ν choose hc t) measurable_const)
    measurable_const ((measurable_nextMass ν choose hc t a).div (measurable_prefixMass ν choose hc t))

theorem prefixMass_mul_actionWeight (ν : Measure Ω) [IsProbabilityMeasure ν]
    (choose : (t : ℕ) → Ω → History d m t → MSetAction d m)
    (defaultAction : MSetAction d m) (t : ℕ) (h : History d m t) (a : MSetAction d m) :
    prefixMass ν choose t h * actionWeight ν choose defaultAction t h a = nextMass ν choose t h a := by
  by_cases hz : prefixMass ν choose t h = 0
  · have hn : nextMass ν choose t h a = 0 := le_antisymm
      (by simpa only [hz] using nextMass_le_prefixMass ν choose t h a) (nextMass_nonneg ν choose t h a)
    simp [hz, hn]
  · simp only [actionWeight, if_neg hz]
    field_simp

def behavioralPolicy (ν : Measure Ω) [IsProbabilityMeasure ν]
    (choose : (t : ℕ) → Ω → History d m t → MSetAction d m)
    (hc : ∀ t, Measurable (Function.uncurry (choose t)))
    (defaultAction : MSetAction d m) : Policy d m where
  kernel t := {
    toFun h := finiteAtomicMeasure (actionWeight ν choose defaultAction t h) id
    measurable' := measurable_finiteAtomicMeasure _
      (measurable_actionWeight ν choose hc defaultAction t) id }
  isMarkov t := {
    isProbabilityMeasure h := finiteAtomicMeasure_isProbabilityMeasure _
      (actionWeight_nonneg ν choose defaultAction t h) id
      (sum_actionWeight ν choose hc defaultAction t h) }

theorem behavioralPolicy_real_singleton (ν : Measure Ω) [IsProbabilityMeasure ν]
    (choose : (t : ℕ) → Ω → History d m t → MSetAction d m)
    (hc : ∀ t, Measurable (Function.uncurry (choose t)))
    (defaultAction : MSetAction d m) (t : ℕ) (h : History d m t) (a : MSetAction d m) :
    ((behavioralPolicy ν choose hc defaultAction).kernel t h).real {a} =
      actionWeight ν choose defaultAction t h a := by
  classical
  change (finiteAtomicMeasure (actionWeight ν choose defaultAction t h) id).real {a} = _
  rw [finiteAtomicMeasure_real_apply _ (actionWeight_nonneg ν choose defaultAction t h) _ _
    (measurableSet_singleton a)]
  simp

end
end MsetsPaper.Probability.PrivateSeed
