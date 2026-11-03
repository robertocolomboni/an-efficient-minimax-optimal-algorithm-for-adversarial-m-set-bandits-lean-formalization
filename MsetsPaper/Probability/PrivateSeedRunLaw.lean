import MsetsPaper.Probability.PrivateSeedConsistency
import MsetsPaper.Probability.PolicyActionTree

/-! # Persistent-private-seed learners and observable policies have the same laws

The policy is constructed before the loss process is quantified. Equality
holds for every deterministic measurable non-anticipating loss process, every
horizon, and the complete observable history, not only a selected event.
-/

namespace MsetsPaper.Probability.PrivateSeed

open MsetsLower MeasureTheory ProbabilityTheory Set
open PolicyActionTree
open scoped ENNReal ProbabilityTheory BigOperators

noncomputable section

variable {Ω : Type*} [MeasurableSpace Ω] {d m : ℕ}

theorem historyOfActions_feasible (L : LossProcess d m) :
    ∀ t (a : ActionTree (MSetAction d m) t), feasibleHistory L t (historyOfActions L t a) := by
  intro t
  induction t with
  | zero => intro a; trivial
  | succ t ih => rintro ⟨a, b⟩; exact ⟨ih a, rfl⟩

theorem historyOfActions_actionsOfHistory (L : LossProcess d m) :
    ∀ t (h : History d m t), feasibleHistory L t h →
      historyOfActions L t (actionsOfHistory t h) = h := by
  intro t
  induction t with
  | zero => intro h _; cases h; rfl
  | succ t ih =>
      rintro ⟨h, a, y⟩ hh
      change feasibleHistory L t h ∧ y = actionLoss a (L.itemLoss t h) at hh
      simp only [actionsOfHistory, historyOfActions, ih h hh.1, History.snoc]
      exact Prod.ext rfl (Prod.ext rfl hh.2.symm)

theorem privateRun_eq_finiteAtomicMeasure (ν : Measure Ω) [IsProbabilityMeasure ν]
    (choose : (t : ℕ) → Ω → History d m t → MSetAction d m)
    (hc : ∀ t, Measurable (Function.uncurry (choose t))) (L : LossProcess d m) (T : ℕ) :
    ν.map (fun r => deterministicRun (fun t h => choose t r h) L T) =
      finiteAtomicMeasure (fun a => prefixMass ν choose T (historyOfActions L T a))
        (historyOfActions L T) := by
  classical
  let run (r : Ω) := deterministicRun (fun t h => choose t r h) L T
  have hrun : Measurable run := measurable_privateRun choose hc L T
  ext S hS
  let E (a : ActionTree (MSetAction d m) T) := {r | run r = historyOfActions L T a ∧ historyOfActions L T a ∈ S}
  have hE (a : ActionTree (MSetAction d m) T) : MeasurableSet (E a) := by
    by_cases ha : historyOfActions L T a ∈ S
    · simpa only [E, ha, and_true, Set.preimage, Set.mem_singleton_iff] using
        hrun (measurableSet_singleton (historyOfActions L T a))
    · simp [E, ha]
  have hdis : PairwiseDisjoint (↑(Finset.univ : Finset (ActionTree (MSetAction d m) T))) E := by
    intro a _ b _ hab
    apply Set.disjoint_left.mpr
    intro r hra hrb
    exact hab ((historyOfActions_injective L T) (hra.1.symm.trans hrb.1))
  have hun : (⋃ a ∈ (Finset.univ : Finset (ActionTree (MSetAction d m) T)), E a) = run ⁻¹' S := by
    ext r
    simp only [Finset.mem_univ, iUnion_true, mem_iUnion, mem_preimage, E, mem_setOf_eq]
    constructor
    · rintro ⟨a, heq, ha⟩; exact heq.symm ▸ ha
    · intro hr
      have heq := historyOfActions_actionsOfHistory L T (run r) (deterministicRun_feasible choose L r T)
      refine ⟨actionsOfHistory T (run r), heq.symm, ?_⟩
      rw [heq]
      exact hr
  rw [Measure.map_apply hrun hS, ← hun, measure_biUnion_finset hdis (fun a _ => hE a),
    finiteAtomicMeasure_apply _ _ _ hS]
  apply Finset.sum_congr rfl
  intro a _
  by_cases ha : historyOfActions L T a ∈ S
  · simp only [ha, if_pos, mul_one]
    have he : E a = {r | consistent choose T (historyOfActions L T a) r} := by
      ext r
      simp only [E, mem_setOf_eq, ha, and_true]
      exact (consistent_iff_deterministicRun_eq choose L r T _ (historyOfActions_feasible L T a)).symm
    rw [he]
    exact (ENNReal.ofReal_toReal (measure_ne_top _ _)).symm
  · simp [E, ha]

theorem branching_mass_eq_prefixMass (ν : Measure Ω) [IsProbabilityMeasure ν]
    (choose : (t : ℕ) → Ω → History d m t → MSetAction d m)
    (hc : ∀ t, Measurable (Function.uncurry (choose t)))
    (defaultAction : MSetAction d m) (L : LossProcess d m) :
    ∀ t (a : ActionTree (MSetAction d m) t),
      (branchingLaw (behavioralPolicy ν choose hc defaultAction) L).mass t a =
        prefixMass ν choose t (historyOfActions L t a) := by
  intro t
  induction t with
  | zero => intro a; rw [BranchingLaw.mass_zero, prefixMass_zero]
  | succ t ih =>
      rintro ⟨a, b⟩
      rw [BranchingLaw.mass_succ, ih]
      change prefixMass ν choose t (historyOfActions L t a) *
        ((behavioralPolicy ν choose hc defaultAction).kernel t (historyOfActions L t a)).real {b} = _
      rw [behavioralPolicy_real_singleton, prefixMass_mul_actionWeight]
      rfl

/-- One policy, independent of L, represents every persistent-seed experiment. -/
theorem privateRun_map_eq_runLaw (ν : Measure Ω) [IsProbabilityMeasure ν]
    (choose : (t : ℕ) → Ω → History d m t → MSetAction d m)
    (hc : ∀ t, Measurable (Function.uncurry (choose t))) (defaultAction : MSetAction d m)
    (L : LossProcess d m) (T : ℕ) :
    ν.map (fun r => deterministicRun (fun t h => choose t r h) L T) =
      runLaw (behavioralPolicy ν choose hc defaultAction) L T := by
  rw [privateRun_eq_finiteAtomicMeasure ν choose hc L T, runLaw_eq_finiteAtomicMeasure]
  congr 1
  funext a
  exact (branching_mass_eq_prefixMass ν choose hc defaultAction L T a).symm

theorem exists_common_behavioralPolicy (ν : Measure Ω) [IsProbabilityMeasure ν]
    (choose : (t : ℕ) → Ω → History d m t → MSetAction d m)
    (hc : ∀ t, Measurable (Function.uncurry (choose t))) (hmd : m ≤ d) :
    ∃ P : Policy d m, ∀ (L : LossProcess d m) (T : ℕ),
      ν.map (fun r => deterministicRun (fun t h => choose t r h) L T) = runLaw P L T := by
  let a := Classical.choice (nonempty_MSetAction hmd)
  exact ⟨behavioralPolicy ν choose hc a, privateRun_map_eq_runLaw ν choose hc a⟩

theorem privateRun_event_probability (ν : Measure Ω) [IsProbabilityMeasure ν]
    (choose : (t : ℕ) → Ω → History d m t → MSetAction d m)
    (hc : ∀ t, Measurable (Function.uncurry (choose t))) (defaultAction : MSetAction d m)
    (L : LossProcess d m) (T : ℕ) (E : Set (History d m T)) (hE : MeasurableSet E) :
    ν {r | deterministicRun (fun t h => choose t r h) L T ∈ E} =
      runLaw (behavioralPolicy ν choose hc defaultAction) L T E := by
  rw [← privateRun_map_eq_runLaw ν choose hc defaultAction L T,
    Measure.map_apply (measurable_privateRun choose hc L T) hE]
  rfl

end
end MsetsPaper.Probability.PrivateSeed
