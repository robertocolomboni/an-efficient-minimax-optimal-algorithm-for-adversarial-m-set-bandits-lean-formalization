import MsetsPaper.Probability.PrivateSeedPolicy

/-! # Seed consistency is exactly deterministic interaction on feasible histories -/

namespace MsetsPaper.Probability.PrivateSeed

open MsetsLower MeasureTheory ProbabilityTheory Set
open scoped ENNReal ProbabilityTheory BigOperators

noncomputable section

variable {Ω : Type*} [MeasurableSpace Ω] {d m : ℕ}

def feasibleHistory (L : LossProcess d m) : (t : ℕ) → History d m t → Prop
  | 0, _ => True
  | t + 1, h => feasibleHistory L t h.1 ∧ h.2.2 = actionLoss h.2.1 (L.itemLoss t h.1)

theorem deterministicRun_feasible
    (choose : (t : ℕ) → Ω → History d m t → MSetAction d m)
    (L : LossProcess d m) (r : Ω) :
    ∀ t, feasibleHistory L t (deterministicRun (fun t h => choose t r h) L t) := by
  intro t
  induction t with
  | zero => trivial
  | succ t ih => exact ⟨ih, rfl⟩

theorem consistent_iff_deterministicRun_eq
    (choose : (t : ℕ) → Ω → History d m t → MSetAction d m)
    (L : LossProcess d m) (r : Ω) :
    ∀ t (h : History d m t), feasibleHistory L t h →
      (consistent choose t h r ↔ deterministicRun (fun t h => choose t r h) L t = h) := by
  intro t
  induction t with
  | zero =>
      intro h _
      constructor
      · intro _; cases h; rfl
      · intro _; trivial
  | succ t ih =>
      rintro ⟨h, a, y⟩ hh
      change feasibleHistory L t h ∧ y = actionLoss a (L.itemLoss t h) at hh
      change (consistent choose t h r ∧ choose t r h = a) ↔ _
      constructor
      · rintro ⟨hr, ha⟩
        simp only [deterministicRun, (ih h hh.1).mp hr, ha, History.snoc]
        exact Prod.ext rfl (Prod.ext rfl hh.2.symm)
      · intro heq
        have hp := congrArg Prod.fst heq
        change deterministicRun (fun t h => choose t r h) L t = h at hp
        have ha := congrArg (fun H : History d m (t + 1) => H.2.1) heq
        refine ⟨(ih h hh.1).mpr hp, ?_⟩
        change choose t r (deterministicRun (fun t h => choose t r h) L t) = a at ha
        rw [hp] at ha
        exact ha

theorem consistent_deterministicRun
    (choose : (t : ℕ) → Ω → History d m t → MSetAction d m)
    (L : LossProcess d m) (r : Ω) (t : ℕ) :
    consistent choose t (deterministicRun (fun t h => choose t r h) L t) r :=
  (consistent_iff_deterministicRun_eq choose L r t _
    (deterministicRun_feasible choose L r t)).mpr rfl

theorem measurable_privateRun
    (choose : (t : ℕ) → Ω → History d m t → MSetAction d m)
    (hc : ∀ t, Measurable (Function.uncurry (choose t))) (L : LossProcess d m) (t : ℕ) :
    Measurable (fun r => deterministicRun (fun t h => choose t r h) L t) :=
  measurable_deterministicRun choose hc (fun _ => L)
    (fun t => (L.measurable_itemLoss t).comp measurable_snd) t

theorem privateRun_real_singleton_eq_prefixMass (ν : Measure Ω)
    (choose : (t : ℕ) → Ω → History d m t → MSetAction d m)
    (hc : ∀ t, Measurable (Function.uncurry (choose t))) (L : LossProcess d m)
    (t : ℕ) (h : History d m t) (hh : feasibleHistory L t h) :
    (ν.map (fun r => deterministicRun (fun t h => choose t r h) L t)).real {h} =
      prefixMass ν choose t h := by
  rw [measureReal_def, Measure.map_apply (measurable_privateRun choose hc L t) (measurableSet_singleton h)]
  unfold prefixMass
  congr 1
  congr 1
  ext r
  exact (consistent_iff_deterministicRun_eq choose L r t h hh).symm

theorem prefixMass_zero (ν : Measure Ω) [IsProbabilityMeasure ν]
    (choose : (t : ℕ) → Ω → History d m t → MSetAction d m) (h : History d m 0) :
    prefixMass ν choose 0 h = 1 := by simp [prefixMass, consistent]

theorem prefixMass_snoc (ν : Measure Ω)
    (choose : (t : ℕ) → Ω → History d m t → MSetAction d m)
    (t : ℕ) (h : History d m t) (a : MSetAction d m) (y : ℝ) :
    prefixMass ν choose (t + 1) (h.snoc a y) = nextMass ν choose t h a := rfl

end
end MsetsPaper.Probability.PrivateSeed
