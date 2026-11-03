import MsetsPaper.Probability.PolicySeedFixed
import MsetsPaper.Probability.PrivateSeedRunLaw
import MsetsLower.Lower.Statement

/-! # Complementation on the same private seed

The simulated learner is chosen before the adversary.  Its choice rule uses
exactly the original seed, and the induction below is pointwise, including
seeds of probability zero.  The final tail transfer uses this coupling.
-/

namespace MsetsPaper.Lower.ComplementSeed

open MsetsLower MsetsLower.Lower MeasureTheory ProbabilityTheory
open MsetsPaper.Probability MsetsPaper.Probability.PolicySeed
open MsetsPaper.Probability.PrivateSeed

noncomputable section

variable {d s : ℕ}

def complementChoose {Ω : Type*} (hsd : s ≤ d)
    (choose : (t : ℕ) → Ω → History d (d - s) t → MSetAction d (d - s))
    (t : ℕ) (r : Ω) (h : History d s t) : MSetAction d s :=
  actionComplementEquiv d s hsd
    (choose t r ((historyComplementEquiv d s hsd t).symm h))

theorem measurable_complementChoose {Ω : Type*} [MeasurableSpace Ω]
    (hsd : s ≤ d)
    (choose : (t : ℕ) → Ω → History d (d - s) t → MSetAction d (d - s))
    (hc : ∀ t, Measurable (Function.uncurry (choose t))) (t : ℕ) :
    Measurable (Function.uncurry (complementChoose hsd choose t)) :=
  (actionComplementMeasurableEquiv d s hsd).measurable.comp
    ((hc t).comp (measurable_fst.prodMk
      ((historyComplementEquiv d s hsd t).symm.measurable.comp measurable_snd)))

/-- The two runs use the same seed at every round, with identical feedback. -/
theorem deterministicRun_complement {Ω : Type*} (hsd : s ≤ d)
    (hm : 0 < d - s)
    (choose : (t : ℕ) → Ω → History d (d - s) t → MSetAction d (d - s))
    (G : LossProcess d s) (r : Ω) :
    ∀ t, deterministicRun (fun u h ↦ complementChoose hsd choose u r h) G t =
      historyComplementEquiv d s hsd t
        (deterministicRun (fun u h ↦ choose u r h)
          (complementLossProcess hsd hm G) t) := by
  intro t
  induction t with
  | zero => rfl
  | succ t ih =>
      change extendRun G t
        (deterministicRun (fun u h ↦ complementChoose hsd choose u r h) G t,
          complementChoose hsd choose t r
            (deterministicRun (fun u h ↦ complementChoose hsd choose u r h) G t)) =
        historyComplementEquiv d s hsd (t + 1)
          (extendRun (complementLossProcess hsd hm G) t
            (deterministicRun (fun u h ↦ choose u r h) (complementLossProcess hsd hm G) t,
              choose t r
                (deterministicRun (fun u h ↦ choose u r h) (complementLossProcess hsd hm G) t)))
      rw [ih]
      simp only [complementChoose, MeasurableEquiv.symm_apply_apply]
      exact (complement_extendRun hsd hm G t _ _).symm

/-- In particular, external regret agrees for every private seed. -/
theorem deterministicRun_regret_complement {Ω : Type*} (hsd : s ≤ d)
    (hm : 0 < d - s)
    (choose : (t : ℕ) → Ω → History d (d - s) t → MSetAction d (d - s))
    (G : LossProcess d s) (r : Ω) (T : ℕ) :
    pathRegret G T
        (deterministicRun (fun u h ↦ complementChoose hsd choose u r h) G T) =
      pathRegret (complementLossProcess hsd hm G) T
        (deterministicRun (fun u h ↦ choose u r h)
          (complementLossProcess hsd hm G) T) := by
  rw [deterministicRun_complement, pathRegret_complement]

def seededChoose (hsd : s ≤ d) (P : Policy d (d - s)) (T : ℕ) :=
  complementChoose hsd (fun t (r : Seeds T) h ↦
    fixedChoose P (Nat.sub_le d s) r t h)

theorem measurable_seededChoose (hsd : s ≤ d)
    (P : Policy d (d - s)) (T t : ℕ) :
    Measurable (Function.uncurry (seededChoose hsd P T t)) :=
  measurable_complementChoose hsd _
    (fun u ↦ measurable_fixedChoose_joint P (Nat.sub_le d s) u) t

/-- This policy depends on the original learner and horizon, not on G. -/
def seededPolicy (hsd : s ≤ d) (P : Policy d (d - s)) (T : ℕ) : Policy d s :=
  behavioralPolicy (seedMeasure T) (seededChoose hsd P T)
    (measurable_seededChoose hsd P T) (Classical.choice (nonempty_MSetAction hsd))

theorem seededRun_eq (hsd : s ≤ d) (hm : 0 < d - s)
    (P : Policy d (d - s)) (G : LossProcess d s) (T : ℕ) (r : Seeds T) :
    deterministicRun (fun t h ↦ seededChoose hsd P T t r h) G T =
      historyComplementEquiv d s hsd T
        (seedRun P (Nat.sub_le d s) (complementLossProcess hsd hm G) T r) := by
  rw [show seededChoose hsd P T = complementChoose hsd
    (fun t (r : Seeds T) h ↦ fixedChoose P (Nat.sub_le d s) r t h) from rfl,
    deterministicRun_complement hsd hm,
    deterministicRun_fixedChoose_eq_seedRun P (Nat.sub_le d s) r _ T le_rfl]
  rfl

/-- Probability identity obtained from the pointwise common-seed induction. -/
theorem seeded_regret_tail (hsd : s ≤ d) (hm : 0 < d - s)
    (P : Policy d (d - s)) (G : LossProcess d s) (T : ℕ) (b : ℝ) :
    regretTailProbability hsd (seededPolicy hsd P T) G T b =
      regretTailProbability (Nat.sub_le d s) P
        (complementLossProcess hsd hm G) T b := by
  let E : Set (History d s T) := {h | b ≤ pathRegret G T h}
  have hE : MeasurableSet E := measurableSet_pathRegret_ge_of_le hsd G T b
  have hEq := privateRun_event_probability (seedMeasure T) (seededChoose hsd P T)
    (measurable_seededChoose hsd P T) (Classical.choice (nonempty_MSetAction hsd))
    G T E hE
  change (seedMeasure T)
    {r | deterministicRun (fun t h ↦ seededChoose hsd P T t r h) G T ∈ E} =
    runLaw (seededPolicy hsd P T) G T E at hEq
  change runLaw (seededPolicy hsd P T) G T E = _
  rw [← hEq]
  have hevents :
      {r : Seeds T | deterministicRun (fun t h ↦ seededChoose hsd P T t r h) G T ∈ E} =
      {r : Seeds T | seedRun P (Nat.sub_le d s) (complementLossProcess hsd hm G) T r ∈
        {h | b ≤ pathRegret (complementLossProcess hsd hm G) T h}} := by
    ext r
    simp only [Set.mem_setOf_eq, E, seededRun_eq hsd hm,
      ← pathRegret_complement hsd hm]
  rw [hevents, seedRun_event_probability]
  · rfl
  · exact measurableSet_pathRegret_ge_of_le (Nat.sub_le d s) _ T b

theorem lower_tail_via_common_seed {T : ℕ} (hsd : s ≤ d) (hm : 0 < d - s)
    {threshold probability : ℝ}
    (h : ∀ Q : Policy d s, HasRegretLowerTail hsd Q T threshold probability)
    (P : Policy d (d - s)) :
    HasRegretLowerTail (Nat.sub_le d s) P T threshold probability := by
  obtain ⟨G, hG⟩ := h (seededPolicy hsd P T)
  refine ⟨complementLossProcess hsd hm G, ?_⟩
  rw [← seeded_regret_tail hsd hm P G T threshold]
  exact hG

end
end MsetsPaper.Lower.ComplementSeed
