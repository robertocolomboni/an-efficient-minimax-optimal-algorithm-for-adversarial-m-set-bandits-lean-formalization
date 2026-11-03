import MsetsPaper.Lower.ConfidenceObliviousStopping
import MsetsPaper.Lower.ConfidenceObliviousEvents
import MsetsPaper.Probability.PolicySeedFixed
import MsetsPaper.Probability.PolicySeedParametric

/-! # The actual auxiliary algorithm and coupling over private randomness -/

namespace MsetsPaper.Lower.ConfidenceOblivious

open MsetsLower MsetsLower.Lower MsetsLower.Lower.Confidence MsetsPaper.Probability
open MsetsPaper.Probability.PolicySeed
open MeasureTheory ProbabilityTheory Set
open scoped ENNReal ProbabilityTheory

noncomputable section

def auxiliaryChoose {d m T : ℕ} (P : Policy d m) (hmd : m ≤ d) (r : Seeds T)
    (budget : ℝ) (defaultAction : MSetAction d m) :
    (t : ℕ) → History d m t → MSetAction d m :=
  stoppedChoose (fixedChoose P hmd r) hmd budget defaultAction

theorem measurable_auxiliaryChoose_joint {d m T : ℕ} (P : Policy d m) (hmd : m ≤ d)
    (budget : ℝ) (defaultAction : MSetAction d m) (t : ℕ) :
    Measurable (fun x : Seeds T × History d m t => auxiliaryChoose P hmd x.1 budget defaultAction t x.2) :=
  measurable_stoppedChoose_parametric (fixedChoose P hmd)
    (measurable_fixedChoose_joint P hmd) hmd budget defaultAction t

def auxiliaryPolicy {d m T : ℕ} (P : Policy d m) (hmd : m ≤ d) (r : Seeds T)
    (budget : ℝ) (defaultAction : MSetAction d m) : Policy d m :=
  stoppedPolicy (fixedChoose P hmd r) (measurable_fixedChoose P hmd r) hmd budget defaultAction

def auxiliaryRun {d m T : ℕ} (P : Policy d m) (hmd : m ≤ d) (r : Seeds T)
    (budget : ℝ) (defaultAction : MSetAction d m) (L : LossProcess d m) (t : ℕ) :
    History d m t := deterministicRun (auxiliaryChoose P hmd r budget defaultAction) L t

theorem auxiliaryPolicy_runLaw {d m T : ℕ} (P : Policy d m) (hmd : m ≤ d) (r : Seeds T)
    (budget : ℝ) (defaultAction : MSetAction d m) (L : LossProcess d m) (t : ℕ) :
    runLaw (auxiliaryPolicy P hmd r budget defaultAction) L t =
      Measure.dirac (auxiliaryRun P hmd r budget defaultAction L t) :=
  runLaw_deterministic_eq_dirac _ _ _ _

theorem measurable_auxiliaryRun_parametric {Ξ : Type*} [MeasurableSpace Ξ] {d m T : ℕ}
    (P : Policy d m) (hmd : m ≤ d) (budget : ℝ) (defaultAction : MSetAction d m)
    (L : ParametricLossProcess Ξ d m) (t : ℕ) :
    Measurable (fun x : Seeds T × Ξ => auxiliaryRun P hmd x.1 budget defaultAction (L.at x.2) t) := by
  apply measurable_deterministicRun
    (fun t (x : Seeds T × Ξ) h => auxiliaryChoose P hmd x.1 budget defaultAction t h)
  · intro s
    exact (measurable_auxiliaryChoose_joint P hmd budget defaultAction s).comp
      (measurable_fst.fst.prodMk measurable_snd)
  · intro s
    exact (L.measurable_itemLoss s).comp (measurable_fst.snd.prodMk measurable_snd)

theorem auxiliaryRun_penalty_lt {d m T : ℕ}
    (P : Policy d m) (hm : 1 ≤ m) (hmd : m ≤ d) (r : Seeds T)
    (budget : ℝ) (hb : 0 < budget) (j : Fin d)
    (hj : j ∈ confidenceCandidates d m hmd) (L : LossProcess d m) (t : ℕ) :
    cumulativePenalty hmd t (auxiliaryRun P hmd r budget (coreComparator hm hmd j hj) L t) < budget := by
  exact stoppedRun_penalty_lt (fixedChoose P hmd r) hmd budget hb _
    (by simp [candidatePenalty]) L t

theorem auxiliaryRun_total_candidate_pulls_lt {d m T : ℕ}
    (P : Policy d m) (hm : 1 ≤ m) (hmd : m ≤ d) (hT : 0 < T)
    (Delta : ℝ) (hDelta : 0 < Delta) (r : Seeds T)
    (j : Fin d) (hj : j ∈ confidenceCandidates d m hmd) (L : LossProcess d m) :
    let h := auxiliaryRun P hmd r (Delta * T / 8) (coreComparator hm hmd j hj) L T
    History.actionSum (fun a => (candidateCount hmd a : ℝ)) T h < T * (1 + m * Delta) := by
  dsimp only
  rw [total_candidate_pulls_eq hm hmd]
  have h := auxiliaryRun_penalty_lt P hm hmd r (Delta * T / 8) (by positivity) j hj L T
  have hmpos : (0 : ℝ) < m := by exact_mod_cast hm
  nlinarith

theorem auxiliaryPolicy_penalty_ae {d m T : ℕ}
    (P : Policy d m) (hm : 1 ≤ m) (hmd : m ≤ d) (r : Seeds T)
    (budget : ℝ) (hb : 0 < budget) (j : Fin d)
    (hj : j ∈ confidenceCandidates d m hmd) (L : LossProcess d m) (t : ℕ) :
    ∀ᵐ h ∂runLaw (auxiliaryPolicy P hmd r budget (coreComparator hm hmd j hj)) L t,
      cumulativePenalty hmd t h < budget := by
  rw [auxiliaryPolicy_runLaw]
  apply (ae_dirac_iff (measurableSet_lt (measurable_cumulativePenalty hmd t) measurable_const)).2
  exact auxiliaryRun_penalty_lt P hm hmd r budget hb j hj L t

/-- The first and last lines of the manuscript's probability partition.
The two events are disjoint and exhaustive because tau is at most T+1. -/
theorem measureReal_firstReplacement_partition {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsFiniteMeasure μ] (τ : Ω → ℕ) (T : ℕ)
    (hτ : Measurable τ) (hbound : ∀ ω, τ ω ≤ T + 1)
    (E : Set Ω) (hE : MeasurableSet E) :
    μ.real E = μ.real (E ∩ {ω | τ ω ≤ T}) + μ.real (E ∩ {ω | τ ω = T + 1}) := by
  have hu : E = (E ∩ {ω | τ ω ≤ T}) ∪ (E ∩ {ω | τ ω = T + 1}) := by
    ext ω
    constructor
    · intro h
      by_cases ht : τ ω ≤ T
      · exact Or.inl ⟨h, ht⟩
      · exact Or.inr ⟨h, by change τ ω = T + 1; have := hbound ω; omega⟩
    · rintro (h | h) <;> exact h.1
  have hd : Disjoint (E ∩ {ω | τ ω ≤ T}) (E ∩ {ω | τ ω = T + 1}) := by
    apply Set.disjoint_left.mpr
    intro ω hleft hright
    have hle := hleft.2
    have heq := hright.2
    simp only [mem_setOf_eq] at hle heq
    omega
  nth_rw 1 [hu]
  exact measureReal_union (μ := μ) hd (hE.inter (measurableSet_eq_fun hτ measurable_const))

/-- The four lines in the paper: partition the original event, use certain
success on replacement and equality on no replacement, enlarge the first
intersection, then recombine the auxiliary event. -/
theorem firstReplacement_probability_transfer {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsFiniteMeasure μ] (τ : Ω → ℕ) (T : ℕ)
    (hτ : Measurable τ) (hbound : ∀ ω, τ ω ≤ T + 1)
    (E F : Set Ω) (hE : MeasurableSet E) (hF : MeasurableSet F)
    (hcross : {ω | τ ω ≤ T} ⊆ E)
    (hnever : E ∩ {ω | τ ω = T + 1} = F ∩ {ω | τ ω = T + 1}) :
    μ.real F ≤ μ.real E := by
  have hhit : E ∩ {ω | τ ω ≤ T} = {ω | τ ω ≤ T} :=
    Set.inter_eq_right.mpr hcross
  calc
    μ.real E = μ.real (E ∩ {ω | τ ω ≤ T}) +
        μ.real (E ∩ {ω | τ ω = T + 1}) :=
      measureReal_firstReplacement_partition μ τ T hτ hbound E hE
    _ = μ.real {ω | τ ω ≤ T} + μ.real (F ∩ {ω | τ ω = T + 1}) := by rw [hhit, hnever]
    _ ≥ μ.real (F ∩ {ω | τ ω ≤ T}) + μ.real (F ∩ {ω | τ ω = T + 1}) :=
      add_le_add (measureReal_mono (μ := μ)
        (show F ∩ {ω | τ ω ≤ T} ⊆ {ω | τ ω ≤ T} from Set.inter_subset_right)) le_rfl
    _ = μ.real F := (measureReal_firstReplacement_partition μ τ T hτ hbound F hF).symm

/-- For each fixed oblivious noise table, the original learner's regret-tail
probability is at least the auxiliary learner's, over the same private seed. -/
theorem auxiliary_seed_probability_le_original {d m T : ℕ}
    (P : Policy d m) (hm : 1 ≤ m) (hmd : m ≤ d)
    (budget : ℝ) (hb : 0 < budget) (defaultAction : MSetAction d m)
    (Delta : ℝ) (hDelta : 0 ≤ Delta) (hsmall : (m : ℝ) * Delta ≤ 1 / 2 ^ 13)
    (i : Fin d) (hi : i ∈ confidenceCandidates d m hmd) (Z : Table T) :
    let L := (plantedTableLossProcess hm hmd Delta hDelta hsmall i T).at Z
    (seedMeasure T).real
      {r | budget ≤ pathRegret L T (auxiliaryRun P hmd r budget defaultAction L T)} ≤
    (runLaw P L T).real {h | budget ≤ pathRegret L T h} := by
  dsimp only
  letI : Nonempty (MSetAction d m) := nonempty_MSetAction hmd
  let L := (plantedTableLossProcess hm hmd Delta hDelta hsmall i T).at Z
  have hset : MeasurableSet {h : History d m T | budget ≤ pathRegret L T h} :=
    measurableSet_le measurable_const (measurable_pathRegret L T)
  let τ : Seeds T → ℕ := fun r =>
    firstReplacementTime (fixedChoose P hmd r) hmd budget defaultAction L T
  let E : Set (Seeds T) := {r | budget ≤ pathRegret L T
    (deterministicRun (fixedChoose P hmd r) L T)}
  let F : Set (Seeds T) := {r | budget ≤ pathRegret L T
    (auxiliaryRun P hmd r budget defaultAction L T)}
  have hτ : Measurable τ := measurable_firstReplacementTime (fixedChoose P hmd)
    (measurable_fixedChoose_joint P hmd) hmd budget defaultAction L T
  have hbound (r : Seeds T) : τ r ≤ T + 1 :=
    (firstReplacementTime_bounds (fixedChoose P hmd r) hmd budget defaultAction L T).2
  have horig : Measurable (fun r : Seeds T => deterministicRun (fixedChoose P hmd r) L T) := by
    apply measurable_deterministicRun (fun t r h => fixedChoose P hmd r t h)
    · exact measurable_fixedChoose_joint P hmd
    · intro t; exact (L.measurable_itemLoss t).comp measurable_snd
  have haux : Measurable (fun r : Seeds T => auxiliaryRun P hmd r budget defaultAction L T) := by
    apply measurable_deterministicRun (fun t r h => auxiliaryChoose P hmd r budget defaultAction t h)
    · exact measurable_auxiliaryChoose_joint P hmd budget defaultAction
    · intro t; exact (L.measurable_itemLoss t).comp measurable_snd
  have hE : MeasurableSet E := hset.preimage horig
  have hF : MeasurableSet F := hset.preimage haux
  have hcross : {r | τ r ≤ T} ⊆ E := by
    intro r hr
    exact (firstReplacementTime_crossing (fixedChoose P hmd r) hm hmd budget defaultAction L hr).trans
      (penalty_le_planted_regret hm hmd Delta hDelta hsmall i hi Z T _)
  have hnever : E ∩ {r | τ r = T + 1} = F ∩ {r | τ r = T + 1} := by
    ext r
    by_cases hr : τ r = T + 1
    · have heq := (firstReplacementTime_prefix (T := T) (fixedChoose P hmd r) hmd
        budget defaultAction L T (by change T < τ r; omega)).1
      simp only [E, F, mem_inter_iff, mem_setOf_eq, hr, and_true, auxiliaryRun,
        auxiliaryChoose, heq]
    · simp only [mem_inter_iff, mem_setOf_eq, hr, and_false]
  have hprob := firstReplacement_probability_transfer (seedMeasure T) τ T hτ hbound E F hE hF
    hcross hnever
  have hevent : (seedMeasure T).real E = (runLaw P L T).real {h | budget ≤ pathRegret L T h} := by
    rw [measureReal_def, measureReal_def, ← seedRun_event_probability P hmd L T _ hset]
    apply congrArg ENNReal.toReal
    congr 1
    ext r
    change (budget ≤ pathRegret L T (deterministicRun (fixedChoose P hmd r) L T)) ↔ _
    rw [deterministicRun_fixedChoose_eq_seedRun P hmd r L T le_rfl]
    rfl
  exact hprob.trans_eq hevent

end

end MsetsPaper.Lower.ConfidenceOblivious
