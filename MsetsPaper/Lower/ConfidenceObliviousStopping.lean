import MsetsPaper.Lower.ConfidenceOblivious
import MsetsPaper.Probability.DeterministicRun

/-! # Stop before the budget-crossing proposal and remain stopped forever

The original rule is deterministic after fixing the private seed. The flag
remembers rejected proposals, not just the emitted actions. This is the
absorbing auxiliary algorithm in P4, not a reject-and-resume modification.
-/

namespace MsetsPaper.Lower.ConfidenceOblivious

open MsetsLower MsetsLower.Lower MsetsLower.Lower.Confidence MsetsPaper.Probability
open MeasureTheory ProbabilityTheory Set
open scoped ENNReal ProbabilityTheory

noncomputable section

def stoppedBefore {d m : ℕ}
    (choose : (t : ℕ) → History d m t → MSetAction d m) (hmd : m ≤ d) (budget : ℝ) :
    (t : ℕ) → History d m t → Prop
  | 0, _ => False
  | t + 1, h => stoppedBefore choose hmd budget t h.1 ∨
      budget ≤ cumulativePenalty hmd t h.1 + candidatePenalty hmd (choose t h.1)

def wouldStop {d m : ℕ}
    (choose : (t : ℕ) → History d m t → MSetAction d m) (hmd : m ≤ d) (budget : ℝ)
    (t : ℕ) (h : History d m t) : Prop :=
  stoppedBefore choose hmd budget t h ∨
    budget ≤ cumulativePenalty hmd t h + candidatePenalty hmd (choose t h)

def stoppedChoose {d m : ℕ}
    (choose : (t : ℕ) → History d m t → MSetAction d m) (hmd : m ≤ d) (budget : ℝ)
    (defaultAction : MSetAction d m) (t : ℕ) (h : History d m t) : MSetAction d m := by
  classical
  exact if wouldStop choose hmd budget t h then defaultAction else choose t h

theorem measurableSet_stoppedBefore_parametric {Ξ : Type*} [MeasurableSpace Ξ] {d m : ℕ}
    (choose : Ξ → (t : ℕ) → History d m t → MSetAction d m)
    (hchoose : ∀ t, Measurable (fun x : Ξ × History d m t => choose x.1 t x.2))
    (hmd : m ≤ d) (budget : ℝ) : ∀ t, MeasurableSet
      {x : Ξ × History d m t | stoppedBefore (choose x.1) hmd budget t x.2} := by
  intro t
  induction t with
  | zero => simp [stoppedBefore]
  | succ t ih =>
      have hprefix : Measurable (fun x : Ξ × History d m (t + 1) => (x.1, x.2.1)) :=
        measurable_fst.prodMk measurable_snd.fst
      have hD : Measurable (fun x : Ξ × History d m (t + 1) => cumulativePenalty hmd t x.2.1) :=
        (measurable_cumulativePenalty hmd t).comp measurable_snd.fst
      have hpen := (measurable_of_finite (candidatePenalty hmd)).comp ((hchoose t).comp hprefix)
      exact (ih.preimage hprefix).union (measurableSet_le measurable_const (hD.add hpen))

theorem measurableSet_wouldStop_parametric {Ξ : Type*} [MeasurableSpace Ξ] {d m : ℕ}
    (choose : Ξ → (t : ℕ) → History d m t → MSetAction d m)
    (hchoose : ∀ t, Measurable (fun x : Ξ × History d m t => choose x.1 t x.2))
    (hmd : m ≤ d) (budget : ℝ) (t : ℕ) : MeasurableSet
      {x : Ξ × History d m t | wouldStop (choose x.1) hmd budget t x.2} := by
  exact (measurableSet_stoppedBefore_parametric choose hchoose hmd budget t).union
    (measurableSet_le measurable_const
      (((measurable_cumulativePenalty hmd t).comp measurable_snd).add
        ((measurable_of_finite (candidatePenalty hmd)).comp (hchoose t))))

theorem measurable_stoppedChoose_parametric {Ξ : Type*} [MeasurableSpace Ξ] {d m : ℕ}
    (choose : Ξ → (t : ℕ) → History d m t → MSetAction d m)
    (hchoose : ∀ t, Measurable (fun x : Ξ × History d m t => choose x.1 t x.2))
    (hmd : m ≤ d) (budget : ℝ) (defaultAction : MSetAction d m) (t : ℕ) :
    Measurable (fun x : Ξ × History d m t =>
      stoppedChoose (choose x.1) hmd budget defaultAction t x.2) := by
  classical
  exact Measurable.ite (measurableSet_wouldStop_parametric choose hchoose hmd budget t)
    measurable_const (hchoose t)

theorem measurable_stoppedChoose {d m : ℕ}
    (choose : (t : ℕ) → History d m t → MSetAction d m)
    (hchoose : ∀ t, Measurable (choose t)) (hmd : m ≤ d)
    (budget : ℝ) (defaultAction : MSetAction d m) (t : ℕ) :
    Measurable (stoppedChoose choose hmd budget defaultAction t) := by
  have h := measurable_stoppedChoose_parametric (Ξ := Unit) (fun _ => choose)
    (fun t => (hchoose t).comp measurable_snd) hmd budget defaultAction t
  exact h.comp (measurable_prodMk_left (x := ()))

def stoppedPolicy {d m : ℕ}
    (choose : (t : ℕ) → History d m t → MSetAction d m)
    (hchoose : ∀ t, Measurable (choose t)) (hmd : m ≤ d)
    (budget : ℝ) (defaultAction : MSetAction d m) : Policy d m :=
  Policy.deterministic (stoppedChoose choose hmd budget defaultAction)
    (measurable_stoppedChoose choose hchoose hmd budget defaultAction)

theorem stoppedChoose_eq_default_of_stopped {d m : ℕ}
    (choose : (t : ℕ) → History d m t → MSetAction d m) (hmd : m ≤ d)
    (budget : ℝ) (defaultAction : MSetAction d m) (t : ℕ) (h : History d m t)
    (hs : stoppedBefore choose hmd budget t h) :
    stoppedChoose choose hmd budget defaultAction t h = defaultAction := by
  simp only [stoppedChoose, if_pos (show wouldStop choose hmd budget t h from Or.inl hs)]

theorem stoppedRun_penalty_lt {d m : ℕ}
    (choose : (t : ℕ) → History d m t → MSetAction d m) (hmd : m ≤ d)
    (budget : ℝ) (hb : 0 < budget) (defaultAction : MSetAction d m)
    (hdefault : candidatePenalty hmd defaultAction = 0) (L : LossProcess d m) :
    ∀ t, cumulativePenalty hmd t
      (deterministicRun (stoppedChoose choose hmd budget defaultAction) L t) < budget := by
  intro t
  induction t with
  | zero => simpa [deterministicRun, cumulativePenalty, History.actionSum] using hb
  | succ t ih =>
      let h := deterministicRun (stoppedChoose choose hmd budget defaultAction) L t
      change cumulativePenalty hmd t h +
        candidatePenalty hmd (stoppedChoose choose hmd budget defaultAction t h) < budget
      by_cases hs : wouldStop choose hmd budget t h
      · simpa only [stoppedChoose, if_pos hs, hdefault, add_zero] using ih
      · have hc : cumulativePenalty hmd t h + candidatePenalty hmd (choose t h) < budget :=
          lt_of_not_ge (fun hc => hs (Or.inr hc))
        simpa only [stoppedChoose, if_neg hs] using hc

/-- Either the original learner has already crossed the target penalty, or
the two complete histories still coincide and the auxiliary learner has not
stopped. This is the first-replacement coupling argument in inductive form. -/
theorem stoppedRun_coupling {d m : ℕ}
    (choose : (t : ℕ) → History d m t → MSetAction d m) (hm : 1 ≤ m) (hmd : m ≤ d)
    (budget : ℝ) (hb : 0 < budget) (defaultAction : MSetAction d m) (L : LossProcess d m) :
    ∀ t, budget ≤ cumulativePenalty hmd t (deterministicRun choose L t) ∨
      (deterministicRun choose L t =
        deterministicRun (stoppedChoose choose hmd budget defaultAction) L t ∧
       ¬ stoppedBefore choose hmd budget t
        (deterministicRun (stoppedChoose choose hmd budget defaultAction) L t)) := by
  intro t
  induction t with
  | zero => exact Or.inr ⟨rfl, not_false⟩
  | succ t ih =>
      rcases ih with hcross | ⟨heq, hnot⟩
      · left
        change budget ≤ cumulativePenalty hmd t (deterministicRun choose L t) +
          candidatePenalty hmd (choose t (deterministicRun choose L t))
        exact hcross.trans (le_add_of_nonneg_right (candidatePenalty_mem_Ico hm hmd _).1)
      · let h := deterministicRun choose L t
        have hsnot : ¬ stoppedBefore choose hmd budget t h := by
          simpa only [h, ← heq] using hnot
        by_cases hc : budget ≤ cumulativePenalty hmd t h + candidatePenalty hmd (choose t h)
        · exact Or.inl hc
        · right
          have hs : ¬ wouldStop choose hmd budget t h := by
            rintro (hh | hh)
            · exact hsnot hh
            · exact hc hh
          have ha : stoppedChoose choose hmd budget defaultAction t h = choose t h :=
            by simp only [stoppedChoose, if_neg hs]
          have heq' : deterministicRun choose L (t + 1) =
              deterministicRun (stoppedChoose choose hmd budget defaultAction) L (t + 1) := by
            simp only [deterministicRun, ← heq]
            change (h, (choose t h, actionLoss (choose t h) (L.itemLoss t h))) =
              (h, (stoppedChoose choose hmd budget defaultAction t h,
                actionLoss (stoppedChoose choose hmd budget defaultAction t h) (L.itemLoss t h)))
            rw [ha]
          refine ⟨heq', ?_⟩
          rw [← heq']
          change ¬ (stoppedBefore choose hmd budget t h ∨
            budget ≤ cumulativePenalty hmd t h + candidatePenalty hmd (choose t h))
          exact hs

/-- The manuscript's first replacement round, numbered from one. The value
`T+1` denotes no replacement during the first `T` rounds. A replacement is
the rejection of a proposal, even when that proposal equals the default. -/
def firstReplacementTime {d m : ℕ}
    (choose : (t : ℕ) → History d m t → MSetAction d m) (hmd : m ≤ d)
    (budget : ℝ) (defaultAction : MSetAction d m) (L : LossProcess d m) (T : ℕ) : ℕ := by
  classical
  exact Nat.find (show ∃ k : ℕ, k = T + 1 ∨ (1 ≤ k ∧ k ≤ T ∧
    wouldStop choose hmd budget (k - 1)
      (deterministicRun (stoppedChoose choose hmd budget defaultAction) L (k - 1))) from
    ⟨T + 1, Or.inl rfl⟩)

theorem firstReplacementTime_spec {d m : ℕ}
    (choose : (t : ℕ) → History d m t → MSetAction d m) (hmd : m ≤ d)
    (budget : ℝ) (defaultAction : MSetAction d m) (L : LossProcess d m) (T : ℕ) :
    let τ := firstReplacementTime choose hmd budget defaultAction L T
    τ = T + 1 ∨ (1 ≤ τ ∧ τ ≤ T ∧ wouldStop choose hmd budget (τ - 1)
      (deterministicRun (stoppedChoose choose hmd budget defaultAction) L (τ - 1))) := by
  classical
  dsimp only
  unfold firstReplacementTime
  exact Nat.find_spec (show ∃ k : ℕ, k = T + 1 ∨ (1 ≤ k ∧ k ≤ T ∧
    wouldStop choose hmd budget (k - 1)
      (deterministicRun (stoppedChoose choose hmd budget defaultAction) L (k - 1))) from
    ⟨T + 1, Or.inl rfl⟩)

theorem firstReplacementTime_bounds {d m : ℕ}
    (choose : (t : ℕ) → History d m t → MSetAction d m) (hmd : m ≤ d)
    (budget : ℝ) (defaultAction : MSetAction d m) (L : LossProcess d m) (T : ℕ) :
    1 ≤ firstReplacementTime choose hmd budget defaultAction L T ∧
      firstReplacementTime choose hmd budget defaultAction L T ≤ T + 1 := by
  have h := firstReplacementTime_spec choose hmd budget defaultAction L T
  rcases h with h | ⟨hlo, hhi, _⟩ <;> omega

theorem not_wouldStop_before_firstReplacementTime {d m T t : ℕ}
    (choose : (t : ℕ) → History d m t → MSetAction d m) (hmd : m ≤ d)
    (budget : ℝ) (defaultAction : MSetAction d m) (L : LossProcess d m)
    (ht : t + 1 < firstReplacementTime choose hmd budget defaultAction L T) :
    ¬ wouldStop choose hmd budget t
      (deterministicRun (stoppedChoose choose hmd budget defaultAction) L t) := by
  classical
  intro hs
  have hb := firstReplacementTime_bounds choose hmd budget defaultAction L T
  have hsmall := Nat.find_min (show ∃ k : ℕ, k = T + 1 ∨ (1 ≤ k ∧ k ≤ T ∧
    wouldStop choose hmd budget (k - 1)
      (deterministicRun (stoppedChoose choose hmd budget defaultAction) L (k - 1))) from
    ⟨T + 1, Or.inl rfl⟩) ht
  apply hsmall
  exact Or.inr ⟨by omega, by omega, by simpa using hs⟩

/-- Before the first replacement, the histories (hence actions and feedback
already emitted) agree, and no earlier proposal has been rejected. -/
theorem firstReplacementTime_prefix {d m T : ℕ}
    (choose : (t : ℕ) → History d m t → MSetAction d m) (hmd : m ≤ d)
    (budget : ℝ) (defaultAction : MSetAction d m) (L : LossProcess d m) :
    ∀ t, t < firstReplacementTime choose hmd budget defaultAction L T →
      deterministicRun choose L t =
        deterministicRun (stoppedChoose choose hmd budget defaultAction) L t ∧
      ¬ stoppedBefore choose hmd budget t
        (deterministicRun (stoppedChoose choose hmd budget defaultAction) L t) := by
  intro t
  induction t with
  | zero => intro _; exact ⟨rfl, not_false⟩
  | succ t ih =>
    intro ht
    have heq := (ih (by omega)).1
    have hn := not_wouldStop_before_firstReplacementTime choose hmd budget defaultAction L ht
    constructor
    · simp only [deterministicRun, heq]
      rw [show stoppedChoose choose hmd budget defaultAction t
        (deterministicRun (stoppedChoose choose hmd budget defaultAction) L t) =
        choose t (deterministicRun (stoppedChoose choose hmd budget defaultAction) L t) from
        by simp only [stoppedChoose, if_neg hn]]
    · exact hn

theorem firstReplacementTime_crossing {d m T : ℕ}
    (choose : (t : ℕ) → History d m t → MSetAction d m) (hm : 1 ≤ m) (hmd : m ≤ d)
    (budget : ℝ) (defaultAction : MSetAction d m) (L : LossProcess d m)
    (hτ : firstReplacementTime choose hmd budget defaultAction L T ≤ T) :
    budget ≤ cumulativePenalty hmd T (deterministicRun choose L T) := by
  let τ := firstReplacementTime choose hmd budget defaultAction L T
  have hb := firstReplacementTime_bounds choose hmd budget defaultAction L T
  have hs := firstReplacementTime_spec choose hmd budget defaultAction L T
  have hτpos : 1 ≤ τ := hb.1
  have hτle : τ ≤ T := hτ
  have hstop : wouldStop choose hmd budget (τ - 1)
      (deterministicRun (stoppedChoose choose hmd budget defaultAction) L (τ - 1)) := by
    rcases hs with hs | ⟨_, _, hs⟩
    · omega
    · exact hs
  obtain ⟨heq, hnot⟩ := firstReplacementTime_prefix (T := T) choose hmd budget defaultAction L
    (τ - 1) (by omega)
  have hcross : budget ≤ cumulativePenalty hmd τ (deterministicRun choose L τ) := by
    have hp := hstop.resolve_left hnot
    have he : τ = (τ - 1) + 1 := by omega
    rw [he]
    change budget ≤ cumulativePenalty hmd (τ - 1) (deterministicRun choose L (τ - 1)) +
      candidatePenalty hmd (choose (τ - 1) (deterministicRun choose L (τ - 1)))
    simpa only [heq] using hp
  have hmono : Monotone (fun t => cumulativePenalty hmd t (deterministicRun choose L t)) := by
    apply monotone_nat_of_le_succ
    intro t
    change cumulativePenalty hmd t (deterministicRun choose L t) ≤
      cumulativePenalty hmd t (deterministicRun choose L t) + _
    exact le_add_of_nonneg_right (candidatePenalty_mem_Ico hm hmd _).1
  exact hcross.trans (hmono hτle)

theorem firstReplacementTime_eq_horizon_iff {d m T : ℕ}
    (choose : (t : ℕ) → History d m t → MSetAction d m) (hmd : m ≤ d)
    (budget : ℝ) (defaultAction : MSetAction d m) (L : LossProcess d m) :
    firstReplacementTime choose hmd budget defaultAction L T = T + 1 ↔
      ∀ t < T, ¬ wouldStop choose hmd budget t
        (deterministicRun (stoppedChoose choose hmd budget defaultAction) L t) := by
  constructor
  · intro heq t ht
    apply not_wouldStop_before_firstReplacementTime (T := T) choose hmd budget defaultAction L
    omega
  · intro hnone
    rcases firstReplacementTime_spec choose hmd budget defaultAction L T with heq | ⟨hpos, hle, hs⟩
    · exact heq
    · exact False.elim (hnone _ (by omega) hs)

/-- For the zero-penalty default used in P4, the first rejected proposal
really differs from the emitted default action. Thus tau also literally
marks the first action replacement, not merely an internal flag change. -/
theorem firstReplacementTime_replaces_action {d m T : ℕ}
    (choose : (t : ℕ) → History d m t → MSetAction d m) (hmd : m ≤ d)
    (budget : ℝ) (hb : 0 < budget) (defaultAction : MSetAction d m)
    (hdefault : candidatePenalty hmd defaultAction = 0) (L : LossProcess d m)
    (hτ : firstReplacementTime choose hmd budget defaultAction L T ≤ T) :
    let s := firstReplacementTime choose hmd budget defaultAction L T - 1
    let h := deterministicRun (stoppedChoose choose hmd budget defaultAction) L s
    choose s h ≠ defaultAction ∧
      stoppedChoose choose hmd budget defaultAction s h = defaultAction := by
  dsimp only
  let τ := firstReplacementTime choose hmd budget defaultAction L T
  have hs := firstReplacementTime_spec choose hmd budget defaultAction L T
  have hstop : wouldStop choose hmd budget (τ - 1)
      (deterministicRun (stoppedChoose choose hmd budget defaultAction) L (τ - 1)) := by
    rcases hs with heq | ⟨_, _, hs⟩
    · omega
    · exact hs
  have hpos := (firstReplacementTime_bounds choose hmd budget defaultAction L T).1
  have hnot := (firstReplacementTime_prefix (T := T) choose hmd budget defaultAction L
    (τ - 1) (by omega)).2
  have hcross := hstop.resolve_left hnot
  have hprev := stoppedRun_penalty_lt choose hmd budget hb defaultAction hdefault L (τ - 1)
  constructor
  · intro heq
    change choose (τ - 1)
      (deterministicRun (stoppedChoose choose hmd budget defaultAction) L (τ - 1)) = defaultAction at heq
    rw [heq, hdefault, add_zero] at hcross
    exact (not_le_of_gt hprev) hcross
  · exact if_pos hstop

theorem measurable_firstReplacementTime {Ω : Type*} [MeasurableSpace Ω] {d m : ℕ}
    (choose : Ω → (t : ℕ) → History d m t → MSetAction d m)
    (hc : ∀ t, Measurable (fun x : Ω × History d m t => choose x.1 t x.2))
    (hmd : m ≤ d) (budget : ℝ) (defaultAction : MSetAction d m)
    (L : LossProcess d m) (T : ℕ) :
    Measurable (fun ω => firstReplacementTime (choose ω) hmd budget defaultAction L T) := by
  classical
  have hrun (t : ℕ) : Measurable (fun ω =>
      deterministicRun (stoppedChoose (choose ω) hmd budget defaultAction) L t) := by
    apply measurable_deterministicRun
      (fun t ω h => stoppedChoose (choose ω) hmd budget defaultAction t h)
    · exact measurable_stoppedChoose_parametric choose hc hmd budget defaultAction
    · intro s
      exact (L.measurable_itemLoss s).comp measurable_snd
  unfold firstReplacementTime
  apply measurable_find
  intro k
  have hs := (measurableSet_wouldStop_parametric choose hc hmd budget (k - 1)).preimage
    (measurable_id.prodMk (hrun (k - 1)))
  by_cases he : k = T + 1
  · simp [he]
  · by_cases hk : 1 ≤ k ∧ k ≤ T
    · simpa [he, hk.1, hk.2] using hs
    · simp only [he, false_or]
      convert MeasurableSet.empty using 1
      ext ω
      simp only [mem_setOf_eq, mem_empty_iff_false, iff_false, not_and]
      intro hlo hhi
      exact (hk ⟨hlo, hhi⟩).elim

theorem stoppedRun_regret_transfer {d m T : ℕ}
    (choose : (t : ℕ) → History d m t → MSetAction d m) (hm : 1 ≤ m) (hmd : m ≤ d)
    (budget : ℝ) (hb : 0 < budget) (defaultAction : MSetAction d m)
    (Delta : ℝ) (hDelta : 0 ≤ Delta) (hsmall : (m : ℝ) * Delta ≤ 1 / 2 ^ 13)
    (i : Fin d) (hi : i ∈ confidenceCandidates d m hmd) (Z : Table T) :
    let L := (plantedTableLossProcess hm hmd Delta hDelta hsmall i T).at Z
    budget ≤ pathRegret L T
      (deterministicRun (stoppedChoose choose hmd budget defaultAction) L T) →
    budget ≤ pathRegret L T (deterministicRun choose L T) := by
  dsimp only
  intro haux
  let L := (plantedTableLossProcess hm hmd Delta hDelta hsmall i T).at Z
  by_cases hτ : firstReplacementTime choose hmd budget defaultAction L T ≤ T
  · exact (firstReplacementTime_crossing choose hm hmd budget defaultAction L hτ).trans
      (penalty_le_planted_regret hm hmd Delta hDelta hsmall i hi Z T _)
  · have heq := (firstReplacementTime_prefix (T := T) choose hmd budget defaultAction L T
      (by omega)).1
    change budget ≤ pathRegret L T (deterministicRun choose L T)
    rw [heq]
    exact haux

end

end MsetsPaper.Lower.ConfidenceOblivious
