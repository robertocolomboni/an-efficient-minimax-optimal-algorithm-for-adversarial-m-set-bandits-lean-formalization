import MsetsPaper.Probability.PrivateSeedRunLaw
import MsetsPaper.Lower.OrdinaryNewRoute

/-! # New lower endpoints for arbitrary persistent-private-seed algorithms

Every wrapper constructs ONE behavioral policy from the learner before
invoking the lower theorem. The environment is selected only afterwards.
The final probability is over the original private seed, not a new sampler.
-/

namespace MsetsPaper.Lower.PrivateSeedEndpoints

open MsetsLower MsetsLower.Lower MsetsPaper.Probability
open MsetsPaper.Probability.PrivateSeed MeasureTheory Set
open scoped ENNReal

noncomputable section

variable {Ω : Type*} [MeasurableSpace Ω]

theorem private_regret_probability_eq {d m T : ℕ}
    (ν : Measure Ω) [IsProbabilityMeasure ν]
    (choose : (t : ℕ) → Ω → History d m t → MSetAction d m)
    (hc : ∀ t, Measurable (Function.uncurry (choose t))) (a : MSetAction d m)
    (L : LossProcess d m) (b : ℝ) :
    ν.real {r | b ≤ pathRegret L T (deterministicRun (fun t h => choose t r h) L T)} =
      (runLaw (behavioralPolicy ν choose hc a) L T).real {h | b ≤ pathRegret L T h} := by
  letI : Nonempty (MSetAction d m) := ⟨a⟩
  exact congrArg ENNReal.toReal (privateRun_event_probability ν choose hc a L T _
    (measurableSet_le measurable_const (measurable_pathRegret L T)))

theorem lower_bound_explicit {d m T : ℕ}
    (hd : 2 ≤ d) (hm : 1 ≤ m) (hmtop : m ≤ d - 1)
    {delta : ℝ} (hdelta : 0 < delta) (hsmall : delta ≤ (2 : ℝ) ^ (-36 : ℤ))
    (hT : Nat.ceil (64 * (d : ℝ) ^ 2 +
      4 * (d : ℝ) * (min m (d - m) : ℕ) ^ 2 * Real.log (1 / delta)) ≤ T)
    (ν : Measure Ω) [IsProbabilityMeasure ν]
    (choose : (t : ℕ) → Ω → History d m t → MSetAction d m)
    (hc : ∀ t, Measurable (Function.uncurry (choose t))) :
    ∃ L : LossProcess d m,
      (∀ t (h : History d m t) (a : MSetAction d m), actionLoss a (L.itemLoss t h) ∈ Icc (0 : ℝ) 1) ∧
      delta ≤ ν.real {r | (2 : ℝ) ^ (-43 : ℤ) * Real.sqrt ((d : ℝ) * T *
        (Real.log (d.choose m : ℝ) + Real.log (1 / delta))) ≤
          pathRegret L T (deterministicRun (fun t h => choose t r h) L T)} := by
  let a := Classical.choice (nonempty_MSetAction (show m ≤ d by omega))
  let P := behavioralPolicy ν choose hc a
  obtain ⟨L, hL, ht⟩ := NewRoute.lower_bound_explicit hd hm hmtop hdelta hsmall hT P
  refine ⟨L, hL, ?_⟩
  rw [private_regret_probability_eq ν choose hc a L]
  exact ht

theorem lower_action_count_sparse {d m T : ℕ}
    (hm : 1 ≤ m) (h2m : 2 * m ≤ d) (hT : 64 * d ^ 2 ≤ T)
    (hr : (m : ℝ) / d ≤ (2 : ℝ) ^ (-32 : ℤ))
    (ν : Measure Ω) [IsProbabilityMeasure ν]
    (choose : (t : ℕ) → Ω → History d m t → MSetAction d m)
    (hc : ∀ t, Measurable (Function.uncurry (choose t))) :
    ∃ L : LossProcess d m,
      (∀ t (h : History d m t) i, L.itemLoss t h i ∈ Icc (0 : ℝ) (1 / m)) ∧
      (1 : ℝ) / 8 ≤ ν.real {r | (2 : ℝ) ^ (-24 : ℤ) *
        Real.sqrt ((d : ℝ) * T * Real.log (d.choose m : ℝ)) ≤
          pathRegret L T (deterministicRun (fun t h => choose t r h) L T)} := by
  let a := Classical.choice (nonempty_MSetAction (show m ≤ d by omega))
  let P := behavioralPolicy ν choose hc a
  obtain ⟨L, hL, ht⟩ := SparseCapped.lower_action_count_sparse hm h2m hT hr P
  refine ⟨L, hL, ?_⟩
  rw [private_regret_probability_eq ν choose hc a L]
  exact ht

theorem lower_action_count_dense {d m T : ℕ}
    (hm : 1 ≤ m) (h2m : 2 * m ≤ d) (hT : 64 * d ^ 2 ≤ T)
    (hr : (2 : ℝ) ^ (-32 : ℤ) < (m : ℝ) / d)
    (ν : Measure Ω) [IsProbabilityMeasure ν]
    (choose : (t : ℕ) → Ω → History d m t → MSetAction d m)
    (hc : ∀ t, Measurable (Function.uncurry (choose t))) :
    ∃ L : LossProcess d m,
      (∀ t (h h' : History d m t), L.itemLoss t h = L.itemLoss t h') ∧
      (∀ t (h : History d m t) i, L.itemLoss t h i ∈ Icc (0 : ℝ) (1 / m)) ∧
      (2 : ℝ) ^ (-14 : ℤ) ≤ ν.real {r | (2 : ℝ) ^ (-42 : ℤ) *
        Real.sqrt ((d : ℝ) * T * Real.log (d.choose m : ℝ)) ≤
          pathRegret L T (deterministicRun (fun t h => choose t r h) L T)} := by
  let a := Classical.choice (nonempty_MSetAction (show m ≤ d by omega))
  let P := behavioralPolicy ν choose hc a
  obtain ⟨L, ho, hL, ht⟩ := DenseCommonNoise.lower_action_count_dense hm h2m hT hr P
  refine ⟨L, ho, hL, ?_⟩
  rw [private_regret_probability_eq ν choose hc a L]
  exact ht

/-- Paper-facing P2 for an arbitrary persistent private seed. A single
non-anticipating loss process is selected for the whole learner seed law. -/
theorem lower_action_count_sparse_action_losses {d m T : ℕ}
    (hm : 1 ≤ m) (h2m : 2 * m ≤ d) (hT : 64 * d ^ 2 ≤ T)
    (hr : (m : ℝ) / d ≤ (2 : ℝ) ^ (-32 : ℤ))
    (ν : Measure Ω) [IsProbabilityMeasure ν]
    (choose : (t : ℕ) → Ω → History d m t → MSetAction d m)
    (hc : ∀ t, Measurable (Function.uncurry (choose t))) :
    ∃ L : LossProcess d m,
      (∀ t (h : History d m t) (a : MSetAction d m),
        actionLoss a (L.itemLoss t h) ∈ Icc (0 : ℝ) 1) ∧
      (1 : ℝ) / 8 ≤ ν.real {r | (2 : ℝ) ^ (-24 : ℤ) *
        Real.sqrt ((d : ℝ) * T * Real.log (d.choose m : ℝ)) ≤
          pathRegret L T (deterministicRun (fun t h => choose t r h) L T)} := by
  let a := Classical.choice (nonempty_MSetAction (show m ≤ d by omega))
  let P := behavioralPolicy ν choose hc a
  obtain ⟨L, hL, ht⟩ := SparseCapped.lower_action_count_sparse_action_losses hm h2m hT hr P
  refine ⟨L, hL, ?_⟩
  rw [private_regret_probability_eq ν choose hc a L]
  exact ht

/-- Paper-facing P3 for an arbitrary persistent private seed. One oblivious
sequence is chosen before the seed is realized. -/
theorem lower_action_count_dense_action_losses {d m T : ℕ}
    (hm : 1 ≤ m) (h2m : 2 * m ≤ d) (hT : 64 * d ^ 2 ≤ T)
    (hr : (2 : ℝ) ^ (-32 : ℤ) < (m : ℝ) / d)
    (ν : Measure Ω) [IsProbabilityMeasure ν]
    (choose : (t : ℕ) → Ω → History d m t → MSetAction d m)
    (hc : ∀ t, Measurable (Function.uncurry (choose t))) :
    ∃ L : LossProcess d m,
      (∀ t (h h' : History d m t), L.itemLoss t h = L.itemLoss t h') ∧
      (∀ t (h : History d m t) (a : MSetAction d m),
        actionLoss a (L.itemLoss t h) ∈ Icc (0 : ℝ) 1) ∧
      (2 : ℝ) ^ (-14 : ℤ) ≤ ν.real {r | (2 : ℝ) ^ (-42 : ℤ) *
        Real.sqrt ((d : ℝ) * T * Real.log (d.choose m : ℝ)) ≤
          pathRegret L T (deterministicRun (fun t h => choose t r h) L T)} := by
  let a := Classical.choice (nonempty_MSetAction (show m ≤ d by omega))
  let P := behavioralPolicy ν choose hc a
  obtain ⟨L, ho, hL, ht⟩ := DenseCommonNoise.lower_action_count_dense_action_losses hm h2m hT hr P
  refine ⟨L, ho, hL, ?_⟩
  rw [private_regret_probability_eq ν choose hc a L]
  exact ht

theorem lower_confidence_oblivious {d m T : ℕ}
    (hm : 1 ≤ m) (h2m : 2 * m ≤ d)
    {delta : ℝ} (hdelta : 0 < delta) (hsmall : delta ≤ (2 : ℝ) ^ (-36 : ℤ))
    (hT : 4 * (d : ℝ) * (m : ℝ) ^ 2 * Real.log (1 / delta) ≤ T)
    (ν : Measure Ω) [IsProbabilityMeasure ν]
    (choose : (t : ℕ) → Ω → History d m t → MSetAction d m)
    (hc : ∀ t, Measurable (Function.uncurry (choose t))) :
    ∃ L : LossProcess d m,
      (∀ t (h h' : History d m t), L.itemLoss t h = L.itemLoss t h') ∧
      (∀ t (h : History d m t) i, L.itemLoss t h i ∈ Icc (0 : ℝ) (1 / m)) ∧
      delta ≤ ν.real {r | (2 : ℝ) ^ (-16 : ℤ) * Real.sqrt ((d : ℝ) * T * Real.log (1 / delta)) ≤
        pathRegret L T (deterministicRun (fun t h => choose t r h) L T)} := by
  let a := Classical.choice (nonempty_MSetAction (show m ≤ d by omega))
  let P := behavioralPolicy ν choose hc a
  obtain ⟨L, ho, hL, ht⟩ := ConfidenceOblivious.lower_confidence_oblivious hm h2m hdelta hsmall hT P
  refine ⟨L, ho, hL, ?_⟩
  rw [private_regret_probability_eq ν choose hc a L]
  exact ht

/-- Paper-facing P4 for an arbitrary persistent private seed. One oblivious
sequence is chosen for the whole seed law, before the seed is realized. -/
theorem lower_confidence_oblivious_action_losses {d m T : ℕ}
    (hm : 1 ≤ m) (h2m : 2 * m ≤ d)
    {delta : ℝ} (hdelta : 0 < delta) (hsmall : delta ≤ (2 : ℝ) ^ (-36 : ℤ))
    (hT : 4 * (d : ℝ) * (m : ℝ) ^ 2 * Real.log (1 / delta) ≤ T)
    (ν : Measure Ω) [IsProbabilityMeasure ν]
    (choose : (t : ℕ) → Ω → History d m t → MSetAction d m)
    (hc : ∀ t, Measurable (Function.uncurry (choose t))) :
    ∃ L : LossProcess d m,
      (∀ t (h h' : History d m t), L.itemLoss t h = L.itemLoss t h') ∧
      (∀ t (h : History d m t) (a : MSetAction d m),
        actionLoss a (L.itemLoss t h) ∈ Icc (0 : ℝ) 1) ∧
      delta ≤ ν.real {r | (2 : ℝ) ^ (-16 : ℤ) * Real.sqrt ((d : ℝ) * T * Real.log (1 / delta)) ≤
        pathRegret L T (deterministicRun (fun t h => choose t r h) L T)} := by
  let a := Classical.choice (nonempty_MSetAction (show m ≤ d by omega))
  let P := behavioralPolicy ν choose hc a
  obtain ⟨L, ho, hL, ht⟩ := ConfidenceOblivious.lower_confidence_oblivious_action_losses
    hm h2m hdelta hsmall hT P
  refine ⟨L, ho, hL, ?_⟩
  rw [private_regret_probability_eq ν choose hc a L]
  exact ht

theorem ordinary_bandits_lower_bound_explicit {K T : ℕ} (hK : 2 ≤ K)
    {delta : ℝ} (hdelta : 0 < delta) (hsmall : delta ≤ (2 : ℝ) ^ (-36 : ℤ))
    (hT : Nat.ceil (64 * (K : ℝ) ^ 2 + 4 * (K : ℝ) * Real.log (1 / delta)) ≤ T)
    (ν : Measure Ω) [IsProbabilityMeasure ν]
    (choose : (t : ℕ) → Ω → History K 1 t → MSetAction K 1)
    (hc : ∀ t, Measurable (Function.uncurry (choose t))) :
    ∃ L : LossProcess K 1,
      (∀ t (h : History K 1 t) i, L.itemLoss t h i ∈ Icc (0 : ℝ) 1) ∧
      delta ≤ ν.real {r | (2 : ℝ) ^ (-43 : ℤ) * Real.sqrt ((K : ℝ) * T *
        (Real.log (K : ℝ) + Real.log (1 / delta))) ≤
          pathRegret L T (deterministicRun (fun t h => choose t r h) L T)} := by
  let a := Classical.choice (nonempty_MSetAction (show 1 ≤ K by omega))
  let P := behavioralPolicy ν choose hc a
  obtain ⟨L, hL, ht⟩ := NewRoute.ordinary_bandits_lower_bound_explicit hK hdelta hsmall hT P
  refine ⟨L, hL, ?_⟩
  rw [private_regret_probability_eq ν choose hc a L]
  exact ht

end
end MsetsPaper.Lower.PrivateSeedEndpoints
