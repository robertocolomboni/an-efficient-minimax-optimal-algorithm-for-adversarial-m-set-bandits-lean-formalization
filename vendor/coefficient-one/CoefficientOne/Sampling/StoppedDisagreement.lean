import CoefficientOne.Sampling.FrozenCoupling
import CoefficientOne.Sampling.ConditionalLaw
import CoefficientOne.Sampling.ContinuationDisagreement

/-! # Conditioning the second disagreement at the actual first disagreement -/

open MeasureTheory Set
open scoped BigOperators ENNReal

namespace CoefficientOne.Sampling
noncomputable section

theorem stoppedSeed_bound_finiteMarks {n : ℕ} {β : Type*} [Fintype β]
    (τ : Seed n → WithTop ℕ) (mark : Seed n → β)
    (hmark : ∀ b, StoppedObservableEvent τ {ω | mark ω = b})
    (hbound : ∀ ω, τ ω ≠ ⊤ → τ ω ≤ (n : WithTop ℕ))
    (C : β → (a : StopIndex n) → Set (PrefixOrders a.1.val (prefixReference a.2) ×
      FutureUniforms a.1.val (prefixReference a.2)))
    (hC : ∀ b a, MeasurableSet (C b a)) (c : ℝ≥0∞)
    (hc : ∀ b a, prefixFutureMeasure a.1.val (prefixReference a.2) (C b a) ≤ c) :
    seedMeasure n (⋃ b : β, stoppedFutureEvent (hmark b) (C b)) ≤
      seedMeasure n {ω | τ ω ≠ ⊤} * c := by
  classical
  have hm (b : β) : MeasurableSet ({ω | mark ω = b} ∩ {ω | τ ω ≠ ⊤}) := by
    rw [← iUnion_stoppedSlice τ {ω | mark ω = b} hbound]
    exact MeasurableSet.iUnion (measurableSet_stoppedSlice (hmark b))
  have hd : Pairwise (fun b d : β => Disjoint
      ({ω | mark ω = b} ∩ {ω | τ ω ≠ ⊤}) ({ω | mark ω = d} ∩ {ω | τ ω ≠ ⊤})) := by
    intro b d hbd
    exact Set.disjoint_left.mpr fun ω hω hω' => hbd (hω.1.symm.trans hω'.1)
  have he : (⋃ b : β, {ω | mark ω = b} ∩ {ω | τ ω ≠ ⊤}) = {ω | τ ω ≠ ⊤} := by
    ext ω
    simp
  calc
    _ ≤ ∑' b : β, seedMeasure n (stoppedFutureEvent (hmark b) (C b)) := measure_iUnion_le _
    _ ≤ ∑' b : β, seedMeasure n ({ω | mark ω = b} ∩ {ω | τ ω ≠ ⊤}) * c :=
      ENNReal.tsum_le_tsum fun b => stoppedSeed_bound (hmark b) hbound (C b) (hC b) c (hc b)
    _ = (∑' b : β, seedMeasure n ({ω | mark ω = b} ∩ {ω | τ ω ≠ ⊤})) * c := by
      simp only [tsum_fintype, Finset.sum_mul]
    _ = _ := by rw [← measure_iUnion hd hm, he]

variable {n : ℕ}

def stoppedSelected (w v : Fin n → ℝ) (k : ℕ) (ω : Seed n) : Finset (Fin n) :=
  historySelected v k ((firstDisagreement w v k ω).untopD 0) ω

theorem stoppedSelected_eq_at_stop (w v : Fin n → ℝ) (k t : ℕ) (ω : Seed n)
    (ht : firstDisagreement w v k ω = (t : WithTop ℕ)) :
    stoppedSelected w v k ω = historySelected v k t ω := by
  unfold stoppedSelected
  rw [ht]
  rfl

theorem stoppedSelected_observable (w v : Fin n → ℝ) (k : ℕ) (A : Finset (Fin n)) :
    StoppedObservableEvent (firstDisagreement w v k) {ω | stoppedSelected w v k ω = A} := by
  intro t
  have he : {ω | stoppedSelected w v k ω = A} ∩
      {ω | firstDisagreement w v k ω = (t.val : WithTop ℕ)} =
      {ω | historySelected v k t.val ω = A} ∩
      {ω | firstDisagreement w v k ω = (t.val : WithTop ℕ)} := by
    ext ω
    constructor
    · rintro ⟨hA, ht⟩
      exact ⟨(stoppedSelected_eq_at_stop w v k t.val ω ht).symm.trans hA, ht⟩
    · rintro ⟨hA, ht⟩
      exact ⟨(stoppedSelected_eq_at_stop w v k t.val ω ht).trans hA, ht⟩
  rw [he]
  exact (historySelected_prefixObservable v k t.val A).inter
    (firstDisagreement_fiber_prefixObservable w v k t.val)

def stoppedContinuationDisagreement (w v : Fin n → ℝ) (k : ℕ) (A : Finset (Fin n))
    (a : StopIndex n) : Set (PrefixOrders a.1.val (prefixReference a.2) ×
      FutureUniforms a.1.val (prefixReference a.2)) :=
  if k - A.card ≤ (remainingSet a.1.val (prefixReference a.2)).card then
    {z | futureContinuation w a.1.val (prefixReference a.2) (k - A.card) z ≠
      futureContinuation v a.1.val (prefixReference a.2) (k - A.card) z}
  else ∅

theorem measurableSet_stoppedContinuationDisagreement (w v : Fin n → ℝ) (k : ℕ)
    (A : Finset (Fin n)) (a : StopIndex n) :
    MeasurableSet (stoppedContinuationDisagreement w v k A a) := by
  unfold stoppedContinuationDisagreement
  split_ifs
  · exact (measurableSet_eq_fun (measurable_futureContinuation w _ _ _)
      (measurable_futureContinuation v _ _ _)).compl
  · exact MeasurableSet.empty

theorem secondDisagreement_mem_stoppedFuture (w v : Fin n → ℝ) (k : ℕ) (hk : k ≤ n)
    (A : Finset (Fin n)) (ω : Seed n) (hA : stoppedSelected w v k ω = A)
    (hE : ω ∈ secondDisagreementEvent w v k) :
    ω ∈ stoppedFutureEvent (stoppedSelected_observable w v k A)
      (stoppedContinuationDisagreement w v k A) := by
  classical
  have hD := secondDisagreementEvent_subset_first w v k hE
  have hs : ω ∈ ⋃ a : StopIndex n,
      stoppedSlice (firstDisagreement w v k) {ω | stoppedSelected w v k ω = A} a := by
    rw [iUnion_stoppedSlice _ _ (firstDisagreement_le_dimension w v k)]
    exact ⟨hA, hD⟩
  obtain ⟨a, ha⟩ := Set.mem_iUnion.mp hs
  have ht := ha.2.1
  have hhist : historySelected v k a.1.val ω = A :=
    (stoppedSelected_eq_at_stop w v k a.1.val ω ht).symm.trans hA
  have hpast := ha
  rw [← stoppedPastSection_event (stoppedSelected_observable w v k A) a] at hpast
  obtain ⟨z, hz, rfl⟩ := hpast
  apply Set.mem_iUnion.mpr
  refine ⟨a, z, ⟨hz.1, ?_⟩, rfl⟩
  have hr := historyQuota_le_remaining_card v k a.1.val hk (assemblePrefixSeed _ _ z)
  have hq : historyQuota v k a.1.val (assemblePrefixSeed _ _ z) = k - A.card := by
    rw [historyQuota, hhist]
  rw [hq] at hr
  have hR : historyRemaining a.1.val (assemblePrefixSeed _ _ z) =
      remainingSet a.1.val (prefixReference a.2) := by
    exact prefixOrder_drop_toFinset a.1.val (prefixReference a.2) z.1
  rw [hR] at hr
  change (z.1, z.2.2) ∈ stoppedContinuationDisagreement w v k A a
  rw [stoppedContinuationDisagreement, if_pos hr]
  intro he
  have hf (b : Fin n → ℝ) :
      futureContinuation b a.1.val (prefixReference a.2) (k - A.card) (z.1, z.2.2) =
        sequentialList b (fun i => ((assemblePrefixSeed _ _ z).2 i : ℝ))
          ((List.ofFn (assemblePrefixSeed _ _ z).1).drop a.1.val) (k - A.card) := by
    have h := futureContinuation_restrict b a.1.val (prefixReference a.2) (k - A.card)
      z.1 (assemblePrefixSeed _ _ z).2
    simpa [assemblePrefixSeed, cubeSampler] using h
  have hfrag :
      sequentialList w (fun i => ((assemblePrefixSeed _ _ z).2 i : ℝ))
        ((List.ofFn (assemblePrefixSeed _ _ z).1).drop a.1.val)
        (historyQuota v k a.1.val (assemblePrefixSeed _ _ z)) =
      sequentialList v (fun i => ((assemblePrefixSeed _ _ z).2 i : ℝ))
        ((List.ofFn (assemblePrefixSeed _ _ z).1).drop a.1.val)
        (historyQuota v k a.1.val (assemblePrefixSeed _ _ z)) := by
    rw [hq, ← hf w, ← hf v]
    exact he
  have hne := ((mem_secondDisagreementEvent_iff w v k _).mp hE).2
  rw [frozenSampler_eq_at_stop w v k a.1.val _ ht] at hne
  apply hne
  rw [sequentialSampler_eq_history_union_continuation v k a.1.val]
  rw [← hfrag]
  rfl

theorem secondDisagreement_probability_le (w v : Fin n → ℝ)
    (hw : ∀ i, 0 < w i) (hv : ∀ i, 0 < v i) (k : ℕ) (hk : k ≤ n)
    (δ : ℝ) (hδ : 0 ≤ δ)
    (hthreshold : ∀ R q, q ≤ R.card → ∀ i ∈ R,
      |quotaThreshold w R q i - quotaThreshold v R q i| ≤ δ) :
    seedMeasure n (secondDisagreementEvent w v k) ≤
      seedMeasure n (firstDisagreementEvent w v k) * ENNReal.ofReal ((n : ℝ) * δ) := by
  have hsub : secondDisagreementEvent w v k ⊆
      ⋃ A : Finset (Fin n), stoppedFutureEvent (stoppedSelected_observable w v k A)
        (stoppedContinuationDisagreement w v k A) := by
    intro ω hω
    exact Set.mem_iUnion.mpr ⟨stoppedSelected w v k ω,
      secondDisagreement_mem_stoppedFuture w v k hk _ ω rfl hω⟩
  apply (measure_mono hsub).trans
  apply stoppedSeed_bound_finiteMarks (firstDisagreement w v k) (stoppedSelected w v k)
    (stoppedSelected_observable w v k) (firstDisagreement_le_dimension w v k)
    (stoppedContinuationDisagreement w v k) (measurableSet_stoppedContinuationDisagreement w v k)
  intro A a
  unfold stoppedContinuationDisagreement
  split_ifs with hr
  · exact futureContinuation_disagreement_le w v hw hv a.1.val (prefixReference a.2)
      (k - A.card) hr δ hδ hthreshold
  · simp

theorem secondDisagreement_probability_le_real (w v : Fin n → ℝ)
    (hw : ∀ i, 0 < w i) (hv : ∀ i, 0 < v i) (k : ℕ) (hk : k ≤ n)
    (δ : ℝ) (hδ : 0 ≤ δ)
    (hthreshold : ∀ R q, q ≤ R.card → ∀ i ∈ R,
      |quotaThreshold w R q i - quotaThreshold v R q i| ≤ δ) :
    (seedMeasure n (secondDisagreementEvent w v k)).toReal ≤
      (seedMeasure n (firstDisagreementEvent w v k)).toReal * ((n : ℝ) * δ) := by
  have h := secondDisagreement_probability_le w v hw hv k hk δ hδ hthreshold
  have ht : seedMeasure n (firstDisagreementEvent w v k) * ENNReal.ofReal ((n : ℝ) * δ) ≠ ⊤ :=
    ENNReal.mul_ne_top (measure_ne_top _ _) ENNReal.ofReal_ne_top
  have hr := ENNReal.toReal_mono ht h
  simpa only [ENNReal.toReal_mul, ENNReal.toReal_ofReal (mul_nonneg (Nat.cast_nonneg n) hδ)] using hr

end
end CoefficientOne.Sampling
