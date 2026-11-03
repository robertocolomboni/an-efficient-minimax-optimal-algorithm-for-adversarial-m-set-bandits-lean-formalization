import CoefficientOne.Sampling.SequentialHistory

/-!
# The law of the continuation after a revealed history

The residual law is derived from the prefix product-seed identity and the
fixed-order exactness theorem. Histories refer to the actual recursion.
-/

noncomputable section

open EffectiveResistance MeasureTheory Set
open scoped ENNReal unitInterval

namespace CoefficientOne.Sampling

def extendFutureUniforms {n : ℕ} (ℓ : ℕ) (ρ : Equiv.Perm (Fin n))
    (v : FutureUniforms ℓ ρ) : Fin n → ℝ :=
  fun i => if hi : ¬Revealed ℓ ρ i then (v ⟨i, hi⟩ : ℝ) else 0

theorem measurable_extendFutureUniforms {n : ℕ} (ℓ : ℕ) (ρ : Equiv.Perm (Fin n)) :
    Measurable (extendFutureUniforms ℓ ρ) := by
  apply measurable_pi_iff.mpr
  intro i
  by_cases hi : ¬Revealed ℓ ρ i
  · simp only [extendFutureUniforms, dif_pos hi]
    exact measurable_subtype_coe.comp (measurable_pi_apply (⟨i, hi⟩ : {i // ¬Revealed ℓ ρ i}))
  · simp only [extendFutureUniforms, dif_neg hi]
    exact measurable_const

def futureContinuation {n : ℕ} (w : Fin n → ℝ) (ℓ : ℕ) (ρ : Equiv.Perm (Fin n))
    (r : ℕ) (z : PrefixOrders ℓ ρ × FutureUniforms ℓ ρ) : Finset (Fin n) :=
  sequentialList w (extendFutureUniforms ℓ ρ z.2) ((List.ofFn z.1.val).drop ℓ) r

theorem measurable_futureContinuation {n : ℕ} (w : Fin n → ℝ) (ℓ : ℕ)
    (ρ : Equiv.Perm (Fin n)) (r : ℕ) : Measurable (futureContinuation w ℓ ρ r) := by
  apply measurable_from_prod_countable_right
  intro π
  exact (measurable_sequentialList ((List.ofFn π.val).drop ℓ) r).comp
    (measurable_const.prodMk (measurable_extendFutureUniforms ℓ ρ))

theorem prefixOrder_drop_toFinset {n : ℕ} (ℓ : ℕ) (ρ : Equiv.Perm (Fin n))
    (π : PrefixOrders ℓ ρ) : ((List.ofFn π.val).drop ℓ).toFinset = remainingSet ℓ ρ := by
  rw [permutation_drop_toFinset, prefixMatches_remainingSet π.property]

theorem futureContinuation_restrict {n : ℕ} (w : Fin n → ℝ) (ℓ : ℕ)
    (ρ : Equiv.Perm (Fin n)) (r : ℕ) (π : PrefixOrders ℓ ρ) (u : Fin n → unitInterval) :
    futureContinuation w ℓ ρ r (π, (splitUniforms ℓ ρ u).2) =
      cubeSampler w ((List.ofFn π.val).drop ℓ) r u := by
  apply sequentialList_uniforms_congr
  intro i hi
  have hmem : i ∈ remainingSet ℓ ρ := by
    rw [← prefixOrder_drop_toFinset ℓ ρ π]
    exact List.mem_toFinset.mpr hi
  have hnot : ¬Revealed ℓ ρ i := (Finset.mem_filter.mp hmem).2
  simp only [extendFutureUniforms, dif_pos hnot]
  rfl

theorem futureContinuation_fixedOrder_measurePreserving {n : ℕ}
    (w : Fin n → ℝ) (hw : ∀ i, 0 < w i) (ℓ : ℕ) (ρ : Equiv.Perm (Fin n))
    (r : ℕ) (hr : r ≤ (remainingSet ℓ ρ).card) (π : PrefixOrders ℓ ρ) :
    MeasurePreserving (fun v => futureContinuation w ℓ ρ r (π, v))
      (uniformCube {i // ¬Revealed ℓ ρ i})
      (lawMeasure (restrictedLaw w hw (remainingSet ℓ ρ) r hr)) := by
  have hn := nodup_drop (List.ofFn π.val) (List.nodup_ofFn.mpr π.val.injective) ℓ
  have hfull := cubeSampler_measurePreserving w hw ((List.ofFn π.val).drop ℓ) hn r
    (by rwa [← List.toFinset_card_of_nodup hn, prefixOrder_drop_toFinset])
  have hres : MeasurePreserving (fun u : Fin n → unitInterval => (splitUniforms ℓ ρ u).2)
      (uniformCube (Fin n)) (uniformCube {i // ¬Revealed ℓ ρ i}) :=
    measurePreserving_snd.comp (splitUniforms_measurePreserving ℓ ρ)
  have hm : Measurable (fun v => futureContinuation w ℓ ρ r (π, v)) :=
    (measurable_futureContinuation w ℓ ρ r).comp measurable_prodMk_left
  refine ⟨hm, ?_⟩
  rw [← hres.map_eq, Measure.map_map hm hres.measurable]
  have hf : (fun v => futureContinuation w ℓ ρ r (π, v)) ∘
      (fun u : Fin n → unitInterval => (splitUniforms ℓ ρ u).2) =
        cubeSampler w ((List.ofFn π.val).drop ℓ) r :=
    funext fun u => futureContinuation_restrict w ℓ ρ r π u
  rw [hf]
  simpa only [prefixOrder_drop_toFinset] using hfull.map_eq

theorem futureContinuation_measurePreserving {n : ℕ}
    (w : Fin n → ℝ) (hw : ∀ i, 0 < w i) (ℓ : ℕ) (ρ : Equiv.Perm (Fin n))
    (r : ℕ) (hr : r ≤ (remainingSet ℓ ρ).card) :
    MeasurePreserving (futureContinuation w ℓ ρ r) (prefixFutureMeasure ℓ ρ)
      (lawMeasure (restrictedLaw w hw (remainingSet ℓ ρ) r hr)) := by
  have h := (MeasurePreserving.id (uniformMeasure (PrefixOrders ℓ ρ))).skew_product
    (g := fun π v => futureContinuation w ℓ ρ r (π, v))
    (measurable_futureContinuation w ℓ ρ r)
    (Filter.Eventually.of_forall fun π =>
      (futureContinuation_fixedOrder_measurePreserving w hw ℓ ρ r hr π).map_eq)
  exact measurePreserving_snd.comp h

theorem futureContinuation_probability {n : ℕ}
    (w : Fin n → ℝ) (hw : ∀ i, 0 < w i) (ℓ : ℕ) (ρ : Equiv.Perm (Fin n))
    (r : ℕ) (hr : r ≤ (remainingSet ℓ ρ).card) (S : Finset (Fin n)) :
    prefixFutureMeasure ℓ ρ {z | futureContinuation w ℓ ρ r z = S} =
      ENNReal.ofReal (restrictedMass w (remainingSet ℓ ρ) r S) := by
  have h := (futureContinuation_measurePreserving w hw ℓ ρ r hr).measure_preimage
    (measurableSet_singleton S).nullMeasurableSet
  simpa only [Set.preimage, Set.mem_singleton_iff, lawMeasure_singleton, restrictedLaw] using h

def historyEvent {n : ℕ} (w : Fin n → ℝ) (k ℓ : ℕ) (ρ : Equiv.Perm (Fin n))
    (A : Finset (Fin n)) : Set (Seed n) :=
  {ω | PrefixMatches ℓ ρ ω.1 ∧ historySelected w k ℓ ω = A}

def historyPastSection {n : ℕ} (w : Fin n → ℝ) (k ℓ : ℕ) (ρ : Equiv.Perm (Fin n))
    (A : Finset (Fin n)) : Set (PastUniforms ℓ ρ) :=
  prefixPastSection (historySelected_prefixObservable w k ℓ A) ρ

theorem measurableSet_historyPastSection {n : ℕ} (w : Fin n → ℝ) (k ℓ : ℕ)
    (ρ : Equiv.Perm (Fin n)) (A : Finset (Fin n)) :
    MeasurableSet (historyPastSection w k ℓ ρ A) := measurableSet_prefixPastSection _ _

theorem historyEvent_eq_prefix {n : ℕ} (w : Fin n → ℝ) (k ℓ : ℕ)
    (ρ : Equiv.Perm (Fin n)) (A : Finset (Fin n)) :
    historyEvent w k ℓ ρ A = prefixEvent ℓ ρ (historyPastSection w k ℓ ρ A) Set.univ := by
  rw [prefixPastEvent_eq]
  ext ω
  constructor
  · rintro ⟨hπ, hA⟩
    exact ⟨hπ, (prefixPastSection_spec (historySelected_prefixObservable w k ℓ A) ρ ω hπ).mp hA⟩
  · rintro ⟨hπ, hA⟩
    exact ⟨hπ, (prefixPastSection_spec (historySelected_prefixObservable w k ℓ A) ρ ω hπ).mpr hA⟩

theorem measurableSet_historyEvent {n : ℕ} (w : Fin n → ℝ) (k ℓ : ℕ)
    (ρ : Equiv.Perm (Fin n)) (A : Finset (Fin n)) :
    MeasurableSet (historyEvent w k ℓ ρ A) := by
  rw [historyEvent_eq_prefix]
  exact measurableSet_prefixEvent ℓ ρ (measurableSet_historyPastSection w k ℓ ρ A) MeasurableSet.univ

def historyContinuation {n : ℕ} (w : Fin n → ℝ) (k ℓ : ℕ) (ω : Seed n) : Finset (Fin n) :=
  sequentialList w (fun i => (ω.2 i : ℝ)) ((List.ofFn ω.1).drop ℓ) (historyQuota w k ℓ ω)

theorem historyContinuation_assemble {n : ℕ} (w : Fin n → ℝ) (k ℓ : ℕ)
    (ρ : Equiv.Perm (Fin n)) (A : Finset (Fin n)) (z : SplitPrefixSeed ℓ ρ)
    (hz : z.2.1 ∈ historyPastSection w k ℓ ρ A) :
    historyContinuation w k ℓ (assemblePrefixSeed ℓ ρ z) =
      futureContinuation w ℓ ρ (k - A.card) (z.1, z.2.2) := by
  have hA : historySelected w k ℓ (assemblePrefixSeed ℓ ρ z) = A := by
    apply (prefixPastSection_spec (historySelected_prefixObservable w k ℓ A) ρ
      (assemblePrefixSeed ℓ ρ z) (assemblePrefixSeed_prefix ℓ ρ z)).mpr
    simpa [assemblePrefixSeed, historyPastSection] using hz
  have hq : historyQuota w k ℓ (assemblePrefixSeed ℓ ρ z) = k - A.card := by
    rw [historyQuota, hA]
  change cubeSampler w ((List.ofFn z.1.val).drop ℓ)
    (historyQuota w k ℓ (assemblePrefixSeed ℓ ρ z)) ((assemblePrefixSeed ℓ ρ z).2) = _
  rw [hq, ← futureContinuation_restrict w ℓ ρ (k - A.card) z.1]
  simp [assemblePrefixSeed]

theorem history_joint_event_eq_prefix {n : ℕ} (w : Fin n → ℝ) (k ℓ : ℕ)
    (ρ : Equiv.Perm (Fin n)) (A S : Finset (Fin n)) :
    historyEvent w k ℓ ρ A ∩ {ω | historyContinuation w k ℓ ω = S} =
      prefixEvent ℓ ρ (historyPastSection w k ℓ ρ A)
        {z | futureContinuation w ℓ ρ (k - A.card) z = S} := by
  rw [historyEvent_eq_prefix]
  ext ω
  constructor
  · rintro ⟨⟨z, hz, rfl⟩, hS⟩
    refine ⟨z, ⟨hz.1, ?_⟩, rfl⟩
    change futureContinuation w ℓ ρ (k - A.card) (z.1, z.2.2) = S
    rw [← historyContinuation_assemble w k ℓ ρ A z hz.1]
    exact hS
  · rintro ⟨z, hz, rfl⟩
    refine ⟨⟨z, ⟨hz.1, Set.mem_univ _⟩, rfl⟩, ?_⟩
    change historyContinuation w k ℓ (assemblePrefixSeed ℓ ρ z) = S
    rw [historyContinuation_assemble w k ℓ ρ A z hz.1]
    exact hz.2

/-- The actual continuation, jointly with its revealed history, has the residual product law. -/
theorem historyContinuation_joint_probability {n : ℕ}
    (w : Fin n → ℝ) (hw : ∀ i, 0 < w i) (k ℓ : ℕ) (ρ : Equiv.Perm (Fin n))
    (A S : Finset (Fin n)) (hr : k - A.card ≤ (remainingSet ℓ ρ).card) :
    seedMeasure n (historyEvent w k ℓ ρ A ∩ {ω | historyContinuation w k ℓ ω = S}) =
      seedMeasure n (historyEvent w k ℓ ρ A) *
        ENNReal.ofReal (restrictedMass w (remainingSet ℓ ρ) (k - A.card) S) := by
  rw [history_joint_event_eq_prefix]
  have hC : MeasurableSet {z | futureContinuation w ℓ ρ (k - A.card) z = S} :=
    measurableSet_eq_fun (measurable_futureContinuation w ℓ ρ (k - A.card)) measurable_const
  rw [seedMeasure_prefixEvent_eq_past_mul_future ℓ ρ
      (measurableSet_historyPastSection w k ℓ ρ A) hC,
    ← historyEvent_eq_prefix, futureContinuation_probability w hw ℓ ρ (k - A.card) hr S]

theorem historyEvent_quota_admissible {n : ℕ} (w : Fin n → ℝ) (k ℓ : ℕ)
    (hk : k ≤ n) (ρ : Equiv.Perm (Fin n)) (A : Finset (Fin n))
    (hH : 0 < seedMeasure n (historyEvent w k ℓ ρ A)) :
    k - A.card ≤ (remainingSet ℓ ρ).card := by
  have hn : (historyEvent w k ℓ ρ A).Nonempty := by
    by_contra h
    rw [Set.not_nonempty_iff_eq_empty.mp h, measure_empty] at hH
    exact lt_irrefl _ hH
  obtain ⟨ω, hπ, hA⟩ := hn
  have hq := historyQuota_le_remaining_card w k ℓ hk ω
  simpa only [historyQuota, hA, historyRemaining, permutation_drop_toFinset,
    prefixMatches_remainingSet hπ] using hq

/-- On every positive-probability history, the law is derived without an assumed residual kernel. -/
theorem historyContinuation_joint_probability_of_pos {n : ℕ}
    (w : Fin n → ℝ) (hw : ∀ i, 0 < w i) (k ℓ : ℕ) (hk : k ≤ n)
    (ρ : Equiv.Perm (Fin n)) (A S : Finset (Fin n))
    (hH : 0 < seedMeasure n (historyEvent w k ℓ ρ A)) :
    seedMeasure n (historyEvent w k ℓ ρ A ∩ {ω | historyContinuation w k ℓ ω = S}) =
      seedMeasure n (historyEvent w k ℓ ρ A) *
        ENNReal.ofReal (restrictedMass w (remainingSet ℓ ρ) (k - A.card) S) :=
  historyContinuation_joint_probability w hw k ℓ ρ A S
    (historyEvent_quota_admissible w k ℓ hk ρ A hH)

/-- Explicit conditional atom probabilities for every positive revealed history. -/
theorem historyContinuation_conditional_probability {n : ℕ}
    (w : Fin n → ℝ) (hw : ∀ i, 0 < w i) (k ℓ : ℕ) (hk : k ≤ n)
    (ρ : Equiv.Perm (Fin n)) (A S : Finset (Fin n))
    (hH : 0 < seedMeasure n (historyEvent w k ℓ ρ A)) :
    seedMeasure n (historyEvent w k ℓ ρ A ∩ {ω | historyContinuation w k ℓ ω = S}) /
        seedMeasure n (historyEvent w k ℓ ρ A) =
      ENNReal.ofReal (restrictedMass w (remainingSet ℓ ρ) (k - A.card) S) := by
  rw [historyContinuation_joint_probability_of_pos w hw k ℓ hk ρ A S hH, mul_comm,
    ENNReal.mul_div_cancel_right (ne_of_gt hH) (measure_ne_top _ _)]

end CoefficientOne.Sampling
