import CoefficientOne.Sampling.ThresholdHazardProbability

/-! # The exact conditional identity for the first differing decision -/

open scoped BigOperators
open MeasureTheory Set
namespace CoefficientOne.Sampling
noncomputable section
set_option maxHeartbeats 1000000

theorem historyAgreement_of_le {n : ℕ} (w v : Fin n → ℝ) (k j ℓ : ℕ)
    (hj : j ≤ ℓ) (ω : Seed n)
    (h : historySelected w k ℓ ω = historySelected v k ℓ ω) :
    historySelected w k j ω = historySelected v k j ω := by
  simp only [historySelected_eq_output_inter] at h ⊢
  ext i
  by_cases hi : i ∈ ((List.ofFn ω.1).take j).toFinset
  · have hil : i ∈ ((List.ofFn ω.1).take ℓ).toFinset := by
      simp only [List.mem_toFinset, mem_permutation_take_iff, Revealed] at hi ⊢
      exact lt_of_lt_of_le hi hj
    have he := congrArg (fun S : Finset (Fin n) => i ∈ S) h
    simpa [hi, hil] using he
  · simp [hi]

theorem firstDisagreement_gt_iff_historyAgreement {n : ℕ} (w v : Fin n → ℝ)
    (k ℓ : ℕ) (hℓ : ℓ ≤ n) (ω : Seed n) :
    (ℓ : WithTop ℕ) < firstDisagreement w v k ω ↔
      historySelected w k ℓ ω = historySelected v k ℓ ω := by
  by_cases ht : firstDisagreement w v k ω = ⊤
  · simp only [ht, WithTop.natCast_lt_top, true_iff]
    exact (firstDisagreement_eq_top_iff w v k ω).mp ht ℓ hℓ
  obtain ⟨t, ht'⟩ := WithTop.ne_top_iff_exists.mp ht
  have hs := (firstDisagreement_eq_coe_iff w v k t ω).mp ht'.symm
  rw [← ht']
  constructor
  · intro h
    apply hs.2.2 ℓ
    exact (WithTop.coe_lt_coe (a := t) (b := ℓ)).mp h
  · intro h
    have hlt : ℓ < t := by
      by_contra hn
      exact hs.2.1 (historyAgreement_of_le w v k t ℓ (Nat.le_of_not_gt hn) ω h)
    exact (WithTop.coe_lt_coe (a := t) (b := ℓ)).mpr hlt

theorem firstDisagreement_eq_succ_iff_agreement_hazard {n : ℕ} (w v : Fin n → ℝ)
    (k : ℕ) (ℓ : Fin n) (ω : Seed n) :
    firstDisagreement w v k ω = ((ℓ.val + 1 : ℕ) : WithTop ℕ) ↔
      historySelected w k ℓ.val ω = historySelected v k ℓ.val ω ∧
        ω ∈ thresholdHazard w v k ℓ := by
  constructor
  · intro hs
    exact ⟨((firstDisagreement_eq_coe_iff w v k (ℓ.val + 1) ω).mp hs).2.2
      ℓ.val (by omega), firstDisagreement_mem_hazard w v k ℓ ω hs⟩
  · rintro ⟨hprev, hh⟩
    apply (firstDisagreement_eq_coe_iff w v k (ℓ.val + 1) ω).mpr
    refine ⟨by omega, ?_, fun j hj => historyAgreement_of_le w v k j ℓ.val (by omega) ω hprev⟩
    let i := ω.1 ℓ
    let tail := (List.ofFn ω.1).drop (ℓ.val + 1)
    have hd : (List.ofFn ω.1).drop ℓ.val = i :: tail := by
      dsimp [i, tail]
      rw [List.drop_eq_getElem_cons (l := List.ofFn ω.1) (i := ℓ.val) (by simpa using ℓ.isLt),
        List.getElem_ofFn]
    have hn : (List.ofFn ω.1).Nodup := List.nodup_ofFn.mpr ω.1.injective
    have hnt : (i :: tail).Nodup := hd ▸ nodup_drop _ hn ℓ.val
    have hq : prefixQuota v (fun j => (ω.2 j : ℝ)) (List.ofFn ω.1) k ℓ.val =
        prefixQuota w (fun j => (ω.2 j : ℝ)) (List.ofFn ω.1) k ℓ.val := by
      change k - (historySelected v k ℓ.val ω).card = k - (historySelected w k ℓ.val ω).card
      rw [hprev]
    have hwstep := prefixSelected_succ_of_drop w (fun j => (ω.2 j : ℝ)) _ hn k ℓ.val i tail hd
    have hvstep := prefixSelected_succ_of_drop v (fun j => (ω.2 j : ℝ)) _ hn k ℓ.val i tail hd
    have hbase : prefixSelected w (fun j => (ω.2 j : ℝ)) (List.ofFn ω.1) k ℓ.val =
        prefixSelected v (fun j => (ω.2 j : ℝ)) (List.ofFn ω.1) k ℓ.val := hprev
    rw [hq, ← hbase] at hvstep
    have hi : i ∉ prefixSelected w (fun j => (ω.2 j : ℝ)) (List.ofFn ω.1) k ℓ.val := by
      change i ∉ historySelected w k ℓ.val ω
      rw [historySelected_eq_output_inter]
      exact fun h => nextIndex_notMem_revealed ℓ.val ℓ.isLt ω (Finset.mem_inter.mp h).2
    have hdec : SelectsHead w (fun j => (ω.2 j : ℝ)) i tail (historyQuota w k ℓ.val ω) ≠
        SelectsHead v (fun j => (ω.2 j : ℝ)) i tail (historyQuota w k ℓ.val ω) := by
      apply (selectsHead_disagreement_iff w v (fun j => (ω.2 j : ℝ)) i tail hnt _).mpr
      simpa only [thresholdHazard, mem_setOf_eq, nextHistoryThreshold, historyRemaining, hd] using hh
    intro he
    have hei := congrArg (fun S : Finset (Fin n) => i ∈ S) he
    change (i ∈ prefixSelected w _ _ k _) = (i ∈ prefixSelected v _ _ k _) at hei
    rw [hwstep, hvstep] at hei
    change SelectsHead w _ i tail (prefixQuota w _ _ k ℓ.val) ≠
      SelectsHead v _ i tail (prefixQuota w _ _ k ℓ.val) at hdec
    split_ifs at hei <;> simp_all only [Finset.mem_insert, true_or] <;> exact hdec rfl

theorem firstDisagreement_eq_succ_event {n : ℕ} (w v : Fin n → ℝ) (k : ℕ) (ℓ : Fin n) :
    {ω | firstDisagreement w v k ω = ((ℓ.val + 1 : ℕ) : WithTop ℕ)} =
      {ω | (ℓ.val : WithTop ℕ) < firstDisagreement w v k ω} ∩ thresholdHazard w v k ℓ := by
  ext ω
  rw [mem_setOf_eq, firstDisagreement_eq_succ_iff_agreement_hazard,
    mem_inter_iff, mem_setOf_eq, firstDisagreement_gt_iff_historyAgreement w v k ℓ.val ℓ.isLt.le]

theorem observable_history_hazard_integral {n : ℕ} (w v : Fin n → ℝ)
    (hw : ∀ i, 0 < w i) (hv : ∀ i, 0 < v i) (k : ℕ) (hk : k ≤ n) (ℓ : Fin n)
    (B : Set (Seed n)) (hB : PrefixObservableEvent ℓ.val B)
    (ρ : Equiv.Perm (Fin n)) (A : Finset (Fin n)) :
    (∫ ω in B ∩ historyEvent w k ℓ.val ρ A,
      (thresholdHazard w v k ℓ).indicator (fun _ => (1 : ℝ)) ω ∂seedMeasure n) =
    ∫ ω in B ∩ historyEvent w k ℓ.val ρ A,
      thresholdGapMean w v (historyRemaining ℓ.val ω) (historyQuota w k ℓ.val ω) ∂seedMeasure n := by
  by_cases hzero : seedMeasure n (B ∩ historyEvent w k ℓ.val ρ A) = 0
  · rw [Measure.restrict_eq_zero.mpr hzero, integral_zero_measure, integral_zero_measure]
  have hr := historyEvent_quota_admissible w k ℓ.val hk ρ A
    (lt_of_lt_of_le (pos_iff_ne_zero.mpr hzero) (measure_mono Set.inter_subset_right))
  let C := prefixPastSection hB ρ ∩ historyPastSection w k ℓ.val ρ A
  have hC : MeasurableSet C := (measurableSet_prefixPastSection hB ρ).inter
    (measurableSet_historyPastSection w k ℓ.val ρ A)
  have hBz (z : SplitPrefixSeed ℓ.val ρ) :
      assemblePrefixSeed ℓ.val ρ z ∈ B ↔ z.2.1 ∈ prefixPastSection hB ρ := by
    simpa [assemblePrefixSeed] using prefixPastSection_spec hB ρ
      (assemblePrefixSeed ℓ.val ρ z) (assemblePrefixSeed_prefix ℓ.val ρ z)
  have heC : B ∩ historyEvent w k ℓ.val ρ A = prefixEvent ℓ.val ρ C Set.univ := by
    rw [historyEvent_eq_prefix]
    ext ω
    constructor
    · rintro ⟨hb, ⟨z, hz, rfl⟩⟩
      exact ⟨z, ⟨⟨(hBz z).mp hb, hz.1⟩, Set.mem_univ _⟩, rfl⟩
    · rintro ⟨z, hz, rfl⟩
      exact ⟨(hBz z).mpr hz.1.1, ⟨z, ⟨hz.1.2, Set.mem_univ _⟩, rfl⟩⟩
  have heHaz : (B ∩ historyEvent w k ℓ.val ρ A) ∩ thresholdHazard w v k ℓ =
      prefixEvent ℓ.val ρ C (futureThresholdHazard w v ℓ ρ (k - A.card)) := by
    rw [heC]
    ext ω
    constructor
    · rintro ⟨⟨z, hz, rfl⟩, hh⟩
      exact ⟨z, ⟨hz.1, (thresholdHazard_assemble w v k ℓ ρ A z hz.1.2).mp hh⟩, rfl⟩
    · rintro ⟨z, hz, rfl⟩
      exact ⟨⟨z, ⟨hz.1, Set.mem_univ _⟩, rfl⟩,
        (thresholdHazard_assemble w v k ℓ ρ A z hz.1.2).mpr hz.2⟩
  have hleft : (∫ ω in B ∩ historyEvent w k ℓ.val ρ A,
      (thresholdHazard w v k ℓ).indicator (fun _ => (1 : ℝ)) ω ∂seedMeasure n) =
      (seedMeasure n ((B ∩ historyEvent w k ℓ.val ρ A) ∩ thresholdHazard w v k ℓ)).toReal := by
    rw [integral_indicator (measurableSet_thresholdHazard w v k ℓ),
      Measure.restrict_restrict (measurableSet_thresholdHazard w v k ℓ), setIntegral_const]
    simp [Set.inter_comm, measureReal_def]
  rw [hleft, heHaz, seedMeasure_prefixEvent_eq_past_mul_future ℓ.val ρ hC
    (measurableSet_futureThresholdHazard w v hw hv ℓ ρ _ hr), ← heC,
    ENNReal.toReal_mul, futureThresholdHazard_probability w v hw hv ℓ ρ _ hr]
  have he : (∫ ω in B ∩ historyEvent w k ℓ.val ρ A,
      thresholdGapMean w v (historyRemaining ℓ.val ω) (historyQuota w k ℓ.val ω) ∂seedMeasure n) =
      ∫ _ in B ∩ historyEvent w k ℓ.val ρ A,
        thresholdGapMean w v (remainingSet ℓ.val ρ) (k - A.card) ∂seedMeasure n := by
    apply setIntegral_congr_fun (hB.measurableSet.inter (measurableSet_historyEvent w k ℓ.val ρ A))
    intro ω hω
    dsimp only
    have hs := samplerHistoryState_on_historyEvent w k ℓ.val ρ A ω hω.2
    rw [show historyRemaining ℓ.val ω = remainingSet ℓ.val ρ from congrArg Prod.fst hs,
      show historyQuota w k ℓ.val ω = k - A.card from congrArg Prod.snd hs]
  rw [he, setIntegral_const]
  rfl

theorem observable_hazard_integral {n : ℕ} (w v : Fin n → ℝ)
    (hw : ∀ i, 0 < w i) (hv : ∀ i, 0 < v i) (k : ℕ) (hk : k ≤ n) (ℓ : Fin n)
    (B : Set (Seed n)) (hB : PrefixObservableEvent ℓ.val B) :
    (∫ ω in B, (thresholdHazard w v k ℓ).indicator (fun _ => (1 : ℝ)) ω ∂seedMeasure n) =
      ∫ ω in B, thresholdGapMean w v (historyRemaining ℓ.val ω)
        (historyQuota w k ℓ.val ω) ∂seedMeasure n := by
  have hI := ((integrable_const (1 : ℝ)).indicator (measurableSet_thresholdHazard w v k ℓ)
    (μ := seedMeasure n)).restrict (s := B)
  have hG := (integrable_historyStatistic w k ℓ.val
    (fun z => thresholdGapMean w v z.1 z.2)).restrict (s := B)
  change Integrable (fun ω => thresholdGapMean w v (historyRemaining ℓ.val ω)
    (historyQuota w k ℓ.val ω)) ((seedMeasure n).restrict B) at hG
  rw [integral_eq_sum_fibers ((seedMeasure n).restrict B) (historyKey w k ℓ.val)
      (measurable_historyKey w k ℓ.val) _ hI,
    integral_eq_sum_fibers ((seedMeasure n).restrict B) (historyKey w k ℓ.val)
      (measurable_historyKey w k ℓ.val) _ hG]
  apply Finset.sum_congr rfl
  intro z _
  by_cases hz : (historyKey w k ℓ.val ⁻¹' {z}).Nonempty
  · obtain ⟨ω₀, hω₀⟩ := hz
    have he : historyKey w k ℓ.val ω₀ = z := hω₀
    rw [← he, historyKey_fiber,
      Measure.restrict_restrict (measurableSet_historyEvent w k ℓ.val ω₀.1
        (historySelected w k ℓ.val ω₀)), Set.inter_comm]
    exact observable_history_hazard_integral w v hw hv k hk ℓ B hB
      ω₀.1 (historySelected w k ℓ.val ω₀)
  · rw [Set.not_nonempty_iff_eq_empty.mp hz]
    simp

theorem firstDisagreement_conditional_probability {n : ℕ} (w v : Fin n → ℝ)
    (hw : ∀ i, 0 < w i) (hv : ∀ i, 0 < v i) (k : ℕ) (hk : k ≤ n) (ℓ : Fin n)
    (B : Set (Seed n)) (hB : PrefixObservableEvent ℓ.val B) :
    (seedMeasure n (B ∩ {ω | firstDisagreement w v k ω = ((ℓ.val + 1 : ℕ) : WithTop ℕ)})).toReal =
      ∫ ω in B, {ω | (ℓ.val : WithTop ℕ) < firstDisagreement w v k ω}.indicator
        (fun ω => thresholdGapMean w v (historyRemaining ℓ.val ω)
          (historyQuota w k ℓ.val ω)) ω ∂seedMeasure n := by
  let E := {ω | (ℓ.val : WithTop ℕ) < firstDisagreement w v k ω}
  have hE : PrefixObservableEvent ℓ.val E := by
    have he : E = {ω | historySelected w k ℓ.val ω = historySelected v k ℓ.val ω} := by
      ext ω
      exact firstDisagreement_gt_iff_historyAgreement w v k ℓ.val ℓ.isLt.le ω
    rw [he]
    exact historyAgreement_prefixObservable w v k ℓ.val
  have h := observable_hazard_integral w v hw hv k hk ℓ (B ∩ E) (hB.inter hE)
  rw [integral_indicator (measurableSet_thresholdHazard w v k ℓ),
    Measure.restrict_restrict (measurableSet_thresholdHazard w v k ℓ), setIntegral_const] at h
  have hevents : thresholdHazard w v k ℓ ∩ (B ∩ E) =
      B ∩ {ω | firstDisagreement w v k ω = ((ℓ.val + 1 : ℕ) : WithTop ℕ)} := by
    rw [firstDisagreement_eq_succ_event]
    ext ω
    simp only [mem_inter_iff]
    tauto
  rw [hevents] at h
  change _ = ∫ ω in B, E.indicator _ ω ∂seedMeasure n
  rw [integral_indicator hE.measurableSet, Measure.restrict_restrict hE.measurableSet,
    Set.inter_comm E B]
  simpa only [measureReal_def, smul_eq_mul, mul_one] using h

end
end CoefficientOne.Sampling
