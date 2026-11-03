import CoefficientOne.Sampling.FirstDisagreementHazard
import CoefficientOne.Sampling.CutVariance

/-! # Exact hazard probabilities under the finite revealed-history partition -/

open scoped BigOperators
open MeasureTheory Set

namespace CoefficientOne.Sampling
noncomputable section
set_option maxHeartbeats 1000000

theorem quotaThreshold_mem_Icc {ι : Type*} [Fintype ι] [DecidableEq ι]
    (w : ι → ℝ) (hw : ∀ i, 0 < w i) (R : Finset ι) (r : ℕ) (hr : r ≤ R.card)
    (i : ι) (hi : i ∈ R) : quotaThreshold w R r i ∈ Icc (0 : ℝ) 1 := by
  unfold quotaThreshold
  split_ifs with h0 hf
  · exact ⟨le_rfl, zero_le_one⟩
  · exact ⟨zero_le_one, le_rfl⟩
  · exact ⟨(sequentialThreshold_pos w hw R r (by omega) hr i hi).le,
      (sequentialThreshold_lt_one w hw R r (by omega) (by omega) i hi).le⟩

def futureThresholdHazard {n : ℕ} (w v : Fin n → ℝ) (ℓ : Fin n)
    (ρ : Equiv.Perm (Fin n)) (r : ℕ) : Set (PrefixOrders ℓ.val ρ × FutureUniforms ℓ.val ρ) :=
  {z | let i := remainingOrder ℓ.val ρ z.1 ⟨ℓ, Nat.lt_irrefl ℓ.val⟩
    ((z.2 i : ℝ) ≤ quotaThreshold w (remainingSet ℓ.val ρ) r i.val) ≠
      ((z.2 i : ℝ) ≤ quotaThreshold v (remainingSet ℓ.val ρ) r i.val)}

theorem futureThresholdHazard_probability {n : ℕ} (w v : Fin n → ℝ)
    (hw : ∀ i, 0 < w i) (hv : ∀ i, 0 < v i) (ℓ : Fin n)
    (ρ : Equiv.Perm (Fin n)) (r : ℕ) (hr : r ≤ (remainingSet ℓ.val ρ).card) :
    ((prefixFutureMeasure ℓ.val ρ) (futureThresholdHazard w v ℓ ρ r)).toReal =
      (∑ i ∈ remainingSet ℓ.val ρ,
        |quotaThreshold w (remainingSet ℓ.val ρ) r i - quotaThreshold v (remainingSet ℓ.val ρ) r i|) /
          (remainingSet ℓ.val ρ).card := by
  let Q := {i : Fin n // ¬Revealed ℓ.val ρ i}
  haveI : Nonempty Q := ⟨⟨ρ ℓ, by simp [Revealed]⟩⟩
  let p : Q → unitInterval := fun i => ⟨quotaThreshold w (remainingSet ℓ.val ρ) r i.val,
    quotaThreshold_mem_Icc w hw _ r hr i.val (by simpa [remainingSet] using i.property)⟩
  let q : Q → unitInterval := fun i => ⟨quotaThreshold v (remainingSet ℓ.val ρ) r i.val,
    quotaThreshold_mem_Icc v hv _ r hr i.val (by simpa [remainingSet] using i.property)⟩
  have he := nextReveal_threshold_disagreement_real ℓ.val ρ ⟨ℓ, Nat.lt_irrefl ℓ.val⟩ p q
  have hc : Fintype.card Q = (remainingSet ℓ.val ρ).card := by
    rw [Fintype.card_subtype]
    rfl
  change ((prefixFutureMeasure ℓ.val ρ) (futureThresholdHazard w v ℓ ρ r)).toReal = _ at he
  rw [he, hc]
  simp only [p, q]
  rw [div_eq_mul_inv, mul_comm]
  congr 1
  symm
  exact Finset.sum_subtype (remainingSet ℓ.val ρ) (fun i => by simp [remainingSet]) _

theorem measurableSet_futureThresholdHazard {n : ℕ} (w v : Fin n → ℝ)
    (hw : ∀ i, 0 < w i) (hv : ∀ i, 0 < v i) (ℓ : Fin n)
    (ρ : Equiv.Perm (Fin n)) (r : ℕ) (hr : r ≤ (remainingSet ℓ.val ρ).card) :
    MeasurableSet (futureThresholdHazard w v ℓ ρ r) := by
  let Q := {i : Fin n // ¬Revealed ℓ.val ρ i}
  haveI : Nonempty Q := ⟨⟨ρ ℓ, by simp [Revealed]⟩⟩
  let p : Q → unitInterval := fun i => ⟨quotaThreshold w (remainingSet ℓ.val ρ) r i.val,
    quotaThreshold_mem_Icc w hw _ r hr i.val (by simpa [remainingSet] using i.property)⟩
  let q : Q → unitInterval := fun i => ⟨quotaThreshold v (remainingSet ℓ.val ρ) r i.val,
    quotaThreshold_mem_Icc v hv _ r hr i.val (by simpa [remainingSet] using i.property)⟩
  exact (measurableSet_thresholdDisagreement p q).preimage
    (nextReveal_measurePreserving ℓ.val ρ ⟨ℓ, Nat.lt_irrefl ℓ.val⟩).measurable

theorem thresholdHazard_assemble {n : ℕ} (w v : Fin n → ℝ) (k : ℕ) (ℓ : Fin n)
    (ρ : Equiv.Perm (Fin n)) (A : Finset (Fin n)) (z : SplitPrefixSeed ℓ.val ρ)
    (hz : z.2.1 ∈ historyPastSection w k ℓ.val ρ A) :
    assemblePrefixSeed ℓ.val ρ z ∈ thresholdHazard w v k ℓ ↔
      (z.1, z.2.2) ∈ futureThresholdHazard w v ℓ ρ (k - A.card) := by
  have hA : historySelected w k ℓ.val (assemblePrefixSeed ℓ.val ρ z) = A := by
    apply (prefixPastSection_spec (historySelected_prefixObservable w k ℓ.val A) ρ
      (assemblePrefixSeed ℓ.val ρ z) (assemblePrefixSeed_prefix ℓ.val ρ z)).mpr
    simpa [assemblePrefixSeed, historyPastSection] using hz
  have hR : historyRemaining ℓ.val (assemblePrefixSeed ℓ.val ρ z) = remainingSet ℓ.val ρ :=
    prefixOrder_drop_toFinset ℓ.val ρ z.1
  have hq : historyQuota w k ℓ.val (assemblePrefixSeed ℓ.val ρ z) = k - A.card := by
    rw [historyQuota, hA]
  let j : {j : Fin n // ¬j.val < ℓ.val} := ⟨ℓ, Nat.lt_irrefl ℓ.val⟩
  have hu := congrArg (fun p : PastUniforms ℓ.val ρ × FutureUniforms ℓ.val ρ =>
      p.2 (remainingOrder ℓ.val ρ z.1 j)) ((splitUniforms ℓ.val ρ).apply_symm_apply z.2)
  change ((assemblePrefixSeed ℓ.val ρ z).2 (z.1.val ℓ)) =
    z.2.2 (remainingOrder ℓ.val ρ z.1 j) at hu
  simp only [thresholdHazard, mem_setOf_eq, nextHistoryThreshold, hR, hq]
  change (((assemblePrefixSeed ℓ.val ρ z).2 (z.1.val ℓ) : ℝ) ≤ _) ≠
      (((assemblePrefixSeed ℓ.val ρ z).2 (z.1.val ℓ) : ℝ) ≤ _) ↔ _
  rw [hu]
  rfl

theorem historyEvent_hazard_eq_prefix {n : ℕ} (w v : Fin n → ℝ) (k : ℕ) (ℓ : Fin n)
    (ρ : Equiv.Perm (Fin n)) (A : Finset (Fin n)) :
    historyEvent w k ℓ.val ρ A ∩ thresholdHazard w v k ℓ =
      prefixEvent ℓ.val ρ (historyPastSection w k ℓ.val ρ A)
        (futureThresholdHazard w v ℓ ρ (k - A.card)) := by
  rw [historyEvent_eq_prefix]
  ext ω
  constructor
  · rintro ⟨⟨z, hz, rfl⟩, hS⟩
    exact ⟨z, ⟨hz.1, (thresholdHazard_assemble w v k ℓ ρ A z hz.1).mp hS⟩, rfl⟩
  · rintro ⟨z, hz, rfl⟩
    exact ⟨⟨z, ⟨hz.1, Set.mem_univ _⟩, rfl⟩,
      (thresholdHazard_assemble w v k ℓ ρ A z hz.1).mpr hz.2⟩

def thresholdGapMean {n : ℕ} (w v : Fin n → ℝ) (R : Finset (Fin n)) (r : ℕ) : ℝ :=
  (∑ i ∈ R, |quotaThreshold w R r i - quotaThreshold v R r i|) / R.card

theorem historyEvent_hazard_integral {n : ℕ} (w v : Fin n → ℝ)
    (hw : ∀ i, 0 < w i) (hv : ∀ i, 0 < v i) (k : ℕ) (hk : k ≤ n) (ℓ : Fin n)
    (ρ : Equiv.Perm (Fin n)) (A : Finset (Fin n)) :
    (∫ ω in historyEvent w k ℓ.val ρ A, (thresholdHazard w v k ℓ).indicator (fun _ => (1 : ℝ)) ω
      ∂seedMeasure n) =
      ∫ ω in historyEvent w k ℓ.val ρ A,
        thresholdGapMean w v (historyRemaining ℓ.val ω) (historyQuota w k ℓ.val ω) ∂seedMeasure n := by
  by_cases hzero : seedMeasure n (historyEvent w k ℓ.val ρ A) = 0
  · rw [Measure.restrict_eq_zero.mpr hzero, integral_zero_measure, integral_zero_measure]
  have hr := historyEvent_quota_admissible w k ℓ.val hk ρ A (pos_iff_ne_zero.mpr hzero)
  have hleft : (∫ ω in historyEvent w k ℓ.val ρ A,
      (thresholdHazard w v k ℓ).indicator (fun _ => (1 : ℝ)) ω ∂seedMeasure n) =
      (seedMeasure n (historyEvent w k ℓ.val ρ A ∩ thresholdHazard w v k ℓ)).toReal := by
    rw [integral_indicator (measurableSet_thresholdHazard w v k ℓ),
      Measure.restrict_restrict (measurableSet_thresholdHazard w v k ℓ), setIntegral_const]
    simp [Set.inter_comm, measureReal_def]
  rw [hleft, historyEvent_hazard_eq_prefix,
    seedMeasure_prefixEvent_eq_past_mul_future ℓ.val ρ
      (measurableSet_historyPastSection w k ℓ.val ρ A)
      (measurableSet_futureThresholdHazard w v hw hv ℓ ρ _ hr),
    ← historyEvent_eq_prefix, ENNReal.toReal_mul, futureThresholdHazard_probability w v hw hv ℓ ρ _ hr]
  have he : (∫ ω in historyEvent w k ℓ.val ρ A,
      thresholdGapMean w v (historyRemaining ℓ.val ω) (historyQuota w k ℓ.val ω) ∂seedMeasure n) =
      ∫ _ in historyEvent w k ℓ.val ρ A,
        thresholdGapMean w v (remainingSet ℓ.val ρ) (k - A.card) ∂seedMeasure n := by
    apply setIntegral_congr_fun (measurableSet_historyEvent w k ℓ.val ρ A)
    intro ω hω
    dsimp only
    have hs := samplerHistoryState_on_historyEvent w k ℓ.val ρ A ω hω
    rw [show historyRemaining ℓ.val ω = remainingSet ℓ.val ρ from congrArg Prod.fst hs,
      show historyQuota w k ℓ.val ω = k - A.card from congrArg Prod.snd hs]
  rw [he, setIntegral_const]
  rfl

theorem thresholdHazard_probability {n : ℕ} (w v : Fin n → ℝ)
    (hw : ∀ i, 0 < w i) (hv : ∀ i, 0 < v i) (k : ℕ) (hk : k ≤ n) (ℓ : Fin n) :
    (seedMeasure n (thresholdHazard w v k ℓ)).toReal =
      ∫ ω, thresholdGapMean w v (historyRemaining ℓ.val ω) (historyQuota w k ℓ.val ω) ∂seedMeasure n := by
  have hI := (integrable_const (1 : ℝ)).indicator (measurableSet_thresholdHazard w v k ℓ)
    (μ := seedMeasure n)
  have hG := integrable_historyStatistic w k ℓ.val (fun z => thresholdGapMean w v z.1 z.2)
  change Integrable (fun ω => thresholdGapMean w v (historyRemaining ℓ.val ω)
    (historyQuota w k ℓ.val ω)) (seedMeasure n) at hG
  have he : (seedMeasure n (thresholdHazard w v k ℓ)).toReal =
      ∫ ω, (thresholdHazard w v k ℓ).indicator (fun _ => (1 : ℝ)) ω ∂seedMeasure n := by
    rw [integral_indicator (measurableSet_thresholdHazard w v k ℓ), setIntegral_const]
    simp [measureReal_def]
  rw [he, integral_eq_sum_fibers (seedMeasure n) (historyKey w k ℓ.val)
      (measurable_historyKey w k ℓ.val) _ hI,
    integral_eq_sum_fibers (seedMeasure n) (historyKey w k ℓ.val)
      (measurable_historyKey w k ℓ.val) _ hG]
  apply Finset.sum_congr rfl
  intro z _
  by_cases hz : (historyKey w k ℓ.val ⁻¹' {z}).Nonempty
  · obtain ⟨ω₀, hω₀⟩ := hz
    have he : historyKey w k ℓ.val ω₀ = z := hω₀
    rw [← he, historyKey_fiber]
    exact historyEvent_hazard_integral w v hw hv k hk ℓ ω₀.1 (historySelected w k ℓ.val ω₀)
  · rw [Set.not_nonempty_iff_eq_empty.mp hz]
    simp

end
end CoefficientOne.Sampling
