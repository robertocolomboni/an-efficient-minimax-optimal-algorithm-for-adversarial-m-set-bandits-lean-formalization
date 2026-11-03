import CoefficientOne.Sampling.VariationHistory
import CoefficientOne.Sampling.FiniteStateIntegration

/-! # Conditional drift of actual covariance energies on revealed histories -/

open scoped BigOperators
open EffectiveResistance Matrix MeasureTheory
namespace CoefficientOne.Sampling
noncomputable section

theorem historyEvent_next_variance_active {n : ℕ} (w : Fin n → ℝ) (hw : ∀ i, 0 < w i)
    (k ℓ : ℕ) (hℓ : ℓ < n) (ρ : Equiv.Perm (Fin n)) (A : Finset (Fin n))
    (hr0 : 0 < k - A.card) (hrtop : k - A.card < (remainingSet ℓ ρ).card)
    (a : Fin n → ℝ) :
    (∫ ω in historyEvent w k ℓ ρ A,
      quadraticForm (samplerCovariance w k (ℓ + 1) ω) a ∂seedMeasure n) =
      (seedMeasure n (historyEvent w k ℓ ρ A)).toReal *
        residualNextVariance w (remainingSet ℓ ρ) (k - A.card) a := by
  let Q := {i : Fin n // ¬Revealed ℓ ρ i}
  haveI : Nonempty Q := ⟨⟨ρ ⟨ℓ, hℓ⟩, by simp [Revealed]⟩⟩
  let j : {j : Fin n // ¬j.val < ℓ} := ⟨⟨ℓ, hℓ⟩, Nat.lt_irrefl ℓ⟩
  let p := residualThreshold w hw ℓ ρ (k - A.card) hr0 hrtop
  let b := nextRevealBit ℓ ρ j p
  let g := fun z : PrefixOrders ℓ ρ × FutureUniforms ℓ ρ => ((b z).1.val, (b z).2)
  let F := fun q : Fin n × Bool => quadraticForm
    (residualCovariance w ((remainingSet ℓ ρ).erase q.1)
      (if q.2 then k - A.card - 1 else k - A.card)) a
  have hb : Measurable b :=
    (measurable_thresholdDecision p).comp (nextReveal_measurePreserving ℓ ρ j).measurable
  have hg : Measurable g := by
    exact (measurable_subtype_coe.comp hb.fst).prodMk hb.snd
  have he := historyEvent_integral w k ℓ ρ A (actualNextDecision w k ℓ hℓ)
    (measurable_actualNextDecision w k ℓ hℓ) g hg
    (fun z hz => actualNextDecision_assemble w hw k ℓ hℓ ρ A hr0 hrtop z hz) F
  have hleft : (∫ ω in historyEvent w k ℓ ρ A,
      quadraticForm (samplerCovariance w k (ℓ + 1) ω) a ∂seedMeasure n) =
      ∫ ω in historyEvent w k ℓ ρ A, F (actualNextDecision w k ℓ hℓ ω) ∂seedMeasure n := by
    apply setIntegral_congr_fun (measurableSet_historyEvent w k ℓ ρ A)
    intro ω hω
    dsimp only
    rw [samplerCovariance_succ_on_history w k ℓ hℓ ρ A ω hω]
  rw [hleft, he]
  congr 1
  have hnext := residualNextReveal_integral w hw ℓ ρ j (k - A.card) hr0 hrtop
    (fun q : Q × Bool => F (q.1.val, q.2))
  change (∫ z, F ((b z).1.val, (b z).2) ∂prefixFutureMeasure ℓ ρ) = _
  rw [hnext]
  rw [residualNextVariance, if_pos ⟨hr0, hrtop⟩]
  congr 1
  symm
  change (∑ i ∈ remainingSet ℓ ρ, _) = ∑ i : Q, _
  exact Finset.sum_subtype (remainingSet ℓ ρ) (fun i => by simp [remainingSet]) _

theorem historyEvent_next_variance_forced {n : ℕ} (w : Fin n → ℝ) (hw : ∀ i, 0 < w i)
    (k ℓ : ℕ) (hk : k ≤ n) (hℓ : ℓ < n) (ρ : Equiv.Perm (Fin n)) (A : Finset (Fin n))
    (ht : k - A.card = 0 ∨ k - A.card = (remainingSet ℓ ρ).card) (a : Fin n → ℝ) :
    (∫ ω in historyEvent w k ℓ ρ A,
      quadraticForm (samplerCovariance w k (ℓ + 1) ω) a ∂seedMeasure n) = 0 := by
  have he : (∫ ω in historyEvent w k ℓ ρ A,
      quadraticForm (samplerCovariance w k (ℓ + 1) ω) a ∂seedMeasure n) =
      ∫ _ in historyEvent w k ℓ ρ A, (0 : ℝ) ∂seedMeasure n := by
    apply setIntegral_congr_fun (measurableSet_historyEvent w k ℓ ρ A)
    intro ω hω
    have hs := samplerHistoryState_on_historyEvent w k ℓ ρ A ω hω
    have hR : historyRemaining ℓ ω = remainingSet ℓ ρ := congrArg Prod.fst hs
    have hr : historyQuota w k ℓ ω = k - A.card := congrArg Prod.snd hs
    have hterm : historyQuota w k ℓ ω = 0 ∨
        historyQuota w k ℓ ω = (historyRemaining ℓ ω).card := by simpa [hR, hr] using ht
    dsimp only
    rw [samplerCovariance_next_forced w hw k ℓ hk hℓ ω hterm]
    simp [quadraticForm]
  rw [he, integral_zero]

theorem historyEvent_variance_drift {n : ℕ} (w : Fin n → ℝ) (hw : ∀ i, 0 < w i)
    (k ℓ : ℕ) (hk : k ≤ n) (hℓ : ℓ < n) (ρ : Equiv.Perm (Fin n))
    (A : Finset (Fin n)) (a : Fin n → ℝ) :
    (∫ ω in historyEvent w k ℓ ρ A,
      quadraticForm (samplerCovariance w k (ℓ + 1) ω) a ∂seedMeasure n) ≤
      ∫ ω in historyEvent w k ℓ ρ A,
        (quadraticForm (samplerCovariance w k ℓ ω) a -
          quadraticForm (samplerCovariance w k ℓ ω) a / (historyRemaining ℓ ω).card) ∂seedMeasure n := by
  by_cases hzero : seedMeasure n (historyEvent w k ℓ ρ A) = 0
  · rw [Measure.restrict_eq_zero.mpr hzero, integral_zero_measure, integral_zero_measure]
  have hr := historyEvent_quota_admissible w k ℓ hk ρ A (pos_iff_ne_zero.mpr hzero)
  have hcurrent : (∫ ω in historyEvent w k ℓ ρ A,
      (quadraticForm (samplerCovariance w k ℓ ω) a -
        quadraticForm (samplerCovariance w k ℓ ω) a / (historyRemaining ℓ ω).card) ∂seedMeasure n) =
      (seedMeasure n (historyEvent w k ℓ ρ A)).toReal *
        (quadraticForm (residualCovariance w (remainingSet ℓ ρ) (k - A.card)) a -
          quadraticForm (residualCovariance w (remainingSet ℓ ρ) (k - A.card)) a /
            (remainingSet ℓ ρ).card) := by
    have he : (∫ ω in historyEvent w k ℓ ρ A,
        (quadraticForm (samplerCovariance w k ℓ ω) a -
          quadraticForm (samplerCovariance w k ℓ ω) a / (historyRemaining ℓ ω).card) ∂seedMeasure n) =
        ∫ _ in historyEvent w k ℓ ρ A,
          (quadraticForm (residualCovariance w (remainingSet ℓ ρ) (k - A.card)) a -
          quadraticForm (residualCovariance w (remainingSet ℓ ρ) (k - A.card)) a /
            (remainingSet ℓ ρ).card) ∂seedMeasure n := by
      apply setIntegral_congr_fun (measurableSet_historyEvent w k ℓ ρ A)
      intro ω hω
      have hs := samplerHistoryState_on_historyEvent w k ℓ ρ A ω hω
      have hR : historyRemaining ℓ ω = remainingSet ℓ ρ := congrArg Prod.fst hs
      have hq : historyQuota w k ℓ ω = k - A.card := congrArg Prod.snd hs
      simp only [samplerCovariance, hR, hq]
    rw [he, setIntegral_const]
    rfl
  rw [hcurrent]
  have hd := residual_uniform_variance_drop w hw (remainingSet ℓ ρ) (k - A.card) hr a
  by_cases hactive : 0 < k - A.card ∧ k - A.card < (remainingSet ℓ ρ).card
  · rw [historyEvent_next_variance_active w hw k ℓ hℓ ρ A hactive.1 hactive.2]
    exact mul_le_mul_of_nonneg_left (by linarith) ENNReal.toReal_nonneg
  · have ht : k - A.card = 0 ∨ k - A.card = (remainingSet ℓ ρ).card := by omega
    rw [historyEvent_next_variance_forced w hw k ℓ hk hℓ ρ A ht]
    simp only [residualNextVariance, if_neg hactive] at hd
    exact mul_nonneg ENNReal.toReal_nonneg (by linarith)

def historyKey {n : ℕ} (w : Fin n → ℝ) (k ℓ : ℕ) (ω : Seed n) :
    (Fin n → Fin n) × Finset (Fin n) :=
  (fun j => if j.val < ℓ then ω.1 j else j, historySelected w k ℓ ω)

theorem measurable_historyKey {n : ℕ} (w : Fin n → ℝ) (k ℓ : ℕ) :
    Measurable (historyKey w k ℓ) := by
  have hf : Measurable (fun z : Equiv.Perm (Fin n) × Finset (Fin n) =>
    ((fun j => if j.val < ℓ then z.1 j else j), z.2 ∩ ((List.ofFn z.1).take ℓ).toFinset)) :=
      measurable_of_finite _
  have he : historyKey w k ℓ = fun ω : Seed n =>
      ((fun j => if j.val < ℓ then ω.1 j else j),
        sequentialSampler w k ω ∩ ((List.ofFn ω.1).take ℓ).toFinset) := by
    funext ω
    simp only [historyKey, historySelected_eq_output_inter]
  rw [he]
  exact fun _ hs => measurable_samplerOrderOutput w k (hf hs)

theorem historyKey_fiber {n : ℕ} (w : Fin n → ℝ) (k ℓ : ℕ) (ω₀ : Seed n) :
    historyKey w k ℓ ⁻¹' {historyKey w k ℓ ω₀} =
      historyEvent w k ℓ ω₀.1 (historySelected w k ℓ ω₀) := by
  ext ω
  change historyKey w k ℓ ω = historyKey w k ℓ ω₀ ↔
    PrefixMatches ℓ ω₀.1 ω.1 ∧ historySelected w k ℓ ω = historySelected w k ℓ ω₀
  constructor
  · intro he
    refine ⟨?_, congrArg Prod.snd he⟩
    intro j hj
    have h := congrFun (congrArg Prod.fst he) j
    simpa only [historyKey, if_pos hj] using h
  · rintro ⟨hπ, hA⟩
    apply Prod.ext
    · funext j
      by_cases hj : j.val < ℓ
      · simp only [historyKey, if_pos hj]
        exact hπ j hj
      · simp only [historyKey, if_neg hj]
    · exact hA

/-- The one-step conditional drift integrated over the actual finite history
partition; no conditional expectation or Markov kernel is postulated. -/
theorem sampler_variance_drift {n : ℕ} (w : Fin n → ℝ) (hw : ∀ i, 0 < w i)
    (k ℓ : ℕ) (hk : k ≤ n) (hℓ : ℓ < n) (a : Fin n → ℝ) :
    (∫ ω, quadraticForm (samplerCovariance w k (ℓ + 1) ω) a ∂seedMeasure n) ≤
      ∫ ω, (quadraticForm (samplerCovariance w k ℓ ω) a -
        quadraticForm (samplerCovariance w k ℓ ω) a / (historyRemaining ℓ ω).card) ∂seedMeasure n := by
  have hnext : Integrable (fun ω => quadraticForm (samplerCovariance w k (ℓ + 1) ω) a)
      (seedMeasure n) := integrable_historyStatistic w k (ℓ + 1)
    (fun z => quadraticForm (residualCovariance w z.1 z.2) a)
  have hcurrent : Integrable (fun ω => quadraticForm (samplerCovariance w k ℓ ω) a -
        quadraticForm (samplerCovariance w k ℓ ω) a / (historyRemaining ℓ ω).card)
      (seedMeasure n) := integrable_historyStatistic w k ℓ
    (fun z => quadraticForm (residualCovariance w z.1 z.2) a -
      quadraticForm (residualCovariance w z.1 z.2) a / z.1.card)
  rw [integral_eq_sum_fibers (seedMeasure n) (historyKey w k ℓ) (measurable_historyKey w k ℓ) _ hnext,
    integral_eq_sum_fibers (seedMeasure n) (historyKey w k ℓ) (measurable_historyKey w k ℓ) _ hcurrent]
  apply Finset.sum_le_sum
  intro z _
  by_cases hz : (historyKey w k ℓ ⁻¹' {z}).Nonempty
  · obtain ⟨ω₀, hω₀⟩ := hz
    have he : historyKey w k ℓ ω₀ = z := hω₀
    rw [← he, historyKey_fiber]
    exact historyEvent_variance_drift w hw k ℓ hk hℓ ω₀.1 (historySelected w k ℓ ω₀) a
  · rw [Set.not_nonempty_iff_eq_empty.mp hz]
    simp

end
end CoefficientOne.Sampling
