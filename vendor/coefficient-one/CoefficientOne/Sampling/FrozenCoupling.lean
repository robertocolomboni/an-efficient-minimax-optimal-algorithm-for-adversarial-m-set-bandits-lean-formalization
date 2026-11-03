import CoefficientOne.Sampling.FrozenContinuation
import CoefficientOne.Sampling.OutputMetric

/-! # The two-error decomposition on the actual common probability space -/

open MeasureTheory Set

namespace CoefficientOne.Sampling
noncomputable section

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

theorem measurable_frozenContinuationAt (w v : ι → ℝ) (order : List ι)
    (hn : order.Nodup) (r ℓ : ℕ) :
    Measurable (fun u : ι → ℝ => frozenContinuationAt w v u order r ℓ) := by
  have hp := measurable_prefixSelected v order hn r ℓ
  have hq : Measurable (fun u : ι → ℝ => prefixQuota v u order r ℓ) :=
    (measurable_of_finite (fun P : Finset ι => r - P.card)).comp hp
  have hc : Measurable (fun p : ℕ × (ι → ℝ) => sequentialList w p.2 (order.drop ℓ) p.1) := by
    apply measurable_from_prod_countable_right
    intro s
    exact (measurable_sequentialList (order.drop ℓ) s).comp (measurable_const.prodMk measurable_id)
  exact (measurable_of_finite (fun p : Finset ι × Finset ι => p.1 ∪ p.2)).comp
    (hp.prodMk (hc.comp (hq.prodMk measurable_id)))

theorem measurable_frozenContinuationAt_seed {n : ℕ} (w v : Fin n → ℝ) (k ℓ : ℕ) :
    Measurable (fun ω : Seed n =>
      frozenContinuationAt w v (fun i => (ω.2 i : ℝ)) (List.ofFn ω.1) k ℓ) := by
  apply measurable_from_prod_countable_right
  intro π
  exact (measurable_frozenContinuationAt w v (List.ofFn π) (List.nodup_ofFn.mpr π.injective) k ℓ).comp
    (measurable_pi_iff.mpr fun i => measurable_subtype_coe.comp (measurable_pi_apply i))

def firstDisagreementEvent {n : ℕ} (w v : Fin n → ℝ) (k : ℕ) : Set (Seed n) :=
  {ω | firstDisagreement w v k ω ≠ ⊤}

def secondDisagreementEvent {n : ℕ} (w v : Fin n → ℝ) (k : ℕ) : Set (Seed n) :=
  ⋃ ℓ : Fin (n + 1), {ω | firstDisagreement w v k ω = (ℓ.val : WithTop ℕ)} ∩
    {ω | sequentialSampler v k ω ≠
      frozenContinuationAt w v (fun i => (ω.2 i : ℝ)) (List.ofFn ω.1) k ℓ.val}

theorem measurableSet_firstDisagreementEvent {n : ℕ} (w v : Fin n → ℝ) (k : ℕ) :
    MeasurableSet (firstDisagreementEvent w v k) := by
  have he : firstDisagreementEvent w v k =
      {ω | sequentialSampler w k ω = sequentialSampler v k ω}ᶜ := by
    ext ω
    exact not_congr (firstDisagreement_eq_top_iff_output_eq w v k ω)
  rw [he]
  exact (measurableSet_eq_fun
    ((measurable_sequentialSampler k).comp (measurable_const.prodMk measurable_id))
    ((measurable_sequentialSampler k).comp (measurable_const.prodMk measurable_id))).compl

theorem measurableSet_secondDisagreementEvent {n : ℕ} (w v : Fin n → ℝ) (k : ℕ) :
    MeasurableSet (secondDisagreementEvent w v k) := by
  apply MeasurableSet.iUnion
  intro ℓ
  apply (firstDisagreement_fiber_prefixObservable w v k ℓ.val).measurableSet.inter
  exact (measurableSet_eq_fun
    ((measurable_sequentialSampler k).comp (measurable_const.prodMk measurable_id))
    (measurable_frozenContinuationAt_seed w v k ℓ.val)).compl

theorem mem_secondDisagreementEvent_iff {n : ℕ} (w v : Fin n → ℝ) (k : ℕ) (ω : Seed n) :
    ω ∈ secondDisagreementEvent w v k ↔
      ω ∈ firstDisagreementEvent w v k ∧ sequentialSampler v k ω ≠ frozenSampler w v k ω := by
  simp only [secondDisagreementEvent, mem_iUnion, mem_inter_iff, mem_setOf_eq]
  constructor
  · rintro ⟨ℓ, hstop, hne⟩
    refine ⟨?_, ?_⟩
    · change firstDisagreement w v k ω ≠ ⊤
      exact hstop ▸ WithTop.coe_ne_top
    · rwa [frozenSampler_eq_at_stop w v k ℓ.val ω hstop]
  · rintro ⟨hstop, hne⟩
    obtain ⟨ℓ, hℓ⟩ := WithTop.ne_top_iff_exists.mp hstop
    have hℓn := (firstDisagreement_eq_coe_iff w v k ℓ ω).mp hℓ.symm
    refine ⟨⟨ℓ, by omega⟩, hℓ.symm, ?_⟩
    rwa [← frozenSampler_eq_at_stop w v k ℓ ω hℓ.symm]

theorem secondDisagreementEvent_subset_first {n : ℕ} (w v : Fin n → ℝ) (k : ℕ) :
    secondDisagreementEvent w v k ⊆ firstDisagreementEvent w v k :=
  fun ω hω => ((mem_secondDisagreementEvent_iff w v k ω).mp hω).1

theorem frozenCoupling_pointwise_bound {n : ℕ} (w v : Fin n → ℝ) (hw : ∀ i, 0 < w i)
    (k : ℕ) (hk : k ≤ n) (ω : Seed n) :
    outputDistance (sequentialSampler w k ω) (sequentialSampler v k ω) ≤
      (firstDisagreementEvent w v k).indicator (fun _ => (2 : ℝ)) ω +
        (secondDisagreementEvent w v k).indicator (fun _ => (n : ℝ)) ω := by
  classical
  by_cases hD : ω ∈ firstDisagreementEvent w v k
  · rw [Set.indicator_of_mem hD]
    by_cases hE : ω ∈ secondDisagreementEvent w v k
    · rw [Set.indicator_of_mem hE]
      have hb := outputDistance_le_card (sequentialSampler w k ω) (sequentialSampler v k ω)
      simp only [Fintype.card_fin] at hb
      linarith
    · rw [Set.indicator_of_notMem hE]
      have heq : sequentialSampler v k ω = frozenSampler w v k ω := by
        by_contra hne
        exact hE ((mem_secondDisagreementEvent_iff w v k ω).mpr ⟨hD, hne⟩)
      rw [heq, frozenSampler_distance_two w v hw k hk ω hD]
      norm_num
  · rw [Set.indicator_of_notMem hD,
      Set.indicator_of_notMem (fun h => hD (secondDisagreementEvent_subset_first w v k h))]
    have htop : firstDisagreement w v k ω = ⊤ := by
      simpa only [firstDisagreementEvent, mem_setOf_eq, not_not] using hD
    rw [(firstDisagreement_eq_top_iff_output_eq w v k ω).mp htop, outputDistance_self]
    norm_num

theorem frozenCoupling_expectation_bound {n : ℕ} (w v : Fin n → ℝ) (hw : ∀ i, 0 < w i)
    (k : ℕ) (hk : k ≤ n) :
    expectedOutputDistance (seedMeasure n) (sequentialSampler w k) (sequentialSampler v k) ≤
      2 * (seedMeasure n (firstDisagreementEvent w v k)).toReal +
        n * (seedMeasure n (secondDisagreementEvent w v k)).toReal := by
  have hD := measurableSet_firstDisagreementEvent w v k
  have hE := measurableSet_secondDisagreementEvent w v k
  have hDI := (integrable_const (2 : ℝ)).indicator hD (μ := seedMeasure n)
  have hEI := (integrable_const (n : ℝ)).indicator hE (μ := seedMeasure n)
  have hbound := integral_mono
    (integrable_outputDistance (seedMeasure n)
      ((measurable_sequentialSampler k).comp (measurable_const.prodMk measurable_id))
      ((measurable_sequentialSampler k).comp (measurable_const.prodMk measurable_id)))
    (hDI.add hEI) (frozenCoupling_pointwise_bound w v hw k hk)
  simp only [Pi.add_apply, Function.comp_apply, id_eq] at hbound
  rw [integral_add hDI hEI, integral_indicator hD, integral_indicator hE,
    setIntegral_const, setIntegral_const] at hbound
  simpa only [expectedOutputDistance, measureReal_def, smul_eq_mul, mul_comm] using hbound

end
end CoefficientOne.Sampling
