import CoefficientOne.Sampling.VarianceTelescope

/-! # The cut energies are the actual conditional variances of total counts

Conditional expectation on a positive history event is written as the
normalized set integral. The selected prefix contributes a constant, whose
variance is proved to vanish.
-/

open scoped BigOperators
open EffectiveResistance Matrix MeasureTheory
namespace CoefficientOne.Sampling
noncomputable section

theorem samplerOutput_assemble {n : ℕ} (w : Fin n → ℝ) (k ℓ : ℕ)
    (ρ : Equiv.Perm (Fin n)) (A : Finset (Fin n)) (z : SplitPrefixSeed ℓ ρ)
    (hz : z.2.1 ∈ historyPastSection w k ℓ ρ A) :
    sequentialSampler w k (assemblePrefixSeed ℓ ρ z) =
      A ∪ futureContinuation w ℓ ρ (k - A.card) (z.1, z.2.2) := by
  have hA : historySelected w k ℓ (assemblePrefixSeed ℓ ρ z) = A := by
    apply (prefixPastSection_spec (historySelected_prefixObservable w k ℓ A) ρ
      (assemblePrefixSeed ℓ ρ z) (assemblePrefixSeed_prefix ℓ ρ z)).mpr
    simpa [assemblePrefixSeed, historyPastSection] using hz
  rw [sequentialSampler_eq_history_union_continuation w k ℓ (assemblePrefixSeed ℓ ρ z), hA]
  change A ∪ historyContinuation w k ℓ (assemblePrefixSeed ℓ ρ z) = _
  rw [historyContinuation_assemble w k ℓ ρ A z hz]

theorem historyOutput_integral {n : ℕ} (w : Fin n → ℝ) (hw : ∀ i, 0 < w i)
    (k ℓ : ℕ) (ρ : Equiv.Perm (Fin n)) (A : Finset (Fin n))
    (hr : k - A.card ≤ (remainingSet ℓ ρ).card) (f : Finset (Fin n) → ℝ) :
    (∫ ω in historyEvent w k ℓ ρ A, f (sequentialSampler w k ω) ∂seedMeasure n) =
      (seedMeasure n (historyEvent w k ℓ ρ A)).toReal *
        lawExpectation (restrictedLaw w hw (remainingSet ℓ ρ) (k - A.card) hr) (fun S => f (A ∪ S)) := by
  have hf : Measurable (sequentialSampler w k) :=
    (measurable_sequentialSampler k).comp (measurable_const.prodMk measurable_id)
  have hg : Measurable (fun z => A ∪ futureContinuation w ℓ ρ (k - A.card) z) :=
    (measurable_of_finite (fun S : Finset (Fin n) => A ∪ S)).comp
      (measurable_futureContinuation w ℓ ρ (k - A.card))
  rw [historyEvent_integral w k ℓ ρ A (sequentialSampler w k) hf
    (fun z => A ∪ futureContinuation w ℓ ρ (k - A.card) z) hg
    (fun z hz => samplerOutput_assemble w k ℓ ρ A z hz) f]
  congr 1
  have hp := futureContinuation_measurePreserving w hw ℓ ρ (k - A.card) hr
  have hm : Measurable (fun S : Finset (Fin n) => f (A ∪ S)) := measurable_of_finite _
  have hi := integral_map (μ := prefixFutureMeasure ℓ ρ) hp.measurable.aemeasurable hm.aestronglyMeasurable
  rw [hp.map_eq, integral_lawMeasure] at hi
  exact hi.symm

def historyConditionalExpectation {n : ℕ} (w : Fin n → ℝ) (k ℓ : ℕ)
    (ρ : Equiv.Perm (Fin n)) (A : Finset (Fin n)) (f : Finset (Fin n) → ℝ) : ℝ :=
  (∫ ω in historyEvent w k ℓ ρ A, f (sequentialSampler w k ω) ∂seedMeasure n) /
    (seedMeasure n (historyEvent w k ℓ ρ A)).toReal

theorem historyConditionalExpectation_eq {n : ℕ} (w : Fin n → ℝ) (hw : ∀ i, 0 < w i)
    (k ℓ : ℕ) (hk : k ≤ n) (ρ : Equiv.Perm (Fin n)) (A : Finset (Fin n))
    (hH : 0 < seedMeasure n (historyEvent w k ℓ ρ A)) (f : Finset (Fin n) → ℝ) :
    historyConditionalExpectation w k ℓ ρ A f =
      lawExpectation (restrictedLaw w hw (remainingSet ℓ ρ) (k - A.card)
        (historyEvent_quota_admissible w k ℓ hk ρ A hH)) (fun S => f (A ∪ S)) := by
  unfold historyConditionalExpectation
  rw [historyOutput_integral w hw k ℓ ρ A (historyEvent_quota_admissible w k ℓ hk ρ A hH)]
  have hz : (seedMeasure n (historyEvent w k ℓ ρ A)).toReal ≠ 0 :=
    ENNReal.toReal_ne_zero.mpr ⟨hH.ne', measure_ne_top _ _⟩
  field_simp

theorem historySelected_disjoint_remaining {n : ℕ} (w : Fin n → ℝ) (k ℓ : ℕ)
    (ρ : Equiv.Perm (Fin n)) (A : Finset (Fin n))
    (hH : 0 < seedMeasure n (historyEvent w k ℓ ρ A)) : Disjoint A (remainingSet ℓ ρ) := by
  have hne : (historyEvent w k ℓ ρ A).Nonempty := by
    by_contra h
    rw [Set.not_nonempty_iff_eq_empty.mp h, measure_empty] at hH
    exact lt_irrefl _ hH
  obtain ⟨ω, hπ, hA⟩ := hne
  have hd : Disjoint (((List.ofFn ω.1).take ℓ).toFinset) (((List.ofFn ω.1).drop ℓ).toFinset) :=
    List.disjoint_toFinset_iff_disjoint.mpr
      (List.disjoint_take_drop (List.nodup_ofFn.mpr ω.1.injective) le_rfl)
  rw [permutation_drop_toFinset, prefixMatches_remainingSet hπ] at hd
  apply hd.mono_left
  rw [← hA, historySelected_eq_output_inter]
  exact Finset.inter_subset_right

theorem residual_variance_union {ι : Type*} [Fintype ι] [DecidableEq ι]
    (w : ι → ℝ) (hw : ∀ i, 0 < w i) (R : Finset ι) (r : ℕ) (hr : r ≤ R.card)
    (A : Finset ι) (hA : Disjoint A R) (a : ι → ℝ) :
    lawVariance (restrictedLaw w hw R r hr) (fun S => subsetLinearStatistic a (A ∪ S)) =
      residualVariance w hw R r hr a := by
  have hval (S : Finset ι) (hS : S ∈ R.powersetCard r) :
      subsetLinearStatistic a (A ∪ S) = subsetLinearStatistic a A + 1 * subsetLinearStatistic a S := by
    have hd : Disjoint A S := hA.mono_right (Finset.mem_powersetCard.mp hS).1
    simp [subsetLinearStatistic, Finset.sum_union hd]
  have hm : lawExpectation (restrictedLaw w hw R r hr) (fun S => subsetLinearStatistic a (A ∪ S)) =
      lawExpectation (restrictedLaw w hw R r hr) (fun S => subsetLinearStatistic a A + 1 * subsetLinearStatistic a S) :=
    restrictedSum_congr w R r _ _ hval
  calc
    _ = lawVariance (restrictedLaw w hw R r hr) (fun S => subsetLinearStatistic a A + 1 * subsetLinearStatistic a S) := by
      unfold lawVariance
      rw [hm]
      apply restrictedSum_congr
      intro S hS
      dsimp only
      rw [hval S hS]
    _ = _ := by rw [lawVariance_affine]; simp [residualVariance]

def historyConditionalVariance {n : ℕ} (w : Fin n → ℝ) (k ℓ : ℕ)
    (ρ : Equiv.Perm (Fin n)) (A : Finset (Fin n)) (a : Fin n → ℝ) : ℝ :=
  historyConditionalExpectation w k ℓ ρ A (fun S =>
    (subsetLinearStatistic a S - historyConditionalExpectation w k ℓ ρ A (subsetLinearStatistic a)) ^ 2)

/-- The variance of the total statistic under conditioning on the actual
revealed history is exactly its residual covariance energy. -/
theorem historyConditionalVariance_eq_covariance {n : ℕ} (w : Fin n → ℝ) (hw : ∀ i, 0 < w i)
    (k ℓ : ℕ) (hk : k ≤ n) (ρ : Equiv.Perm (Fin n)) (A : Finset (Fin n))
    (hH : 0 < seedMeasure n (historyEvent w k ℓ ρ A)) (a : Fin n → ℝ) :
    historyConditionalVariance w k ℓ ρ A a =
      quadraticForm (residualCovariance w (remainingSet ℓ ρ) (k - A.card)) a := by
  unfold historyConditionalVariance
  rw [historyConditionalExpectation_eq w hw k ℓ hk ρ A hH,
    historyConditionalExpectation_eq w hw k ℓ hk ρ A hH]
  change lawVariance (restrictedLaw w hw (remainingSet ℓ ρ) (k - A.card)
    (historyEvent_quota_admissible w k ℓ hk ρ A hH))
      (fun S => subsetLinearStatistic a (A ∪ S)) = _
  rw [residual_variance_union w hw _ _ _ A (historySelected_disjoint_remaining w k ℓ ρ A hH),
    residualVariance_eq_covariance]

theorem historyConditional_cut_variance {n : ℕ} (w : Fin n → ℝ) (hw : ∀ i, 0 < w i)
    (k ℓ : ℕ) (hk : k ≤ n) (ω : Seed n)
    (hH : 0 < seedMeasure n (historyEvent w k ℓ ω.1 (historySelected w k ℓ ω)))
    (a : Fin n → ℝ) (s : ℝ) :
    historyConditionalVariance w k ℓ ω.1 (historySelected w k ℓ ω) (cutVector a s) =
      samplerCutVariance w k ℓ a s ω := by
  rw [historyConditionalVariance_eq_covariance w hw k ℓ hk _ _ hH]
  simp only [samplerCutVariance, samplerCovariance, historyRemaining,
    permutation_drop_toFinset, historyQuota]

end
end CoefficientOne.Sampling
