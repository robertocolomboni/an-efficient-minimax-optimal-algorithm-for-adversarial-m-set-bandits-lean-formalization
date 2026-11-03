import CoefficientOne.Sampling.ResidualNetwork
import CoefficientOne.Sampling.SequentialHistory

/-! # Variation along the actual common-seed sampler

The covariance is zero-padded to the original coordinate space. The finite
sum runs over all n reveals; forced states have zero covariance. The complete
history trajectory is proved to have the order/output product-law description.
-/

open scoped BigOperators
open EffectiveResistance Matrix MeasureTheory
namespace CoefficientOne.Sampling
noncomputable section

def outputHistoryState {n : ℕ} (k ℓ : ℕ)
    (z : Equiv.Perm (Fin n) × Finset (Fin n)) : Finset (Fin n) × ℕ :=
  (((List.ofFn z.1).drop ℓ).toFinset,
    k - (z.2 ∩ ((List.ofFn z.1).take ℓ).toFinset).card)

def samplerHistoryState {n : ℕ} (w : Fin n → ℝ) (k ℓ : ℕ) (ω : Seed n) :
    Finset (Fin n) × ℕ := (historyRemaining ℓ ω, historyQuota w k ℓ ω)

theorem samplerHistoryState_eq_outputHistoryState {n : ℕ} (w : Fin n → ℝ)
    (k ℓ : ℕ) (ω : Seed n) :
    samplerHistoryState w k ℓ ω = outputHistoryState k ℓ (ω.1, sequentialSampler w k ω) := by
  simp only [samplerHistoryState, outputHistoryState, historyRemaining, historyQuota,
    historySelected_eq_output_inter]

theorem measurable_samplerOrderOutput {n : ℕ} (w : Fin n → ℝ) (k : ℕ) :
    Measurable (fun ω : Seed n => (ω.1, sequentialSampler w k ω)) := by
  exact measurable_fst.prodMk
    ((measurable_sequentialSampler k).comp (measurable_const.prodMk measurable_id))

theorem measurable_historyStatistic {n : ℕ} (w : Fin n → ℝ) (k ℓ : ℕ)
    (F : Finset (Fin n) × ℕ → ℝ) :
    Measurable (fun ω => F (samplerHistoryState w k ℓ ω)) := by
  simp_rw [samplerHistoryState_eq_outputHistoryState]
  have hf : Measurable (fun z : Equiv.Perm (Fin n) × Finset (Fin n) =>
      F (outputHistoryState k ℓ z)) := measurable_of_finite _
  exact fun _ hs => measurable_samplerOrderOutput w k (hf hs)

theorem integrable_historyStatistic {n : ℕ} (w : Fin n → ℝ) (k ℓ : ℕ)
    (F : Finset (Fin n) × ℕ → ℝ) :
    Integrable (fun ω => F (samplerHistoryState w k ℓ ω)) (seedMeasure n) := by
  simp_rw [samplerHistoryState_eq_outputHistoryState]
  let g := fun z : Equiv.Perm (Fin n) × Finset (Fin n) => F (outputHistoryState k ℓ z)
  have hg : Measurable g := measurable_of_finite _
  exact (integrable_map_measure hg.aestronglyMeasurable
    (measurable_samplerOrderOutput w k).aemeasurable).mp Integrable.of_finite

/-- Equality of the entire history law with the pre-sampled X description,
for every real function of that finite trajectory. -/
theorem historyTrajectory_integral_eq_product {n : ℕ} (w : Fin n → ℝ)
    (hw : ∀ i, 0 < w i) (k : ℕ) (hk : k ≤ n)
    (G : (ℕ → Finset (Fin n) × ℕ) → ℝ) :
    (∫ ω, G (fun ℓ => samplerHistoryState w k ℓ ω) ∂seedMeasure n) =
      ∫ z, G (fun ℓ => outputHistoryState k ℓ z)
        ∂((uniformMeasure (Equiv.Perm (Fin n))).prod
          (lawMeasure (restrictedLaw w hw Finset.univ k (by simpa using hk)))) := by
  have he (ω : Seed n) : (fun ℓ => samplerHistoryState w k ℓ ω) =
      fun ℓ => outputHistoryState k ℓ (ω.1, sequentialSampler w k ω) := by
    funext ℓ
    exact samplerHistoryState_eq_outputHistoryState w k ℓ ω
  simp_rw [he]
  have hm : Measurable (fun z : Equiv.Perm (Fin n) × Finset (Fin n) =>
      G (fun ℓ => outputHistoryState k ℓ z)) := measurable_of_finite _
  have hmp := sequentialSampler_joint_measurePreserving w hw k hk
  have hi := integral_map (μ := seedMeasure n) hmp.measurable.aemeasurable hm.aestronglyMeasurable
  rw [hmp.map_eq] at hi
  exact hi.symm

def samplerCovariance {n : ℕ} (w : Fin n → ℝ) (k ℓ : ℕ) (ω : Seed n) :
    Matrix (Fin n) (Fin n) ℝ :=
  residualCovariance w (historyRemaining ℓ ω) (historyQuota w k ℓ ω)

def variationContribution {n : ℕ} (w : Fin n → ℝ) (k ℓ : ℕ)
    (a : Fin n → ℝ) (ω : Seed n) : ℝ :=
  l1Norm (samplerCovariance w k ℓ ω *ᵥ a) / (historyRemaining ℓ ω).card

def samplerVariation {n : ℕ} (w : Fin n → ℝ) (k : ℕ) (a : Fin n → ℝ) : ℝ :=
  ∫ ω, ∑ ℓ ∈ Finset.range n, variationContribution w k ℓ a ω ∂seedMeasure n

def samplerCutVariance {n : ℕ} (w : Fin n → ℝ) (k ℓ : ℕ)
    (a : Fin n → ℝ) (s : ℝ) (ω : Seed n) : ℝ :=
  quadraticForm (samplerCovariance w k ℓ ω) (cutVector a s)

theorem samplerCovariance_terminal {n : ℕ} (w : Fin n → ℝ) (hw : ∀ i, 0 < w i)
    (k ℓ : ℕ) (ω : Seed n)
    (ht : historyQuota w k ℓ ω = 0 ∨ historyQuota w k ℓ ω = (historyRemaining ℓ ω).card) :
    samplerCovariance w k ℓ ω = 0 := by
  unfold samplerCovariance
  rcases ht with h | h
  · rw [h, residualCovariance_zero]
  · rw [h, residualCovariance_full w hw]

theorem variationContribution_terminal {n : ℕ} (w : Fin n → ℝ) (hw : ∀ i, 0 < w i)
    (k ℓ : ℕ) (a : Fin n → ℝ) (ω : Seed n)
    (ht : historyQuota w k ℓ ω = 0 ∨ historyQuota w k ℓ ω = (historyRemaining ℓ ω).card) :
    variationContribution w k ℓ a ω = 0 := by
  simp [variationContribution, samplerCovariance_terminal w hw k ℓ ω ht, l1Norm]

theorem integrable_variationContribution {n : ℕ} (w : Fin n → ℝ) (k ℓ : ℕ)
    (a : Fin n → ℝ) : Integrable (variationContribution w k ℓ a) (seedMeasure n) :=
  integrable_historyStatistic w k ℓ (fun z => l1Norm (residualCovariance w z.1 z.2 *ᵥ a) / z.1.card)

theorem integrable_samplerCutVariance {n : ℕ} (w : Fin n → ℝ) (k ℓ : ℕ)
    (a : Fin n → ℝ) (s : ℝ) : Integrable (samplerCutVariance w k ℓ a s) (seedMeasure n) :=
  integrable_historyStatistic w k ℓ (fun z => quadraticForm (residualCovariance w z.1 z.2) (cutVector a s))

theorem samplerVariation_eq_sum {n : ℕ} (w : Fin n → ℝ) (k : ℕ) (a : Fin n → ℝ) :
    samplerVariation w k a =
      ∑ ℓ ∈ Finset.range n, ∫ ω, variationContribution w k ℓ a ω ∂seedMeasure n := by
  exact integral_finsetSum _ (fun ℓ _ => integrable_variationContribution w k ℓ a)

end
end CoefficientOne.Sampling
