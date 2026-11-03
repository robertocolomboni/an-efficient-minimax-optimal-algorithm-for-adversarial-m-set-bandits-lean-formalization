import CoefficientOne.Sampling.VarianceTelescope
import CoefficientOne.Sampling.UnitCurrentCovariance

/-! # The complete variation bound for the positive-weight common-seed sampler -/

open scoped BigOperators
open EffectiveResistance Matrix MeasureTheory
namespace CoefficientOne.Sampling
noncomputable section

def statePhiContribution {n : ℕ} (w : Fin n → ℝ) (hw : ∀ i, 0 < w i) (k ℓ : ℕ)
    (a : Fin n → ℝ) (ω : Seed n) : ℝ :=
  (residualNetwork w hw (historyRemaining ℓ ω) (historyQuota w k ℓ ω)).edgeVariation a /
    (historyRemaining ℓ ω).card

theorem integrable_statePhiContribution {n : ℕ} (w : Fin n → ℝ) (hw : ∀ i, 0 < w i)
    (k ℓ : ℕ) (a : Fin n → ℝ) : Integrable (statePhiContribution w hw k ℓ a) (seedMeasure n) :=
  integrable_historyStatistic w k ℓ (fun z => (residualNetwork w hw z.1 z.2).edgeVariation a / z.1.card)

theorem variationContribution_le_two_phi {n : ℕ} (w : Fin n → ℝ) (hw : ∀ i, 0 < w i)
    (k ℓ : ℕ) (a : Fin n → ℝ) (ω : Seed n) :
    variationContribution w k ℓ a ω ≤ 2 * statePhiContribution w hw k ℓ a ω := by
  have h := l1_laplacian_le_two_edgeVariation
    (residualNetwork w hw (historyRemaining ℓ ω) (historyQuota w k ℓ ω)) a
  rw [residualNetwork_laplacian] at h
  have hd := div_le_div_of_nonneg_right h (Nat.cast_nonneg (historyRemaining ℓ ω).card)
  simpa only [variationContribution, samplerCovariance, statePhiContribution, mul_div_assoc] using hd

theorem statePhi_coarea {n : ℕ} (w : Fin n → ℝ) (hw : ∀ i, 0 < w i)
    (k ℓ : ℕ) (a : Fin n → ℝ) :
    (∫ ω, statePhiContribution w hw k ℓ a ω ∂seedMeasure n) =
      ∫ s : ℝ, ∫ ω, quadraticForm (samplerCovariance w k ℓ ω) (cutVector a s) /
        (historyRemaining ℓ ω).card ∂seedMeasure n := by
  have h := finite_state_coarea (seedMeasure n)
    (fun ω : Seed n => (ω.1, sequentialSampler w k ω)) (measurable_samplerOrderOutput w k)
    (fun z => residualNetwork w hw (outputHistoryState k ℓ z).1 (outputHistoryState k ℓ z).2)
    (fun z => ((outputHistoryState k ℓ z).1.card : ℝ)⁻¹) a
  simp_rw [← samplerHistoryState_eq_outputHistoryState, samplerHistoryState,
    residualNetwork_laplacian] at h
  simpa only [statePhiContribution, samplerCovariance, div_eq_mul_inv, mul_comm] using h

theorem integrable_expected_stateCut {n : ℕ} (w : Fin n → ℝ) (hw : ∀ i, 0 < w i)
    (k ℓ : ℕ) (a : Fin n → ℝ) :
    Integrable (fun s : ℝ => ∫ ω, quadraticForm (samplerCovariance w k ℓ ω) (cutVector a s) /
      (historyRemaining ℓ ω).card ∂seedMeasure n) := by
  have h := integrable_finite_state_cut (seedMeasure n)
    (fun ω : Seed n => (ω.1, sequentialSampler w k ω)) (measurable_samplerOrderOutput w k)
    (fun z => residualNetwork w hw (outputHistoryState k ℓ z).1 (outputHistoryState k ℓ z).2)
    (fun z => ((outputHistoryState k ℓ z).1.card : ℝ)⁻¹) a
  simp_rw [← samplerHistoryState_eq_outputHistoryState, samplerHistoryState,
    residualNetwork_laplacian] at h
  simpa only [samplerCovariance, div_eq_mul_inv, mul_comm] using h

theorem samplerVariation_le_twice_integrated_cuts {n : ℕ} (w : Fin n → ℝ)
    (hw : ∀ i, 0 < w i) (k : ℕ) (a : Fin n → ℝ) :
    samplerVariation w k a ≤ 2 * ∫ s : ℝ,
      ∑ ℓ ∈ Finset.range n, ∫ ω, quadraticForm (samplerCovariance w k ℓ ω) (cutVector a s) /
        (historyRemaining ℓ ω).card ∂seedMeasure n := by
  rw [samplerVariation_eq_sum]
  calc
    _ ≤ ∑ ℓ ∈ Finset.range n, 2 * ∫ ω, statePhiContribution w hw k ℓ a ω ∂seedMeasure n := by
      apply Finset.sum_le_sum
      intro ℓ _
      rw [← integral_const_mul]
      exact integral_mono (integrable_variationContribution w k ℓ a)
        ((integrable_statePhiContribution w hw k ℓ a).const_mul 2)
        (variationContribution_le_two_phi w hw k ℓ a)
    _ = 2 * ∑ ℓ ∈ Finset.range n, ∫ ω, statePhiContribution w hw k ℓ a ω ∂seedMeasure n := by
      rw [Finset.mul_sum]
    _ = _ := by
      congr 1
      simp_rw [statePhi_coarea w hw k]
      rw [integral_finsetSum _ (fun ℓ _ => integrable_expected_stateCut w hw k ℓ a)]

/-- The dynamic-to-static bound, including all forced and endpoint states. -/
theorem samplerVariation_le_two_residualPhi {n : ℕ} (w : Fin n → ℝ)
    (hw : ∀ i, 0 < w i) (k : ℕ) (hk : k ≤ n) (a : Fin n → ℝ) :
    samplerVariation w k a ≤ 2 * (residualNetwork w hw Finset.univ k).edgeVariation a := by
  have h := samplerVariation_le_twice_integrated_cuts w hw k a
  apply h.trans
  apply mul_le_mul_of_nonneg_left _ (by norm_num)
  rw [edgeVariation_eq_integral_cut_energy]
  apply integral_mono
  · exact integrable_finsetSum _ (fun ℓ _ => integrable_expected_stateCut w hw k ℓ a)
  · exact integrable_cut_energy (residualNetwork w hw Finset.univ k) a
  · intro s
    rw [residualNetwork_laplacian, residualCovariance_univ w hw k (by simpa using hk)]
    have htel := sampler_variance_telescope w hw k hk (cutVector a s)
    have hQ (ℓ : ℕ) : Integrable (fun ω => quadraticForm (samplerCovariance w k ℓ ω) (cutVector a s) /
        (historyRemaining ℓ ω).card) (seedMeasure n) := integrable_historyStatistic w k ℓ
      (fun z => quadraticForm (residualCovariance w z.1 z.2) (cutVector a s) / z.1.card)
    rw [integral_finsetSum _ (fun ℓ _ => hQ ℓ)] at htel
    exact htel

theorem residualPhi_univ_eq_covariancePhi {n : ℕ} (w : Fin n → ℝ)
    (hw : ∀ i, 0 < w i) (k : ℕ) (hkpos : 1 ≤ k) (hktop : k ≤ n - 1) (a : Fin n → ℝ) :
    (residualNetwork w hw Finset.univ k).edgeVariation a =
      (externalFieldCovarianceNetwork w hw k hkpos (by simpa using hktop)).edgeVariation a := by
  rw [edgeVariation_eq_integral_cut_energy, edgeVariation_eq_integral_cut_energy]
  simp only [residualNetwork_laplacian,
    residualCovariance_univ w hw k (by simpa using (hktop.trans (Nat.sub_le n 1))),
    externalFieldCovarianceNetwork_laplacian]

/-- Both inequalities in the manuscript's variation lemma, for the actual
positive-weight sampler and every deterministic perturbation direction. -/
theorem samplerVariation_bound {n : ℕ} (w : Fin n → ℝ) (hw : ∀ i, 0 < w i)
    (k : ℕ) (hkpos : 1 ≤ k) (hktop : k ≤ n - 1) (a : Fin n → ℝ) :
    samplerVariation w k a ≤
      2 * (externalFieldCovarianceNetwork w hw k hkpos (by simpa using hktop)).edgeVariation a ∧
    2 * (externalFieldCovarianceNetwork w hw k hkpos (by simpa using hktop)).edgeVariation a ≤
      3 * l1Norm (covarianceMatrix w k *ᵥ a) := by
  constructor
  · have h := samplerVariation_le_two_residualPhi w hw k (hktop.trans (Nat.sub_le n 1)) a
    rwa [residualPhi_univ_eq_covariancePhi w hw k hkpos hktop] at h
  · have h := covariance_edgeVariation_le_three_halves_l1 w hw k hkpos (by simpa using hktop) a
    linarith

theorem samplerVariation_le_three_l1 {n : ℕ} (w : Fin n → ℝ) (hw : ∀ i, 0 < w i)
    (k : ℕ) (hkpos : 1 ≤ k) (hktop : k ≤ n - 1) (a : Fin n → ℝ) :
    samplerVariation w k a ≤ 3 * l1Norm (covarianceMatrix w k *ᵥ a) :=
  (samplerVariation_bound w hw k hkpos hktop a).1.trans
    (samplerVariation_bound w hw k hkpos hktop a).2

end
end CoefficientOne.Sampling
