import MsetsPaper.Lower.ConfidenceObliviousCounts
import MsetsPaper.Lower.ConfidenceObliviousTableBridge
import MsetsPaper.Lower.ConfidenceObliviousSeeded
import MsetsPaper.Lower.ConfidenceObliviousParameters

/-! # The stopped learner's actual averaged KL budget -/

namespace MsetsPaper.Lower.ConfidenceOblivious

open MsetsLower MsetsLower.Feedback MsetsLower.Lower MsetsLower.Lower.Confidence
open MsetsPaper.Probability.PolicySeed
open MeasureTheory ProbabilityTheory InformationTheory Set
open scoped ENNReal ProbabilityTheory BigOperators

noncomputable section

theorem auxiliary_reference_penalty_ae {d m T : ℕ}
    (P : Policy d m) (hm : 1 ≤ m) (hmd : m ≤ d) (hT : 0 < T)
    (Delta : ℝ) (hDelta : 0 < Delta) (hsmall : (m : ℝ) * Delta ≤ 1 / 2 ^ 13)
    (r : Seeds T) (j : Fin d) (hj : j ∈ confidenceCandidates d m hmd) :
    let A := auxiliaryPolicy P hmd r (Delta * T / 8) (coreComparator hm hmd j hj)
    ∀ᵐ h ∂(referenceProcess A hm hmd Delta hDelta.le hsmall).law T,
      cumulativePenalty hmd T h < Delta * T / 8 := by
  dsimp only
  rw [← referenceMixture_eq_process]
  apply Measure.ae_comp_of_ae_ae
    (measurableSet_lt (measurable_cumulativePenalty hmd T) measurable_const)
  apply ae_of_all
  intro Z
  rw [parametricRunKernel_apply]
  exact auxiliaryPolicy_penalty_ae P hm hmd r (Delta * T / 8)
    (by positivity) j hj ((referenceTableLossProcess hm hmd T).at Z) T

theorem auxiliary_reference_total_candidate_pulls_lt_ae {d m T : ℕ}
    (P : Policy d m) (hm : 1 ≤ m) (hmd : m ≤ d) (hT : 0 < T)
    (Delta : ℝ) (hDelta : 0 < Delta) (hsmall : (m : ℝ) * Delta ≤ 1 / 2 ^ 13)
    (r : Seeds T) (j : Fin d) (hj : j ∈ confidenceCandidates d m hmd) :
    let A := auxiliaryPolicy P hmd r (Delta * T / 8) (coreComparator hm hmd j hj)
    ∀ᵐ h ∂(referenceProcess A hm hmd Delta hDelta.le hsmall).law T,
      History.actionSum (fun a => (candidateCount hmd a : ℝ)) T h < T * (1 + m * Delta) := by
  dsimp only
  rw [← referenceMixture_eq_process]
  have hmeas : Measurable (History.actionSum (fun a => (candidateCount hmd a : ℝ)) T) :=
    History.measurable_actionSum_of_finite _ T
  apply Measure.ae_comp_of_ae_ae (measurableSet_lt hmeas measurable_const)
  apply ae_of_all
  intro Z
  rw [parametricRunKernel_apply, auxiliaryPolicy_runLaw]
  apply (ae_dirac_iff (measurableSet_lt hmeas measurable_const)).2
  exact auxiliaryRun_total_candidate_pulls_lt P hm hmd hT Delta hDelta r j hj _

theorem auxiliary_reference_expected_totalCount_le {d m T : ℕ}
    (P : Policy d m) (hm : 1 ≤ m) (hmd : m ≤ d) (hT : 0 < T)
    (Delta : ℝ) (hDelta : 0 < Delta) (hsmall : (m : ℝ) * Delta ≤ 1 / 2 ^ 13)
    (r : Seeds T) (j : Fin d) (hj : j ∈ confidenceCandidates d m hmd) :
    let A := auxiliaryPolicy P hmd r (Delta * T / 8) (coreComparator hm hmd j hj)
    (∑ i ∈ confidenceCandidates d m hmd, ∫ h, History.selectedCount i T h
      ∂(referenceProcess A hm hmd Delta hDelta.le hsmall).law T) ≤
      T * (1 + m * Delta) := by
  dsimp only
  let A := auxiliaryPolicy P hmd r (Delta * T / 8) (coreComparator hm hmd j hj)
  let μ : Measure (History d m T) := (referenceProcess A hm hmd Delta hDelta.le hsmall).law T
  letI : IsProbabilityMeasure μ := by dsimp [μ]; infer_instance
  have hi (i : Fin d) : Integrable (History.selectedCount (m := m) i T) μ := by
    dsimp only [μ]
    exact Integrable.of_mem_Icc 0 (T : ℝ)
      (History.measurable_selectedCount (m := m) i T).aemeasurable
      (ae_of_all _ (History.selectedCount_mem_Icc i T))
  rw [← integral_finsetSum _ (fun i _ => hi i)]
  have hb : ∀ᵐ h ∂μ,
      (∑ i ∈ confidenceCandidates d m hmd, History.selectedCount i T h) ≤
        T * (1 + m * Delta) := by
    filter_upwards [auxiliary_reference_total_candidate_pulls_lt_ae P hm hmd hT
      Delta hDelta hsmall r j hj] with h hh
    rw [sum_selectedCount_candidates]
    exact hh.le
  have hc : Integrable (fun _ : History d m T => (T : ℝ) * (1 + m * Delta)) μ := by
    dsimp only [μ]
    exact integrable_const _
  have hint := integral_mono_ae (integrable_finset_sum _ (fun i _ => hi i)) hc hb
  have hu : μ.real univ = 1 := by dsimp only [μ]; exact probReal_univ
  simpa [integral_const, hu] using hint

theorem auxiliary_average_KL_le {d m T : ℕ}
    (P : Policy d m) (hm : 1 ≤ m) (hmd : m ≤ d) (hT : 0 < T)
    (Delta : ℝ) (hDelta : 0 < Delta) (hsmall : (m : ℝ) * Delta ≤ 1 / 2 ^ 13)
    (r : Seeds T) (j : Fin d) (hj : j ∈ confidenceCandidates d m hmd) :
    let A := auxiliaryPolicy P hmd r (Delta * T / 8) (coreComparator hm hmd j hj)
    (∑ i ∈ confidenceCandidates d m hmd,
      (klDiv ((referenceProcess A hm hmd Delta hDelta.le hsmall).law T)
        ((plantedProcess A hm hmd Delta hDelta.le hsmall i).law T)).toReal) /
      (confidenceCandidates d m hmd).card ≤
      2 ^ 11 * (Delta ^ 2 * T / (confidenceCandidates d m hmd).card) * (1 + m * Delta) := by
  dsimp only
  let A := auxiliaryPolicy P hmd r (Delta * T / 8) (coreComparator hm hmd j hj)
  have hs := Finset.sum_le_sum (s := confidenceCandidates d m hmd) (fun i _ =>
    reference_planted_KL_toReal_le (T := T) A hm hmd Delta hDelta.le hsmall i)
  rw [← Finset.mul_sum] at hs
  have hb := mul_le_mul_of_nonneg_left
    (auxiliary_reference_expected_totalCount_le P hm hmd hT Delta hDelta hsmall r j hj)
    (by positivity : (0 : ℝ) ≤ 128 * (4 * Delta) ^ 2)
  have hd := div_le_div_of_nonneg_right (hs.trans hb)
    (show (0 : ℝ) ≤ (confidenceCandidates d m hmd).card by positivity)
  refine hd.trans_eq ?_
  ring

theorem auxiliary_average_KL_gap_le {d m T : ℕ}
    (P : Policy d m) (hm : 1 ≤ m) (h2m : 2 * m ≤ d) (hmd : m ≤ d)
    {delta : ℝ} (hdelta : 0 < delta) (hdsmall : delta ≤ (2 : ℝ) ^ (-36 : ℤ))
    (hT : 4 * (d : ℝ) * (m : ℝ) ^ 2 * Real.log (1 / delta) ≤ T)
    (r : Seeds T) (j : Fin d) (hj : j ∈ confidenceCandidates d m hmd) :
    let ht := horizon_pos hm h2m hdelta hdsmall hT
    let hp := gap_pos hm h2m hmd hdelta hdsmall ht
    let hs : (m : ℝ) * gap hmd T delta ≤ 1 / 2 ^ 13 := by
      have hh := (gap_small hm h2m hmd hdelta hdsmall hT).1
      norm_num at hh ⊢
      exact hh
    let A := auxiliaryPolicy P hmd r (gap hmd T delta * T / 8) (coreComparator hm hmd j hj)
    (∑ i ∈ confidenceCandidates d m hmd,
      (klDiv ((referenceProcess A hm hmd (gap hmd T delta) hp.le hs).law T)
        ((plantedProcess A hm hmd (gap hmd T delta) hp.le hs i).law T)).toReal) /
      (confidenceCandidates d m hmd).card ≤ (2 : ℝ) ^ (-12 : ℤ) * Real.log (1 / delta) := by
  dsimp only
  have ht := horizon_pos hm h2m hdelta hdsmall hT
  have hp := gap_pos hm h2m hmd hdelta hdsmall ht
  have hs : (m : ℝ) * gap hmd T delta ≤ 1 / 2 ^ 13 := by
    have hh := (gap_small hm h2m hmd hdelta hdsmall hT).1
    norm_num at hh ⊢
    exact hh
  have h := auxiliary_average_KL_le P hm hmd ht (gap hmd T delta) hp hs r j hj
  rw [gap_square_time_div_candidates hm h2m hmd hdelta hdsmall ht] at h
  apply h.trans
  have hlog := (log_inverse_positive hdelta hdsmall).le
  have hbound : 1 + (m : ℝ) * gap hmd T delta ≤ 2 := by linarith
  have hh := mul_le_mul_of_nonneg_left hbound
    (show 0 ≤ (2 : ℝ) ^ 11 * ((2 : ℝ) ^ (-24 : ℤ) * Real.log (1 / delta)) by positivity)
  norm_num at hh ⊢
  linarith

end
end MsetsPaper.Lower.ConfidenceOblivious
