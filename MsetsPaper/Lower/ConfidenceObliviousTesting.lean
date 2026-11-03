import MsetsPaper.Lower.ConfidenceObliviousBudget
import MsetsPaper.Lower.ConfidenceObliviousAveraging
import MsetsPaper.Probability.BinaryKL

/-! # Joint convexity, event data processing, and the strict confidence separation -/

namespace MsetsPaper.Lower.ConfidenceOblivious

open MsetsLower MsetsLower.Lower MsetsLower.Lower.Confidence MsetsPaper.Probability
open MsetsPaper.Probability.PolicySeed
open MeasureTheory ProbabilityTheory InformationTheory Set
open scoped ENNReal ProbabilityTheory BigOperators

noncomputable section

theorem binary_confidence_separation {a b delta : ℝ}
    (ha : a ∈ Icc (0 : ℝ) 1) (hb : b ∈ Icc (0 : ℝ) 1)
    (hc : BinaryCompatible a b) (ha_lower : (1 : ℝ) / 16 ≤ a)
    (hdelta : 0 < delta) (hdsmall : delta ≤ (2 : ℝ) ^ (-36 : ℤ))
    (hKL : binaryKL a b ≤ (2 : ℝ) ^ (-12 : ℤ) * Real.log (1 / delta)) :
    delta < b := by
  by_contra hnot
  have hbd : b ≤ delta := le_of_not_gt hnot
  have hb0 : 0 < b := by
    by_contra h
    have hz : b = 0 := le_antisymm (le_of_not_gt h) hb.1
    have := hc.1 hz
    linarith
  have hb1 : b < 1 := hbd.trans_lt (hdsmall.trans_lt (by norm_num))
  have hlog := log_inverse_positive hdelta hdsmall
  have hlog_two := log_inverse_ge_thirty_six_log_two hdelta hdsmall
  have hlog_order : Real.log (1 / delta) ≤ Real.log (1 / b) :=
    Real.log_le_log (by positivity) (one_div_le_one_div_of_le hb0 hbd)
  have hlow := binaryKL_lower_bound ha.1 ha.2 hb0 hb1
  have hmul := mul_le_mul_of_nonneg_left hlog_order ha.1
  have hmul_lower := mul_le_mul_of_nonneg_right ha_lower hlog.le
  rw [show (2 : ℝ) ^ (-12 : ℤ) = 1 / 4096 by norm_num] at hKL
  linarith

theorem finite_binary_confidence_separation {ι : Type*} [Fintype ι]
    (w p q : ι → ℝ) (hw : ∀ i, 0 ≤ w i) (hwsum : ∑ i, w i = 1)
    (hp : ∀ i, p i ∈ Icc (0 : ℝ) 1) (hq : ∀ i, q i ∈ Icc (0 : ℝ) 1)
    (hc : ∀ i, BinaryCompatible (p i) (q i))
    {delta : ℝ} (hdelta : 0 < delta) (hdsmall : delta ≤ (2 : ℝ) ^ (-36 : ℤ))
    (hp_lower : (1 : ℝ) / 16 ≤ ∑ i, w i * p i)
    (hKL : (∑ i, w i * binaryKL (p i) (q i)) ≤
      (2 : ℝ) ^ (-12 : ℤ) * Real.log (1 / delta)) :
    delta < ∑ i, w i * q i := by
  have hmem (f : ι → ℝ) (hf : ∀ i, f i ∈ Icc (0 : ℝ) 1) :
      (∑ i, w i * f i) ∈ Icc (0 : ℝ) 1 := by
    constructor
    · exact Finset.sum_nonneg fun i _ => mul_nonneg (hw i) (hf i).1
    · calc
        _ ≤ ∑ i, w i * 1 := Finset.sum_le_sum fun i _ =>
          mul_le_mul_of_nonneg_left (hf i).2 (hw i)
        _ = 1 := by simpa using hwsum
  exact binary_confidence_separation (hmem p hp) (hmem q hq)
    (BinaryCompatible_finite_mixture w p q hw hwsum hp hq hc) hp_lower hdelta hdsmall
    ((binaryKL_finite_mixture w p q hw hwsum hp hq hc).trans hKL)

theorem weighted_events_confidence_separation {ι Ω : Type*} [Fintype ι] [MeasurableSpace Ω]
    (w : ι → ℝ) (hw : ∀ i, 0 ≤ w i) (hwsum : ∑ i, w i = 1)
    (P : Measure Ω) (Q : ι → Measure Ω)
    [IsProbabilityMeasure P] [∀ i, IsProbabilityMeasure (Q i)]
    (E : ι → Set Ω) (hE : ∀ i, MeasurableSet (E i))
    (hfinite : ∀ i, klDiv P (Q i) ≠ ∞)
    {delta : ℝ} (hdelta : 0 < delta) (hdsmall : delta ≤ (2 : ℝ) ^ (-36 : ℤ))
    (hp_lower : (1 : ℝ) / 16 ≤ ∑ i, w i * P.real (E i))
    (hKL : (∑ i, w i * (klDiv P (Q i)).toReal) ≤
      (2 : ℝ) ^ (-12 : ℤ) * Real.log (1 / delta)) :
    delta < ∑ i, w i * (Q i).real (E i) := by
  have hprob (μ : Measure Ω) [IsProbabilityMeasure μ] (S : Set Ω) :
      μ.real S ∈ Icc (0 : ℝ) 1 :=
    ⟨measureReal_nonneg, (measureReal_mono (subset_univ S)).trans_eq probReal_univ⟩
  apply finite_binary_confidence_separation w (fun i => P.real (E i))
    (fun i => (Q i).real (E i)) hw hwsum (fun i => hprob P (E i))
    (fun i => hprob (Q i) (E i))
    (fun i => binaryKL_event_compatible P (Q i) (hE i) (klDiv_ne_top_iff.mp (hfinite i)).1)
    hdelta hdsmall hp_lower
  exact (Finset.sum_le_sum (fun i _ => mul_le_mul_of_nonneg_left
    (binaryKL_event_le_klDiv P (Q i) (hE i) (hfinite i)) (hw i))).trans hKL

theorem sum_candidate_weights {d m : ℕ} (hmd : m ≤ d)
    (hN : 0 < (confidenceCandidates d m hmd).card) :
    (∑ i : Fin d, if i ∈ confidenceCandidates d m hmd then
      (1 : ℝ) / (confidenceCandidates d m hmd).card else 0) = 1 := by
  classical
  have hNr : ((confidenceCandidates d m hmd).card : ℝ) ≠ 0 := by exact_mod_cast hN.ne'
  simp [Finset.sum_ite_mem, hNr]

theorem sum_candidate_weighted {d m : ℕ} (hmd : m ≤ d) (f : Fin d → ℝ) :
    (∑ i : Fin d, (if i ∈ confidenceCandidates d m hmd then
      (1 : ℝ) / (confidenceCandidates d m hmd).card else 0) * f i) =
      (∑ i ∈ confidenceCandidates d m hmd, f i) / (confidenceCandidates d m hmd).card := by
  classical
  simp only [ite_mul, zero_mul, one_div_mul_eq_div]
  simp [Finset.sum_ite_mem, Finset.sum_div]

theorem auxiliary_planted_average_event_gt {d m T : ℕ}
    (P : Policy d m) (hm : 1 ≤ m) (h2m : 2 * m ≤ d) (hmd : m ≤ d)
    {delta : ℝ} (hdelta : 0 < delta) (hdsmall : delta ≤ (2 : ℝ) ^ (-36 : ℤ))
    (hT : 4 * (d : ℝ) * (m : ℝ) ^ 2 * Real.log (1 / delta) ≤ T)
    (r : Seeds T) (j : Fin d) (hj : j ∈ confidenceCandidates d m hmd)
    (hp : 0 < gap hmd T delta) (hs : (m : ℝ) * gap hmd T delta ≤ 1 / 2 ^ 13) :
    let Delta := gap hmd T delta
    let A := auxiliaryPolicy P hmd r (Delta * T / 8) (coreComparator hm hmd j hj)
    delta < (∑ i ∈ confidenceCandidates d m hmd,
      (plantedMixture A hm hmd Delta hp.le hs i T).real (scoreEvent hmd Delta i T)) /
        (confidenceCandidates d m hmd).card := by
  classical
  dsimp only
  let Delta := gap hmd T delta
  let A := auxiliaryPolicy P hmd r (Delta * T / 8) (coreComparator hm hmd j hj)
  let w (i : Fin d) : ℝ := if i ∈ confidenceCandidates d m hmd then
    1 / (confidenceCandidates d m hmd).card else 0
  have hN := (candidate_card_bounds hm h2m hmd).1
  have hNpos : 0 < (confidenceCandidates d m hmd).card := by omega
  have ht := horizon_pos hm h2m hdelta hdsmall hT
  have hmpos : (0 : ℝ) < m := by exact_mod_cast (show 0 < m by omega)
  have hNr : (2 : ℝ) ≤ (confidenceCandidates d m hmd).card := by exact_mod_cast hN
  have hscale : Delta ≤ ((confidenceCandidates d m hmd).card : ℝ) / (8 * m) := by
    apply (le_div_iff₀ (by positivity : (0 : ℝ) < 8 * m)).mpr
    change (m : ℝ) * Delta ≤ 1 / 2 ^ 13 at hs
    nlinarith
  have href := auxiliary_reference_average_event P hm hmd hN ht Delta hp hscale r j hj
  change (5 : ℝ) / 24 ≤ (∑ i ∈ confidenceCandidates d m hmd,
    (referenceMixture A hm hmd T).real (scoreEvent hmd Delta i T)) / _ at href
  rw [referenceMixture_eq_process A hm hmd Delta hp.le hs T] at href
  have hw (i : Fin d) : 0 ≤ w i := by dsimp [w]; split_ifs <;> positivity
  have hwsum : ∑ i, w i = 1 := sum_candidate_weights hmd hNpos
  have hbound := auxiliary_average_KL_gap_le P hm h2m hmd hdelta hdsmall hT r j hj
  have hresult := weighted_events_confidence_separation w hw hwsum
    ((referenceProcess A hm hmd Delta hp.le hs).law T)
    (fun i => (plantedProcess A hm hmd Delta hp.le hs i).law T)
    (fun i => scoreEvent hmd Delta i T) (fun i => measurableSet_scoreEvent hmd Delta i T)
    (fun i => reference_planted_KL_finite A hm hmd Delta hp.le hs i)
    hdelta hdsmall
    (by
      rw [sum_candidate_weighted]
      linarith [href])
    (by
      rw [sum_candidate_weighted]
      exact hbound)
  rw [sum_candidate_weighted] at hresult
  simpa only [plantedMixture_eq_process] using hresult

end
end MsetsPaper.Lower.ConfidenceOblivious
