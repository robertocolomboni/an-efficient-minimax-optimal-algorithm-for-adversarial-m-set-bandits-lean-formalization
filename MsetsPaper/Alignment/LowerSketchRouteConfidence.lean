import MsetsPaper.Alignment.LowerSketch
import MsetsPaper.Probability.ProductFixingBridge

/-! Coefficient-80 confidence sketch, including the private-seed averaging
before selecting the planted index and the final product-space fixing. -/
namespace MsetsPaper.Alignment.LowerSketchRoute.Confidence
open MsetsLower MsetsLower.Lower MsetsLower.Lower.Confidence
open MsetsPaper.Lower MsetsPaper.Lower.ConfidenceOblivious
open MsetsPaper.Probability MsetsPaper.Probability.PolicySeed
open MeasureTheory ProbabilityTheory InformationTheory Set
open scoped ENNReal ProbabilityTheory BigOperators
noncomputable section

theorem reference_planted_KL_finite {d m T : ℕ}
    (P : Policy d m) (hm : 1 ≤ m) (hmd : m ≤ d)
    (Delta : ℝ) (hDelta : 0 ≤ Delta) (hsmall : (m : ℝ) * Delta ≤ 1 / 2 ^ 13) (i : Fin d) :
    klDiv ((referenceProcess P hm hmd Delta hDelta hsmall).law T)
      ((plantedProcess P hm hmd Delta hDelta hsmall i).law T) ≠ ∞ := by
  exact ne_of_lt (lt_of_le_of_lt (LowerSketch.Confidence.history_KL_eighty_expectedCount P hm hmd Delta hDelta hsmall i)
    (ENNReal.mul_lt_top ENNReal.ofReal_lt_top ENNReal.ofReal_lt_top))


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
  have h := LowerSketch.Confidence.auxiliary_average_KL_eighty P hm hmd ht
    (gap hmd T delta) hp hs r j hj
  have heq : 80 * (4 * gap hmd T delta) ^ 2 /
      (confidenceCandidates d m hmd).card * (T * (1 + m * gap hmd T delta)) =
      1280 * ((gap hmd T delta) ^ 2 * T / (confidenceCandidates d m hmd).card) *
        (1 + m * gap hmd T delta) := by ring
  rw [heq, gap_square_time_div_candidates hm h2m hmd hdelta hdsmall ht] at h
  apply h.trans
  have hlog := (log_inverse_positive hdelta hdsmall).le
  have hbound : 1 + (m : ℝ) * gap hmd T delta ≤ 2 := by linarith
  have hh := mul_le_mul_of_nonneg_left hbound
    (show 0 ≤ 1280 * ((2 : ℝ) ^ (-24 : ℤ) * Real.log (1 / delta)) by positivity)
  norm_num at hh ⊢
  nlinarith

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


theorem exists_planted_coordinate_joint_gt {d m T : ℕ}
    (P : Policy d m) (hm : 1 ≤ m) (h2m : 2 * m ≤ d) (hmd : m ≤ d)
    {delta : ℝ} (hdelta : 0 < delta) (hdsmall : delta ≤ (2 : ℝ) ^ (-36 : ℤ))
    (hT : 4 * (d : ℝ) * (m : ℝ) ^ 2 * Real.log (1 / delta) ≤ T)
    (hp : 0 < gap hmd T delta) (hs : (m : ℝ) * gap hmd T delta ≤ 1 / 2 ^ 13) :
    ∃ i ∈ confidenceCandidates d m hmd,
      delta < (parametricRunWithParameterKernel P
        (plantedTableLossProcess hm hmd (gap hmd T delta) hp.le hs i T) T ∘ₘ
          DenseCommonNoise.noiseTableMeasure T).real
          (parametricRegretEvent (plantedTableLossProcess hm hmd (gap hmd T delta) hp.le hs i T) T
            (gap hmd T delta * T / 8)) := by
  have hN := (candidate_card_bounds hm h2m hmd).1
  have hne : (confidenceCandidates d m hmd).Nonempty := Finset.card_pos.mp (by omega)
  obtain ⟨j, hj⟩ := hne
  let a := coreComparator hm hmd j hj
  let f := auxiliaryPlantedProbability (T := T) P hm hmd a (gap hmd T delta) hp.le hs
  have havg (r : Seeds T) :
      delta < (∑ i ∈ confidenceCandidates d m hmd, f i r) / (confidenceCandidates d m hmd).card := by
    dsimp only [f]
    simp_rw [auxiliaryPlantedProbability_eq_mixture]
    exact auxiliary_planted_average_event_gt P hm h2m hmd hdelta hdsmall hT r j hj hp hs
  obtain ⟨i, hi, hstrict⟩ := exists_index_integral_gt_of_average_gt
    (seedMeasure T) (confidenceCandidates d m hmd) ⟨j, hj⟩ f
    (fun i _ => measurable_auxiliaryPlantedProbability P hm hmd a (gap hmd T delta) hp.le hs i)
    (fun i _ r => auxiliaryPlantedProbability_mem_Icc P hm hmd a (gap hmd T delta) hp.le hs i r) havg
  refine ⟨i, hi, hstrict.trans_le ?_⟩
  exact auxiliary_seed_average_le_original_joint P hm hmd
    (horizon_pos hm h2m hdelta hdsmall hT) a (gap hmd T delta) hp hs i hi


theorem lower_confidence_oblivious {d m T : ℕ}
    (hm : 1 ≤ m) (h2m : 2 * m ≤ d)
    {delta : ℝ} (hdelta : 0 < delta) (hdsmall : delta ≤ (2 : ℝ) ^ (-36 : ℤ))
    (hT : 4 * (d : ℝ) * (m : ℝ) ^ 2 * Real.log (1 / delta) ≤ T) (P : Policy d m) :
    ∃ L : LossProcess d m,
      (∀ t (h h' : History d m t), L.itemLoss t h = L.itemLoss t h') ∧
      (∀ t (h : History d m t) i, L.itemLoss t h i ∈ Icc (0 : ℝ) (1 / m)) ∧
      delta ≤ (runLaw P L T).real
        {h | (2 : ℝ) ^ (-16 : ℤ) * Real.sqrt ((d : ℝ) * T * Real.log (1 / delta)) ≤
          pathRegret L T h} := by
  have hmd : m ≤ d := by omega
  have ht := horizon_pos hm h2m hdelta hdsmall hT
  have hp := gap_pos hm h2m hmd hdelta hdsmall ht
  have hs : (m : ℝ) * gap hmd T delta ≤ 1 / 2 ^ 13 := by
    have hh := (gap_small hm h2m hmd hdelta hdsmall hT).1
    norm_num at hh ⊢
    exact hh
  obtain ⟨i, hi, htail⟩ := exists_planted_coordinate_joint_gt P hm h2m hmd hdelta hdsmall hT hp hs
  obtain ⟨Z, hZ⟩ := MsetsPaper.Probability.exists_fixed_parametric_regret_via_product
    hmd (DenseCommonNoise.noiseTableMeasure T) P
    (plantedTableLossProcess hm hmd (gap hmd T delta) hp.le hs i T) T
    (gap hmd T delta * T / 8) delta htail.le
  let L := (plantedTableLossProcess hm hmd (gap hmd T delta) hp.le hs i T).at Z
  refine ⟨L, planted_oblivious hm hmd (gap hmd T delta) hp.le hs i Z, ?_, ?_⟩
  · intro t h j
    exact planted_item_bounds hm hmd (tableNoise_mem_Icc Z t) hp.le hs i j
  · refine hZ.trans (ENNReal.toReal_mono (measure_ne_top _ _) (measure_mono ?_))
    intro h hh
    exact (gap_threshold_dominates_target hm h2m hmd (log_inverse_positive hdelta hdsmall).le ht).trans hh


end
end MsetsPaper.Alignment.LowerSketchRoute.Confidence
