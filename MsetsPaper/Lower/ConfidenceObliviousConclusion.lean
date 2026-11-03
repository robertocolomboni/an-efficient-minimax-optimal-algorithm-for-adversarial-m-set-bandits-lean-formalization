import MsetsPaper.Lower.ConfidenceObliviousTesting
import MsetsPaper.Lower.ConfidenceObliviousSeedAverage
import MsetsPaper.Probability.FiniteSeedSelection
import MsetsPaper.Probability.ProductFixingBridge

/-! # The new P4 endpoint, with an actual deterministic oblivious witness -/

namespace MsetsPaper.Lower.ConfidenceOblivious

open MsetsLower MsetsLower.Feedback MsetsLower.Lower MsetsLower.Lower.Confidence
open MsetsPaper.Probability MsetsPaper.Probability.PolicySeed
open MeasureTheory ProbabilityTheory Set
open scoped ENNReal ProbabilityTheory BigOperators

noncomputable section

theorem reference_item_bounds {d m : ℕ} (hm : 1 ≤ m) (hmd : m ≤ d)
    {z : ℝ} (hz : z ∈ Icc (-1 : ℝ) 1) (i : Fin d) :
    referenceItemLoss hmd z i ∈ Icc ((1 : ℝ) / (8 * m)) (1 / (2 * m)) := by
  have hmpos : (0 : ℝ) < m := by exact_mod_cast hm
  have hlo := div_le_div_of_nonneg_right (show (1 : ℝ) / 8 ≤ 1 / 4 + z / 8 by linarith [hz.1]) hmpos.le
  have hhi := div_le_div_of_nonneg_right (show (1 : ℝ) / 4 + z / 8 ≤ 3 / 8 by linarith [hz.2]) hmpos.le
  have hpos : (0 : ℝ) ≤ 1 / (8 * m) := by positivity
  have heq : (1 : ℝ) / 8 / m = 1 / (8 * m) := by ring
  have heq' : (3 : ℝ) / 8 / m + 1 / (8 * m) = 1 / (2 * m) := by ring
  rw [heq] at hlo
  unfold referenceItemLoss candidateIndicator
  split_ifs <;> simp only [mul_one, mul_zero, add_zero] <;> constructor <;> linarith

theorem planted_item_bounds {d m : ℕ} (hm : 1 ≤ m) (hmd : m ≤ d)
    {z Delta : ℝ} (hz : z ∈ Icc (-1 : ℝ) 1) (hDelta : 0 ≤ Delta)
    (hsmall : (m : ℝ) * Delta ≤ 1 / 2 ^ 13) (i j : Fin d) :
    plantedItemLoss hmd z Delta 1 i j ∈ Icc (0 : ℝ) (1 / m) := by
  have href := reference_item_bounds hm hmd hz j
  have hshape := shape_mem_Icc hz
  have hp0 : 0 ≤ Delta * shape z := mul_nonneg hDelta hshape.1
  have hp1 : Delta * shape z ≤ Delta := by nlinarith [hshape.2]
  have hsmall' := (Delta_lt_one_div_eight_m hm hsmall).le
  have hupper : (1 : ℝ) / (2 * m) ≤ 1 / m := by
    have hmpos : (0 : ℝ) < m := by exact_mod_cast hm
    exact one_div_le_one_div_of_le hmpos (by nlinarith)
  unfold plantedItemLoss
  split_ifs <;> simp only [mul_one, mul_zero, sub_zero] <;> constructor <;> linarith [href.1, href.2]

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

/-- Stronger P4 construction: the final index and the final noise table are independent of
the private seed. Only the original learner remains randomized. -/
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

/-- Paper-facing P4: only action-loss normalization is exposed. The stronger
itemwise construction remains available as `lower_confidence_oblivious`. -/
theorem lower_confidence_oblivious_action_losses {d m T : ℕ}
    (hm : 1 ≤ m) (h2m : 2 * m ≤ d)
    {delta : ℝ} (hdelta : 0 < delta) (hdsmall : delta ≤ (2 : ℝ) ^ (-36 : ℤ))
    (hT : 4 * (d : ℝ) * (m : ℝ) ^ 2 * Real.log (1 / delta) ≤ T) (P : Policy d m) :
    ∃ L : LossProcess d m,
      (∀ t (h h' : History d m t), L.itemLoss t h = L.itemLoss t h') ∧
      (∀ t (h : History d m t) (a : MSetAction d m),
        actionLoss a (L.itemLoss t h) ∈ Icc (0 : ℝ) 1) ∧
      delta ≤ (runLaw P L T).real
        {h | (2 : ℝ) ^ (-16 : ℤ) * Real.sqrt ((d : ℝ) * T * Real.log (1 / delta)) ≤
          pathRegret L T h} := by
  obtain ⟨L, ho, _hitem, htail⟩ := lower_confidence_oblivious hm h2m hdelta hdsmall hT P
  exact ⟨L, ho, L.action_mem_Icc, htail⟩

end
end MsetsPaper.Lower.ConfidenceOblivious
