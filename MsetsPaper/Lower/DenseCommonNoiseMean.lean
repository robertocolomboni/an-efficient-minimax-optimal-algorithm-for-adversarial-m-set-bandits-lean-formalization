import MsetsPaper.Lower.DenseCommonNoiseTower
import MsetsPaper.Lower.DenseCommonNoiseFixedSeed
import MsetsPaper.Probability.ProductSeedAverage

/-! # The actual learner-score mean under the dense experiment

The factor `2/3` is proved by exposing each fresh noise coordinate in the
original finite table. It is not supplied as a hypothesis about the score.
-/

namespace MsetsPaper.Lower.DenseCommonNoise

open MsetsLower MsetsLower.Feedback MsetsLower.Lower MeasureTheory ProbabilityTheory Set
open scoped ENNReal ProbabilityTheory BigOperators

noncomputable section

def fixedSignScoreMean {d m : ℕ} (P : Policy d m) (hm : 0 < m)
    (eta : ℝ) (heta : 0 ≤ eta) (hs : eta ≤ 1 / 16) (U : Signs m) (T : ℕ) : ℝ :=
  ∫ Z, ∫ h, learnerScore (U, Z) T h
    ∂runLaw P ((tableLossProcess hm eta heta hs T).at (U, Z)) T ∂noiseTableMeasure T

def fixedSignActionMean {d m : ℕ} (P : Policy d m) (hm : 0 < m)
    (eta : ℝ) (heta : 0 ≤ eta) (hs : eta ≤ 1 / 16) (U : Signs m) (T : ℕ) : ℝ :=
  ∫ Z, ∫ h, History.actionSum (fun a => actionLoss a (signVector U)) T h
    ∂runLaw P ((tableLossProcess hm eta heta hs T).at (U, Z)) T ∂noiseTableMeasure T

def fixedSignNextMean {d m : ℕ} (P : Policy d m) (hm : 0 < m)
    (eta : ℝ) (heta : 0 ≤ eta) (hs : eta ≤ 1 / 16) (U : Signs m) (T : ℕ) : ℝ :=
  ∫ Z, ∫ h, ∫ a, actionLoss a (signVector U) ∂P.kernel T h
    ∂runLaw P ((tableLossProcess hm eta heta hs T).at (U, Z)) T ∂noiseTableMeasure T

theorem integrable_scoreRunIntegral {d m T : ℕ}
    (P : Policy d m) (hm : 0 < m) (eta : ℝ) (heta : 0 ≤ eta) (hs : eta ≤ 1 / 16)
    (U : Signs m) :
    Integrable (fun Z => ∫ h, learnerScore (U, Z) T h
      ∂runLaw P ((tableLossProcess hm eta heta hs T).at (U, Z)) T) (noiseTableMeasure T) := by
  refine integrable_tableRunIntegral (T := T) P hm eta heta hs U
    (fun Zh => learnerScore (U, Zh.1) T Zh.2) ?_ ((m : ℝ) * T) ?_
  · exact (measurable_learnerScore T).comp
      ((measurable_const.prodMk measurable_fst).prodMk measurable_snd)
  · intro Z h
    exact abs_learnerScore_le (U, Z) T h

theorem integrable_actionRunIntegral {d m T : ℕ}
    (P : Policy d m) (hm : 0 < m) (eta : ℝ) (heta : 0 ≤ eta) (hs : eta ≤ 1 / 16)
    (U : Signs m) :
    Integrable (fun Z => ∫ h, History.actionSum (fun a => actionLoss a (signVector U)) T h
      ∂runLaw P ((tableLossProcess hm eta heta hs T).at (U, Z)) T) (noiseTableMeasure T) := by
  refine integrable_tableRunIntegral (T := T) P hm eta heta hs U
    (fun Zh => History.actionSum (fun a => actionLoss a (signVector U)) T Zh.2)
    ?_ ((m : ℝ) * T) ?_
  · exact (History.measurable_actionSum_of_finite _ T).comp measurable_snd
  · intro Z h
    exact abs_actionSum_le (signVector U) (abs_signVector_le U) T h

theorem integrable_nextRunIntegral {d m T : ℕ}
    (P : Policy d m) (hm : 0 < m) (eta : ℝ) (heta : 0 ≤ eta) (hs : eta ≤ 1 / 16)
    (U : Signs m) :
    Integrable (fun Z => ∫ h, ∫ a, actionLoss a (signVector U) ∂P.kernel T h
      ∂runLaw P ((tableLossProcess hm eta heta hs T).at (U, Z)) T) (noiseTableMeasure T) := by
  refine integrable_tableRunIntegral (T := T) P hm eta heta hs U
    (fun Zh => ∫ a, actionLoss a (signVector U) ∂P.kernel T Zh.2) ?_ (m : ℝ) ?_
  · exact (measurable_expected_actionSign P (signVector U) T).comp measurable_snd
  · intro Z h
    exact abs_expected_actionSign_le P (signVector U) (abs_signVector_le U) T h

theorem fixedSignScoreMean_succ {d m T : ℕ}
    (P : Policy d m) (hm : 0 < m) (eta : ℝ) (heta : 0 ≤ eta) (hs : eta ≤ 1 / 16)
    (U : Signs m) :
    fixedSignScoreMean P hm eta heta hs U (T + 1) =
      fixedSignScoreMean P hm eta heta hs U T +
        (2 / 3 : ℝ) * fixedSignNextMean P hm eta heta hs U T := by
  unfold fixedSignScoreMean fixedSignNextMean
  rw [integral_noiseTable_snoc (integrable_scoreRunIntegral P hm eta heta hs U)]
  simp_rw [integral_learnerScore_runLaw_snoc P hm eta heta hs U]
  have hshape : Integrable (fun z : Noise => shape z.val) noiseMeasure :=
    Integrable.of_bound (measurable_shape.comp measurable_subtype_coe).aestronglyMeasurable 1
      (ae_of_all _ fun z => by
        simpa only [Real.norm_eq_abs, abs_of_nonneg (shape_mem_Icc z.property).1]
          using (shape_mem_Icc z.property).2)
  simp_rw [integral_add (integrable_const _) (hshape.mul_const _), integral_mul_const]
  simp only [integral_const, probReal_univ, smul_eq_mul, one_mul, integral_shape_noiseMeasure]
  rw [integral_add (integrable_scoreRunIntegral P hm eta heta hs U)
    ((integrable_nextRunIntegral P hm eta heta hs U).const_mul _), integral_const_mul]

theorem fixedSignActionMean_succ {d m T : ℕ}
    (P : Policy d m) (hm : 0 < m) (eta : ℝ) (heta : 0 ≤ eta) (hs : eta ≤ 1 / 16)
    (U : Signs m) :
    fixedSignActionMean P hm eta heta hs U (T + 1) =
      fixedSignActionMean P hm eta heta hs U T + fixedSignNextMean P hm eta heta hs U T := by
  unfold fixedSignActionMean fixedSignNextMean
  rw [integral_noiseTable_snoc (integrable_actionRunIntegral P hm eta heta hs U)]
  simp_rw [integral_actionSum_runLaw_snoc P hm eta heta hs U]
  simp only [integral_const, probReal_univ, smul_eq_mul, one_mul]
  exact integral_add (integrable_actionRunIntegral P hm eta heta hs U)
    (integrable_nextRunIntegral P hm eta heta hs U)

/-- Exact fresh-noise tower identity, retaining the actual policy run law. -/
theorem fixedSignScoreMean_eq_two_thirds_actionMean {d m : ℕ}
    (P : Policy d m) (hm : 0 < m) (eta : ℝ) (heta : 0 ≤ eta) (hs : eta ≤ 1 / 16)
    (U : Signs m) :
    ∀ T : ℕ, fixedSignScoreMean P hm eta heta hs U T =
      (2 / 3 : ℝ) * fixedSignActionMean P hm eta heta hs U T := by
  intro T
  induction T with
  | zero => simp [fixedSignScoreMean, fixedSignActionMean, learnerScore, History.actionSum]
  | succ T ih =>
      rw [fixedSignScoreMean_succ, fixedSignActionMean_succ, ih]
      ring

/-- Averaging the original deterministic-table run laws is exactly the
integral against their operational mixture, also for signed bounded functions. -/
theorem integral_noiseMixture {d m T : ℕ}
    (P : Policy d m) (hm : 0 < m) (eta : ℝ) (heta : 0 ≤ eta) (hs : eta ≤ 1 / 16)
    (U : Signs m) (f : History d m T → ℝ) (hf : Measurable f)
    (C : ℝ) (hC : ∀ h, |f h| ≤ C) :
    (∫ h, f h ∂noiseMixture P hm eta heta hs U T) =
      ∫ Z, ∫ h, f h ∂runLaw P ((tableLossProcess hm eta heta hs T).at (U, Z)) T
        ∂noiseTableMeasure T := by
  have hmap : ((noiseTableMeasure T) ⊗ₘ fixedSignRunKernel P hm eta heta hs U T).map
      Prod.snd = noiseMixture P hm eta heta hs U T := Measure.snd_compProd _ _
  rw [← hmap, integral_map measurable_snd.aemeasurable hf.aestronglyMeasurable]
  have hfi : Integrable (fun x : (Fin T → Noise) × History d m T => f x.2)
      ((noiseTableMeasure T) ⊗ₘ fixedSignRunKernel P hm eta heta hs U T) :=
    Integrable.of_bound (hf.comp measurable_snd).aestronglyMeasurable C
      (ae_of_all _ fun x => by simpa only [Real.norm_eq_abs] using hC x.2)
  rw [Measure.integral_compProd hfi]
  simp only [fixedSignRunKernel_apply]

theorem fixedSignActionMean_eq_signedSelections {d m T : ℕ}
    (P : Policy d m) (hm : 0 < m) (h2m : 2 * m ≤ d)
    (eta : ℝ) (heta : 0 ≤ eta) (hs : eta ≤ 1 / 16) (U : Signs m) :
    fixedSignActionMean P hm eta heta hs U T =
      ∑ i : Fin (2 * m), signValue (U i) *
        expectedSelections P hm eta heta hs U T (Fin.castLE h2m i) := by
  unfold fixedSignActionMean
  rw [← integral_noiseMixture P hm eta heta hs U _
    (History.measurable_actionSum_of_finite _ T) ((m : ℝ) * T)
    (abs_actionSum_le (signVector U) (abs_signVector_le U) T)]
  simp_rw [actionSum_eq_signedCounts h2m U]
  rw [integral_finsetSum _ (fun i _ =>
    (Integrable.of_mem_Icc 0 T (History.measurable_selectedCount _ T).aemeasurable
      (ae_of_all _ (History.selectedCount_mem_Icc (Fin.castLE h2m i) T))).const_mul _)]
  simp only [integral_const_mul, expectedSelections]

theorem integral_learnerScore_joint_eq_signMean {d m T : ℕ}
    (P : Policy d m) (hm : 0 < m) (eta : ℝ) (heta : 0 ≤ eta) (hs : eta ≤ 1 / 16) :
    (∫ x, learnerScore x.1 T x.2 ∂jointLaw P hm eta heta hs T T) =
      ∫ U, fixedSignScoreMean P hm eta heta hs U T ∂signsMeasure m := by
  letI := parametricRunKernel_isMarkov P (tableLossProcess hm eta heta hs T) T
  rw [jointLaw_eq_compProd]
  rw [Measure.integral_compProd (integrable_learnerScore _)]
  simp_rw [parametricRunKernel_apply]
  change (∫ xi : Table m T, (∫ h, learnerScore xi T h
      ∂runLaw P ((tableLossProcess hm eta heta hs T).at xi) T)
      ∂(signsMeasure m).prod (noiseTableMeasure T)) = _
  have hmeas : Measurable (fun xi : Table m T => ∫ h, learnerScore xi T h
      ∂parametricRunKernel P (tableLossProcess hm eta heta hs T) T xi) :=
    (measurable_learnerScore T).stronglyMeasurable.integral_kernel_prod_right'.measurable
  have hbound (xi : Table m T) : |∫ h, learnerScore xi T h
      ∂parametricRunKernel P (tableLossProcess hm eta heta hs T) T xi| ≤ (m : ℝ) * T := by
    simpa [Real.norm_eq_abs] using norm_integral_le_of_norm_le_const
      (μ := parametricRunKernel P (tableLossProcess hm eta heta hs T) T xi)
      (f := learnerScore xi T) (ae_of_all _ fun h => by
        simpa only [Real.norm_eq_abs] using abs_learnerScore_le xi T h)
  have hi : Integrable (fun xi : Table m T => ∫ h, learnerScore xi T h
      ∂runLaw P ((tableLossProcess hm eta heta hs T).at xi) T)
      ((signsMeasure m).prod (noiseTableMeasure T)) := by
    simpa only [parametricRunKernel_apply] using
      (Integrable.of_bound (μ := (signsMeasure m).prod (noiseTableMeasure T))
        hmeas.aestronglyMeasurable ((m : ℝ) * T)
        (ae_of_all _ fun xi => by simpa only [Real.norm_eq_abs] using hbound xi))
  exact integral_prod _ hi

/-- The exact identity used in the manuscript, before the `T/16` sign-bias
bound is applied. Both sides use the actual randomized-policy experiment. -/
theorem integral_learnerScore_joint_eq_signedSelections {d m T : ℕ}
    (P : Policy d m) (hm : 0 < m) (h2m : 2 * m ≤ d)
    (eta : ℝ) (heta : 0 ≤ eta) (hs : eta ≤ 1 / 16) :
    (∫ x, learnerScore x.1 T x.2 ∂jointLaw P hm eta heta hs T T) =
      (2 / 3 : ℝ) * ∫ U, ∑ i : Fin (2 * m), signValue (U i) *
        expectedSelections P hm eta heta hs U T (Fin.castLE h2m i) ∂signsMeasure m := by
  rw [integral_learnerScore_joint_eq_signMean]
  simp_rw [fixedSignScoreMean_eq_two_thirds_actionMean,
    fixedSignActionMean_eq_signedSelections P hm h2m eta heta hs]
  exact integral_const_mul _ _

/-- For each private seed separately, first perform sign testing and average
the noise/sign experiment. No private-seed average has yet been taken. -/
theorem fixedSeed_integral_learnerScore_joint_le {d m T : ℕ}
    (P : Policy d m) (hmd : m ≤ d)
    (r : MsetsPaper.Probability.PolicySeed.Seeds T)
    (hm : 0 < m) (h2m : 2 * m ≤ d) (hT : d ^ 2 ≤ T) :
    let ht : 0 < T := lt_of_lt_of_le (pow_pos (by omega : 0 < d) 2) hT
    let he := (eta_pos hm ht).le
    let hs := (eta_le_one_div_256 hm h2m hT).trans (by norm_num : (1:ℝ)/256 ≤ 1/16)
    (∫ x, learnerScore x.1 T x.2
      ∂jointLaw (MsetsPaper.Probability.PolicySeed.fixedPolicy P hmd r)
        hm (eta m T) he hs T T) ≤ (m : ℝ) * T / 12 := by
  dsimp only
  rw [integral_learnerScore_joint_eq_signedSelections _ hm h2m]
  exact fixedSeed_two_thirds_integral_signedCount_le P hmd r hm h2m hT

/-- The private seed is averaged only after its uniform fixed-seed score
bound has been proved, in the order used by the manuscript. -/
theorem integral_learnerScore_joint_le {d m T : ℕ}
    (P : Policy d m) (hm : 0 < m) (h2m : 2 * m ≤ d) (hT : d ^ 2 ≤ T) :
    let ht : 0 < T := lt_of_lt_of_le (pow_pos (by omega : 0 < d) 2) hT
    let he := (eta_pos hm ht).le
    let hs := (eta_le_one_div_256 hm h2m hT).trans (by norm_num : (1:ℝ)/256 ≤ 1/16)
    (∫ x, learnerScore x.1 T x.2 ∂jointLaw P hm (eta m T) he hs T T) ≤
      (m : ℝ) * T / 12 := by
  dsimp only
  have hmd : m ≤ d := by omega
  have ht : 0 < T := lt_of_lt_of_le (pow_pos (by omega : 0 < d) 2) hT
  have he := (eta_pos hm ht).le
  have hs := (eta_le_one_div_256 hm h2m hT).trans (by norm_num : (1:ℝ)/256 ≤ 1/16)
  have havg := MsetsPaper.Probability.integral_parametric_fixedSeed_average
    hmd (tableMeasure m T) P (tableLossProcess hm (eta m T) he hs T) T
    (fun x => learnerScore x.1 T x.2) (measurable_learnerScore T)
    ((m : ℝ) * T) (fun x => abs_learnerScore_le x.1 T x.2)
  change Integrable (fun r : MsetsPaper.Probability.PolicySeed.Seeds T =>
      ∫ x, learnerScore x.1 T x.2
        ∂jointLaw (MsetsPaper.Probability.PolicySeed.fixedPolicy P hmd r)
          hm (eta m T) he hs T T) _ ∧
    (∫ x, learnerScore x.1 T x.2 ∂jointLaw P hm (eta m T) he hs T T) = _ at havg
  rw [havg.2]
  calc
    _ ≤ ∫ _r : MsetsPaper.Probability.PolicySeed.Seeds T, (m : ℝ) * T / 12
        ∂MsetsPaper.Probability.PolicySeed.seedMeasure T :=
      integral_mono havg.1 (integrable_const _) (fun r =>
        fixedSeed_integral_learnerScore_joint_le P hmd r hm h2m hT)
    _ = _ := by simp

end

end MsetsPaper.Lower.DenseCommonNoise
