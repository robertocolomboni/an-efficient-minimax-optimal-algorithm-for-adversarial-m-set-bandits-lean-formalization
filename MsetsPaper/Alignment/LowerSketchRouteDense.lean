import MsetsPaper.Alignment.LowerSketch
import MsetsPaper.Probability.ProductFixingBridge
import MsetsPaper.Probability.ProductSeedAverage

/-! The dense sketch reaches its tail through the exact Top_m regret identity.
Pairing is used only to lower-bound the comparator's expectation. -/
namespace MsetsPaper.Alignment.LowerSketchRoute.Dense
open MsetsLower MsetsLower.Feedback MsetsLower.Lower MsetsLower.Probability
open MsetsPaper.Lower MsetsPaper.Lower.DenseCommonNoise
open MeasureTheory ProbabilityTheory InformationTheory Set
open scoped ENNReal ProbabilityTheory BigOperators
noncomputable section

theorem history_KL_eighty_uniform {d m T : ℕ}
    (P : Policy d m) (hm : 0 < m) {e : ℝ} (he : 0 ≤ e) (hs : e ≤ 1 / 16)
    (U : Fin d → ℝ) (hU : ∀ j, |U j| ≤ 1) (i : Fin d) :
    klDiv ((observableProcess P hm e he hs (Function.update U i 1)
      (update_signs_bounded U hU i (by norm_num))).law T)
      ((observableProcess P hm e he hs (Function.update U i (-1))
        (update_signs_bounded U hU i (by norm_num))).law T) ≤
      ENNReal.ofReal (80 * (2 * e / m) ^ 2 * T) := by
  apply (LowerSketch.Dense.history_KL_eighty_expectedCount P hm he hs U hU i).trans
  rw [ENNReal.ofReal_mul (by positivity : (0 : ℝ) ≤ 80 * (2 * e / m) ^ 2)]
  apply mul_le_mul_right
  apply ENNReal.ofReal_le_ofReal
  calc
    _ ≤ ∫ _h : History d m T, (T : ℝ)
        ∂(observableProcess P hm e he hs (Function.update U i 1)
          (update_signs_bounded U hU i (by norm_num))).law T := by
      apply integral_mono
      · exact Integrable.of_mem_Icc 0 (T : ℝ) (History.measurable_selectedCount i T).aemeasurable
          (ae_of_all _ (History.selectedCount_mem_Icc i T))
      · exact integrable_const _
      · intro h
        exact (History.selectedCount_mem_Icc i T h).2
    _ = _ := by simp

theorem eighty_flip_budget {m T : ℕ} (hm : 0 < m) (hT : 0 < T) :
    80 * (2 * eta m T / m) ^ 2 * T = (5 : ℝ) / 256 := by
  have h := total_flip_budget hm hT
  nlinarith

theorem observable_flip_KL_le_one_div_32 {d m T : ℕ}
    (P : Policy d m) (hm : 0 < m) (h2m : 2 * m ≤ d) (hT : d ^ 2 ≤ T)
    (U : Fin d → ℝ) (hU : ∀ j, |U j| ≤ 1) (i : Fin d) :
    let ht : 0 < T := lt_of_lt_of_le (pow_pos (by omega : 0 < d) 2) hT
    let he := (eta_pos hm ht).le
    let hs := (eta_le_one_div_256 hm h2m hT).trans (by norm_num : (1:ℝ)/256 ≤ 1/16)
    klDiv ((observableProcess P hm (eta m T) he hs (Function.update U i 1)
      (update_signs_bounded U hU i (by norm_num))).law T)
      ((observableProcess P hm (eta m T) he hs (Function.update U i (-1))
        (update_signs_bounded U hU i (by norm_num))).law T) ≤
      ENNReal.ofReal ((1 : ℝ) / 32) := by
  dsimp only
  have ht : 0 < T := lt_of_lt_of_le (pow_pos (by omega : 0 < d) 2) hT
  apply (history_KL_eighty_uniform P hm (eta_pos hm ht).le
    ((eta_le_one_div_256 hm h2m hT).trans (by norm_num)) U hU i).trans
  rw [eighty_flip_budget hm ht]
  exact ENNReal.ofReal_le_ofReal (by norm_num)

theorem observable_flip_TV_le_one_eighth {d m T : ℕ}
    (P : Policy d m) (hm : 0 < m) (h2m : 2 * m ≤ d) (hT : d ^ 2 ≤ T)
    (U : Fin d → ℝ) (hU : ∀ j, |U j| ≤ 1) (i : Fin d) :
    let ht : 0 < T := lt_of_lt_of_le (pow_pos (by omega : 0 < d) 2) hT
    let he := (eta_pos hm ht).le
    let hs := (eta_le_one_div_256 hm h2m hT).trans (by norm_num : (1:ℝ)/256 ≤ 1/16)
    totalVariationDistance
      ((observableProcess P hm (eta m T) he hs (Function.update U i 1)
        (update_signs_bounded U hU i (by norm_num))).law T)
      ((observableProcess P hm (eta m T) he hs (Function.update U i (-1))
        (update_signs_bounded U hU i (by norm_num))).law T) ≤ (1 : ℝ) / 8 := by
  dsimp only
  exact tv_le_one_eighth_of_kl _ _ (observable_flip_KL_le_one_div_32 P hm h2m hT U hU i)


theorem observable_flip_count_bias_le {d m T : ℕ}
    (P : Policy d m) (hm : 0 < m) (h2m : 2 * m ≤ d) (hT : d ^ 2 ≤ T)
    (U : Fin d → ℝ) (hU : ∀ j, |U j| ≤ 1) (i : Fin d) :
    let ht : 0 < T := lt_of_lt_of_le (pow_pos (by omega : 0 < d) 2) hT
    let he := (eta_pos hm ht).le
    let hs := (eta_le_one_div_256 hm h2m hT).trans (by norm_num : (1:ℝ)/256 ≤ 1/16)
    |((∫ h, History.selectedCount i T h
      ∂(observableProcess P hm (eta m T) he hs (Function.update U i 1)
        (update_signs_bounded U hU i (by norm_num))).law T) -
      ∫ h, History.selectedCount i T h
      ∂(observableProcess P hm (eta m T) he hs (Function.update U i (-1))
        (update_signs_bounded U hU i (by norm_num))).law T) / 2| ≤ (T : ℝ) / 16 := by
  dsimp only
  exact count_bias_le_of_tv i _ _ (observable_flip_TV_le_one_eighth P hm h2m hT U hU i)


theorem integral_sign_expectedSelections_le {d m T : ℕ}
    (P : Policy d m) (hm : 0 < m) (h2m : 2 * m ≤ d) (hT : d ^ 2 ≤ T)
    (i : Fin (2 * m)) :
    let ht : 0 < T := lt_of_lt_of_le (pow_pos (by omega : 0 < d) 2) hT
    let he := (eta_pos hm ht).le
    let hs := (eta_le_one_div_256 hm h2m hT).trans (by norm_num : (1:ℝ)/256 ≤ 1/16)
    (∫ U : Signs m, signValue (U i) *
      expectedSelections P hm (eta m T) he hs U T (Fin.castLE h2m i) ∂signsMeasure m) ≤
      (T : ℝ) / 16 := by
  dsimp only
  apply sign_mixture_le_of_pair_bound
  intro U
  have h := observable_flip_count_bias_le P hm h2m hT
    (signVector U) (abs_signVector_le U) (Fin.castLE h2m i)
  dsimp only at h
  have hle := (le_abs_self _).trans h
  unfold expectedSelections
  rw [noiseMixture_eq_observableProcess, noiseMixture_eq_observableProcess]
  simpa [signVector_update h2m, signValue] using hle


theorem two_thirds_integral_signedCount_le {d m T : ℕ}
    (P : Policy d m) (hm : 0 < m) (h2m : 2 * m ≤ d) (hT : d ^ 2 ≤ T) :
    let ht : 0 < T := lt_of_lt_of_le (pow_pos (by omega : 0 < d) 2) hT
    let he := (eta_pos hm ht).le
    let hs := (eta_le_one_div_256 hm h2m hT).trans (by norm_num : (1:ℝ)/256 ≤ 1/16)
    (2 / 3 : ℝ) * (∫ U : Signs m, ∑ i : Fin (2 * m), signValue (U i) *
      expectedSelections P hm (eta m T) he hs U T (Fin.castLE h2m i) ∂signsMeasure m) ≤
      (m : ℝ) * T / 12 := by
  dsimp only
  rw [integral_finsetSum _ (fun _ _ => Integrable.of_finite)]
  calc
    _ ≤ (2 / 3 : ℝ) * ∑ _i : Fin (2 * m), ((T : ℝ) / 16) :=
      mul_le_mul_of_nonneg_left
        (Finset.sum_le_sum fun i _ => integral_sign_expectedSelections_le P hm h2m hT i)
        (by norm_num)
    _ = _ := by simp; ring


theorem integral_learnerScore_joint_le_conditional {d m T : ℕ}
    (P : Policy d m) (hm : 0 < m) (h2m : 2 * m ≤ d) (hT : d ^ 2 ≤ T) :
    let ht : 0 < T := lt_of_lt_of_le (pow_pos (by omega : 0 < d) 2) hT
    let he := (eta_pos hm ht).le
    let hs := (eta_le_one_div_256 hm h2m hT).trans (by norm_num : (1:ℝ)/256 ≤ 1/16)
    (∫ x, learnerScore x.1 T x.2 ∂jointLaw P hm (eta m T) he hs T T) ≤
      (m : ℝ) * T / 12 := by
  dsimp only
  rw [integral_learnerScore_joint_eq_signedSelections P hm h2m]
  exact two_thirds_integral_signedCount_le P hm h2m hT

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
  exact integral_learnerScore_joint_le_conditional
    (MsetsPaper.Probability.PolicySeed.fixedPolicy P hmd r) hm h2m hT

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


def topComparatorScore {d m T : ℕ} (xi : Table m T) (t : ℕ) : ℝ :=
  SparseCapped.topScore m (fun i : Fin d => signVector xi.1 i * shapeSum xi t)

def topDeficit {d m T : ℕ} (xi : Table m T) (t : ℕ) (h : History d m t) : ℝ :=
  topComparatorScore (d := d) xi t - learnerScore xi t h

theorem measurable_topComparatorScore {d m T : ℕ} (t : ℕ) :
    Measurable (fun xi : Table m T => topComparatorScore (d := d) xi t) := by
  change Measurable (fun xi : Table m T =>
    ⨆ a : MSetAction d m, actionLoss a (fun i => signVector xi.1 i * shapeSum xi t))
  apply Measurable.iSup
  intro a
  apply measurable_actionLoss a
  exact Measurable.of_eval fun i =>
    ((measurable_of_finite (fun U : Signs m => signVector U i)).comp measurable_fst).mul
      (measurable_shapeSum t)

theorem abs_topComparatorScore_le {d m T : ℕ} (hmd : m ≤ d)
    (xi : Table m T) (t : ℕ) : |topComparatorScore (d := d) xi t| ≤ (m : ℝ) * t := by
  obtain ⟨a, ha⟩ := SparseCapped.topScore_attained hmd
    (fun i : Fin d => signVector xi.1 i * shapeSum xi t)
  unfold topComparatorScore
  rw [← ha]
  have heq : actionLoss a (fun i => signVector xi.1 i * shapeSum xi t) =
      actionLoss a (signVector xi.1) * shapeSum xi t := by
    simp only [actionLoss_eq_finset_sum, Finset.sum_mul]
  rw [heq, abs_mul, abs_of_nonneg (shapeSum_mem_Icc xi t).1]
  exact mul_le_mul (abs_action_sign_sum_le _ _ (abs_signVector_le xi.1))
    (shapeSum_mem_Icc xi t).2 (shapeSum_mem_Icc xi t).1 (Nat.cast_nonneg m)

theorem measurable_topDeficit {d m T : ℕ} (t : ℕ) :
    Measurable (fun x : Table m T × History d m t => topDeficit x.1 t x.2) :=
  ((measurable_topComparatorScore t).comp measurable_fst).sub (measurable_learnerScore t)

theorem integrable_topComparatorScore {d m T t : ℕ} (hmd : m ≤ d)
    (μ : Measure (Table m T × History d m t)) [IsFiniteMeasure μ] :
    Integrable (fun x => topComparatorScore (d := d) x.1 t) μ :=
  Integrable.of_bound ((measurable_topComparatorScore t).comp measurable_fst).aestronglyMeasurable
    ((m : ℝ) * t) (ae_of_all _ fun x => by
      simpa only [Real.norm_eq_abs] using abs_topComparatorScore_le hmd x.1 t)

theorem integrable_topDeficit {d m T t : ℕ} (hmd : m ≤ d)
    (μ : Measure (Table m T × History d m t)) [IsFiniteMeasure μ] :
    Integrable (fun x => topDeficit x.1 t x.2) μ :=
  (integrable_topComparatorScore hmd μ).sub (integrable_learnerScore μ)

theorem topDeficit_le {d m T : ℕ} (hmd : m ≤ d)
    (xi : Table m T) (t : ℕ) (h : History d m t) :
    topDeficit xi t h ≤ 2 * ((m : ℝ) * t) := by
  have htop := (le_abs_self _).trans (abs_topComparatorScore_le hmd xi t)
  have hlearner := (abs_le.mp (abs_learnerScore_le xi t h)).1
  dsimp only [topDeficit]
  linarith

theorem integral_topComparatorScore_ge {d m T : ℕ}
    (P : Policy d m) (hm : 0 < m) (h2m : 2 * m ≤ d)
    (e : ℝ) (he : 0 ≤ e) (hs : e ≤ 1 / 16) :
    (m : ℝ) * T / 3 ≤
      ∫ x, topComparatorScore (d := d) x.1 T ∂jointLaw P hm e he hs T T := by
  rw [← integral_comparatorScore_joint P hm h2m e he hs]
  apply integral_mono (integrable_comparatorScore h2m _)
    (integrable_topComparatorScore (by omega) _)
  intro x
  exact LowerSketch.Dense.paired_score_le_topScore h2m (signVector x.1.1) (shapeSum x.1 T)

theorem topDeficit_mean_ge {d m T : ℕ}
    (P : Policy d m) (hm : 0 < m) (h2m : 2 * m ≤ d) (hT : d ^ 2 ≤ T) :
    let ht : 0 < T := lt_of_lt_of_le (pow_pos (by omega : 0 < d) 2) hT
    let he := (eta_pos hm ht).le
    let hs := (eta_le_one_div_256 hm h2m hT).trans (by norm_num : (1:ℝ)/256 ≤ 1/16)
    (m : ℝ) * T / 4 ≤
      ∫ x, topDeficit x.1 T x.2 ∂jointLaw P hm (eta m T) he hs T T := by
  dsimp only
  unfold topDeficit
  rw [integral_sub (integrable_topComparatorScore (by omega) _) (integrable_learnerScore _)]
  have htop := integral_topComparatorScore_ge (T := T) P hm h2m (eta m T)
    (eta_pos hm (lt_of_lt_of_le (pow_pos (by omega : 0 < d) 2) hT)).le
    ((eta_le_one_div_256 hm h2m hT).trans (by norm_num))
  have hlearner := integral_learnerScore_joint_le P hm h2m hT
  dsimp only at hlearner
  linarith

theorem topDeficit_joint_tail {d m T : ℕ}
    (P : Policy d m) (hm : 0 < m) (h2m : 2 * m ≤ d) (hT : d ^ 2 ≤ T) :
    let ht : 0 < T := lt_of_lt_of_le (pow_pos (by omega : 0 < d) 2) hT
    let he := (eta_pos hm ht).le
    let hs := (eta_le_one_div_256 hm h2m hT).trans (by norm_num : (1:ℝ)/256 ≤ 1/16)
    (1 : ℝ) / 16 ≤ (jointLaw P hm (eta m T) he hs T T).real
      {x | (m : ℝ) * T / 8 ≤ topDeficit x.1 T x.2} := by
  dsimp only
  apply MsetsPaper.Lower.deficit_tail_one_sixteenth _ _ (measurable_topDeficit T)
    (integrable_topDeficit (by omega) _)
  · have ht : 0 < T := lt_of_lt_of_le (pow_pos (by omega : 0 < d) 2) hT
    positivity
  · exact topDeficit_mean_ge P hm h2m hT
  · exact ae_of_all _ fun x => topDeficit_le (by omega) x.1 T x.2

theorem regret_joint_tail {d m T : ℕ}
    (P : Policy d m) (hm : 0 < m) (h2m : 2 * m ≤ d) (hT : d ^ 2 ≤ T) :
    let ht : 0 < T := lt_of_lt_of_le (pow_pos (by omega : 0 < d) 2) hT
    let he := (eta_pos hm ht).le
    let hs := (eta_le_one_div_256 hm h2m hT).trans (by norm_num : (1:ℝ)/256 ≤ 1/16)
    (1 : ℝ) / 16 ≤ (jointLaw P hm (eta m T) he hs T T).real
      (parametricRegretEvent (tableLossProcess hm (eta m T) he hs T) T
        ((m : ℝ) * Real.sqrt T / 1024)) := by
  dsimp only
  have ht : 0 < T := lt_of_lt_of_le (pow_pos (by omega : 0 < d) 2) hT
  have he := (eta_pos hm ht).le
  have hs := (eta_le_one_div_256 hm h2m hT).trans (by norm_num : (1:ℝ)/256 ≤ 1/16)
  letI : Nonempty (MSetAction d m) := nonempty_MSetAction (by omega)
  have hpath (x : Table m T × History d m T) :
      eta m T / m * topDeficit x.1 T x.2 =
        parametricPathRegret (tableLossProcess hm (eta m T) he hs T) T x := by
    rw [show x = (x.1, x.2) from rfl, parametricPathRegret_eq_at]
    exact (LowerSketch.Dense.regret_eq_topScore hm (by omega) (eta m T) he hs T x.1 T x.2).symm
  have htail := MsetsPaper.Lower.scaled_regret_tail_of_deficit_tail
    (jointLaw P hm (eta m T) he hs T T) (fun x => topDeficit x.1 T x.2)
    (parametricPathRegret (tableLossProcess hm (eta m T) he hs T) T)
    (div_nonneg he (Nat.cast_nonneg m)) (ae_of_all _ fun x => (hpath x).le)
    (topDeficit_joint_tail P hm h2m hT)
  simpa only [eta_scaled_threshold hm ht, parametricRegretEvent] using htail



theorem exists_oblivious_dense_table_natural_threshold {d m T : ℕ}
    (P : Policy d m) (hm : 0 < m) (h2m : 2 * m ≤ d) (hT : d ^ 2 ≤ T) :
    ∃ L : LossProcess d m,
      (∀ t (h h' : History d m t), L.itemLoss t h = L.itemLoss t h') ∧
      (∀ t (h : History d m t) i, L.itemLoss t h i ∈ Icc (0 : ℝ) (1 / m)) ∧
      (1 : ℝ) / 16 ≤ (runLaw P L T).real
        {h | (m : ℝ) * Real.sqrt T / 1024 ≤ pathRegret L T h} := by
  have ht : 0 < T := lt_of_lt_of_le (pow_pos (by omega : 0 < d) 2) hT
  have he := (eta_pos hm ht).le
  have hs := (eta_le_one_div_256 hm h2m hT).trans (by norm_num : (1:ℝ)/256 ≤ 1/16)
  obtain ⟨xi, hxi⟩ := MsetsPaper.Probability.exists_fixed_parametric_regret_via_product
    (by omega : m ≤ d)
    (tableMeasure m T) P (tableLossProcess hm (eta m T) he hs T) T
    ((m : ℝ) * Real.sqrt T / 1024) ((1 : ℝ) / 16) (regret_joint_tail P hm h2m hT)
  refine ⟨(tableLossProcess hm (eta m T) he hs T).at xi, ?_, ?_, hxi⟩
  · exact tableLossProcess_oblivious hm (eta m T) he hs T xi
  · exact tableLossProcess_item_mem_Icc hm (eta m T) he hs T xi


theorem lower_action_count_dense {d m T : ℕ}
    (hm : 1 ≤ m) (h2m : 2 * m ≤ d) (hT : 64 * d ^ 2 ≤ T)
    (hr : (2 : ℝ) ^ (-32 : ℤ) < (m : ℝ) / d) (P : Policy d m) :
    ∃ L : LossProcess d m,
      (∀ t (h h' : History d m t), L.itemLoss t h = L.itemLoss t h') ∧
      (∀ t (h : History d m t) i, L.itemLoss t h i ∈ Icc (0 : ℝ) (1 / m)) ∧
      (2 : ℝ) ^ (-14 : ℤ) ≤ (runLaw P L T).real
        {h | (2 : ℝ) ^ (-42 : ℤ) *
          Real.sqrt ((d : ℝ) * T * Real.log (d.choose m : ℝ)) ≤ pathRegret L T h} := by
  have hm0 : 0 < m := by omega
  have hd : 0 < d := by omega
  have hTweak : d ^ 2 ≤ T := by nlinarith
  have ht : 0 < T := lt_of_lt_of_le (pow_pos hd 2) hTweak
  obtain ⟨L, hobl, hitem, htail⟩ :=
    exists_oblivious_dense_table_natural_threshold P hm0 h2m hTweak
  refine ⟨L, hobl, hitem, ?_⟩
  have hcomparison := dense_threshold_strict_comparisons hm0 h2m ht hr
  have hsubset : {h : History d m T | (m : ℝ) * Real.sqrt T / 1024 ≤ pathRegret L T h} ⊆
      {h | (2 : ℝ) ^ (-42 : ℤ) *
        Real.sqrt ((d : ℝ) * T * Real.log (d.choose m : ℝ)) ≤ pathRegret L T h} := by
    intro h hh
    exact (hcomparison.1.trans hcomparison.2).le.trans hh
  calc
    (2 : ℝ) ^ (-14 : ℤ) ≤ (1 : ℝ) / 16 := by norm_num
    _ ≤ _ := htail
    _ ≤ _ := ENNReal.toReal_mono (measure_ne_top _ _) (measure_mono hsubset)


end
end MsetsPaper.Alignment.LowerSketchRoute.Dense
