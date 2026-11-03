import MsetsPaper.Lower.DenseCommonNoiseInformation
import MsetsLower.Information.SequentialKL

set_option maxHeartbeats 800000

/-!
# Observable adaptive kernels for the new common-noise construction

The action kernel is the learner's actual policy, common to both sign environments.
The scalar feedback is the computed action loss with fresh uniform noise, as proved
by `actual_feedback_law`. This file establishes the native sequential information
bound. Identifying this fresh-noise recursion with the pre-sampled table experiment
is a separate obligation; no such identification is assumed here.
-/

namespace MsetsPaper.Lower.DenseCommonNoise

open MsetsLower MsetsLower.Feedback MsetsLower.Lower MeasureTheory
open ProbabilityTheory InformationTheory Set
open scoped ENNReal ProbabilityTheory BigOperators

noncomputable section

def latentActionKernel {d m : ℕ} (eta : ℝ) (U : Fin d → ℝ) :
    Kernel (MSetAction d m) ℝ where
  toFun a := feedbackDensityMeasure (feedbackParameter eta U a)
  measurable' := measurable_of_finite _

def latentFeedbackKernel {d m : ℕ} (eta : ℝ) (U : Fin d → ℝ) (t : ℕ) :
    Kernel (History d m t × MSetAction d m) ℝ :=
  (latentActionKernel eta U).comap Prod.snd measurable_snd

@[simp] theorem latentFeedbackKernel_apply {d m : ℕ}
    (eta : ℝ) (U : Fin d → ℝ) (t : ℕ) (ha : History d m t × MSetAction d m) :
    latentFeedbackKernel eta U t ha =
      feedbackDensityMeasure (feedbackParameter eta U ha.2) := rfl

theorem latentFeedbackKernel_isMarkov {d m : ℕ} (hm : 0 < m)
    {eta : ℝ} (heta : 0 ≤ eta) (hetaSmall : eta ≤ 1 / 16)
    (U : Fin d → ℝ) (hU : ∀ i, |U i| ≤ 1) (t : ℕ) :
    IsMarkovKernel (latentFeedbackKernel (m := m) eta U t) := by
  constructor
  intro ha
  exact ⟨feedbackDensityMeasure_apply_univ
    ((abs_feedbackParameter_le hm heta U hU ha.2).trans hetaSmall)⟩

def observationShift {d m : ℕ} :
    (MSetAction d m × ℝ) ≃ᵐ (MSetAction d m × ℝ) :=
  MeasurableEquiv.prodCongr (MeasurableEquiv.refl _) feedbackShift

def latentRoundKernel {d m : ℕ} (P : Policy d m) (eta : ℝ)
    (U : Fin d → ℝ) (t : ℕ) : Kernel (History d m t) (MSetAction d m × ℝ) :=
  P.kernel t ⊗ₖ latentFeedbackKernel eta U t

def observableRoundKernel {d m : ℕ} (P : Policy d m) (eta : ℝ)
    (U : Fin d → ℝ) (t : ℕ) : Kernel (History d m t) (MSetAction d m × ℝ) :=
  (latentRoundKernel P eta U t).map observationShift

theorem observableRoundKernel_isMarkov {d m : ℕ} (P : Policy d m) (hm : 0 < m)
    {eta : ℝ} (heta : 0 ≤ eta) (hetaSmall : eta ≤ 1 / 16)
    (U : Fin d → ℝ) (hU : ∀ i, |U i| ≤ 1) (t : ℕ) :
    IsMarkovKernel (observableRoundKernel P eta U t) := by
  letI := latentFeedbackKernel_isMarkov hm heta hetaSmall U hU t
  unfold observableRoundKernel latentRoundKernel
  exact Kernel.IsMarkovKernel.map _ observationShift.measurable

def observableProcess {d m : ℕ} (P : Policy d m) (hm : 0 < m)
    (eta : ℝ) (heta : 0 ≤ eta) (hetaSmall : eta ≤ 1 / 16)
    (U : Fin d → ℝ) (hU : ∀ i, |U i| ≤ 1) : HistoryKernelProcess d m where
  kernel t := observableRoundKernel P eta U t
  isMarkov t := observableRoundKernel_isMarkov P hm heta hetaSmall U hU t

def latentRatio {d m : ℕ} (eta : ℝ) (U V : Fin d → ℝ)
    (a : MSetAction d m) (y : ℝ) : ℝ≥0∞ :=
  feedbackDensityRatio (feedbackParameter eta U a) (feedbackParameter eta V a) y

theorem measurable_latentRatio {d m : ℕ} (eta : ℝ) (U V : Fin d → ℝ) :
    Measurable (Function.uncurry (latentRatio (m := m) eta U V)) := by
  exact measurable_from_prod_countable_right
    (fun a : MSetAction d m => measurable_feedbackDensityRatio
      (feedbackParameter eta U a) (feedbackParameter eta V a))

theorem latentFeedback_withDensity {d m : ℕ} (hm : 0 < m)
    {eta : ℝ} (heta : 0 ≤ eta) (hetaSmall : eta ≤ 1 / 16)
    (U V : Fin d → ℝ) (hU : ∀ i, |U i| ≤ 1) (hV : ∀ i, |V i| ≤ 1)
    (t : ℕ) (ha : History d m t × MSetAction d m) :
    latentFeedbackKernel eta U t ha =
      (latentFeedbackKernel eta V t ha).withDensity (latentRatio eta U V ha.2) := by
  exact feedbackDensityMeasure_withDensity_ratio
    ((abs_feedbackParameter_le hm heta U hU ha.2).trans hetaSmall)
    ((abs_feedbackParameter_le hm heta V hV ha.2).trans hetaSmall)

/-- Exact conditional KL integral for an arbitrary common history/action law.
The likelihood ratio is the explicit density ratio of the actual feedback. -/
theorem latentTwoStage_klDiv {d m t : ℕ}
    (μ : Measure (History d m t × MSetAction d m)) [IsProbabilityMeasure μ]
    (hm : 0 < m) {eta : ℝ} (heta : 0 ≤ eta) (hetaSmall : eta ≤ 1 / 16)
    (U V : Fin d → ℝ) (hU : ∀ i, |U i| ≤ 1) (hV : ∀ i, |V i| ≤ 1) :
    klDiv (μ ⊗ₘ latentFeedbackKernel eta U t) (μ ⊗ₘ latentFeedbackKernel eta V t) =
      ∫⁻ ha, klDiv (feedbackDensityMeasure (feedbackParameter eta U ha.2))
        (feedbackDensityMeasure (feedbackParameter eta V ha.2)) ∂μ := by
  letI := latentFeedbackKernel_isMarkov hm heta hetaSmall U hU t
  letI := latentFeedbackKernel_isMarkov hm heta hetaSmall V hV t
  let ratio : (History d m t × MSetAction d m) × ℝ → ℝ≥0∞ :=
    fun hay => latentRatio eta U V hay.1.2 hay.2
  have hr : Measurable ratio := by
    have hbase : Measurable (fun ay : MSetAction d m × ℝ =>
        latentRatio eta U V ay.1 ay.2) := measurable_latentRatio eta U V
    have hproj : Measurable (fun hay : (History d m t × MSetAction d m) × ℝ =>
        (hay.1.2, hay.2)) := measurable_fst.snd.prodMk measurable_snd
    simpa only [Function.comp_def, Function.uncurry, ratio] using hbase.comp hproj
  have hd : μ ⊗ₘ latentFeedbackKernel eta U t =
      (μ ⊗ₘ latentFeedbackKernel eta V t).withDensity ratio :=
    Dense.compProd_eq_withDensity_of_apply μ _ _
      (fun ha => latentRatio eta U V ha.2) hr
      (latentFeedback_withDensity hm heta hetaSmall U V hU hV t)
  letI : IsFiniteMeasure ((μ ⊗ₘ latentFeedbackKernel eta V t).withDensity ratio) := by
    rw [← hd]; infer_instance
  calc
    _ = ∫⁻ hay, ENNReal.ofReal (klFun (ratio hay).toReal)
        ∂(μ ⊗ₘ latentFeedbackKernel eta V t) := by
      conv_lhs => rw [hd]
      exact Dense.klDiv_withDensity_eq_lintegral_klFun _ ratio hr
    _ = ∫⁻ ha, ∫⁻ y, ENNReal.ofReal (klFun (latentRatio eta U V ha.2 y).toReal)
        ∂latentFeedbackKernel eta V t ha ∂μ := by
      rw [Measure.lintegral_compProd (by fun_prop)]
    _ = _ := by
      apply lintegral_congr
      intro ha
      have hd' := latentFeedback_withDensity hm heta hetaSmall U V hU hV t ha
      letI : IsFiniteMeasure ((latentFeedbackKernel eta V t ha).withDensity
          (latentRatio eta U V ha.2)) := by rw [← hd']; infer_instance
      change _ = klDiv (latentFeedbackKernel eta U t ha) (latentFeedbackKernel eta V t ha)
      rw [hd']
      symm
      exact Dense.klDiv_withDensity_eq_lintegral_klFun _ _
        (measurable_feedbackDensityRatio _ _)

/-- One adaptive round: the common learner action costs no information, and
the lossless scalar shift costs none either. -/
theorem observable_roundKL_eq {d m : ℕ} (P : Policy d m) (hm : 0 < m)
    {eta : ℝ} (heta : 0 ≤ eta) (hetaSmall : eta ≤ 1 / 16)
    (U V : Fin d → ℝ) (hU : ∀ i, |U i| ≤ 1) (hV : ∀ i, |V i| ≤ 1) (t : ℕ) :
    (observableProcess P hm eta heta hetaSmall U hU).roundKL
      (observableProcess P hm eta heta hetaSmall V hV) t =
      ∫⁻ ha, klDiv (feedbackDensityMeasure (feedbackParameter eta U ha.2))
        (feedbackDensityMeasure (feedbackParameter eta V ha.2))
        ∂((observableProcess P hm eta heta hetaSmall U hU).law t ⊗ₘ P.kernel t) := by
  letI := latentFeedbackKernel_isMarkov hm heta hetaSmall U hU t
  letI := latentFeedbackKernel_isMarkov hm heta hetaSmall V hV t
  letI : IsMarkovKernel (latentRoundKernel P eta U t) := by
    unfold latentRoundKernel; infer_instance
  letI : IsMarkovKernel (latentRoundKernel P eta V t) := by
    unfold latentRoundKernel; infer_instance
  unfold HistoryKernelProcess.roundKL
  change klDiv
    (_ ⊗ₘ (latentRoundKernel P eta U t).map observationShift)
    (_ ⊗ₘ (latentRoundKernel P eta V t).map observationShift) = _
  rw [Measure.compProd_map observationShift.measurable,
    Measure.compProd_map observationShift.measurable,
    Dense.klDiv_map_measurableEmbedding
      (MeasurableEmbedding.id.prodMap observationShift.measurableEmbedding)]
  unfold latentRoundKernel
  rw [← Dense.klDiv_map_measurableEmbedding MeasurableEquiv.prodAssoc.symm.measurableEmbedding]
  simp only [Measure.compProd_assoc]
  exact latentTwoStage_klDiv _ hm heta hetaSmall U V hU hV

/-- Before discarding the selection indicator, the exact conditional bound
charges information only when the flipped item is selected. -/
theorem observable_roundKL_flip_le_indicator {d m : ℕ}
    (P : Policy d m) (hm : 0 < m)
    {eta : ℝ} (heta : 0 ≤ eta) (hetaSmall : eta ≤ 1 / 16)
    (U : Fin d → ℝ) (hU : ∀ j, |U j| ≤ 1) (i : Fin d) (t : ℕ) :
    (observableProcess P hm eta heta hetaSmall (Function.update U i 1)
      (update_signs_bounded U hU i (by norm_num))).roundKL
        (observableProcess P hm eta heta hetaSmall (Function.update U i (-1))
          (update_signs_bounded U hU i (by norm_num))) t ≤
      ∫⁻ ha, ENNReal.ofReal
        (128 * (2 * eta / m) ^ 2 * (if i ∈ ha.2.val then 1 else 0))
        ∂((observableProcess P hm eta heta hetaSmall (Function.update U i 1)
          (update_signs_bounded U hU i (by norm_num))).law t ⊗ₘ P.kernel t) := by
  rw [observable_roundKL_eq]
  apply lintegral_mono
  intro ha
  have hp := (abs_feedbackParameter_le hm heta (Function.update U i 1)
    (update_signs_bounded U hU i (by norm_num)) ha.2).trans hetaSmall
  have hn := (abs_feedbackParameter_le hm heta (Function.update U i (-1))
    (update_signs_bounded U hU i (by norm_num)) ha.2).trans hetaSmall
  have hkl := FeedbackSharp.klDiv_feedbackDensityMeasure_le_one_twenty_eight hp hn
  rw [feedbackParameter_flip_sq] at hkl
  simpa only [mul_assoc] using hkl

/-- Uniform per-round consequence of the preceding indicator budget. -/
theorem observable_roundKL_flip_le {d m : ℕ}
    (P : Policy d m) (hm : 0 < m)
    {eta : ℝ} (heta : 0 ≤ eta) (hetaSmall : eta ≤ 1 / 16)
    (U : Fin d → ℝ) (hU : ∀ j, |U j| ≤ 1) (i : Fin d) (t : ℕ) :
    (observableProcess P hm eta heta hetaSmall (Function.update U i 1)
      (update_signs_bounded U hU i (by norm_num))).roundKL
        (observableProcess P hm eta heta hetaSmall (Function.update U i (-1))
          (update_signs_bounded U hU i (by norm_num))) t ≤
      ENNReal.ofReal (128 * (2 * eta / m) ^ 2) := by
  apply (observable_roundKL_flip_le_indicator P hm heta hetaSmall U hU i t).trans
  calc
    _ ≤ ∫⁻ _ha, ENNReal.ofReal (128 * (2 * eta / m) ^ 2)
        ∂((observableProcess P hm eta heta hetaSmall (Function.update U i 1)
          (update_signs_bounded U hU i (by norm_num))).law t ⊗ₘ P.kernel t) := by
      apply lintegral_mono
      intro ha
      by_cases hi : i ∈ ha.2.val
      · simp [hi]
      · simp [hi]
    _ = _ := by simp

/-- The actual stochastic action/feedback process accumulates at most the
manuscript's flip budget. No history-law KL bound is assumed. -/
theorem observable_flip_KL_le {d m T : ℕ}
    (P : Policy d m) (hm : 0 < m)
    {eta : ℝ} (heta : 0 ≤ eta) (hetaSmall : eta ≤ 1 / 16)
    (U : Fin d → ℝ) (hU : ∀ j, |U j| ≤ 1) (i : Fin d) :
    klDiv
      ((observableProcess P hm eta heta hetaSmall (Function.update U i 1)
        (update_signs_bounded U hU i (by norm_num))).law T)
      ((observableProcess P hm eta heta hetaSmall (Function.update U i (-1))
        (update_signs_bounded U hU i (by norm_num))).law T) ≤
      ENNReal.ofReal (128 * (2 * eta / m) ^ 2 * T) := by
  have h := HistoryKernelProcess.klDiv_law_le_sum
    (observableProcess P hm eta heta hetaSmall (Function.update U i 1)
      (update_signs_bounded U hU i (by norm_num)))
    (observableProcess P hm eta heta hetaSmall (Function.update U i (-1))
      (update_signs_bounded U hU i (by norm_num))) T
    (fun _ => ENNReal.ofReal (128 * (2 * eta / m) ^ 2))
    (fun t _ => observable_roundKL_flip_le P hm heta hetaSmall U hU i t)
  simpa [ENNReal.ofReal_mul (by positivity : (0 : ℝ) ≤ 128 * (2 * eta / m) ^ 2),
    mul_comm] using h

/-- The precise `1/32` information bound after inserting `eta=m/(128√T)`. -/
theorem observable_flip_KL_le_one_div_32 {d m T : ℕ}
    (P : Policy d m) (hm : 0 < m) (h2m : 2 * m ≤ d) (hT : d ^ 2 ≤ T)
    (U : Fin d → ℝ) (hU : ∀ j, |U j| ≤ 1) (i : Fin d) :
    let ht : 0 < T := lt_of_lt_of_le (pow_pos (by omega : 0 < d) 2) hT
    let he := (eta_pos hm ht).le
    let hs := (eta_le_one_div_256 hm h2m hT).trans (by norm_num : (1:ℝ)/256 ≤ 1/16)
    klDiv
      ((observableProcess P hm (eta m T) he hs (Function.update U i 1)
        (update_signs_bounded U hU i (by norm_num))).law T)
      ((observableProcess P hm (eta m T) he hs (Function.update U i (-1))
        (update_signs_bounded U hU i (by norm_num))).law T) ≤
      ENNReal.ofReal ((1 : ℝ) / 32) := by
  dsimp only
  have ht : 0 < T := lt_of_lt_of_le (pow_pos (by omega : 0 < d) 2) hT
  convert observable_flip_KL_le (T := T) P hm (eta_pos hm ht).le
    ((eta_le_one_div_256 hm h2m hT).trans (by norm_num)) U hU i using 1
  rw [total_flip_budget hm ht]

end

end MsetsPaper.Lower.DenseCommonNoise
