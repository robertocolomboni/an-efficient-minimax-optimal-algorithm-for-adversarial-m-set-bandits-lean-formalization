import MsetsPaper.Lower.SparseCappedLaw
import MsetsPaper.Lower.DenseCommonNoiseProcess

/-!
# Actual fresh-noise kernels and native conditional KL for P2

Both bit environments use the same arbitrary randomized Policy kernel.
Activity is a measurable finite mask computed from the common preceding
history, so it is identical in the conditional comparison. The learner's
random action contributes zero KL; only its actual scalar feedback is charged.
The identification with the presampled table law is a separate theorem.
-/

namespace MsetsPaper.Lower.SparseCapped

open MsetsLower MsetsLower.History MsetsLower.Feedback MsetsLower.Lower
open MeasureTheory ProbabilityTheory InformationTheory Set
open scoped ENNReal ProbabilityTheory BigOperators

noncomputable section

def activeMask {d m : ℕ} (c t : ℕ) (h : History d m t) : Bits d :=
  fun i => if selectedCount i t h < (c : ℝ) then true else false

theorem measurable_activeMask {d m : ℕ} (c t : ℕ) :
    Measurable (activeMask (d := d) (m := m) c t) := by
  apply measurable_pi_lambda
  intro i
  exact Measurable.ite (measurableSet_lt (measurable_selectedCount i t) measurable_const)
    measurable_const measurable_const

def maskVector {d : ℕ} (U M : Bits d) : Fin d → ℝ :=
  fun i => bitValue (M i) * bitValue (U i)

theorem maskVector_activeMask {d m : ℕ} (c : ℕ) (U : Bits d) (t : ℕ)
    (h : History d m t) : maskVector U (activeMask c t h) = activeVector c U t h := by
  funext i
  unfold maskVector activeMask activeVector activeIndicator
  split <;> simp [bitValue]

def latentMaskActionKernel {d m : ℕ} (eta : ℝ) (U : Bits d) :
    Kernel (Bits d × MSetAction d m) ℝ where
  toFun ma := feedbackDensityMeasure
    (DenseCommonNoise.feedbackParameter eta (maskVector U ma.1) ma.2)
  measurable' := measurable_of_finite _

def latentFeedbackKernel {d m : ℕ} (c : ℕ) (eta : ℝ) (U : Bits d) (t : ℕ) :
    Kernel (History d m t × MSetAction d m) ℝ :=
  (latentMaskActionKernel eta U).comap (fun ha => (activeMask c t ha.1, ha.2))
    (((measurable_activeMask c t).comp measurable_fst).prodMk measurable_snd)

@[simp] theorem latentFeedbackKernel_apply {d m : ℕ} (c : ℕ)
    (eta : ℝ) (U : Bits d) (t : ℕ) (ha : History d m t × MSetAction d m) :
    latentFeedbackKernel c eta U t ha =
      feedbackDensityMeasure (feedbackParameter c eta U t ha.1 ha.2) := by
  change feedbackDensityMeasure
    (DenseCommonNoise.feedbackParameter eta (maskVector U (activeMask c t ha.1)) ha.2) = _
  rw [maskVector_activeMask]
  rfl

theorem latentFeedbackKernel_isMarkov {d m : ℕ} (hm : 0 < m) (c : ℕ)
    {eta : ℝ} (heta : 0 ≤ eta) (hs : eta ≤ 1 / 16) (U : Bits d) (t : ℕ) :
    IsMarkovKernel (latentFeedbackKernel (m := m) c eta U t) := by
  constructor
  intro ha
  rw [latentFeedbackKernel_apply]
  exact ⟨feedbackDensityMeasure_apply_univ
    ((abs_feedbackParameter_le hm c heta U t ha.1 ha.2).trans hs)⟩

def latentRoundKernel {d m : ℕ} (P : Policy d m) (c : ℕ) (eta : ℝ)
    (U : Bits d) (t : ℕ) : Kernel (History d m t) (MSetAction d m × ℝ) :=
  P.kernel t ⊗ₖ latentFeedbackKernel c eta U t

def observableRoundKernel {d m : ℕ} (P : Policy d m) (c : ℕ) (eta : ℝ)
    (U : Bits d) (t : ℕ) : Kernel (History d m t) (MSetAction d m × ℝ) :=
  (latentRoundKernel P c eta U t).map DenseCommonNoise.observationShift

theorem observableRoundKernel_isMarkov {d m : ℕ} (P : Policy d m) (hm : 0 < m) (c : ℕ)
    {eta : ℝ} (heta : 0 ≤ eta) (hs : eta ≤ 1 / 16) (U : Bits d) (t : ℕ) :
    IsMarkovKernel (observableRoundKernel P c eta U t) := by
  letI := latentFeedbackKernel_isMarkov hm c heta hs U t
  unfold observableRoundKernel latentRoundKernel
  exact Kernel.IsMarkovKernel.map _ DenseCommonNoise.observationShift.measurable

def observableProcess {d m : ℕ} (P : Policy d m) (hm : 0 < m) (c : ℕ)
    (eta : ℝ) (heta : 0 ≤ eta) (hs : eta ≤ 1 / 16) (U : Bits d) :
    HistoryKernelProcess d m where
  kernel t := observableRoundKernel P c eta U t
  isMarkov t := observableRoundKernel_isMarkov P hm c heta hs U t

/-- Fresh uniform noise produces exactly the conditional feedback law above. -/
theorem actual_feedback_law {d m : ℕ} (hm : 0 < m) (c : ℕ)
    {eta : ℝ} (heta : 0 ≤ eta) (hs : eta ≤ 1 / 16)
    (U : Bits d) (t : ℕ) (h : History d m t) (a : MSetAction d m) :
    DenseCommonNoise.noiseMeasure.map
        (fun z : Noise => actionLoss a (itemLoss c eta z.val U t h)) =
      (latentFeedbackKernel c eta U t (h, a)).map DenseCommonNoise.feedbackShift := by
  rw [latentFeedbackKernel_apply]
  exact DenseCommonNoise.actual_feedback_law hm heta hs (activeVector c U t h)
    (abs_activeVector_le c U t h) a

def latentRatio {d m : ℕ} (c : ℕ) (eta : ℝ) (U V : Bits d) (t : ℕ)
    (ha : History d m t × MSetAction d m) (y : ℝ) : ℝ≥0∞ :=
  feedbackDensityRatio (feedbackParameter c eta U t ha.1 ha.2)
    (feedbackParameter c eta V t ha.1 ha.2) y

set_option maxHeartbeats 800000 in
-- Composing the finite activity mask with the real-valued feedback density
-- elaborates through the nested history product and the finite function type.
theorem measurable_latentRatio {d m : ℕ} (c : ℕ) (eta : ℝ) (U V : Bits d) (t : ℕ) :
    Measurable (Function.uncurry (latentRatio (m := m) c eta U V t)) := by
  have hbase : Measurable (fun may : (Bits d × MSetAction d m) × ℝ =>
      feedbackDensityRatio (DenseCommonNoise.feedbackParameter eta (maskVector U may.1.1) may.1.2)
        (DenseCommonNoise.feedbackParameter eta (maskVector V may.1.1) may.1.2) may.2) :=
    measurable_from_prod_countable_right (fun ma : Bits d × MSetAction d m =>
      measurable_feedbackDensityRatio
        (DenseCommonNoise.feedbackParameter eta (maskVector U ma.1) ma.2)
        (DenseCommonNoise.feedbackParameter eta (maskVector V ma.1) ma.2))
  have hproj : Measurable (fun hay : (History d m t × MSetAction d m) × ℝ =>
      ((activeMask c t hay.1.1, hay.1.2), hay.2)) :=
    (((measurable_activeMask c t).comp measurable_fst.fst).prodMk
      measurable_fst.snd).prodMk measurable_snd
  convert hbase.comp hproj using 1
  funext hay
  simp only [Function.comp_def, Function.uncurry, latentRatio, feedbackParameter,
    maskVector_activeMask]

theorem latentFeedback_withDensity {d m : ℕ} (hm : 0 < m) (c : ℕ)
    {eta : ℝ} (heta : 0 ≤ eta) (hs : eta ≤ 1 / 16) (U V : Bits d)
    (t : ℕ) (ha : History d m t × MSetAction d m) :
    latentFeedbackKernel c eta U t ha =
      (latentFeedbackKernel c eta V t ha).withDensity (latentRatio c eta U V t ha) := by
  simp only [latentFeedbackKernel_apply]
  exact feedbackDensityMeasure_withDensity_ratio
    ((abs_feedbackParameter_le hm c heta U t ha.1 ha.2).trans hs)
    ((abs_feedbackParameter_le hm c heta V t ha.1 ha.2).trans hs)

/-- The native two-stage KL equality, including the common randomized action. -/
theorem latentTwoStage_klDiv {d m t : ℕ}
    (μ : Measure (History d m t × MSetAction d m)) [IsProbabilityMeasure μ]
    (hm : 0 < m) (c : ℕ) {eta : ℝ} (heta : 0 ≤ eta) (hs : eta ≤ 1 / 16) (U V : Bits d) :
    klDiv (μ ⊗ₘ latentFeedbackKernel c eta U t) (μ ⊗ₘ latentFeedbackKernel c eta V t) =
      ∫⁻ ha, klDiv (feedbackDensityMeasure (feedbackParameter c eta U t ha.1 ha.2))
        (feedbackDensityMeasure (feedbackParameter c eta V t ha.1 ha.2)) ∂μ := by
  letI := latentFeedbackKernel_isMarkov hm c heta hs U t
  letI := latentFeedbackKernel_isMarkov hm c heta hs V t
  let ratioFn : (History d m t × MSetAction d m) × ℝ → ℝ≥0∞ :=
    fun hay => latentRatio c eta U V t hay.1 hay.2
  have hr : Measurable ratioFn := measurable_latentRatio c eta U V t
  have hd : μ ⊗ₘ latentFeedbackKernel c eta U t =
      (μ ⊗ₘ latentFeedbackKernel c eta V t).withDensity ratioFn :=
    Dense.compProd_eq_withDensity_of_apply μ _ _ (latentRatio c eta U V t) hr
      (latentFeedback_withDensity hm c heta hs U V t)
  letI : IsFiniteMeasure ((μ ⊗ₘ latentFeedbackKernel c eta V t).withDensity ratioFn) := by
    rw [← hd]; infer_instance
  calc
    _ = ∫⁻ hay, ENNReal.ofReal (klFun (ratioFn hay).toReal)
        ∂(μ ⊗ₘ latentFeedbackKernel c eta V t) := by
      conv_lhs => rw [hd]
      exact Dense.klDiv_withDensity_eq_lintegral_klFun _ ratioFn hr
    _ = ∫⁻ ha, ∫⁻ y, ENNReal.ofReal (klFun (latentRatio c eta U V t ha y).toReal)
        ∂latentFeedbackKernel c eta V t ha ∂μ := by
      rw [Measure.lintegral_compProd (by fun_prop)]
    _ = _ := by
      apply lintegral_congr
      intro ha
      have hd' := latentFeedback_withDensity hm c heta hs U V t ha
      letI : IsFiniteMeasure ((latentFeedbackKernel c eta V t ha).withDensity
          (latentRatio c eta U V t ha)) := by rw [← hd']; infer_instance
      rw [← latentFeedbackKernel_apply c eta U t ha, ← latentFeedbackKernel_apply c eta V t ha]
      rw [hd']
      symm
      exact Dense.klDiv_withDensity_eq_lintegral_klFun _ _ (measurable_feedbackDensityRatio _ _)

theorem observable_roundKL_eq {d m : ℕ} (P : Policy d m) (hm : 0 < m) (c : ℕ)
    {eta : ℝ} (heta : 0 ≤ eta) (hs : eta ≤ 1 / 16) (U V : Bits d) (t : ℕ) :
    (observableProcess P hm c eta heta hs U).roundKL (observableProcess P hm c eta heta hs V) t =
      ∫⁻ ha, klDiv (feedbackDensityMeasure (feedbackParameter c eta U t ha.1 ha.2))
        (feedbackDensityMeasure (feedbackParameter c eta V t ha.1 ha.2))
        ∂((observableProcess P hm c eta heta hs U).law t ⊗ₘ P.kernel t) := by
  letI := latentFeedbackKernel_isMarkov hm c heta hs U t
  letI := latentFeedbackKernel_isMarkov hm c heta hs V t
  letI : IsMarkovKernel (latentRoundKernel P c eta U t) := by
    unfold latentRoundKernel; infer_instance
  letI : IsMarkovKernel (latentRoundKernel P c eta V t) := by
    unfold latentRoundKernel; infer_instance
  unfold HistoryKernelProcess.roundKL
  change klDiv (_ ⊗ₘ (latentRoundKernel P c eta U t).map DenseCommonNoise.observationShift)
    (_ ⊗ₘ (latentRoundKernel P c eta V t).map DenseCommonNoise.observationShift) = _
  rw [Measure.compProd_map DenseCommonNoise.observationShift.measurable,
    Measure.compProd_map DenseCommonNoise.observationShift.measurable,
    Dense.klDiv_map_measurableEmbedding
      (MeasurableEmbedding.id.prodMap DenseCommonNoise.observationShift.measurableEmbedding)]
  unfold latentRoundKernel
  rw [← Dense.klDiv_map_measurableEmbedding MeasurableEquiv.prodAssoc.symm.measurableEmbedding]
  simp only [Measure.compProd_assoc]
  exact latentTwoStage_klDiv _ hm c heta hs U V

theorem observable_roundKL_bit_le_indicator {d m : ℕ}
    (P : Policy d m) (hm : 0 < m) (c : ℕ) {eta : ℝ}
    (heta : 0 ≤ eta) (hs : eta ≤ 1 / 16) (U : Bits d) (i : Fin d) (t : ℕ) :
    (observableProcess P hm c eta heta hs (Function.update U i false)).roundKL
        (observableProcess P hm c eta heta hs (Function.update U i true)) t ≤
      ∫⁻ ha, ENNReal.ofReal
        (128 * (eta / m) ^ 2 * activeIndicator c t ha.1 i * selectedIndicator i ha.2)
        ∂((observableProcess P hm c eta heta hs (Function.update U i false)).law t ⊗ₘ
          P.kernel t) := by
  rw [observable_roundKL_eq]
  exact lintegral_mono (fun ha => feedback_bit_KL_le hm c heta hs U i t ha.1 ha.2)

end

end MsetsPaper.Lower.SparseCapped
