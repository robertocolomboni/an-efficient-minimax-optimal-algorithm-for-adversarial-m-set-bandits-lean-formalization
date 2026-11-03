import MsetsPaper.Lower.ConfidenceOblivious
import MsetsPaper.Lower.DenseCommonNoiseProcess
import MsetsLower.Lower.Confidence.KLProcess

/-! # Fresh-noise history laws for the oblivious confidence instances

The action-dependent affine feedback map is the same in both environments.
The general internally proved two-stage density/KL theorem is reused, not an
old confidence lower-bound conclusion or stopped-adversary construction.
-/

namespace MsetsPaper.Lower.ConfidenceOblivious

open MsetsLower MsetsLower.Feedback MsetsLower.Lower MsetsLower.Lower.Confidence
open MeasureTheory ProbabilityTheory InformationTheory Set
open scoped ENNReal ProbabilityTheory BigOperators

noncomputable section

def oneHot {d : ℕ} (i : Fin d) (j : Fin d) : ℝ := if j = i then 1 else 0

theorem abs_oneHot_le {d : ℕ} (i j : Fin d) : |oneHot i j| ≤ 1 := by
  unfold oneHot
  split <;> norm_num

theorem actionLoss_oneHot {d m : ℕ} (i : Fin d) (a : MSetAction d m) :
    actionLoss a (oneHot i) = if i ∈ a.val then 1 else 0 := by
  classical
  rw [actionLoss_eq_finset_sum]
  simp [oneHot]

theorem feedbackParameter_oneHot {d m : ℕ} (hm : 1 ≤ m) (Delta : ℝ)
    (i : Fin d) (a : MSetAction d m) :
    DenseCommonNoise.feedbackParameter (4 * m * Delta) (oneHot i) a =
      -4 * Delta * (if i ∈ a.val then 1 else 0) := by
  have hm0 : (m : ℝ) ≠ 0 := by exact_mod_cast Nat.ne_of_gt hm
  unfold DenseCommonNoise.feedbackParameter
  rw [actionLoss_oneHot]
  field_simp

theorem feedbackParameter_zero {d m : ℕ} (eta : ℝ) (a : MSetAction d m) :
    DenseCommonNoise.feedbackParameter eta (fun _ => (0 : ℝ)) a = 0 := by
  simp [DenseCommonNoise.feedbackParameter, actionLoss]

theorem feedback_scale_admissible {m : ℕ} {Delta : ℝ}
    (hDelta : 0 ≤ Delta) (hsmall : (m : ℝ) * Delta ≤ 1 / 2 ^ 13) :
    0 ≤ 4 * (m : ℝ) * Delta ∧ 4 * (m : ℝ) * Delta ≤ 1 / 16 := by
  constructor
  · positivity
  · nlinarith

theorem planted_feedback_identity {d m : ℕ} (hm : 1 ≤ m) (hmd : m ≤ d)
    (Delta z : ℝ) (i : Fin d) (a : MSetAction d m) :
    actionLoss a (plantedItemLoss hmd z Delta 1 i) =
      confidenceScalarFeedback hmd a
        (feedbackMap (DenseCommonNoise.feedbackParameter (4 * m * Delta) (oneHot i) a) z) := by
  rw [actionLoss_plantedItemLoss hm hmd, feedbackParameter_oneHot hm]
  unfold confidenceScalarFeedback confidenceFeedbackBase feedbackMap
  ring

theorem reference_feedback_identity {d m : ℕ} (hm : 1 ≤ m) (hmd : m ≤ d)
    (eta z : ℝ) (a : MSetAction d m) :
    actionLoss a (referenceItemLoss hmd z) =
      confidenceScalarFeedback hmd a
        (feedbackMap (DenseCommonNoise.feedbackParameter eta (fun _ => (0 : ℝ)) a) z) := by
  rw [actionLoss_referenceItemLoss hm hmd, feedbackParameter_zero]
  unfold confidenceScalarFeedback confidenceFeedbackBase feedbackMap
  ring

def freshRoundKernel {d m : ℕ} (P : Policy d m) (hmd : m ≤ d)
    (eta : ℝ) (U : Fin d → ℝ) (t : ℕ) : Kernel (History d m t) (MSetAction d m × ℝ) :=
  (DenseCommonNoise.latentRoundKernel P eta U t).map (confidenceFeedbackEquiv hmd)

theorem freshRoundKernel_isMarkov {d m : ℕ} (P : Policy d m) (hm : 1 ≤ m) (hmd : m ≤ d)
    {eta : ℝ} (heta : 0 ≤ eta) (hs : eta ≤ 1 / 16)
    (U : Fin d → ℝ) (hU : ∀ i, |U i| ≤ 1) (t : ℕ) :
    IsMarkovKernel (freshRoundKernel P hmd eta U t) := by
  letI := DenseCommonNoise.latentFeedbackKernel_isMarkov hm heta hs U hU t
  unfold freshRoundKernel DenseCommonNoise.latentRoundKernel
  exact Kernel.IsMarkovKernel.map _ (confidenceFeedbackEquiv hmd).measurable

def freshProcess {d m : ℕ} (P : Policy d m) (hm : 1 ≤ m) (hmd : m ≤ d)
    (eta : ℝ) (heta : 0 ≤ eta) (hs : eta ≤ 1 / 16)
    (U : Fin d → ℝ) (hU : ∀ i, |U i| ≤ 1) : HistoryKernelProcess d m where
  kernel t := freshRoundKernel P hmd eta U t
  isMarkov t := freshRoundKernel_isMarkov P hm hmd heta hs U hU t

theorem freshRoundKernel_fst {d m : ℕ} (P : Policy d m) (hm : 1 ≤ m) (hmd : m ≤ d)
    {eta : ℝ} (heta : 0 ≤ eta) (hs : eta ≤ 1 / 16)
    (U : Fin d → ℝ) (hU : ∀ i, |U i| ≤ 1) (t : ℕ) :
    Kernel.fst (freshRoundKernel P hmd eta U t) = P.kernel t := by
  letI := DenseCommonNoise.latentFeedbackKernel_isMarkov hm heta hs U hU t
  unfold freshRoundKernel
  rw [Kernel.fst_eq, ← Kernel.map_comp_right _ (confidenceFeedbackEquiv hmd).measurable measurable_fst]
  change Kernel.map (DenseCommonNoise.latentRoundKernel P eta U t) Prod.fst = P.kernel t
  rw [← Kernel.fst_eq]
  unfold DenseCommonNoise.latentRoundKernel
  exact Kernel.fst_compProd _ _

theorem fresh_roundKL_eq {d m : ℕ} (P : Policy d m) (hm : 1 ≤ m) (hmd : m ≤ d)
    {eta : ℝ} (heta : 0 ≤ eta) (hs : eta ≤ 1 / 16)
    (U V : Fin d → ℝ) (hU : ∀ i, |U i| ≤ 1) (hV : ∀ i, |V i| ≤ 1) (t : ℕ) :
    (freshProcess P hm hmd eta heta hs U hU).roundKL
      (freshProcess P hm hmd eta heta hs V hV) t =
      ∫⁻ ha, klDiv (feedbackDensityMeasure (DenseCommonNoise.feedbackParameter eta U ha.2))
        (feedbackDensityMeasure (DenseCommonNoise.feedbackParameter eta V ha.2))
        ∂((freshProcess P hm hmd eta heta hs U hU).law t ⊗ₘ P.kernel t) := by
  letI := DenseCommonNoise.latentFeedbackKernel_isMarkov hm heta hs U hU t
  letI := DenseCommonNoise.latentFeedbackKernel_isMarkov hm heta hs V hV t
  letI : IsMarkovKernel (DenseCommonNoise.latentRoundKernel P eta U t) := by
    unfold DenseCommonNoise.latentRoundKernel; infer_instance
  letI : IsMarkovKernel (DenseCommonNoise.latentRoundKernel P eta V t) := by
    unfold DenseCommonNoise.latentRoundKernel; infer_instance
  unfold HistoryKernelProcess.roundKL
  change klDiv
    (_ ⊗ₘ (DenseCommonNoise.latentRoundKernel P eta U t).map (confidenceFeedbackEquiv hmd))
    (_ ⊗ₘ (DenseCommonNoise.latentRoundKernel P eta V t).map (confidenceFeedbackEquiv hmd)) = _
  rw [Measure.compProd_map (confidenceFeedbackEquiv hmd).measurable,
    Measure.compProd_map (confidenceFeedbackEquiv hmd).measurable,
    Dense.klDiv_map_measurableEmbedding
      (MeasurableEmbedding.id.prodMap (confidenceFeedbackEquiv hmd).measurableEmbedding)]
  unfold DenseCommonNoise.latentRoundKernel
  rw [← Dense.klDiv_map_measurableEmbedding MeasurableEquiv.prodAssoc.symm.measurableEmbedding]
  simp only [Measure.compProd_assoc]
  exact DenseCommonNoise.latentTwoStage_klDiv _ hm heta hs U V hU hV

def referenceProcess {d m : ℕ} (P : Policy d m) (hm : 1 ≤ m) (hmd : m ≤ d)
    (Delta : ℝ) (hDelta : 0 ≤ Delta) (hsmall : (m : ℝ) * Delta ≤ 1 / 2 ^ 13) :
    HistoryKernelProcess d m :=
  freshProcess P hm hmd (4 * m * Delta) (feedback_scale_admissible hDelta hsmall).1
    (feedback_scale_admissible hDelta hsmall).2 (fun _ => 0) (by intro j; norm_num)

def plantedProcess {d m : ℕ} (P : Policy d m) (hm : 1 ≤ m) (hmd : m ≤ d)
    (Delta : ℝ) (hDelta : 0 ≤ Delta) (hsmall : (m : ℝ) * Delta ≤ 1 / 2 ^ 13) (i : Fin d) :
    HistoryKernelProcess d m :=
  freshProcess P hm hmd (4 * m * Delta) (feedback_scale_admissible hDelta hsmall).1
    (feedback_scale_admissible hDelta hsmall).2 (oneHot i) (abs_oneHot_le i)

theorem conditional_feedback_KL_le_indicator {d m : ℕ} (hm : 1 ≤ m)
    (Delta : ℝ) (hDelta : 0 ≤ Delta) (hsmall : (m : ℝ) * Delta ≤ 1 / 2 ^ 13)
    (i : Fin d) (a : MSetAction d m) :
    klDiv (feedbackDensityMeasure 0)
      (feedbackDensityMeasure (-4 * Delta * (if i ∈ a.val then 1 else 0))) ≤
      ENNReal.ofReal (128 * (4 * Delta) ^ 2 * (if i ∈ a.val then 1 else 0)) := by
  have hp : |DenseCommonNoise.feedbackParameter (4 * m * Delta) (oneHot i) a| ≤ 1 / 16 :=
    (DenseCommonNoise.abs_feedbackParameter_le hm (feedback_scale_admissible hDelta hsmall).1
      (oneHot i) (abs_oneHot_le i) a).trans (feedback_scale_admissible hDelta hsmall).2
  rw [feedbackParameter_oneHot hm] at hp
  have hh := FeedbackSharp.klDiv_feedbackDensityMeasure_le_one_twenty_eight
    (by norm_num : |(0 : ℝ)| ≤ 1 / 16) hp
  by_cases hi : i ∈ a.val <;> simpa [hi] using hh

theorem reference_planted_roundKL_le_indicator {d m : ℕ}
    (P : Policy d m) (hm : 1 ≤ m) (hmd : m ≤ d)
    (Delta : ℝ) (hDelta : 0 ≤ Delta) (hsmall : (m : ℝ) * Delta ≤ 1 / 2 ^ 13)
    (i : Fin d) (t : ℕ) :
    (referenceProcess P hm hmd Delta hDelta hsmall).roundKL
      (plantedProcess P hm hmd Delta hDelta hsmall i) t ≤
      ∫⁻ ha, ENNReal.ofReal (128 * (4 * Delta) ^ 2 * (if i ∈ ha.2.val then 1 else 0))
        ∂((referenceProcess P hm hmd Delta hDelta hsmall).law t ⊗ₘ P.kernel t) := by
  unfold referenceProcess plantedProcess
  rw [fresh_roundKL_eq]
  apply lintegral_mono
  intro ha
  dsimp only
  rw [feedbackParameter_zero, feedbackParameter_oneHot hm]
  exact conditional_feedback_KL_le_indicator hm Delta hDelta hsmall i ha.2

end

end MsetsPaper.Lower.ConfidenceOblivious
