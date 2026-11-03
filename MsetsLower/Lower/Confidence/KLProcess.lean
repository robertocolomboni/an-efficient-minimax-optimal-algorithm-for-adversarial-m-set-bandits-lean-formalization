import MsetsLower.Feedback.MeasureKL
import MsetsLower.Lower.Confidence.Selection
import MsetsLower.Lower.Confidence.KLArithmetic
import MsetsLower.Lower.Dense.AdaptiveLaw

/-!
# Adaptive stochastic laws for the confidence construction

This file constructs the reference law `P₀` and the planted law `Pᵢ` on
the observable action--scalar-feedback history.  The latent normalized
feedback is mapped by the exact affine formula in the manuscript, so the
policy sees the genuine aggregate action loss.
-/

namespace MsetsLower.Lower.Confidence

open MsetsLower Feedback
open MeasureTheory ProbabilityTheory InformationTheory Set
open scoped ENNReal ProbabilityTheory

noncomputable section

/-- Action-dependent deterministic offset of the confidence feedback. -/
def confidenceFeedbackBase {n k : Nat} (hkn : k ≤ n)
    (A : MSetAction n k) : Real :=
  (1 : Real) / 4 + (candidateCount hkn A : Real) / (8 * (k : Real))

theorem measurable_confidenceFeedbackBase {n k : Nat} (hkn : k ≤ n) :
    Measurable (confidenceFeedbackBase hkn) :=
  measurable_of_finite _

/-- Convert normalized feedback `F_u(Z)` into the literal scalar action
loss observed by the learner. -/
def confidenceScalarFeedback {n k : Nat} (hkn : k ≤ n)
    (A : MSetAction n k) (y : Real) : Real :=
  confidenceFeedbackBase hkn A + y / 4

/-- The lossless action--feedback encoding and its explicit inverse. -/
def confidenceFeedbackEquiv {n k : Nat} (hkn : k ≤ n) :
    (MSetAction n k × Real) ≃ᵐ (MSetAction n k × Real) where
  toEquiv :=
    { toFun := fun Ay =>
        (Ay.1, confidenceScalarFeedback hkn Ay.1 Ay.2)
      invFun := fun Ax =>
        (Ax.1, 4 * (Ax.2 - confidenceFeedbackBase hkn Ax.1))
      left_inv := by
        rintro ⟨A, y⟩
        apply Prod.ext
        · rfl
        · dsimp [confidenceScalarFeedback]
          ring
      right_inv := by
        rintro ⟨A, x⟩
        apply Prod.ext
        · rfl
        · dsimp [confidenceScalarFeedback]
          ring }
  measurable_toFun := by
    exact measurable_fst.prodMk
      (((measurable_confidenceFeedbackBase hkn).comp measurable_fst).add
        (measurable_snd.div_const 4))
  measurable_invFun := by
    exact measurable_fst.prodMk <|
      measurable_const.mul <|
        measurable_snd.sub <|
          (measurable_confidenceFeedbackBase hkn).comp measurable_fst

theorem measurableEmbedding_confidenceFeedbackEquiv {n k : Nat}
    (hkn : k ≤ n) :
    MeasurableEmbedding (confidenceFeedbackEquiv hkn) :=
  (confidenceFeedbackEquiv hkn).measurableEmbedding

/-- The history--action states at which candidate `i` is both active and
selected. -/
def confidenceActiveSelectedSet {n k : Nat} (hkn : k ≤ n)
    (B : Real) (i : Fin n) (t : Nat) :
    Set (History n k t × MSetAction n k) :=
  {ha | cumulativePenalty hkn t ha.1 < B ∧ i ∈ ha.2.1}

theorem measurableSet_confidenceActiveSelectedSet {n k : Nat}
    (hkn : k ≤ n) (B : Real) (i : Fin n) (t : Nat) :
    MeasurableSet (confidenceActiveSelectedSet hkn B i t) := by
  have hfirst : MeasurableSet
      {ha : History n k t × MSetAction n k |
        cumulativePenalty hkn t ha.1 < B} := by
    exact ((measurable_cumulativePenalty hkn t).comp measurable_fst)
      measurableSet_Iio
  have hsecond : MeasurableSet
      {ha : History n k t × MSetAction n k | i ∈ ha.2.1} := by
    exact measurable_snd
      (show MeasurableSet {A : MSetAction n k | i ∈ A.1} from
        MeasurableSet.of_discrete)
  exact hfirst.inter hsecond

/-- Reference normalized feedback is `F₀(Z)`. -/
def confidenceReferenceFeedbackKernel {n k t : Nat} :
    Kernel (History n k t × MSetAction n k) Real :=
  Kernel.const _ (feedbackDensityMeasure 0)

theorem confidenceReferenceFeedbackKernel_isMarkov {n k t : Nat} :
    IsMarkovKernel
      (confidenceReferenceFeedbackKernel :
        Kernel (History n k t × MSetAction n k) Real) := by
  letI : IsProbabilityMeasure (feedbackDensityMeasure 0) :=
    ⟨feedbackDensityMeasure_apply_univ (by norm_num)⟩
  unfold confidenceReferenceFeedbackKernel
  infer_instance

/-- Planted normalized feedback is `F_{-4Δ}(Z)` precisely at active
selected states, and `F₀(Z)` elsewhere. -/
def confidencePlantedFeedbackKernel {n k : Nat} (hkn : k ≤ n)
    (Delta B : Real) (i : Fin n) (t : Nat) :
    Kernel (History n k t × MSetAction n k) Real := by
  classical
  exact Kernel.piecewise
    (measurableSet_confidenceActiveSelectedSet hkn B i t)
      (Kernel.const _ (feedbackDensityMeasure (-4 * Delta)))
      (Kernel.const _ (feedbackDensityMeasure 0))

theorem confidencePlantedFeedbackKernel_isMarkov {n k : Nat}
    (hkn : k ≤ n) {Delta : Real} (hDelta : |4 * Delta| ≤ 1 / 16)
    (B : Real) (i : Fin n) (t : Nat) :
    IsMarkovKernel
      (confidencePlantedFeedbackKernel hkn Delta B i t) := by
  classical
  have hneg : |-4 * Delta| ≤ 1 / 16 := by simpa [abs_mul] using hDelta
  letI : IsProbabilityMeasure (feedbackDensityMeasure (-4 * Delta)) :=
    ⟨feedbackDensityMeasure_apply_univ hneg⟩
  letI : IsProbabilityMeasure (feedbackDensityMeasure 0) :=
    ⟨feedbackDensityMeasure_apply_univ (by norm_num)⟩
  unfold confidencePlantedFeedbackKernel
  infer_instance

@[simp] theorem confidenceReferenceFeedbackKernel_apply {n k t : Nat}
    (ha : History n k t × MSetAction n k) :
    (confidenceReferenceFeedbackKernel :
      Kernel (History n k t × MSetAction n k) Real) ha =
      feedbackDensityMeasure 0 := rfl

theorem confidencePlantedFeedbackKernel_apply_of_mem {n k : Nat}
    (hkn : k ≤ n) (Delta B : Real) (i : Fin n) (t : Nat)
    (ha : History n k t × MSetAction n k)
    (ha_mem : ha ∈ confidenceActiveSelectedSet hkn B i t) :
    confidencePlantedFeedbackKernel hkn Delta B i t ha =
      feedbackDensityMeasure (-4 * Delta) := by
  classical
  rw [confidencePlantedFeedbackKernel, Kernel.piecewise_apply, if_pos ha_mem]
  rfl

theorem confidencePlantedFeedbackKernel_apply_of_notMem {n k : Nat}
    (hkn : k ≤ n) (Delta B : Real) (i : Fin n) (t : Nat)
    (ha : History n k t × MSetAction n k)
    (ha_notMem : ha ∉ confidenceActiveSelectedSet hkn B i t) :
    confidencePlantedFeedbackKernel hkn Delta B i t ha =
      feedbackDensityMeasure 0 := by
  classical
  rw [confidencePlantedFeedbackKernel, Kernel.piecewise_apply, if_neg ha_notMem]
  rfl

/-- First sample the policy action, then the reference normalized feedback. -/
def confidenceReferenceLatentRoundKernel {n k : Nat} (P : Policy n k)
    (t : Nat) : Kernel (History n k t) (MSetAction n k × Real) :=
  P.kernel t ⊗ₖ
    (confidenceReferenceFeedbackKernel :
      Kernel (History n k t × MSetAction n k) Real)

/-- First sample the policy action, then the planted normalized feedback. -/
def confidencePlantedLatentRoundKernel {n k : Nat} (P : Policy n k)
    (hkn : k ≤ n) (Delta B : Real) (i : Fin n) (t : Nat) :
    Kernel (History n k t) (MSetAction n k × Real) :=
  P.kernel t ⊗ₖ confidencePlantedFeedbackKernel hkn Delta B i t

/-- Observable reference round kernel. -/
def confidenceReferenceRoundKernel {n k : Nat} (P : Policy n k)
    (hkn : k ≤ n) (t : Nat) :
    Kernel (History n k t) (MSetAction n k × Real) :=
  (confidenceReferenceLatentRoundKernel P t).map
    (confidenceFeedbackEquiv hkn)

/-- Observable planted round kernel. -/
def confidencePlantedRoundKernel {n k : Nat} (P : Policy n k)
    (hkn : k ≤ n) (Delta B : Real) (i : Fin n) (t : Nat) :
    Kernel (History n k t) (MSetAction n k × Real) :=
  (confidencePlantedLatentRoundKernel P hkn Delta B i t).map
    (confidenceFeedbackEquiv hkn)

theorem confidenceReferenceRoundKernel_isMarkov {n k : Nat}
    (P : Policy n k) (hkn : k ≤ n) (t : Nat) :
    IsMarkovKernel (confidenceReferenceRoundKernel P hkn t) := by
  letI : IsMarkovKernel
      (confidenceReferenceFeedbackKernel :
        Kernel (History n k t × MSetAction n k) Real) :=
    confidenceReferenceFeedbackKernel_isMarkov
  unfold confidenceReferenceRoundKernel confidenceReferenceLatentRoundKernel
  exact Kernel.IsMarkovKernel.map _ (confidenceFeedbackEquiv hkn).measurable

theorem confidencePlantedRoundKernel_isMarkov {n k : Nat}
    (P : Policy n k) (hkn : k ≤ n) {Delta : Real}
    (hDelta : |4 * Delta| ≤ 1 / 16) (B : Real) (i : Fin n) (t : Nat) :
    IsMarkovKernel (confidencePlantedRoundKernel P hkn Delta B i t) := by
  letI : IsMarkovKernel
      (confidencePlantedFeedbackKernel hkn Delta B i t) :=
    confidencePlantedFeedbackKernel_isMarkov hkn hDelta B i t
  unfold confidencePlantedRoundKernel confidencePlantedLatentRoundKernel
  exact Kernel.IsMarkovKernel.map _ (confidenceFeedbackEquiv hkn).measurable

/-- Reference stochastic process `P₀` on observable histories. -/
def confidenceReferenceProcess {n k : Nat} (P : Policy n k)
    (hkn : k ≤ n) : HistoryKernelProcess n k where
  kernel t := confidenceReferenceRoundKernel P hkn t
  isMarkov t := confidenceReferenceRoundKernel_isMarkov P hkn t

/-- Planted stochastic process `Pᵢ` on observable histories. -/
def confidencePlantedProcess {n k : Nat} (P : Policy n k)
    (hkn : k ≤ n) (Delta : Real) (hDelta : |4 * Delta| ≤ 1 / 16)
    (B : Real) (i : Fin n) : HistoryKernelProcess n k where
  kernel t := confidencePlantedRoundKernel P hkn Delta B i t
  isMarkov t := confidencePlantedRoundKernel_isMarkov P hkn hDelta B i t

/-! ## Identification with the manuscript's item losses -/

theorem confidenceScalarFeedback_zero_eq_reference_actionLoss
    {n k : Nat} (hk : 1 ≤ k) (hkn : k ≤ n)
    (A : MSetAction n k) (z : Real) :
    confidenceScalarFeedback hkn A (feedbackMap 0 z) =
      actionLoss A (referenceItemLoss hkn z) := by
  rw [actionLoss_referenceItemLoss hk hkn]
  unfold confidenceScalarFeedback confidenceFeedbackBase feedbackMap
  ring

theorem confidenceScalarFeedback_planted_of_mem
    {n k : Nat} (hk : 1 ≤ k) (hkn : k ≤ n)
    (Delta B : Real) (i : Fin n) (t : Nat)
    (h : History n k t) (A : MSetAction n k) (z : Real)
    (hmem : (h, A) ∈ confidenceActiveSelectedSet hkn B i t) :
    confidenceScalarFeedback hkn A (feedbackMap (-4 * Delta) z) =
      actionLoss A
        (plantedItemLoss hkn z Delta (activeIndicator hkn B t h) i) := by
  have hactive : cumulativePenalty hkn t h < B := hmem.1
  have hi : i ∈ A.1 := hmem.2
  rw [actionLoss_plantedItemLoss hk hkn]
  simp only [activeIndicator, hactive, if_pos, hi]
  unfold confidenceScalarFeedback confidenceFeedbackBase feedbackMap
  ring

theorem confidenceScalarFeedback_planted_of_notMem
    {n k : Nat} (hk : 1 ≤ k) (hkn : k ≤ n)
    (Delta B : Real) (i : Fin n) (t : Nat)
    (h : History n k t) (A : MSetAction n k) (z : Real)
    (hnot : (h, A) ∉ confidenceActiveSelectedSet hkn B i t) :
    confidenceScalarFeedback hkn A (feedbackMap 0 z) =
      actionLoss A
        (plantedItemLoss hkn z Delta (activeIndicator hkn B t h) i) := by
  rw [actionLoss_plantedItemLoss hk hkn]
  by_cases hactive : cumulativePenalty hkn t h < B
  · have hi : i ∉ A.1 := by
      intro hi
      exact hnot ⟨hactive, hi⟩
    rw [activeIndicator, if_pos hactive, if_neg hi]
    unfold confidenceScalarFeedback confidenceFeedbackBase feedbackMap
    ring
  · rw [activeIndicator, if_neg hactive]
    unfold confidenceScalarFeedback confidenceFeedbackBase feedbackMap
    ring

/-! ## Conditional likelihood ratio -/

/-- Pointwise density ratio of the reference feedback relative to the
planted feedback.  It is one when the two conditional laws coincide. -/
def confidenceFeedbackLikelihoodRatio {n k : Nat} (hkn : k ≤ n)
    (Delta B : Real) (i : Fin n) (t : Nat)
    (ha : History n k t × MSetAction n k) (y : Real) : ℝ≥0∞ := by
  classical
  exact if ha ∈ confidenceActiveSelectedSet hkn B i t then
    feedbackDensityRatio 0 (-4 * Delta) y else 1

theorem measurable_uncurry_confidenceFeedbackLikelihoodRatio
    {n k : Nat} (hkn : k ≤ n) (Delta B : Real) (i : Fin n) (t : Nat) :
    Measurable
      (Function.uncurry
        (confidenceFeedbackLikelihoodRatio hkn Delta B i t)) := by
  classical
  apply Measurable.ite
  · exact (measurableSet_confidenceActiveSelectedSet hkn B i t).preimage
      measurable_fst
  · exact (measurable_feedbackDensityRatio 0 (-4 * Delta)).comp measurable_snd
  · exact measurable_const

theorem confidenceFeedbackLikelihoodRatio_of_mem
    {n k : Nat} (hkn : k ≤ n) (Delta B : Real) (i : Fin n) (t : Nat)
    (ha : History n k t × MSetAction n k)
    (hmem : ha ∈ confidenceActiveSelectedSet hkn B i t) :
    confidenceFeedbackLikelihoodRatio hkn Delta B i t ha =
      feedbackDensityRatio 0 (-4 * Delta) := by
  classical
  funext y
  simp [confidenceFeedbackLikelihoodRatio, hmem]

theorem confidenceFeedbackLikelihoodRatio_of_notMem
    {n k : Nat} (hkn : k ≤ n) (Delta B : Real) (i : Fin n) (t : Nat)
    (ha : History n k t × MSetAction n k)
    (hnot : ha ∉ confidenceActiveSelectedSet hkn B i t) :
    confidenceFeedbackLikelihoodRatio hkn Delta B i t ha = 1 := by
  classical
  funext y
  simp [confidenceFeedbackLikelihoodRatio, hnot]

/-- Pointwise reweighting of the planted conditional feedback recovers the
reference conditional feedback. -/
theorem confidenceFeedbackKernel_eq_withDensity
    {n k : Nat} (hkn : k ≤ n) {Delta : Real}
    (hDelta : |4 * Delta| ≤ 1 / 16) (B : Real) (i : Fin n) (t : Nat)
    (ha : History n k t × MSetAction n k) :
    (confidenceReferenceFeedbackKernel :
      Kernel (History n k t × MSetAction n k) Real) ha =
      (confidencePlantedFeedbackKernel hkn Delta B i t ha).withDensity
        (confidenceFeedbackLikelihoodRatio hkn Delta B i t ha) := by
  classical
  have hneg : |-4 * Delta| ≤ 1 / 16 := by simpa [abs_mul] using hDelta
  by_cases hmem : ha ∈ confidenceActiveSelectedSet hkn B i t
  · rw [confidenceReferenceFeedbackKernel_apply,
      confidencePlantedFeedbackKernel_apply_of_mem hkn Delta B i t ha hmem,
      confidenceFeedbackLikelihoodRatio_of_mem hkn Delta B i t ha hmem]
    exact feedbackDensityMeasure_withDensity_ratio (by norm_num) hneg
  · rw [confidenceReferenceFeedbackKernel_apply,
      confidencePlantedFeedbackKernel_apply_of_notMem hkn Delta B i t ha hmem,
      confidenceFeedbackLikelihoodRatio_of_notMem hkn Delta B i t ha hmem,
      withDensity_one]

theorem measurable_confidenceFeedbackLikelihoodRatio
    {n k : Nat} (hkn : k ≤ n) (Delta B : Real) (i : Fin n) (t : Nat)
    (ha : History n k t × MSetAction n k) :
    Measurable (confidenceFeedbackLikelihoodRatio hkn Delta B i t ha) := by
  exact (measurable_uncurry_confidenceFeedbackLikelihoodRatio
    hkn Delta B i t).comp (measurable_const.prodMk measurable_id)

/-! ## Exact conditional KL -/

/-- Reweighting the final feedback coordinate lifts through an arbitrary
common history--action law. -/
theorem confidenceTwoStage_eq_withDensity
    {n k t : Nat}
    (μ : Measure (History n k t × MSetAction n k)) [SFinite μ]
    (hkn : k ≤ n) {Delta : Real} (hDelta : |4 * Delta| ≤ 1 / 16)
    (B : Real) (i : Fin n) :
    μ ⊗ₘ (confidenceReferenceFeedbackKernel :
        Kernel (History n k t × MSetAction n k) Real) =
      (μ ⊗ₘ confidencePlantedFeedbackKernel hkn Delta B i t).withDensity
        (Function.uncurry
          (confidenceFeedbackLikelihoodRatio hkn Delta B i t)) := by
  letI : IsMarkovKernel
      (confidenceReferenceFeedbackKernel :
        Kernel (History n k t × MSetAction n k) Real) :=
    confidenceReferenceFeedbackKernel_isMarkov
  letI : IsMarkovKernel
      (confidencePlantedFeedbackKernel hkn Delta B i t) :=
    confidencePlantedFeedbackKernel_isMarkov hkn hDelta B i t
  apply Dense.compProd_eq_withDensity_of_apply μ _ _
      (confidenceFeedbackLikelihoodRatio hkn Delta B i t)
      (measurable_uncurry_confidenceFeedbackLikelihoodRatio hkn Delta B i t)
  exact confidenceFeedbackKernel_eq_withDensity hkn hDelta B i t

/-- The likelihood-ratio integral at a fixed history--action state is
exactly the KL divergence of its two conditional feedback laws. -/
theorem lintegral_confidenceFeedbackLikelihoodRatio_eq_klDiv
    {n k t : Nat} (hkn : k ≤ n) {Delta : Real}
    (hDelta : |4 * Delta| ≤ 1 / 16) (B : Real) (i : Fin n)
    (ha : History n k t × MSetAction n k) :
    (∫⁻ y, ENNReal.ofReal
        (klFun ((confidenceFeedbackLikelihoodRatio hkn Delta B i t ha y).toReal))
      ∂confidencePlantedFeedbackKernel hkn Delta B i t ha) =
      klDiv
        ((confidenceReferenceFeedbackKernel :
          Kernel (History n k t × MSetAction n k) Real) ha)
        (confidencePlantedFeedbackKernel hkn Delta B i t ha) := by
  letI : IsMarkovKernel
      (confidenceReferenceFeedbackKernel :
        Kernel (History n k t × MSetAction n k) Real) :=
    confidenceReferenceFeedbackKernel_isMarkov
  letI : IsMarkovKernel
      (confidencePlantedFeedbackKernel hkn Delta B i t) :=
    confidencePlantedFeedbackKernel_isMarkov hkn hDelta B i t
  letI : IsFiniteMeasure
      ((confidencePlantedFeedbackKernel hkn Delta B i t ha).withDensity
        (confidenceFeedbackLikelihoodRatio hkn Delta B i t ha)) := by
    rw [← confidenceFeedbackKernel_eq_withDensity hkn hDelta B i t ha]
    infer_instance
  symm
  rw [confidenceFeedbackKernel_eq_withDensity hkn hDelta B i t ha]
  exact Dense.klDiv_withDensity_eq_lintegral_klFun _ _
    (measurable_confidenceFeedbackLikelihoodRatio hkn Delta B i t ha)

/-- Chain rule for a common history--action law followed by the reference
or planted confidence feedback kernel. -/
theorem klDiv_confidenceTwoStage_eq_lintegral
    {n k t : Nat}
    (μ : Measure (History n k t × MSetAction n k)) [IsProbabilityMeasure μ]
    (hkn : k ≤ n) {Delta : Real} (hDelta : |4 * Delta| ≤ 1 / 16)
    (B : Real) (i : Fin n) :
    klDiv
        (μ ⊗ₘ (confidenceReferenceFeedbackKernel :
          Kernel (History n k t × MSetAction n k) Real))
        (μ ⊗ₘ confidencePlantedFeedbackKernel hkn Delta B i t) =
      ∫⁻ ha,
        klDiv
          ((confidenceReferenceFeedbackKernel :
            Kernel (History n k t × MSetAction n k) Real) ha)
          (confidencePlantedFeedbackKernel hkn Delta B i t ha) ∂μ := by
  letI : IsMarkovKernel
      (confidenceReferenceFeedbackKernel :
        Kernel (History n k t × MSetAction n k) Real) :=
    confidenceReferenceFeedbackKernel_isMarkov
  letI : IsMarkovKernel
      (confidencePlantedFeedbackKernel hkn Delta B i t) :=
    confidencePlantedFeedbackKernel_isMarkov hkn hDelta B i t
  let ratio : (History n k t × MSetAction n k) × Real → ℝ≥0∞ :=
    Function.uncurry (confidenceFeedbackLikelihoodRatio hkn Delta B i t)
  have hratio : Measurable ratio :=
    measurable_uncurry_confidenceFeedbackLikelihoodRatio hkn Delta B i t
  have hden := confidenceTwoStage_eq_withDensity
    μ hkn hDelta B i
  letI : IsFiniteMeasure
      ((μ ⊗ₘ confidencePlantedFeedbackKernel hkn Delta B i t).withDensity
        ratio) := by
    rw [← hden]
    infer_instance
  calc
    klDiv
        (μ ⊗ₘ (confidenceReferenceFeedbackKernel :
          Kernel (History n k t × MSetAction n k) Real))
        (μ ⊗ₘ confidencePlantedFeedbackKernel hkn Delta B i t) =
      klDiv
        ((μ ⊗ₘ confidencePlantedFeedbackKernel hkn Delta B i t).withDensity
          ratio)
        (μ ⊗ₘ confidencePlantedFeedbackKernel hkn Delta B i t) := by rw [hden]
    _ = ∫⁻ x, ENNReal.ofReal (klFun (ratio x).toReal)
          ∂(μ ⊗ₘ confidencePlantedFeedbackKernel hkn Delta B i t) :=
      Dense.klDiv_withDensity_eq_lintegral_klFun _ ratio hratio
    _ = ∫⁻ ha, ∫⁻ y,
          ENNReal.ofReal
            (klFun
              ((confidenceFeedbackLikelihoodRatio hkn Delta B i t ha y).toReal))
          ∂confidencePlantedFeedbackKernel hkn Delta B i t ha ∂μ := by
      rw [Measure.lintegral_compProd (by fun_prop)]
      rfl
    _ = ∫⁻ ha,
          klDiv
            ((confidenceReferenceFeedbackKernel :
              Kernel (History n k t × MSetAction n k) Real) ha)
            (confidencePlantedFeedbackKernel hkn Delta B i t ha) ∂μ := by
      apply lintegral_congr
      intro ha
      exact lintegral_confidenceFeedbackLikelihoodRatio_eq_klDiv
        hkn hDelta B i ha

/-! ## One adaptive round -/

/-- The observable affine encoding is lossless, hence does not change the
one-round KL divergence. -/
theorem confidenceReference_roundKL_eq_latent
    {n k : Nat} (P : Policy n k) (hkn : k ≤ n) {Delta : Real}
    (hDelta : |4 * Delta| ≤ 1 / 16) (B : Real) (i : Fin n) (t : Nat) :
    (confidenceReferenceProcess P hkn).roundKL
        (confidencePlantedProcess P hkn Delta hDelta B i) t =
      klDiv
        ((confidenceReferenceProcess P hkn).law t ⊗ₘ
          confidenceReferenceLatentRoundKernel P t)
        ((confidenceReferenceProcess P hkn).law t ⊗ₘ
          confidencePlantedLatentRoundKernel P hkn Delta B i t) := by
  letI : IsMarkovKernel (confidenceReferenceLatentRoundKernel P t) := by
    letI : IsMarkovKernel
        (confidenceReferenceFeedbackKernel :
          Kernel (History n k t × MSetAction n k) Real) :=
      confidenceReferenceFeedbackKernel_isMarkov
    unfold confidenceReferenceLatentRoundKernel
    infer_instance
  letI : IsMarkovKernel
      (confidencePlantedLatentRoundKernel P hkn Delta B i t) := by
    letI : IsMarkovKernel
        (confidencePlantedFeedbackKernel hkn Delta B i t) :=
      confidencePlantedFeedbackKernel_isMarkov hkn hDelta B i t
    unfold confidencePlantedLatentRoundKernel
    infer_instance
  unfold HistoryKernelProcess.roundKL
  change klDiv
      ((confidenceReferenceProcess P hkn).law t ⊗ₘ
        confidenceReferenceRoundKernel P hkn t)
      ((confidenceReferenceProcess P hkn).law t ⊗ₘ
        confidencePlantedRoundKernel P hkn Delta B i t) = _
  rw [confidenceReferenceRoundKernel, confidencePlantedRoundKernel,
    Measure.compProd_map (confidenceFeedbackEquiv hkn).measurable,
    Measure.compProd_map (confidenceFeedbackEquiv hkn).measurable]
  exact Dense.klDiv_map_measurableEmbedding
    (MeasurableEmbedding.id.prodMap
      (measurableEmbedding_confidenceFeedbackEquiv hkn)) _ _

/-- Reassociate the latent law into the common history--action prefix and
the environment-dependent feedback kernel. -/
theorem confidenceReference_roundKL_eq_twoStage
    {n k : Nat} (P : Policy n k) (hkn : k ≤ n) {Delta : Real}
    (hDelta : |4 * Delta| ≤ 1 / 16) (B : Real) (i : Fin n) (t : Nat) :
    (confidenceReferenceProcess P hkn).roundKL
        (confidencePlantedProcess P hkn Delta hDelta B i) t =
      klDiv
        (((confidenceReferenceProcess P hkn).law t ⊗ₘ P.kernel t) ⊗ₘ
          (confidenceReferenceFeedbackKernel :
            Kernel (History n k t × MSetAction n k) Real))
        (((confidenceReferenceProcess P hkn).law t ⊗ₘ P.kernel t) ⊗ₘ
          confidencePlantedFeedbackKernel hkn Delta B i t) := by
  letI : IsMarkovKernel
      (confidenceReferenceFeedbackKernel :
        Kernel (History n k t × MSetAction n k) Real) :=
    confidenceReferenceFeedbackKernel_isMarkov
  letI : IsMarkovKernel
      (confidencePlantedFeedbackKernel hkn Delta B i t) :=
    confidencePlantedFeedbackKernel_isMarkov hkn hDelta B i t
  letI : IsMarkovKernel (confidenceReferenceLatentRoundKernel P t) := by
    unfold confidenceReferenceLatentRoundKernel
    infer_instance
  letI : IsMarkovKernel
      (confidencePlantedLatentRoundKernel P hkn Delta B i t) := by
    unfold confidencePlantedLatentRoundKernel
    infer_instance
  rw [confidenceReference_roundKL_eq_latent P hkn hDelta B i t]
  unfold confidenceReferenceLatentRoundKernel
    confidencePlantedLatentRoundKernel
  rw [← Dense.klDiv_map_measurableEmbedding
    MeasurableEquiv.prodAssoc.symm.measurableEmbedding]
  simp only [Measure.compProd_assoc]

/-- Exact one-round KL formula under the actual reference prefix law and
arbitrary history-measurable randomized policy. -/
theorem confidenceReference_roundKL_eq_lintegral
    {n k : Nat} (P : Policy n k) (hkn : k ≤ n) {Delta : Real}
    (hDelta : |4 * Delta| ≤ 1 / 16) (B : Real) (i : Fin n) (t : Nat) :
    (confidenceReferenceProcess P hkn).roundKL
        (confidencePlantedProcess P hkn Delta hDelta B i) t =
      ∫⁻ ha,
        klDiv
          ((confidenceReferenceFeedbackKernel :
            Kernel (History n k t × MSetAction n k) Real) ha)
          (confidencePlantedFeedbackKernel hkn Delta B i t ha)
        ∂((confidenceReferenceProcess P hkn).law t ⊗ₘ P.kernel t) := by
  rw [confidenceReference_roundKL_eq_twoStage P hkn hDelta B i t]
  exact klDiv_confidenceTwoStage_eq_lintegral _ hkn hDelta B i

/-- The pointwise information budget: the feedback-density constant on the
active-selected set and zero elsewhere. -/
def confidenceConditionalKLBudget
    {n k : Nat} (hkn : k ≤ n) (Delta B : Real) (i : Fin n) (t : Nat)
    (ha : History n k t × MSetAction n k) : ℝ≥0∞ := by
  classical
  exact if ha ∈ confidenceActiveSelectedSet hkn B i t then
    ENNReal.ofReal (128 * (4 * Delta) ^ 2) else 0

/-- ENNReal indicator of an active round on which candidate `i` is selected. -/
def confidenceActiveSelectedENN
    {n k : Nat} (hkn : k ≤ n) (B : Real) (i : Fin n) (t : Nat)
    (ha : History n k t × MSetAction n k) : ℝ≥0∞ := by
  classical
  exact if ha ∈ confidenceActiveSelectedSet hkn B i t then 1 else 0

theorem measurable_confidenceActiveSelectedENN
    {n k : Nat} (hkn : k ≤ n) (B : Real) (i : Fin n) (t : Nat) :
    Measurable (confidenceActiveSelectedENN hkn B i t) := by
  classical
  unfold confidenceActiveSelectedENN
  exact Measurable.ite
    (measurableSet_confidenceActiveSelectedSet hkn B i t)
    measurable_const measurable_const

theorem confidenceConditionalKLBudget_eq_mul_indicator
    {n k : Nat} (hkn : k ≤ n) (Delta B : Real) (i : Fin n) (t : Nat)
    (ha : History n k t × MSetAction n k) :
    confidenceConditionalKLBudget hkn Delta B i t ha =
      ENNReal.ofReal (128 * (4 * Delta) ^ 2) *
        confidenceActiveSelectedENN hkn B i t ha := by
  classical
  by_cases hmem : ha ∈ confidenceActiveSelectedSet hkn B i t <;>
    simp [confidenceConditionalKLBudget, confidenceActiveSelectedENN, hmem]

/-- The conditional information cost is zero off the active-selected set
and bounded by the feedback-density lemma on that set. -/
theorem confidenceConditionalKL_le
    {n k t : Nat} (hkn : k ≤ n) {Delta : Real}
    (hDelta : |4 * Delta| ≤ 1 / 16) (B : Real) (i : Fin n)
    (ha : History n k t × MSetAction n k) :
    klDiv
        ((confidenceReferenceFeedbackKernel :
          Kernel (History n k t × MSetAction n k) Real) ha)
        (confidencePlantedFeedbackKernel hkn Delta B i t ha) ≤
      confidenceConditionalKLBudget hkn Delta B i t ha := by
  classical
  by_cases hmem : ha ∈ confidenceActiveSelectedSet hkn B i t
  · rw [confidenceConditionalKLBudget, if_pos hmem,
      confidenceReferenceFeedbackKernel_apply,
      confidencePlantedFeedbackKernel_apply_of_mem hkn Delta B i t ha hmem]
    have hneg : |-4 * Delta| ≤ 1 / 16 := by simpa [abs_mul] using hDelta
    calc
      klDiv (feedbackDensityMeasure 0)
          (feedbackDensityMeasure (-4 * Delta)) ≤
          ENNReal.ofReal (128 * (0 - (-4 * Delta)) ^ 2) :=
        klDiv_feedbackDensityMeasure_le (by norm_num) hneg
      _ = ENNReal.ofReal (128 * (4 * Delta) ^ 2) := by ring_nf
  · letI : IsProbabilityMeasure (feedbackDensityMeasure 0) :=
      ⟨feedbackDensityMeasure_apply_univ (by norm_num)⟩
    rw [confidenceConditionalKLBudget, if_neg hmem,
      confidenceReferenceFeedbackKernel_apply,
      confidencePlantedFeedbackKernel_apply_of_notMem hkn Delta B i t ha hmem,
      klDiv_self]

/-- One-round information is the feedback-density constant times the actual
reference probability of selecting the active candidate. -/
theorem confidenceReference_roundKL_le_activeSelected
    {n k : Nat} (P : Policy n k) (hkn : k ≤ n) {Delta : Real}
    (hDelta : |4 * Delta| ≤ 1 / 16) (B : Real) (i : Fin n) (t : Nat) :
    (confidenceReferenceProcess P hkn).roundKL
        (confidencePlantedProcess P hkn Delta hDelta B i) t ≤
      ENNReal.ofReal (128 * (4 * Delta) ^ 2) *
        ∫⁻ ha, confidenceActiveSelectedENN hkn B i t ha
          ∂((confidenceReferenceProcess P hkn).law t ⊗ₘ P.kernel t) := by
  rw [confidenceReference_roundKL_eq_lintegral P hkn hDelta B i t]
  calc
    (∫⁻ ha,
        klDiv
          ((confidenceReferenceFeedbackKernel :
            Kernel (History n k t × MSetAction n k) Real) ha)
          (confidencePlantedFeedbackKernel hkn Delta B i t ha)
        ∂((confidenceReferenceProcess P hkn).law t ⊗ₘ P.kernel t)) ≤
      ∫⁻ ha, confidenceConditionalKLBudget hkn Delta B i t ha
        ∂((confidenceReferenceProcess P hkn).law t ⊗ₘ P.kernel t) := by
      exact lintegral_mono fun ha =>
        confidenceConditionalKL_le hkn hDelta B i ha
    _ = ∫⁻ ha,
        ENNReal.ofReal (128 * (4 * Delta) ^ 2) *
          confidenceActiveSelectedENN hkn B i t ha
        ∂((confidenceReferenceProcess P hkn).law t ⊗ₘ P.kernel t) := by
      apply lintegral_congr
      intro ha
      exact confidenceConditionalKLBudget_eq_mul_indicator
        hkn Delta B i t ha
    _ = ENNReal.ofReal (128 * (4 * Delta) ^ 2) *
        ∫⁻ ha, confidenceActiveSelectedENN hkn B i t ha
          ∂((confidenceReferenceProcess P hkn).law t ⊗ₘ P.kernel t) := by
      rw [lintegral_const_mul _
        (measurable_confidenceActiveSelectedENN hkn B i t)]

/-! ## Accumulating the active-selection probabilities -/

/-- The observable reference round has exactly the policy's action
marginal; the lossless feedback encoding leaves its first coordinate fixed. -/
theorem confidenceReferenceRoundKernel_fst
    {n k : Nat} (P : Policy n k) (hkn : k ≤ n) (t : Nat) :
    Kernel.fst (confidenceReferenceRoundKernel P hkn t) = P.kernel t := by
  letI : IsMarkovKernel
      (confidenceReferenceFeedbackKernel :
        Kernel (History n k t × MSetAction n k) Real) :=
    confidenceReferenceFeedbackKernel_isMarkov
  unfold confidenceReferenceRoundKernel
  rw [Kernel.fst_eq, ← Kernel.map_comp_right _
    (confidenceFeedbackEquiv hkn).measurable measurable_fst]
  change Kernel.map (confidenceReferenceLatentRoundKernel P t) Prod.fst =
    P.kernel t
  rw [← Kernel.fst_eq]
  unfold confidenceReferenceLatentRoundKernel
  exact Kernel.fst_compProd _ _

/-- Projecting a reference history after one more round onto the old
history and new action gives the genuine prefix-law--policy composition. -/
theorem confidenceReference_law_succ_map_historyAction
    {n k : Nat} (P : Policy n k) (hkn : k ≤ n) (t : Nat) :
    ((confidenceReferenceProcess P hkn).law (t + 1)).map
        (fun h : History n k (t + 1) => (h.1, h.2.1)) =
      (confidenceReferenceProcess P hkn).law t ⊗ₘ P.kernel t := by
  letI : IsMarkovKernel (confidenceReferenceRoundKernel P hkn t) :=
    confidenceReferenceRoundKernel_isMarkov P hkn t
  rw [HistoryKernelProcess.law_succ]
  change
    (((confidenceReferenceProcess P hkn).law t ⊗ₘ
      confidenceReferenceRoundKernel P hkn t).map
        (Prod.map id Prod.fst)) = _
  rw [← Measure.compProd_map measurable_fst]
  rw [← Kernel.fst_eq, confidenceReferenceRoundKernel_fst]

theorem ofReal_activeSelected_increment_eq_indicator
    {n k : Nat} (hkn : k ≤ n) (B : Real) (i : Fin n) (t : Nat)
    (ha : History n k t × MSetAction n k) :
    ENNReal.ofReal
        (activeIndicator hkn B t ha.1 * History.selectedIndicator i ha.2) =
      confidenceActiveSelectedENN hkn B i t ha := by
  classical
  by_cases hactive : cumulativePenalty hkn t ha.1 < B <;>
    by_cases hi : i ∈ ha.2.1 <;>
      simp [confidenceActiveSelectedENN, confidenceActiveSelectedSet,
        activeIndicator, History.selectedIndicator, hactive, hi]

theorem ofReal_activeSelectedCount_succ
    {n k : Nat} (hkn : k ≤ n) (B : Real) (i : Fin n) (t : Nat)
    (h : History n k (t + 1)) :
    ENNReal.ofReal (activeSelectedCount hkn B i (t + 1) h) =
      ENNReal.ofReal (activeSelectedCount hkn B i t h.1) +
        confidenceActiveSelectedENN hkn B i t (h.1, h.2.1) := by
  rw [activeSelectedCount_succ]
  rw [ENNReal.ofReal_add
    (activeSelectedCount_nonneg hkn B i t h.1)
    (mul_nonneg (activeIndicator_mem_Icc hkn B t h.1).1
      (History.selectedIndicator_mem_Icc i h.2.1).1)]
  congr 1
  exact ofReal_activeSelected_increment_eq_indicator
    hkn B i t (h.1, h.2.1)

/-- One-step recursion: the increment in expected `W_i` is exactly the
active-selection probability under the actual prefix and policy law. -/
theorem lintegral_activeSelectedCount_succ
    {n k : Nat} (P : Policy n k) (hkn : k ≤ n)
    (B : Real) (i : Fin n) (t : Nat) :
    (∫⁻ h, ENNReal.ofReal (activeSelectedCount hkn B i (t + 1) h)
      ∂(confidenceReferenceProcess P hkn).law (t + 1)) =
      (∫⁻ h, ENNReal.ofReal (activeSelectedCount hkn B i t h)
        ∂(confidenceReferenceProcess P hkn).law t) +
      ∫⁻ ha, confidenceActiveSelectedENN hkn B i t ha
        ∂((confidenceReferenceProcess P hkn).law t ⊗ₘ P.kernel t) := by
  let F : History n k t × MSetAction n k → ℝ≥0∞ := fun ha =>
    ENNReal.ofReal (activeSelectedCount hkn B i t ha.1) +
      confidenceActiveSelectedENN hkn B i t ha
  have hF : Measurable F :=
    ((ENNReal.measurable_ofReal.comp
      (measurable_activeSelectedCount hkn B i t)).comp measurable_fst).add
      (measurable_confidenceActiveSelectedENN hkn B i t)
  have hproj : Measurable
      (fun h : History n k (t + 1) => (h.1, h.2.1)) := by fun_prop
  calc
    (∫⁻ h, ENNReal.ofReal (activeSelectedCount hkn B i (t + 1) h)
      ∂(confidenceReferenceProcess P hkn).law (t + 1)) =
        ∫⁻ h, F (h.1, h.2.1)
          ∂(confidenceReferenceProcess P hkn).law (t + 1) := by
      apply lintegral_congr
      intro h
      exact ofReal_activeSelectedCount_succ hkn B i t h
    _ = ∫⁻ ha, F ha ∂(((confidenceReferenceProcess P hkn).law (t + 1)).map
        (fun h : History n k (t + 1) => (h.1, h.2.1))) := by
      symm
      exact MeasureTheory.lintegral_map hF hproj
    _ = ∫⁻ ha, F ha
        ∂((confidenceReferenceProcess P hkn).law t ⊗ₘ P.kernel t) := by
      rw [confidenceReference_law_succ_map_historyAction]
    _ = (∫⁻ ha, ENNReal.ofReal (activeSelectedCount hkn B i t ha.1)
          ∂((confidenceReferenceProcess P hkn).law t ⊗ₘ P.kernel t)) +
        ∫⁻ ha, confidenceActiveSelectedENN hkn B i t ha
          ∂((confidenceReferenceProcess P hkn).law t ⊗ₘ P.kernel t) := by
      exact lintegral_add_left
        ((ENNReal.measurable_ofReal.comp
          (measurable_activeSelectedCount hkn B i t)).comp measurable_fst) _
    _ = (∫⁻ h, ENNReal.ofReal (activeSelectedCount hkn B i t h)
          ∂(confidenceReferenceProcess P hkn).law t) +
        ∫⁻ ha, confidenceActiveSelectedENN hkn B i t ha
          ∂((confidenceReferenceProcess P hkn).law t ⊗ₘ P.kernel t) := by
      congr 1
      calc
        (∫⁻ ha, ENNReal.ofReal (activeSelectedCount hkn B i t ha.1)
            ∂((confidenceReferenceProcess P hkn).law t ⊗ₘ P.kernel t)) =
          ∫⁻ h, ∫⁻ _A, ENNReal.ofReal (activeSelectedCount hkn B i t h)
            ∂P.kernel t h ∂(confidenceReferenceProcess P hkn).law t := by
          simpa only [Function.comp_apply] using
            (Measure.lintegral_compProd
              ((ENNReal.measurable_ofReal.comp
                (measurable_activeSelectedCount hkn B i t)).comp
                  measurable_fst) :
              (∫⁻ ha, ENNReal.ofReal (activeSelectedCount hkn B i t ha.1)
                ∂((confidenceReferenceProcess P hkn).law t ⊗ₘ P.kernel t)) = _)
        _ = ∫⁻ h, ENNReal.ofReal (activeSelectedCount hkn B i t h)
              ∂(confidenceReferenceProcess P hkn).law t := by simp

/-- The sum of the adaptive one-round indicator probabilities is exactly
the ENNReal expectation of the pathwise stopped count `W_i`. -/
theorem lintegral_activeSelectedCount_eq_sum
    {n k : Nat} (P : Policy n k) (hkn : k ≤ n)
    (B : Real) (i : Fin n) : ∀ T : Nat,
    (∫⁻ h, ENNReal.ofReal (activeSelectedCount hkn B i T h)
      ∂(confidenceReferenceProcess P hkn).law T) =
      ∑ t ∈ Finset.range T,
        ∫⁻ ha, confidenceActiveSelectedENN hkn B i t ha
          ∂((confidenceReferenceProcess P hkn).law t ⊗ₘ P.kernel t) := by
  intro T
  induction T with
  | zero => simp [HistoryKernelProcess.law]
  | succ T ih =>
      rw [lintegral_activeSelectedCount_succ P hkn B i T, ih,
        Finset.sum_range_succ]

theorem lintegral_activeSelectedCount_eq_ofReal_integral
    {n k T : Nat} (P : Policy n k) (hkn : k ≤ n)
    (B : Real) (i : Fin n) :
    (∫⁻ h, ENNReal.ofReal (activeSelectedCount hkn B i T h)
      ∂(confidenceReferenceProcess P hkn).law T) =
      ENNReal.ofReal
        (∫ h, activeSelectedCount hkn B i T h
          ∂(confidenceReferenceProcess P hkn).law T) := by
  symm
  exact ofReal_integral_eq_lintegral_ofReal
    (integrable_activeSelectedCount
      ((confidenceReferenceProcess P hkn).law T) hkn B i)
    (ae_of_all _ fun h => activeSelectedCount_nonneg hkn B i T h)

/-- Sequential confidence KL in exactly the manuscript's `W_i` currency. -/
theorem confidenceReference_klDiv_le_expectedActiveSelected
    {n k T : Nat} (P : Policy n k) (hkn : k ≤ n) {Delta : Real}
    (hfeedback : |4 * Delta| ≤ 1 / 16) (B : Real) (i : Fin n) :
    klDiv
        ((confidenceReferenceProcess P hkn).law T)
        ((confidencePlantedProcess P hkn Delta hfeedback B i).law T) ≤
      ENNReal.ofReal (128 * (4 * Delta) ^ 2) *
        ENNReal.ofReal
          (∫ h, activeSelectedCount hkn B i T h
            ∂(confidenceReferenceProcess P hkn).law T) := by
  rw [(confidenceReferenceProcess P hkn).klDiv_law_eq_sum_roundKL
    (confidencePlantedProcess P hkn Delta hfeedback B i) T]
  calc
    (∑ t ∈ Finset.range T,
      (confidenceReferenceProcess P hkn).roundKL
        (confidencePlantedProcess P hkn Delta hfeedback B i) t) ≤
      ∑ t ∈ Finset.range T,
        ENNReal.ofReal (128 * (4 * Delta) ^ 2) *
          ∫⁻ ha, confidenceActiveSelectedENN hkn B i t ha
            ∂((confidenceReferenceProcess P hkn).law t ⊗ₘ P.kernel t) := by
      exact Finset.sum_le_sum fun t _ =>
        confidenceReference_roundKL_le_activeSelected
          P hkn hfeedback B i t
    _ = ENNReal.ofReal (128 * (4 * Delta) ^ 2) *
        ∑ t ∈ Finset.range T,
          ∫⁻ ha, confidenceActiveSelectedENN hkn B i t ha
            ∂((confidenceReferenceProcess P hkn).law t ⊗ₘ P.kernel t) := by
      rw [Finset.mul_sum]
    _ = ENNReal.ofReal (128 * (4 * Delta) ^ 2) *
        (∫⁻ h, ENNReal.ofReal (activeSelectedCount hkn B i T h)
          ∂(confidenceReferenceProcess P hkn).law T) := by
      rw [lintegral_activeSelectedCount_eq_sum P hkn B i T]
    _ = ENNReal.ofReal (128 * (4 * Delta) ^ 2) *
        ENNReal.ofReal
          (∫ h, activeSelectedCount hkn B i T h
            ∂(confidenceReferenceProcess P hkn).law T) := by
      rw [lintegral_activeSelectedCount_eq_ofReal_integral]

/-- `eq:lower-confidence-kl`: the full adaptive KL bound, including the
selection estimate and the paper's exact numerical constants. -/
theorem lower_confidence_kl
    {n k T : Nat} (P : Policy n k) (hkn : k ≤ n) {Delta : Real}
    (hfeedback : |4 * Delta| ≤ 1 / 16) (B : Real) (i : Fin n)
    {N L : Real} (hN : 0 < N) (hL : 0 ≤ L) (hT : 0 < (T : Real))
    (hDelta : Delta = confidenceDelta N L T)
    (hB : B = Delta * T / 16)
    (hPulls :
      (∫ h, activeSelectedCount hkn B i T h
        ∂(confidenceReferenceProcess P hkn).law T) ≤
        (16 / N) * ((T : Real) + 8 * (k : Real) * B + (k : Real)))
    (hkDelta : (k : Real) * Delta / 2 ≤ 1 / (2 : Real) ^ 14)
    (hkT : (k : Real) / T ≤ 1 / 8) :
    klDiv
        ((confidenceReferenceProcess P hkn).law T)
        ((confidencePlantedProcess P hkn Delta hfeedback B i).law T) ≤
      ENNReal.ofReal ((1 / (2 : Real) ^ 8) * L) := by
  let expectedPulls : Real :=
    ∫ h, activeSelectedCount hkn B i T h
      ∂(confidenceReferenceProcess P hkn).law T
  have harith :
      128 * (4 * Delta) ^ 2 * expectedPulls ≤
        (1 / (2 : Real) ^ 8) * L :=
    lower_confidence_kl_arithmetic hN hL hT hDelta hB hPulls hkDelta hkT
  calc
    klDiv
        ((confidenceReferenceProcess P hkn).law T)
        ((confidencePlantedProcess P hkn Delta hfeedback B i).law T) ≤
      ENNReal.ofReal (128 * (4 * Delta) ^ 2) *
        ENNReal.ofReal expectedPulls :=
      confidenceReference_klDiv_le_expectedActiveSelected
        P hkn hfeedback B i
    _ = ENNReal.ofReal (128 * (4 * Delta) ^ 2 * expectedPulls) := by
      exact (ENNReal.ofReal_mul
        (p := 128 * (4 * Delta) ^ 2) (q := expectedPulls)
        (by positivity)).symm
    _ ≤ ENNReal.ofReal ((1 / (2 : Real) ^ 8) * L) :=
      ENNReal.ofReal_le_ofReal harith

end

end MsetsLower.Lower.Confidence

#print axioms MsetsLower.Lower.Confidence.confidenceFeedbackEquiv
#print axioms MsetsLower.Lower.Confidence.confidenceReferenceProcess
#print axioms MsetsLower.Lower.Confidence.confidencePlantedProcess
#print axioms MsetsLower.Lower.Confidence.confidenceScalarFeedback_zero_eq_reference_actionLoss
#print axioms MsetsLower.Lower.Confidence.confidenceScalarFeedback_planted_of_mem
#print axioms MsetsLower.Lower.Confidence.confidenceScalarFeedback_planted_of_notMem
#print axioms MsetsLower.Lower.Confidence.confidenceTwoStage_eq_withDensity
#print axioms MsetsLower.Lower.Confidence.confidenceReference_roundKL_eq_lintegral
#print axioms MsetsLower.Lower.Confidence.confidenceReference_klDiv_le_expectedActiveSelected
#print axioms MsetsLower.Lower.Confidence.lower_confidence_kl
