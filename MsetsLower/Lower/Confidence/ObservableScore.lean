import MsetsLower.Feedback.Moments
import MsetsLower.Lower.Confidence.KLProcess

/-!
# The confidence score as an observable history statistic

The manuscript initially writes its confidence score using the latent source
variables `Z_t`.  This file gives the single statistic of the genuine
action--scalar-feedback history that is used under both `P₀` and `Pᵢ`.

On a missed round the source variable is recovered from the observed action
`A` and scalar feedback `Y` by
`8 * (Y - 1/4 - candidateCount(A)/(8*k))`.  On a selected round the score's
missed-candidate indicator is zero, so no recovery is needed there.
-/

namespace MsetsLower.Lower.Confidence

open MsetsLower Feedback
open MeasureTheory ProbabilityTheory Set
open scoped BigOperators ENNReal NNReal ProbabilityTheory

noncomputable section

/-- Recover the manuscript's source noise from one genuine observable
action--scalar-feedback pair.  It is total; its source-noise interpretation
is used only on the rounds on which the feedback parameter is zero. -/
def recoveredConfidenceNoise {n k : Nat} (hkn : k ≤ n)
    (A : MSetAction n k) (Y : Real) : Real :=
  8 * (Y - confidenceFeedbackBase hkn A)

theorem recoveredConfidenceNoise_eq_manuscript {n k : Nat} (hkn : k ≤ n)
    (A : MSetAction n k) (Y : Real) :
    recoveredConfidenceNoise hkn A Y =
      8 * (Y - (1 / 4 : Real) - (candidateCount hkn A : Real) / (8 * k)) := by
  unfold recoveredConfidenceNoise confidenceFeedbackBase
  ring

theorem measurable_recoveredConfidenceNoise {n k : Nat} (hkn : k ≤ n) :
    Measurable
      (fun AY : MSetAction n k × Real =>
        recoveredConfidenceNoise hkn AY.1 AY.2) := by
  unfold recoveredConfidenceNoise
  exact measurable_const.mul <|
    measurable_snd.sub <|
      (measurable_confidenceFeedbackBase hkn).comp measurable_fst

@[simp] theorem recoveredConfidenceNoise_confidenceScalarFeedback
    {n k : Nat} (hkn : k ≤ n) (A : MSetAction n k) (y : Real) :
    recoveredConfidenceNoise hkn A (confidenceScalarFeedback hkn A y) = 2 * y := by
  unfold recoveredConfidenceNoise confidenceScalarFeedback
  ring

@[simp] theorem recoveredConfidenceNoise_referenceEncoding
    {n k : Nat} (hkn : k ≤ n) (A : MSetAction n k) (z : Real) :
    recoveredConfidenceNoise hkn A
        (confidenceScalarFeedback hkn A (feedbackMap 0 z)) = z := by
  rw [recoveredConfidenceNoise_confidenceScalarFeedback]
  unfold feedbackMap
  ring

theorem recoveredConfidenceNoise_referenceActionLoss
    {n k : Nat} (hk : 1 ≤ k) (hkn : k ≤ n)
    (A : MSetAction n k) (z : Real) :
    recoveredConfidenceNoise hkn A
        (actionLoss A (referenceItemLoss hkn z)) = z := by
  rw [← confidenceScalarFeedback_zero_eq_reference_actionLoss hk hkn]
  exact recoveredConfidenceNoise_referenceEncoding hkn A z

theorem recoveredConfidenceNoise_plantedActionLoss_of_notMem
    {n k : Nat} (hk : 1 ≤ k) (hkn : k ≤ n)
    (Delta B : Real) (i : Fin n) (t : Nat)
    (h : History n k t) (A : MSetAction n k) (z : Real)
    (hnot : (h, A) ∉ confidenceActiveSelectedSet hkn B i t) :
    recoveredConfidenceNoise hkn A
        (actionLoss A
          (plantedItemLoss hkn z Delta (activeIndicator hkn B t h) i)) = z := by
  rw [← confidenceScalarFeedback_planted_of_notMem
    hk hkn Delta B i t h A z hnot]
  exact recoveredConfidenceNoise_referenceEncoding hkn A z

/-- The sum of `g` applied to the noises literally recovered from the
observed scalar feedback. -/
def observableNoiseShapeSum {n k : Nat} (hkn : k ≤ n) :
    (t : Nat) → History n k t → Real
  | 0, _ => 0
  | t + 1, h =>
      observableNoiseShapeSum hkn t h.1 +
        shape (recoveredConfidenceNoise hkn h.2.1 h.2.2)

@[simp] theorem observableNoiseShapeSum_zero
    {n k : Nat} (hkn : k ≤ n) (h : History n k 0) :
    observableNoiseShapeSum hkn 0 h = 0 := rfl

@[simp] theorem observableNoiseShapeSum_succ
    {n k t : Nat} (hkn : k ≤ n) (h : History n k (t + 1)) :
    observableNoiseShapeSum hkn (t + 1) h =
      observableNoiseShapeSum hkn t h.1 +
        shape (recoveredConfidenceNoise hkn h.2.1 h.2.2) := rfl

theorem measurable_observableNoiseShapeSum {n k : Nat} (hkn : k ≤ n) :
    ∀ t, Measurable (observableNoiseShapeSum hkn t) := by
  intro t
  induction t with
  | zero => exact measurable_const
  | succ t ih =>
      exact (ih.comp measurable_fst).add <|
        measurable_shape.comp <|
          (measurable_recoveredConfidenceNoise hkn).comp measurable_snd

/-- The common observable version of the manuscript score `𝓡_i`. -/
def observableConfidenceScore {n k : Nat} (hkn : k ≤ n)
    (Delta B : Real) (i : Fin n) :
    (t : Nat) → History n k t → Real
  | 0, _ => 0
  | t + 1, h =>
      observableConfidenceScore hkn Delta B i t h.1 +
        candidatePenalty hkn h.2.1 +
        Delta * shape (recoveredConfidenceNoise hkn h.2.1 h.2.2) *
          activeIndicator hkn B t h.1 * missedIndicator i h.2.1

@[simp] theorem observableConfidenceScore_zero
    {n k : Nat} (hkn : k ≤ n) (Delta B : Real) (i : Fin n)
    (h : History n k 0) :
    observableConfidenceScore hkn Delta B i 0 h = 0 := rfl

@[simp] theorem observableConfidenceScore_succ
    {n k t : Nat} (hkn : k ≤ n) (Delta B : Real) (i : Fin n)
    (h : History n k (t + 1)) :
    observableConfidenceScore hkn Delta B i (t + 1) h =
      observableConfidenceScore hkn Delta B i t h.1 +
        candidatePenalty hkn h.2.1 +
        Delta * shape (recoveredConfidenceNoise hkn h.2.1 h.2.2) *
          activeIndicator hkn B t h.1 * missedIndicator i h.2.1 := rfl

theorem measurable_observableConfidenceScore {n k : Nat} (hkn : k ≤ n)
    (Delta B : Real) (i : Fin n) :
    ∀ t, Measurable (observableConfidenceScore hkn Delta B i t) := by
  intro t
  induction t with
  | zero => exact measurable_const
  | succ t ih =>
      have haction : Measurable
          (fun h : History n k (t + 1) => h.2.1) :=
        measurable_fst.comp measurable_snd
      have hshape : Measurable
          (fun h : History n k (t + 1) =>
            shape (recoveredConfidenceNoise hkn h.2.1 h.2.2)) :=
        measurable_shape.comp <|
          (measurable_recoveredConfidenceNoise hkn).comp measurable_snd
      have hactive : Measurable
          (fun h : History n k (t + 1) => activeIndicator hkn B t h.1) :=
        (measurable_activeIndicator hkn B t).comp measurable_fst
      exact ((ih.comp measurable_fst).add <|
        (measurable_of_finite (candidatePenalty hkn)).comp haction).add <|
          (((measurable_const.mul hshape).mul hactive).mul <|
            (measurable_of_finite (missedIndicator i)).comp haction)

/-- The candidate event is now one literal measurable event under both
history laws. -/
def observableConfidenceScoreEvent {n k T : Nat} (hkn : k ≤ n)
    (Delta B : Real) (i : Fin n) : Set (History n k T) :=
  {h | Delta * T / 8 ≤ observableConfidenceScore hkn Delta B i T h}

theorem measurableSet_observableConfidenceScoreEvent
    {n k T : Nat} (hkn : k ≤ n) (Delta B : Real) (i : Fin n) :
    MeasurableSet (observableConfidenceScoreEvent (T := T) hkn Delta B i) :=
  measurableSet_le measurable_const
    (measurable_observableConfidenceScore hkn Delta B i T)

/-- Even under the planted feedback, the recovered-shape term agrees with
the manuscript term after multiplication by the missed-candidate indicator.
If `i` is selected both sides vanish; otherwise the feedback parameter is
zero and `Z` is recovered exactly. -/
theorem recoveredShape_mul_missed_plantedActionLoss
    {n k : Nat} (hk : 1 ≤ k) (hkn : k ≤ n)
    (Delta B : Real) (i : Fin n) (t : Nat)
    (h : History n k t) (A : MSetAction n k) (z : Real) :
    shape (recoveredConfidenceNoise hkn A
        (actionLoss A
          (plantedItemLoss hkn z Delta (activeIndicator hkn B t h) i))) *
        missedIndicator i A =
      shape z * missedIndicator i A := by
  classical
  by_cases hi : i ∈ A.1
  · simp [missedIndicator, hi]
  · have hnot : (h, A) ∉ confidenceActiveSelectedSet hkn B i t := by
      intro hmem
      exact hi hmem.2
    rw [recoveredConfidenceNoise_plantedActionLoss_of_notMem
      hk hkn Delta B i t h A z hnot]

theorem observableConfidenceIncrement_referenceActionLoss
    {n k : Nat} (hk : 1 ≤ k) (hkn : k ≤ n)
    (Delta B : Real) (i : Fin n) (t : Nat)
    (h : History n k t) (A : MSetAction n k) (z : Real) :
    candidatePenalty hkn A +
        Delta * shape (recoveredConfidenceNoise hkn A
          (actionLoss A (referenceItemLoss hkn z))) *
          activeIndicator hkn B t h * missedIndicator i A =
      candidatePenalty hkn A +
        Delta * shape z * activeIndicator hkn B t h * missedIndicator i A := by
  rw [recoveredConfidenceNoise_referenceActionLoss hk hkn]

theorem observableConfidenceIncrement_plantedActionLoss
    {n k : Nat} (hk : 1 ≤ k) (hkn : k ≤ n)
    (Delta B : Real) (i : Fin n) (t : Nat)
    (h : History n k t) (A : MSetAction n k) (z : Real) :
    candidatePenalty hkn A +
        Delta * shape (recoveredConfidenceNoise hkn A
          (actionLoss A
            (plantedItemLoss hkn z Delta (activeIndicator hkn B t h) i))) *
          activeIndicator hkn B t h * missedIndicator i A =
      candidatePenalty hkn A +
        Delta * shape z * activeIndicator hkn B t h * missedIndicator i A := by
  have heq := recoveredShape_mul_missed_plantedActionLoss
    hk hkn Delta B i t h A z
  calc
    _ = candidatePenalty hkn A + Delta * activeIndicator hkn B t h *
          (shape (recoveredConfidenceNoise hkn A
            (actionLoss A
              (plantedItemLoss hkn z Delta (activeIndicator hkn B t h) i))) *
            missedIndicator i A) := by ring
    _ = candidatePenalty hkn A + Delta * activeIndicator hkn B t h *
          (shape z * missedIndicator i A) := by rw [heq]
    _ = _ := by ring

/-! ## Exact pathwise coupling with the manuscript recursions -/

def ReferenceHistoryCompatible {n k : Nat} (hkn : k ≤ n)
    (noise : Nat → Real) : (t : Nat) → History n k t → Prop
  | 0, _ => True
  | t + 1, h =>
      ReferenceHistoryCompatible hkn noise t h.1 ∧
        h.2.2 = actionLoss h.2.1 (referenceItemLoss hkn (noise t))

def PlantedHistoryCompatible {n k : Nat} (hkn : k ≤ n)
    (noise : Nat → Real) (Delta B : Real) (i : Fin n) :
    (t : Nat) → History n k t → Prop
  | 0, _ => True
  | t + 1, h =>
      PlantedHistoryCompatible hkn noise Delta B i t h.1 ∧
        h.2.2 = actionLoss h.2.1
          (plantedItemLoss hkn (noise t) Delta
            (activeIndicator hkn B t h.1) i)

theorem observableNoiseShapeSum_eq_noiseShapeSum_of_referenceCompatible
    {n k : Nat} (hk : 1 ≤ k) (hkn : k ≤ n) (noise : Nat → Real) :
    ∀ (t : Nat) (h : History n k t),
      ReferenceHistoryCompatible hkn noise t h →
      observableNoiseShapeSum hkn t h = noiseShapeSum noise t h := by
  intro t
  induction t with
  | zero => intro h _; rfl
  | succ t ih =>
      intro h hcompat
      rw [observableNoiseShapeSum_succ, noiseShapeSum_succ,
        ih h.1 hcompat.1, hcompat.2,
        recoveredConfidenceNoise_referenceActionLoss hk hkn]

theorem observableConfidenceScore_eq_confidenceScore_of_referenceCompatible
    {n k : Nat} (hk : 1 ≤ k) (hkn : k ≤ n) (noise : Nat → Real)
    (Delta B : Real) (i : Fin n) :
    ∀ (t : Nat) (h : History n k t),
      ReferenceHistoryCompatible hkn noise t h →
      observableConfidenceScore hkn Delta B i t h =
        confidenceScore hkn noise Delta B i t h := by
  intro t
  induction t with
  | zero => intro h _; rfl
  | succ t ih =>
      intro h hcompat
      rw [observableConfidenceScore_succ, confidenceScore_succ,
        ih h.1 hcompat.1, hcompat.2,
        recoveredConfidenceNoise_referenceActionLoss hk hkn]

theorem observableConfidenceScore_eq_confidenceScore_of_plantedCompatible
    {n k : Nat} (hk : 1 ≤ k) (hkn : k ≤ n) (noise : Nat → Real)
    (Delta B : Real) (i : Fin n) :
    ∀ (t : Nat) (h : History n k t),
      PlantedHistoryCompatible hkn noise Delta B i t h →
      observableConfidenceScore hkn Delta B i t h =
        confidenceScore hkn noise Delta B i t h := by
  intro t
  induction t with
  | zero => intro h _; rfl
  | succ t ih =>
      intro h hcompat
      rw [observableConfidenceScore_succ, confidenceScore_succ,
        ih h.1 hcompat.1, hcompat.2]
      have heq := recoveredShape_mul_missed_plantedActionLoss
        hk hkn Delta B i t h.1 h.2.1 (noise t)
      calc
        _ = confidenceScore hkn noise Delta B i t h.1 +
              candidatePenalty hkn h.2.1 +
              Delta * activeIndicator hkn B t h.1 *
                (shape (recoveredConfidenceNoise hkn h.2.1
                  (actionLoss h.2.1
                    (plantedItemLoss hkn (noise t) Delta
                      (activeIndicator hkn B t h.1) i))) *
                  missedIndicator i h.2.1) := by ring
        _ = confidenceScore hkn noise Delta B i t h.1 +
              candidatePenalty hkn h.2.1 +
              Delta * activeIndicator hkn B t h.1 *
                (shape (noise t) * missedIndicator i h.2.1) := by rw [heq]
        _ = _ := by ring

theorem mem_observableConfidenceScoreEvent_iff_referenceCompatible
    {n k T : Nat} (hk : 1 ≤ k) (hkn : k ≤ n) (noise : Nat → Real)
    (Delta B : Real) (i : Fin n) (h : History n k T)
    (hcompat : ReferenceHistoryCompatible hkn noise T h) :
    h ∈ observableConfidenceScoreEvent (T := T) hkn Delta B i ↔
      h ∈ confidenceScoreEvent (T := T) hkn noise Delta B i := by
  unfold observableConfidenceScoreEvent confidenceScoreEvent
  change Delta * (T : Real) / 8 ≤ observableConfidenceScore hkn Delta B i T h ↔
    Delta * (T : Real) / 8 ≤ confidenceScore hkn noise Delta B i T h
  rw [observableConfidenceScore_eq_confidenceScore_of_referenceCompatible
    hk hkn noise Delta B i T h hcompat]

theorem mem_observableConfidenceScoreEvent_iff_plantedCompatible
    {n k T : Nat} (hk : 1 ≤ k) (hkn : k ≤ n) (noise : Nat → Real)
    (Delta B : Real) (i : Fin n) (h : History n k T)
    (hcompat : PlantedHistoryCompatible hkn noise Delta B i T h) :
    h ∈ observableConfidenceScoreEvent (T := T) hkn Delta B i ↔
      h ∈ confidenceScoreEvent (T := T) hkn noise Delta B i := by
  unfold observableConfidenceScoreEvent confidenceScoreEvent
  change Delta * (T : Real) / 8 ≤ observableConfidenceScore hkn Delta B i T h ↔
    Delta * (T : Real) / 8 ≤ confidenceScore hkn noise Delta B i T h
  rw [observableConfidenceScore_eq_confidenceScore_of_plantedCompatible
    hk hkn noise Delta B i T h hcompat]

end

end MsetsLower.Lower.Confidence

#print axioms MsetsLower.Lower.Confidence.measurable_observableNoiseShapeSum
#print axioms MsetsLower.Lower.Confidence.measurable_observableConfidenceScore
#print axioms MsetsLower.Lower.Confidence.observableConfidenceScore_eq_confidenceScore_of_referenceCompatible
#print axioms MsetsLower.Lower.Confidence.observableConfidenceScore_eq_confidenceScore_of_plantedCompatible
#print axioms MsetsLower.Lower.Confidence.mem_observableConfidenceScoreEvent_iff_referenceCompatible
#print axioms MsetsLower.Lower.Confidence.mem_observableConfidenceScoreEvent_iff_plantedCompatible
