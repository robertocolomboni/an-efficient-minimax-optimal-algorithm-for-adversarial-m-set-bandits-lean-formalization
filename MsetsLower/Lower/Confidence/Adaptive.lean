import MsetsLower.Core.HistoryStats
import MsetsLower.Lower.Confidence.Construction

/-!
# Adaptive stopping in the confidence construction

The cumulative penalty and activity indicator are defined from the observable
action history exactly as in the manuscript.  For each fixed noise table this
produces genuine deterministic, history-measurable loss processes.
-/

namespace MsetsLower.Lower.Confidence

open MsetsLower

noncomputable section

/-- Per-round penalty `p_t=(h_t-1)/(8k)`. -/
def candidatePenalty
    {n k : Nat} (hkn : k ≤ n) (A : MSetAction n k) : Real :=
  ((candidateCount hkn A : Real) - 1) / (8 * (k : Real))

theorem candidatePenalty_mem_Ico
    {n k : Nat} (hk : 1 ≤ k) (hkn : k ≤ n) (A : MSetAction n k) :
    candidatePenalty hkn A ∈ Set.Ico (0 : Real) (1 / 8 : Real) := by
  have hkpos : (0 : Real) < k := by exact_mod_cast hk
  have hhpos : (1 : Real) ≤ candidateCount hkn A := by
    exact_mod_cast candidateCount_pos hk hkn A
  have hhle : (candidateCount hkn A : Real) ≤ k := by
    exact_mod_cast candidateCount_le hkn A
  constructor
  · exact div_nonneg (sub_nonneg.mpr hhpos) (by positivity)
  · apply (div_lt_iff₀ (mul_pos (by norm_num) hkpos)).2
    nlinarith

/-- Cumulative penalty `C_t` computed from the first `t` observed actions. -/
def cumulativePenalty
    {n k : Nat} (hkn : k ≤ n) (t : Nat) (h : History n k t) : Real :=
  History.actionSum (candidatePenalty hkn) t h

theorem cumulativePenalty_zero
    {n k : Nat} (hkn : k ≤ n) (h : History n k 0) :
    cumulativePenalty hkn 0 h = 0 := rfl

theorem cumulativePenalty_succ
    {n k t : Nat} (hkn : k ≤ n) (h : History n k (t + 1)) :
    cumulativePenalty hkn (t + 1) h =
      cumulativePenalty hkn t h.1 + candidatePenalty hkn h.2.1 := rfl

theorem measurable_cumulativePenalty
    {n k : Nat} (hkn : k ≤ n) (t : Nat) :
    Measurable (cumulativePenalty hkn t) :=
  History.measurable_actionSum_of_finite _ _

theorem cumulativePenalty_nonneg
    {n k : Nat} (hk : 1 ≤ k) (hkn : k ≤ n)
    (t : Nat) (h : History n k t) :
    0 ≤ cumulativePenalty hkn t h :=
  History.actionSum_nonneg (fun A => (candidatePenalty_mem_Ico hk hkn A).1) t h

/-- Activity indicator `A_t=1{C_{t-1}<B}` (with zero-based round index,
the length-`t` history is the past before round `t`). -/
def activeIndicator
    {n k : Nat} (hkn : k ≤ n) (B : Real) (t : Nat)
    (h : History n k t) : Real :=
  if cumulativePenalty hkn t h < B then 1 else 0

theorem measurable_activeIndicator
    {n k : Nat} (hkn : k ≤ n) (B : Real) (t : Nat) :
    Measurable (activeIndicator hkn B t) := by
  apply Measurable.ite
  · change MeasurableSet (cumulativePenalty hkn t ⁻¹' Set.Iio B)
    exact measurable_cumulativePenalty hkn t measurableSet_Iio
  · exact measurable_const
  · exact measurable_const

theorem activeIndicator_mem_Icc
    {n k : Nat} (hkn : k ≤ n) (B : Real)
    (t : Nat) (h : History n k t) :
    activeIndicator hkn B t h ∈ Set.Icc (0 : Real) 1 := by
  by_cases hactive : cumulativePenalty hkn t h < B <;>
    simp [activeIndicator, hactive]

/-- Reference environment for a fixed noise table. -/
def referenceLossProcess
    {n k : Nat} (hk : 1 ≤ k) (hkn : k ≤ n)
    (noise : Nat → Real) (hnoise : ∀ t, noise t ∈ Set.Icc (-1 : Real) 1) :
    LossProcess n k where
  itemLoss t _ := referenceItemLoss hkn (noise t)
  measurable_itemLoss _ := measurable_const
  action_nonneg t _ A := by
    have hkpos : (0 : Real) < k := by exact_mod_cast hk
    exact (by positivity : (0 : Real) ≤ 1 / 8 + 1 / (8 * (k : Real))).trans
      (actionLoss_referenceItemLoss_mem_Icc hk hkn (hnoise t) A).1
  action_le_one t _ A :=
    (actionLoss_referenceItemLoss_mem_Icc hk hkn (hnoise t) A).2.trans (by norm_num)

/-- Planted environment for a fixed noise table and candidate.  Its only
history dependence is the observable stopping indicator. -/
def plantedLossProcess
    {n k : Nat} (hk : 1 ≤ k) (hkn : k ≤ n)
    (noise : Nat → Real) (hnoise : ∀ t, noise t ∈ Set.Icc (-1 : Real) 1)
    (Delta : Real) (hDelta : 0 ≤ Delta)
    (hsmall : (k : Real) * Delta ≤ 1 / (2 : Real) ^ 13)
    (B : Real) (i : Fin n) : LossProcess n k where
  itemLoss t h :=
    plantedItemLoss hkn (noise t) Delta (activeIndicator hkn B t h) i
  measurable_itemLoss t := by
    change Measurable (fun h : History n k t => fun j : Fin n =>
      referenceItemLoss hkn (noise t) j -
        Delta * Feedback.shape (noise t) * activeIndicator hkn B t h *
          (if j = i then 1 else 0))
    refine Measurable.of_eval fun j => ?_
    exact measurable_const.sub
      ((measurable_const.mul (measurable_activeIndicator hkn B t)).mul measurable_const)
  action_nonneg t h A :=
    (actionLoss_plantedItemLoss_mem_Icc hk hkn (hnoise t) hDelta hsmall
      (activeIndicator_mem_Icc hkn B t h) i A).1
  action_le_one t h A :=
    (actionLoss_plantedItemLoss_mem_Icc hk hkn (hnoise t) hDelta hsmall
      (activeIndicator_mem_Icc hkn B t h) i A).2

/-- Fixing the auxiliary noise table leaves a deterministic non-anticipating
loss process whose action losses are normalized. -/
theorem plantedLossProcess_is_adaptive_adversary
    {n k : Nat} (hk : 1 ≤ k) (hkn : k ≤ n)
    (noise : Nat → Real) (hnoise : ∀ t, noise t ∈ Set.Icc (-1 : Real) 1)
    (Delta : Real) (hDelta : 0 ≤ Delta)
    (hsmall : (k : Real) * Delta ≤ 1 / (2 : Real) ^ 13)
    (B : Real) (i : Fin n) :
    (∀ t, Measurable ((plantedLossProcess hk hkn noise hnoise Delta hDelta
      hsmall B i).itemLoss t)) ∧
    (∀ t h (A : MSetAction n k),
      actionLoss A ((plantedLossProcess hk hkn noise hnoise Delta hDelta
        hsmall B i).itemLoss t h) ∈ Set.Icc (0 : Real) 1) := by
  constructor
  · exact (plantedLossProcess hk hkn noise hnoise Delta hDelta hsmall B i).measurable_itemLoss
  · intro t h A
    exact (plantedLossProcess hk hkn noise hnoise Delta hDelta hsmall B i).action_mem_Icc t h A

end

end MsetsLower.Lower.Confidence
