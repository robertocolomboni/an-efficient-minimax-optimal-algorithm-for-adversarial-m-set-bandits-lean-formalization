import MsetsLower.Lower.Confidence.Adaptive
import MsetsLower.Lower.RegretMeasurability
import Mathlib.Data.Fintype.Order

/-!
# Regret score in the confidence construction

The planted candidate's core comparator turns the pathwise regret into the
score `C_T + Δ Σ g(Z_t) A_t 1{i∉X_t}` from
`eq:lower-confidence-score`.
-/

namespace MsetsLower.Lower.Confidence

open MsetsLower

noncomputable section

/-- Indicator that candidate `i` is missed by an action. -/
def missedIndicator {n k : Nat} (i : Fin n) (A : MSetAction n k) : Real :=
  if i ∉ A.1 then 1 else 0

theorem missedIndicator_mem_Icc
    {n k : Nat} (i : Fin n) (A : MSetAction n k) :
    missedIndicator i A ∈ Set.Icc (0 : Real) 1 := by
  by_cases hi : i ∈ A.1 <;> simp [missedIndicator, hi]

/-- Exact one-round loss difference against `C∪{i}`. -/
theorem planted_played_sub_coreComparator
    {n k : Nat} (hk : 1 ≤ k) (hkn : k ≤ n)
    (i : Fin n) (hi : i ∈ confidenceCandidates n k hkn)
    (z Delta active : Real) (A : MSetAction n k) :
    actionLoss A (plantedItemLoss hkn z Delta active i) -
        actionLoss (coreComparator hk hkn i hi)
          (plantedItemLoss hkn z Delta active i) =
      candidatePenalty hkn A +
        Delta * Feedback.shape z * active * missedIndicator i A := by
  rw [actionLoss_plantedItemLoss hk hkn,
    actionLoss_plantedItemLoss hk hkn,
    candidateCount_coreComparator]
  have hk0 : (k : Real) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt hk)
  by_cases hiA : i ∈ A.1
  · simp [hiA, missedIndicator, candidatePenalty]
    field_simp
  · simp [hiA, missedIndicator, candidatePenalty]
    field_simp
    ring

/-- Recursive form of the paper's score `𝓡_i`. -/
def confidenceScore
    {n k : Nat} (hkn : k ≤ n) (noise : Nat → Real)
    (Delta B : Real) (i : Fin n) :
    (t : Nat) → History n k t → Real
  | 0, _ => 0
  | t + 1, h =>
      confidenceScore hkn noise Delta B i t h.1 + candidatePenalty hkn h.2.1 +
        Delta * Feedback.shape (noise t) * activeIndicator hkn B t h.1 *
          missedIndicator i h.2.1

@[simp] theorem confidenceScore_zero
    {n k : Nat} (hkn : k ≤ n) (noise : Nat → Real)
    (Delta B : Real) (i : Fin n) (h : History n k 0) :
    confidenceScore hkn noise Delta B i 0 h = 0 := rfl

@[simp] theorem confidenceScore_succ
    {n k t : Nat} (hkn : k ≤ n) (noise : Nat → Real)
    (Delta B : Real) (i : Fin n) (h : History n k (t + 1)) :
    confidenceScore hkn noise Delta B i (t + 1) h =
      confidenceScore hkn noise Delta B i t h.1 + candidatePenalty hkn h.2.1 +
        Delta * Feedback.shape (noise t) * activeIndicator hkn B t h.1 *
          missedIndicator i h.2.1 := rfl

/-- Regret against any fixed comparator is bounded by external regret. -/
theorem comparatorRegret_le_pathRegret
    {n k : Nat} (L : LossProcess n k)
    (t : Nat) (h : History n k t) (A : MSetAction n k) :
    realizedCumulativeLoss L t h - comparatorCumulativeLoss L t h A ≤
      pathRegret L t h := by
  have hbelow : BddBelow (Set.range (comparatorCumulativeLoss L t h)) :=
    Finite.bddBelow_range _
  have hbest : bestComparatorCumulativeLoss L t h ≤
      comparatorCumulativeLoss L t h A := by
    exact csInf_le hbelow ⟨A, rfl⟩
  unfold pathRegret
  linarith

/-- The comparator regret is exactly the recursively accumulated confidence
score. -/
theorem comparatorRegret_eq_confidenceScore
    {n k : Nat} (hk : 1 ≤ k) (hkn : k ≤ n)
    (noise : Nat → Real) (hnoise : ∀ t, noise t ∈ Set.Icc (-1 : Real) 1)
    (Delta : Real) (hDelta : 0 ≤ Delta)
    (hsmall : (k : Real) * Delta ≤ 1 / (2 : Real) ^ 13)
    (B : Real) (i : Fin n) (hi : i ∈ confidenceCandidates n k hkn) :
    ∀ (t : Nat) (h : History n k t),
      realizedCumulativeLoss
          (plantedLossProcess hk hkn noise hnoise Delta hDelta hsmall B i) t h -
        comparatorCumulativeLoss
          (plantedLossProcess hk hkn noise hnoise Delta hDelta hsmall B i) t h
          (coreComparator hk hkn i hi) =
        confidenceScore hkn noise Delta B i t h := by
  intro t
  induction t with
  | zero => intro h; simp [realizedCumulativeLoss, comparatorCumulativeLoss,
      confidenceScore]
  | succ t ih =>
      rintro ⟨hprev, ⟨A, y⟩⟩
      change
        (realizedCumulativeLoss
            (plantedLossProcess hk hkn noise hnoise Delta hDelta hsmall B i) t hprev +
          actionLoss A
            (plantedItemLoss hkn (noise t) Delta
              (activeIndicator hkn B t hprev) i)) -
        (comparatorCumulativeLoss
            (plantedLossProcess hk hkn noise hnoise Delta hDelta hsmall B i) t hprev
              (coreComparator hk hkn i hi) +
          actionLoss (coreComparator hk hkn i hi)
            (plantedItemLoss hkn (noise t) Delta
              (activeIndicator hkn B t hprev) i)) = _
      rw [confidenceScore_succ]
      calc
        _ =
            (realizedCumulativeLoss
                (plantedLossProcess hk hkn noise hnoise Delta hDelta hsmall B i) t hprev -
              comparatorCumulativeLoss
                (plantedLossProcess hk hkn noise hnoise Delta hDelta hsmall B i) t hprev
                  (coreComparator hk hkn i hi)) +
              (actionLoss A
                  (plantedItemLoss hkn (noise t) Delta
                    (activeIndicator hkn B t hprev) i) -
                actionLoss (coreComparator hk hkn i hi)
                  (plantedItemLoss hkn (noise t) Delta
                    (activeIndicator hkn B t hprev) i)) := by ring
        _ = confidenceScore hkn noise Delta B i t hprev +
              (candidatePenalty hkn A +
                Delta * Feedback.shape (noise t) * activeIndicator hkn B t hprev *
                  missedIndicator i A) := by
            rw [ih hprev, planted_played_sub_coreComparator hk hkn i hi]
        _ = confidenceScore hkn noise Delta B i t hprev + candidatePenalty hkn A +
              Delta * Feedback.shape (noise t) * activeIndicator hkn B t hprev *
                missedIndicator i A := by ring

/-- Equation `eq:lower-confidence-score`: pathwise external regret dominates
the manuscript score. -/
theorem lower_confidence_score
    {n k : Nat} (hk : 1 ≤ k) (hkn : k ≤ n)
    (noise : Nat → Real) (hnoise : ∀ t, noise t ∈ Set.Icc (-1 : Real) 1)
    (Delta : Real) (hDelta : 0 ≤ Delta)
    (hsmall : (k : Real) * Delta ≤ 1 / (2 : Real) ^ 13)
    (B : Real) (i : Fin n) (hi : i ∈ confidenceCandidates n k hkn)
    (t : Nat) (h : History n k t) :
    confidenceScore hkn noise Delta B i t h ≤
      pathRegret
        (plantedLossProcess hk hkn noise hnoise Delta hDelta hsmall B i) t h := by
  rw [← comparatorRegret_eq_confidenceScore hk hkn noise hnoise Delta hDelta
    hsmall B i hi t h]
  exact comparatorRegret_le_pathRegret _ t h (coreComparator hk hkn i hi)

end

end MsetsLower.Lower.Confidence
