import MsetsLower.Lower.Confidence.Core
import MsetsLower.Lower.Confidence.Adaptive
import MsetsLower.Lower.Confidence.Score

/-!
# Pathwise stopping accounting for the confidence construction

This file formalizes the stopping calculation in
`eq:lower-confidence-total-pulls`.  All four accumulated quantities below are
folds over the literal nested observable history.  In particular, the
one-increment overshoot bound is proved from the stopping rule and the strict
per-round bound `p_t < 1/8`; it is not an additional assumption.
-/

namespace MsetsLower.Lower.Confidence

open MsetsLower
open scoped BigOperators

noncomputable section

/-- The manuscript quantity
`W_i = ∑_t A_t 1{i ∈ X_t}`, accumulated over a nested history. -/
def activeSelectedCount
    {n k : Nat} (hkn : k ≤ n) (B : Real) (i : Fin n) :
    (t : Nat) → History n k t → Real
  | 0, _ => 0
  | t + 1, h =>
      activeSelectedCount hkn B i t h.1 +
        activeIndicator hkn B t h.1 * History.selectedIndicator i h.2.1

@[simp] theorem activeSelectedCount_zero
    {n k : Nat} (hkn : k ≤ n) (B : Real) (i : Fin n)
    (h : History n k 0) :
    activeSelectedCount hkn B i 0 h = 0 := rfl

@[simp] theorem activeSelectedCount_succ
    {n k t : Nat} (hkn : k ≤ n) (B : Real) (i : Fin n)
    (h : History n k (t + 1)) :
    activeSelectedCount hkn B i (t + 1) h =
      activeSelectedCount hkn B i t h.1 +
        activeIndicator hkn B t h.1 * History.selectedIndicator i h.2.1 := rfl

/-- `W_i` is measurable as a statistic of the observable history. -/
theorem measurable_activeSelectedCount
    {n k : Nat} (hkn : k ≤ n) (B : Real) (i : Fin n) :
    ∀ t, Measurable (activeSelectedCount hkn B i t) := by
  intro t
  induction t with
  | zero => exact measurable_const
  | succ t ih =>
      exact (ih.comp measurable_fst).add
        (((measurable_activeIndicator hkn B t).comp measurable_fst).mul
          ((measurable_of_finite (History.selectedIndicator i)).comp
            (measurable_fst.comp measurable_snd)))

/-- Number of active rounds, `∑_t A_t`. -/
def activeRoundCount
    {n k : Nat} (hkn : k ≤ n) (B : Real) :
    (t : Nat) → History n k t → Real
  | 0, _ => 0
  | t + 1, h =>
      activeRoundCount hkn B t h.1 + activeIndicator hkn B t h.1

@[simp] theorem activeRoundCount_zero
    {n k : Nat} (hkn : k ≤ n) (B : Real) (h : History n k 0) :
    activeRoundCount hkn B 0 h = 0 := rfl

@[simp] theorem activeRoundCount_succ
    {n k t : Nat} (hkn : k ≤ n) (B : Real)
    (h : History n k (t + 1)) :
    activeRoundCount hkn B (t + 1) h =
      activeRoundCount hkn B t h.1 + activeIndicator hkn B t h.1 := rfl

/-- Stopped cumulative penalty, `∑_t A_t p_t`. -/
def activePenaltySum
    {n k : Nat} (hkn : k ≤ n) (B : Real) :
    (t : Nat) → History n k t → Real
  | 0, _ => 0
  | t + 1, h =>
      activePenaltySum hkn B t h.1 +
        activeIndicator hkn B t h.1 * candidatePenalty hkn h.2.1

@[simp] theorem activePenaltySum_zero
    {n k : Nat} (hkn : k ≤ n) (B : Real) (h : History n k 0) :
    activePenaltySum hkn B 0 h = 0 := rfl

@[simp] theorem activePenaltySum_succ
    {n k t : Nat} (hkn : k ≤ n) (B : Real)
    (h : History n k (t + 1)) :
    activePenaltySum hkn B (t + 1) h =
      activePenaltySum hkn B t h.1 +
        activeIndicator hkn B t h.1 * candidatePenalty hkn h.2.1 := rfl

/-- Total number of candidate-coordinate pulls on active rounds,
`∑_t A_t h_t`. -/
def activeCandidatePulls
    {n k : Nat} (hkn : k ≤ n) (B : Real) :
    (t : Nat) → History n k t → Real
  | 0, _ => 0
  | t + 1, h =>
      activeCandidatePulls hkn B t h.1 +
        activeIndicator hkn B t h.1 * (candidateCount hkn h.2.1 : Real)

@[simp] theorem activeCandidatePulls_zero
    {n k : Nat} (hkn : k ≤ n) (B : Real) (h : History n k 0) :
    activeCandidatePulls hkn B 0 h = 0 := rfl

@[simp] theorem activeCandidatePulls_succ
    {n k t : Nat} (hkn : k ≤ n) (B : Real)
    (h : History n k (t + 1)) :
    activeCandidatePulls hkn B (t + 1) h =
      activeCandidatePulls hkn B t h.1 +
        activeIndicator hkn B t h.1 * (candidateCount hkn h.2.1 : Real) := rfl

/-- Summing the coordinate indicators over the candidate set gives `h_t`. -/
theorem sum_selectedIndicator_confidenceCandidates
    {n k : Nat} (hkn : k ≤ n) (A : MSetAction n k) :
    ∑ i ∈ confidenceCandidates n k hkn, History.selectedIndicator i A =
      (candidateCount hkn A : Real) := by
  classical
  calc
    ∑ i ∈ confidenceCandidates n k hkn, History.selectedIndicator i A =
        (((confidenceCandidates n k hkn).filter fun i => i ∈ A.1).card : Real) := by
      rw [show ∑ i ∈ confidenceCandidates n k hkn,
          History.selectedIndicator i A =
          (∑ i ∈ confidenceCandidates n k hkn,
            if i ∈ A.1 then (1 : Real) else 0) by rfl,
        Finset.sum_boole]
    _ = (candidateCount hkn A : Real) := by
      congr 1
      simp only [candidateCount]
      congr 1
      ext i
      simp [and_comm]

/-- The first equality in `eq:lower-confidence-total-pulls`:
`∑_{i∈V} W_i = ∑_t A_t h_t`. -/
theorem sum_activeSelectedCount_eq_activeCandidatePulls
    {n k : Nat} (hkn : k ≤ n) (B : Real) :
    ∀ (t : Nat) (h : History n k t),
      ∑ i ∈ confidenceCandidates n k hkn,
          activeSelectedCount hkn B i t h =
        activeCandidatePulls hkn B t h := by
  intro t
  induction t with
  | zero => intro h; simp
  | succ t ih =>
      rintro ⟨hprev, ⟨A, y⟩⟩
      rw [activeCandidatePulls_succ]
      simp only [activeSelectedCount_succ, Finset.sum_add_distrib]
      rw [ih hprev, ← Finset.mul_sum,
        sum_selectedIndicator_confidenceCandidates hkn A]

/-- The one-round identity `h_t = 1 + 8 k p_t`. -/
theorem candidateCount_eq_one_add_eight_mul_penalty
    {n k : Nat} (hk : 1 ≤ k) (hkn : k ≤ n) (A : MSetAction n k) :
    (candidateCount hkn A : Real) =
      1 + 8 * (k : Real) * candidatePenalty hkn A := by
  have hk0 : (k : Real) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt hk)
  simp only [candidatePenalty]
  field_simp [hk0]
  ring

/-- The second equality in `eq:lower-confidence-total-pulls`:
`∑_t A_t h_t = ∑_t A_t + 8k ∑_t A_t p_t`. -/
theorem activeCandidatePulls_eq_rounds_add_penalties
    {n k : Nat} (hk : 1 ≤ k) (hkn : k ≤ n) (B : Real) :
    ∀ (t : Nat) (h : History n k t),
      activeCandidatePulls hkn B t h =
        activeRoundCount hkn B t h +
          8 * (k : Real) * activePenaltySum hkn B t h := by
  intro t
  induction t with
  | zero => intro h; simp
  | succ t ih =>
      rintro ⟨hprev, ⟨A, y⟩⟩
      rw [activeCandidatePulls_succ, activeRoundCount_succ,
        activePenaltySum_succ, ih hprev,
        candidateCount_eq_one_add_eight_mul_penalty hk hkn A]
      ring

/-- There are at most `t` active rounds. -/
theorem activeRoundCount_le_time
    {n k : Nat} (hkn : k ≤ n) (B : Real) :
    ∀ (t : Nat) (h : History n k t),
      activeRoundCount hkn B t h ≤ (t : Real) := by
  intro t
  induction t with
  | zero => intro h; simp
  | succ t ih =>
      rintro ⟨hprev, ⟨A, y⟩⟩
      rw [activeRoundCount_succ]
      have hA := (activeIndicator_mem_Icc hkn B t hprev).2
      have hprevBound := ih hprev
      push_cast
      linarith

/-- Multiplying each nonnegative penalty by an activity indicator in `[0,1]`
cannot increase its cumulative sum. -/
theorem activePenaltySum_le_cumulativePenalty
    {n k : Nat} (hk : 1 ≤ k) (hkn : k ≤ n) (B : Real) :
    ∀ (t : Nat) (h : History n k t),
      activePenaltySum hkn B t h ≤ cumulativePenalty hkn t h := by
  intro t
  induction t with
  | zero =>
      intro h
      change (0 : Real) ≤ 0
      exact le_rfl
  | succ t ih =>
      rintro ⟨hprev, ⟨A, y⟩⟩
      rw [activePenaltySum_succ, cumulativePenalty_succ]
      have hprevBound := ih hprev
      have hA := activeIndicator_mem_Icc hkn B t hprev
      have hp := (candidatePenalty_mem_Ico hk hkn A).1
      have hlast :
          activeIndicator hkn B t hprev * candidatePenalty hkn A ≤
            candidatePenalty hkn A := by
        calc
          activeIndicator hkn B t hprev * candidatePenalty hkn A
              ≤ 1 * candidatePenalty hkn A :=
            mul_le_mul_of_nonneg_right hA.2 hp
          _ = candidatePenalty hkn A := one_mul _
      linarith

/-- The stopped penalty exceeds `B` by at most one strict `< 1/8`
increment.  This is the pathwise overshoot assertion used in the manuscript. -/
theorem activePenaltySum_le_budget_add_one_eighth
    {n k : Nat} (hk : 1 ≤ k) (hkn : k ≤ n)
    {B : Real} (hB : 0 ≤ B) :
    ∀ (t : Nat) (h : History n k t),
      activePenaltySum hkn B t h ≤ B + 1 / 8 := by
  intro t
  induction t with
  | zero =>
      intro h
      change (0 : Real) ≤ B + 1 / 8
      positivity
  | succ t ih =>
      rintro ⟨hprev, ⟨A, y⟩⟩
      rw [activePenaltySum_succ]
      by_cases hactive : cumulativePenalty hkn t hprev < B
      · rw [show activeIndicator hkn B t hprev = 1 by
          simp [activeIndicator, hactive]]
        rw [one_mul]
        have hprevBound :=
          activePenaltySum_le_cumulativePenalty hk hkn B t hprev
        have hp := (candidatePenalty_mem_Ico hk hkn A).2
        linarith
      · rw [show activeIndicator hkn B t hprev = 0 by
          simp [activeIndicator, hactive]]
        rw [zero_mul, add_zero]
        exact ih hprev

/-- Equation `eq:lower-confidence-total-pulls`, with every equality and the
final pathwise bound at the manuscript's exact constants. -/
theorem lower_confidence_total_pulls
    {n k T : Nat} (hk : 1 ≤ k) (hkn : k ≤ n)
    {B : Real} (hB : 0 ≤ B) (h : History n k T) :
    ∑ i ∈ confidenceCandidates n k hkn,
        activeSelectedCount hkn B i T h ≤
      (T : Real) + 8 * (k : Real) * B + (k : Real) := by
  rw [sum_activeSelectedCount_eq_activeCandidatePulls hkn B T h,
    activeCandidatePulls_eq_rounds_add_penalties hk hkn B T h]
  calc
    activeRoundCount hkn B T h +
          8 * (k : Real) * activePenaltySum hkn B T h
        ≤ (T : Real) + 8 * (k : Real) * (B + 1 / 8) :=
      add_le_add (activeRoundCount_le_time hkn B T h)
        (mul_le_mul_of_nonneg_left
          (activePenaltySum_le_budget_add_one_eighth hk hkn hB T h)
          (by positivity))
    _ = (T : Real) + 8 * (k : Real) * B + (k : Real) := by ring

end

end MsetsLower.Lower.Confidence
