import MsetsPaper.Lower.SparseCappedScores

/-! # Capped selection counts on the actual observable histories

This transports the independently proved SparseCounting lemmas to histories,
then bounds the actual learner score by c times the number of active bits.
-/

namespace MsetsPaper.Lower.SparseCapped

open MsetsLower MsetsLower.History MsetsLower.Feedback
open scoped BigOperators

noncomputable section

def historyNatCount {d m : ℕ} (i : Fin d) : (t : ℕ) → History d m t → ℕ
  | 0, _ => 0
  | t + 1, h => historyNatCount i t h.1 + if i ∈ h.2.1.val then 1 else 0

theorem cast_historyNatCount {d m : ℕ} (i : Fin d) :
    ∀ t (h : History d m t), (historyNatCount i t h : ℝ) = selectedCount i t h := by
  intro t
  induction t with
  | zero => intro h; simp [historyNatCount, selectedCount, actionSum]
  | succ t ih =>
    intro h
    change ((historyNatCount i t h.1 + if i ∈ h.2.1.val then 1 else 0 : ℕ) : ℝ) =
      selectedCount i t h.1 + selectedIndicator i h.2.1
    rw [Nat.cast_add, ih]
    by_cases hi : i ∈ h.2.1.val <;> simp [hi, selectedIndicator]

/-- Any continuation after the recorded history is immaterial to its counts. -/
def historyActions {d m : ℕ} (a0 : MSetAction d m) :
    (t : ℕ) → History d m t → ℕ → MSetAction d m
  | 0, _, _ => a0
  | t + 1, h, r => if r = t then h.2.1 else historyActions a0 t h.1 r

theorem selectionCount_historyActions_prefix {d m : ℕ} (a0 : MSetAction d m)
    (i : Fin d) (t : ℕ) (h : History d m (t + 1)) {n : ℕ} (hn : n ≤ t) :
    Sparse.selectionCount (historyActions a0 (t + 1) h) i n =
      Sparse.selectionCount (historyActions a0 t h.1) i n := by
  unfold Sparse.selectionCount
  apply Finset.sum_congr rfl
  intro r hr
  have hrt : r ≠ t := Nat.ne_of_lt ((Finset.mem_range.mp hr).trans_le hn)
  simp only [historyActions, hrt, ite_false]

theorem selectionCount_historyActions {d m : ℕ} (a0 : MSetAction d m) (i : Fin d) :
    ∀ t (h : History d m t),
      Sparse.selectionCount (historyActions a0 t h) i t = historyNatCount i t h := by
  intro t
  induction t with
  | zero => intro h; simp [historyNatCount]
  | succ t ih =>
    intro h
    rw [Sparse.selectionCount_succ, selectionCount_historyActions_prefix a0 i t h le_rfl, ih]
    simp [historyNatCount, historyActions]

def cappedCount {d m : ℕ} (c : ℕ) (i : Fin d) : (t : ℕ) → History d m t → ℕ
  | 0, _ => 0
  | t + 1, h => cappedCount c i t h.1 +
      if i ∈ h.2.1.val ∧ historyNatCount i t h.1 < c then 1 else 0

theorem activeSelectionCount_historyActions {d m : ℕ} (a0 : MSetAction d m)
    (c : ℕ) (i : Fin d) : ∀ t (h : History d m t),
      Sparse.activeSelectionCount (historyActions a0 t h) c i t = cappedCount c i t h := by
  intro t
  induction t with
  | zero => intro h; simp [cappedCount]
  | succ t ih =>
    intro h
    have hp : Sparse.activeSelectionCount (historyActions a0 (t + 1) h) c i t =
        Sparse.activeSelectionCount (historyActions a0 t h.1) c i t := by
      unfold Sparse.activeSelectionCount
      apply Finset.sum_congr rfl
      intro r hr
      have hrt := Finset.mem_range.mp hr
      rw [selectionCount_historyActions_prefix a0 i t h hrt.le]
      simp only [historyActions, Nat.ne_of_lt hrt, ite_false]
    rw [Sparse.activeSelectionCount_succ, hp, ih,
      selectionCount_historyActions_prefix a0 i t h le_rfl, selectionCount_historyActions]
    simp [cappedCount, historyActions]

/-- Reuse of SparseCounting's exact min identity, not a new capped-count assumption. -/
theorem cappedCount_eq_min {d m : ℕ} (hmd : m ≤ d) (c : ℕ) (i : Fin d)
    (t : ℕ) (h : History d m t) : cappedCount c i t h = min c (historyNatCount i t h) := by
  let a0 := Classical.choice (nonempty_MSetAction hmd)
  rw [← activeSelectionCount_historyActions a0 c i, Sparse.activeSelectionCount_eq_min,
    selectionCount_historyActions]

theorem cappedCount_le_cap {d m : ℕ} (hmd : m ≤ d) (c : ℕ) (i : Fin d)
    (t : ℕ) (h : History d m t) : cappedCount c i t h ≤ c := by
  rw [cappedCount_eq_min hmd]
  exact min_le_left _ _

theorem cast_cappedCount_succ {d m : ℕ} (c : ℕ) (i : Fin d)
    (t : ℕ) (h : History d m (t + 1)) :
    (cappedCount c i (t + 1) h : ℝ) = (cappedCount c i t h.1 : ℝ) +
      activeIndicator c t h.1 i * selectedIndicator i h.2.1 := by
  rw [cappedCount, Nat.cast_add]
  unfold activeIndicator
  rw [← cast_historyNatCount]
  simp only [Nat.cast_lt]
  by_cases hi : i ∈ h.2.1.val <;> by_cases hc : historyNatCount i t h.1 < c <;>
    simp [hi, hc, selectedIndicator]

theorem actionLoss_activeVector_eq_sum {d m : ℕ} (c : ℕ) (U : Bits d)
    (t : ℕ) (h : History d m t) (a : MSetAction d m) :
    actionLoss a (activeVector c U t h) =
      ∑ i : Fin d, bitValue (U i) * (activeIndicator c t h i * selectedIndicator i a) := by
  unfold actionLoss
  apply Finset.sum_congr rfl
  intro i _
  by_cases hi : i ∈ a.val <;> simp [hi, activeVector, selectedIndicator, mul_comm]

theorem learnerScore_le_weighted_cappedCount {d m T : ℕ} (c : ℕ) (xi : Table d T) :
    ∀ t (h : History d m t), learnerScore c xi t h ≤
      ∑ i : Fin d, bitValue (xi.1 i) * (cappedCount c i t h : ℝ) := by
  intro t
  induction t with
  | zero => intro h; simp [learnerScore, cappedCount]
  | succ t ih =>
    intro h
    have ha : 0 ≤ actionLoss h.2.1 (activeVector c xi.1 t h.1) := by
      rw [actionLoss_eq_finset_sum]
      exact Finset.sum_nonneg fun i _ => (activeVector_mem_Icc c xi.1 t h.1 i).1
    rw [learnerScore]
    calc
      _ ≤ (∑ i : Fin d, bitValue (xi.1 i) * (cappedCount c i t h.1 : ℝ)) +
          actionLoss h.2.1 (activeVector c xi.1 t h.1) :=
        add_le_add (ih h.1) (by simpa using
          mul_le_mul_of_nonneg_right (shape_mem_Icc (tableNoise_mem_Icc xi t)).2 ha)
      _ = _ := by
        simp only [cast_cappedCount_succ, mul_add, Finset.sum_add_distrib,
          actionLoss_activeVector_eq_sum]

/-- The exact deterministic learner-score bound in the manuscript. -/
theorem learnerScore_le_cap_mul_bits {d m T : ℕ} (hmd : m ≤ d)
    (c : ℕ) (xi : Table d T) (t : ℕ) (h : History d m t) :
    learnerScore c xi t h ≤ (c : ℝ) * ∑ i : Fin d, bitValue (xi.1 i) := by
  calc
    _ ≤ ∑ i : Fin d, bitValue (xi.1 i) * (cappedCount c i t h : ℝ) :=
      learnerScore_le_weighted_cappedCount c xi t h
    _ ≤ ∑ i : Fin d, bitValue (xi.1 i) * (c : ℝ) := by
      apply Finset.sum_le_sum
      intro i _
      exact mul_le_mul_of_nonneg_left (by exact_mod_cast cappedCount_le_cap hmd c i t h)
        (bitValue_mem_Icc (xi.1 i)).1
    _ = _ := by rw [← Finset.sum_mul]; ring

def historyActiveItems {d m : ℕ} (c t : ℕ) (h : History d m t) : Finset (Fin d) :=
  Finset.univ.filter (fun i => historyNatCount i t h < c)

theorem activeItems_historyActions {d m : ℕ} (a0 : MSetAction d m)
    (c t : ℕ) (h : History d m t) :
    Sparse.activeItems (historyActions a0 t h) c t = historyActiveItems c t h := by
  ext i
  simp [Sparse.activeItems, historyActiveItems, selectionCount_historyActions]

theorem historyActiveItems_card_ge {d m : ℕ} (hmd : m ≤ d)
    {c t : ℕ} (hc : 0 < c) (hbudget : 8 * t * m ≤ c * d) (h : History d m t) :
    (7 : ℝ) / 8 * d ≤ ((historyActiveItems c t h).card : ℝ) := by
  let a0 := Classical.choice (nonempty_MSetAction hmd)
  rw [← activeItems_historyActions a0]
  exact Sparse.active_card_ge_seven_eighths (historyActions a0 t h) hc hbudget

/-- The cap is budgeted for t+1 rounds although this count is before the last draw. -/
theorem historyActiveItems_card_before_final {d m : ℕ} (hmd : m ≤ d)
    {c t : ℕ} (hc : 0 < c) (hbudget : 8 * (t + 1) * m ≤ c * d)
    (h : History d m (t + 1)) :
    (7 : ℝ) / 8 * d ≤ ((historyActiveItems c t h.1).card : ℝ) := by
  apply historyActiveItems_card_ge hmd hc _ h.1
  exact (Nat.mul_le_mul_right m (Nat.mul_le_mul_left 8 (Nat.le_succ t))).trans hbudget

end

end MsetsPaper.Lower.SparseCapped
