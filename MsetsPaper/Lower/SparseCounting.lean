import MsetsLower.Core.Protocol

/-!
# Deterministic capped-selection counts for the new sparse construction

Rounds are indexed from zero: `selectionCount A i t` counts selections in
rounds `0,...,t-1`. Thus activity at round `t` depends only on preceding
actions. The paper's `A_{T,i}` corresponds to activity here at `T-1`.

Every theorem holds for an arbitrary sequence of exact-`m` actions. There are
no probabilistic premises, policy assumptions, or unproved lower-tail bounds.
-/

namespace MsetsPaper.Lower.Sparse

open MsetsLower
open scoped BigOperators

/-- Number of times coordinate `i` has been selected before round `t`. -/
def selectionCount {d m : ℕ} (A : ℕ → MSetAction d m) (i : Fin d) (t : ℕ) : ℕ :=
  ∑ r ∈ Finset.range t, if i ∈ (A r).val then 1 else 0

/-- Number of selections of `i` made while its preceding count is below `c`. -/
def activeSelectionCount {d m : ℕ} (A : ℕ → MSetAction d m)
    (c : ℕ) (i : Fin d) (T : ℕ) : ℕ :=
  ∑ t ∈ Finset.range T,
    if i ∈ (A t).val ∧ selectionCount A i t < c then 1 else 0

/-- Active coordinates before round `t`. -/
def activeItems {d m : ℕ} (A : ℕ → MSetAction d m) (c t : ℕ) : Finset (Fin d) :=
  Finset.univ.filter fun i => selectionCount A i t < c

/-- Inactive coordinates before round `t`. -/
def inactiveItems {d m : ℕ} (A : ℕ → MSetAction d m) (c t : ℕ) : Finset (Fin d) :=
  Finset.univ.filter fun i => c ≤ selectionCount A i t

@[simp] theorem selectionCount_zero {d m : ℕ} (A : ℕ → MSetAction d m)
    (i : Fin d) : selectionCount A i 0 = 0 := by
  simp [selectionCount]

theorem selectionCount_succ {d m : ℕ} (A : ℕ → MSetAction d m)
    (i : Fin d) (t : ℕ) :
    selectionCount A i (t + 1) =
      selectionCount A i t + if i ∈ (A t).val then 1 else 0 := by
  simp only [selectionCount, Finset.sum_range_succ]

@[simp] theorem activeSelectionCount_zero {d m : ℕ} (A : ℕ → MSetAction d m)
    (c : ℕ) (i : Fin d) : activeSelectionCount A c i 0 = 0 := by
  simp [activeSelectionCount]

theorem activeSelectionCount_succ {d m : ℕ} (A : ℕ → MSetAction d m)
    (c : ℕ) (i : Fin d) (t : ℕ) :
    activeSelectionCount A c i (t + 1) = activeSelectionCount A c i t +
      if i ∈ (A t).val ∧ selectionCount A i t < c then 1 else 0 := by
  simp only [activeSelectionCount, Finset.sum_range_succ]

/-- Each selected action contributes exactly `m` coordinate selections. -/
theorem selections_per_round {d m : ℕ} (a : MSetAction d m) :
    (∑ i : Fin d, if i ∈ a.val then (1 : ℕ) else 0) = m := by
  simp

/-- The total number of coordinate selections in the first `T` rounds. -/
theorem sum_selectionCount {d m : ℕ} (A : ℕ → MSetAction d m) (T : ℕ) :
    (∑ i : Fin d, selectionCount A i T) = m * T := by
  induction T with
  | zero => simp
  | succ T ih =>
      simp only [selectionCount_succ, Finset.sum_add_distrib, ih, selections_per_round]
      ring

/-- A coordinate is selected actively exactly until its count reaches `c`.
This also covers the degenerate cap `c=0`. -/
theorem activeSelectionCount_eq_min {d m : ℕ} (A : ℕ → MSetAction d m)
    (c : ℕ) (i : Fin d) (T : ℕ) :
    activeSelectionCount A c i T = min c (selectionCount A i T) := by
  induction T with
  | zero => simp
  | succ T ih =>
      rw [activeSelectionCount_succ, selectionCount_succ, ih]
      by_cases hmem : i ∈ (A T).val
      · simp only [hmem, true_and, if_true]
        by_cases hlt : selectionCount A i T < c
        · rw [if_pos hlt, min_eq_right (by omega), min_eq_right (by omega)]
        · rw [if_neg hlt, min_eq_left (by omega), min_eq_left (by omega)]
          omega
      · simp [hmem]

/-- The capped activity bound used in the learner-score estimate. -/
theorem activeSelectionCount_le_cap {d m : ℕ} (A : ℕ → MSetAction d m)
    (c : ℕ) (i : Fin d) (T : ℕ) : activeSelectionCount A c i T ≤ c := by
  rw [activeSelectionCount_eq_min]
  exact min_le_left _ _

theorem selectionCount_mono {d m : ℕ} (A : ℕ → MSetAction d m)
    (i : Fin d) {s t : ℕ} (hst : s ≤ t) :
    selectionCount A i s ≤ selectionCount A i t := by
  unfold selectionCount
  apply Finset.sum_le_sum_of_subset_of_nonneg (Finset.range_mono hst)
  intro r _ _
  exact Nat.zero_le _

/-- A coordinate active at a later round was active at every earlier round. -/
theorem active_at_earlier_round {d m : ℕ} (A : ℕ → MSetAction d m)
    (c : ℕ) (i : Fin d) {s t : ℕ} (hst : s ≤ t)
    (ht : selectionCount A i t < c) : selectionCount A i s < c :=
  (selectionCount_mono A i hst).trans_lt ht

@[simp] theorem mem_activeItems {d m : ℕ} (A : ℕ → MSetAction d m)
    (c t : ℕ) (i : Fin d) :
    i ∈ activeItems A c t ↔ selectionCount A i t < c := by
  simp [activeItems]

@[simp] theorem mem_inactiveItems {d m : ℕ} (A : ℕ → MSetAction d m)
    (c t : ℕ) (i : Fin d) :
    i ∈ inactiveItems A c t ↔ c ≤ selectionCount A i t := by
  simp [inactiveItems]

/-- The active and inactive coordinates partition the dimension. -/
theorem active_card_add_inactive_card {d m : ℕ} (A : ℕ → MSetAction d m)
    (c T : ℕ) : (activeItems A c T).card + (inactiveItems A c T).card = d := by
  have h := Finset.card_filter_add_card_filter_not
    (s := Finset.univ) (p := fun i : Fin d => selectionCount A i T < c)
  simpa [activeItems, inactiveItems, not_lt] using h

/-- Every inactive coordinate accounts for at least `c` previous selections. -/
theorem cap_mul_inactive_card_le {d m : ℕ} (A : ℕ → MSetAction d m)
    (c T : ℕ) : c * (inactiveItems A c T).card ≤ m * T := by
  calc
    c * (inactiveItems A c T).card = ∑ i ∈ inactiveItems A c T, c := by
      simp [Nat.mul_comm]
    _ ≤ ∑ i ∈ inactiveItems A c T, selectionCount A i T := by
      apply Finset.sum_le_sum
      intro i hi
      exact (mem_inactiveItems A c T i).1 hi
    _ ≤ ∑ i : Fin d, selectionCount A i T := by
      apply Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _)
      intro i _ _
      exact Nat.zero_le _
    _ = m * T := sum_selectionCount A T

/-- If the cap budget dominates eight times the number of selections, at most
one eighth of the coordinates are inactive. -/
theorem eight_mul_inactive_card_le_dimension {d m : ℕ} (A : ℕ → MSetAction d m)
    {c T : ℕ} (hc : 0 < c) (hbudget : 8 * T * m ≤ c * d) :
    8 * (inactiveItems A c T).card ≤ d := by
  apply Nat.le_of_mul_le_mul_left (c := c) _ hc
  calc
    c * (8 * (inactiveItems A c T).card) =
        8 * (c * (inactiveItems A c T).card) := by ring
    _ ≤ 8 * (m * T) := Nat.mul_le_mul_left 8 (cap_mul_inactive_card_le A c T)
    _ ≤ c * d := by simpa [Nat.mul_comm, Nat.mul_left_comm, Nat.mul_assoc] using hbudget

/-- The integer, division-free form of at least `7d/8` active coordinates. -/
theorem seven_dimension_le_eight_active_card {d m : ℕ} (A : ℕ → MSetAction d m)
    {c T : ℕ} (hc : 0 < c) (hbudget : 8 * T * m ≤ c * d) :
    7 * d ≤ 8 * (activeItems A c T).card := by
  have hpartition := active_card_add_inactive_card A c T
  have hinactive := eight_mul_inactive_card_le_dimension A hc hbudget
  omega

/-- The displayed real-number form of the active-count bound. -/
theorem active_card_ge_seven_eighths {d m : ℕ} (A : ℕ → MSetAction d m)
    {c T : ℕ} (hc : 0 < c) (hbudget : 8 * T * m ≤ c * d) :
    (7 : ℝ) / 8 * d ≤ ((activeItems A c T).card : ℝ) := by
  have h := seven_dimension_le_eight_active_card A hc hbudget
  have hreal : (7 : ℝ) * d ≤ 8 * ((activeItems A c T).card : ℝ) := by
    exact_mod_cast h
  linarith

/-- Literal before-the-final-round form used in the manuscript. The cap is
chosen using `T`, while only `T-1` actions precede the final round. -/
theorem active_card_before_final_round {d m : ℕ} (A : ℕ → MSetAction d m)
    {c T : ℕ} (hc : 0 < c) (hbudget : 8 * T * m ≤ c * d) :
    (7 : ℝ) / 8 * d ≤ ((activeItems A c (T - 1)).card : ℝ) := by
  apply active_card_ge_seven_eighths A hc
  exact (Nat.mul_le_mul_right m (Nat.mul_le_mul_left 8 (Nat.sub_le T 1))).trans hbudget

end MsetsPaper.Lower.Sparse
