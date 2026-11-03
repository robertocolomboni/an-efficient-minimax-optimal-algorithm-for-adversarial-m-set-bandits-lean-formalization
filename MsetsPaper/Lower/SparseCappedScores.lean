import MsetsPaper.Lower.SparseCappedConstruction
import Mathlib.Order.ConditionallyCompleteLattice.Finset

/-! # Exact scores and regret cancellation for the new sparse adversary -/

namespace MsetsPaper.Lower.SparseCapped

open MsetsLower MsetsLower.History MsetsLower.Feedback MsetsLower.Lower
open MeasureTheory Set
open scoped BigOperators

noncomputable section

def commonLossSum {d T : ℕ} (xi : Table d T) (t : ℕ) : ℝ :=
  ∑ r ∈ Finset.range t, (1 + tableNoise xi r) / 2

def shapeSum {d T : ℕ} (xi : Table d T) (t : ℕ) : ℝ :=
  ∑ r ∈ Finset.range t, shape (tableNoise xi r)

/-- Coordinate score S_i, accumulating only while this coordinate is active. -/
def itemScore {d m T : ℕ} (c : ℕ) (xi : Table d T) :
    (t : ℕ) → History d m t → Fin d → ℝ
  | 0, _, _ => 0
  | t + 1, h, i => itemScore c xi t h.1 i +
      shape (tableNoise xi t) * activeVector c xi.1 t h.1 i

def learnerScore {d m T : ℕ} (c : ℕ) (xi : Table d T) :
    (t : ℕ) → History d m t → ℝ
  | 0, _ => 0
  | t + 1, h => learnerScore c xi t h.1 +
      shape (tableNoise xi t) * actionLoss h.2.1 (activeVector c xi.1 t h.1)

/-- The sum of the m largest coordinates, expressed without selecting an
arbitrary ordering or assuming a measurable maximizing action. -/
def topScore {d : ℕ} (m : ℕ) (S : Fin d → ℝ) : ℝ :=
  sSup (Set.range (fun a : MSetAction d m => actionLoss a S))

def deficit {d m T : ℕ} (c : ℕ) (xi : Table d T) (t : ℕ) (h : History d m t) : ℝ :=
  topScore m (itemScore c xi t h) - learnerScore c xi t h

theorem actionLoss_le_topScore {d m : ℕ} (S : Fin d → ℝ) (a : MSetAction d m) :
    actionLoss a S ≤ topScore m S :=
  le_csSup (Set.finite_range _).bddAbove ⟨a, rfl⟩

theorem topScore_attained {d m : ℕ} (hmd : m ≤ d) (S : Fin d → ℝ) :
    ∃ a : MSetAction d m, actionLoss a S = topScore m S := by
  letI := nonempty_MSetAction hmd
  exact (Set.range_nonempty _).csSup_mem (Set.finite_range _)

theorem topScore_le {d m : ℕ} (hmd : m ≤ d) (S : Fin d → ℝ) {b : ℝ}
    (hb : ∀ a : MSetAction d m, actionLoss a S ≤ b) : topScore m S ≤ b := by
  obtain ⟨a, ha⟩ := topScore_attained hmd S
  rw [← ha]
  exact hb a

theorem shapeSum_mem_Icc {d T : ℕ} (xi : Table d T) (t : ℕ) :
    shapeSum xi t ∈ Icc (0 : ℝ) t := by
  constructor
  · exact Finset.sum_nonneg fun r _ => (shape_mem_Icc (tableNoise_mem_Icc xi r)).1
  · calc
      shapeSum xi t ≤ ∑ _r ∈ Finset.range t, (1 : ℝ) :=
        Finset.sum_le_sum fun r _ => (shape_mem_Icc (tableNoise_mem_Icc xi r)).2
      _ = (t : ℝ) := by simp

theorem itemScore_mem_Icc {d m T : ℕ} (c : ℕ) (xi : Table d T) :
    ∀ t (h : History d m t) i, itemScore c xi t h i ∈ Icc (0 : ℝ) (shapeSum xi t) := by
  intro t
  induction t with
  | zero => intro h i; simp [itemScore, shapeSum]
  | succ t ih =>
    intro h i
    have hg := shape_mem_Icc (tableNoise_mem_Icc xi t)
    have ha := activeVector_mem_Icc c xi.1 t h.1 i
    have hp := ih h.1 i
    rw [itemScore]
    constructor
    · exact add_nonneg hp.1 (mul_nonneg hg.1 ha.1)
    · rw [shapeSum, Finset.sum_range_succ]
      exact add_le_add hp.2 (by simpa using mul_le_mul_of_nonneg_left ha.2 hg.1)

theorem learnerScore_nonneg {d m T : ℕ} (c : ℕ) (xi : Table d T) :
    ∀ t (h : History d m t), 0 ≤ learnerScore c xi t h := by
  intro t
  induction t with
  | zero => intro h; rfl
  | succ t ih =>
    intro h
    rw [learnerScore]
    apply add_nonneg (ih h.1)
    apply mul_nonneg (shape_mem_Icc (tableNoise_mem_Icc xi t)).1
    rw [actionLoss_eq_finset_sum]
    exact Finset.sum_nonneg fun i _ => (activeVector_mem_Icc c xi.1 t h.1 i).1

theorem topScore_mem_Icc {d m T : ℕ} (hmd : m ≤ d) (c : ℕ) (xi : Table d T)
    (t : ℕ) (h : History d m t) :
    topScore m (itemScore c xi t h) ∈ Icc (0 : ℝ) ((m : ℝ) * shapeSum xi t) := by
  obtain ⟨a, ha⟩ := topScore_attained hmd (itemScore c xi t h)
  rw [← ha, actionLoss_eq_finset_sum]
  constructor
  · exact Finset.sum_nonneg fun i _ => (itemScore_mem_Icc c xi t h i).1
  · calc
      _ ≤ ∑ _i ∈ a.val, shapeSum xi t :=
        Finset.sum_le_sum fun i _ => (itemScore_mem_Icc c xi t h i).2
      _ = (m : ℝ) * shapeSum xi t := by simp [a.property]

theorem deficit_le {d m T : ℕ} (hmd : m ≤ d) (c : ℕ) (xi : Table d T)
    (t : ℕ) (h : History d m t) : deficit c xi t h ≤ (m : ℝ) * t := by
  have htop := (topScore_mem_Icc hmd c xi t h).2
  have hshape := mul_le_mul_of_nonneg_left (shapeSum_mem_Icc xi t).2 (Nat.cast_nonneg m)
  have hlearner := learnerScore_nonneg c xi t h
  unfold deficit
  linarith

theorem actionLoss_eq_common_sub_score {d m : ℕ} (hm : 0 < m) (c : ℕ)
    (eta z : ℝ) (U : Bits d) (t : ℕ) (h : History d m t) (a : MSetAction d m) :
    actionLoss a (itemLoss c eta z U t h) =
      (1 + z) / 2 - eta / m * (shape z * actionLoss a (activeVector c U t h)) := by
  rw [actionLoss_feedback_identity hm]
  unfold feedbackMap feedbackParameter DenseCommonNoise.feedbackParameter
  ring

theorem actionLoss_itemScore_succ {d m T : ℕ} (c : ℕ) (xi : Table d T)
    (t : ℕ) (h : History d m (t + 1)) (a : MSetAction d m) :
    actionLoss a (itemScore c xi (t + 1) h) =
      actionLoss a (itemScore c xi t h.1) +
        shape (tableNoise xi t) * actionLoss a (activeVector c xi.1 t h.1) := by
  simp only [actionLoss_eq_finset_sum, itemScore, Finset.sum_add_distrib, Finset.mul_sum]

theorem realizedCumulativeLoss_eq_common_sub_score {d m : ℕ} (hm : 0 < m)
    (c : ℕ) (eta : ℝ) (heta : 0 ≤ eta) (hs : eta ≤ 1 / 16)
    (T : ℕ) (xi : Table d T) : ∀ t (h : History d m t),
    realizedCumulativeLoss ((tableLossProcess hm c eta heta hs T).at xi) t h =
      commonLossSum xi t - eta / m * learnerScore c xi t h := by
  intro t
  induction t with
  | zero => intro h; simp [realizedCumulativeLoss, commonLossSum, learnerScore]
  | succ t ih =>
    intro h
    rw [realizedCumulativeLoss, ih]
    change commonLossSum xi t - eta / m * learnerScore c xi t h.1 +
      actionLoss h.2.1 (itemLoss c eta (tableNoise xi t) xi.1 t h.1) = _
    rw [actionLoss_eq_common_sub_score hm]
    simp only [commonLossSum, Finset.sum_range_succ, learnerScore]
    ring

theorem comparatorCumulativeLoss_eq_common_sub_score {d m : ℕ} (hm : 0 < m)
    (c : ℕ) (eta : ℝ) (heta : 0 ≤ eta) (hs : eta ≤ 1 / 16)
    (T : ℕ) (xi : Table d T) (a : MSetAction d m) : ∀ t (h : History d m t),
    comparatorCumulativeLoss ((tableLossProcess hm c eta heta hs T).at xi) t h a =
      commonLossSum xi t - eta / m * actionLoss a (itemScore c xi t h) := by
  intro t
  induction t with
  | zero => intro h; simp [comparatorCumulativeLoss, commonLossSum, itemScore]
  | succ t ih =>
    intro h
    rw [comparatorCumulativeLoss, ih]
    change commonLossSum xi t - eta / m * actionLoss a (itemScore c xi t h.1) +
      actionLoss a (itemLoss c eta (tableNoise xi t) xi.1 t h.1) = _
    rw [actionLoss_eq_common_sub_score hm, actionLoss_itemScore_succ]
    simp only [commonLossSum, Finset.sum_range_succ]
    ring

theorem bestComparatorCumulativeLoss_eq_common_sub_top {d m : ℕ}
    (hm : 0 < m) (hmd : m ≤ d) (c : ℕ) (eta : ℝ)
    (heta : 0 ≤ eta) (hs : eta ≤ 1 / 16) (T : ℕ) (xi : Table d T)
    (t : ℕ) (h : History d m t) :
    bestComparatorCumulativeLoss ((tableLossProcess hm c eta heta hs T).at xi) t h =
      commonLossSum xi t - eta / m * topScore m (itemScore c xi t h) := by
  letI := nonempty_MSetAction hmd
  have hk : 0 ≤ eta / (m : ℝ) := div_nonneg heta (Nat.cast_nonneg m)
  obtain ⟨a, ha⟩ := topScore_attained hmd (itemScore c xi t h)
  apply le_antisymm
  · have hb := csInf_le (Set.finite_range
        (comparatorCumulativeLoss ((tableLossProcess hm c eta heta hs T).at xi) t h)).bddBelow
        (Set.mem_range_self a)
    rw [comparatorCumulativeLoss_eq_common_sub_score, ha] at hb
    exact hb
  · apply le_csInf (Set.range_nonempty _)
    rintro y ⟨b, rfl⟩
    rw [comparatorCumulativeLoss_eq_common_sub_score]
    exact sub_le_sub_left (mul_le_mul_of_nonneg_left
      (actionLoss_le_topScore (itemScore c xi t h) b) hk) _

/-- Exact equality with the original protocol regret, not a one-sided surrogate. -/
theorem pathRegret_eq_scaled_deficit {d m : ℕ} (hm : 0 < m) (hmd : m ≤ d)
    (c : ℕ) (eta : ℝ) (heta : 0 ≤ eta) (hs : eta ≤ 1 / 16)
    (T : ℕ) (xi : Table d T) (t : ℕ) (h : History d m t) :
    pathRegret ((tableLossProcess hm c eta heta hs T).at xi) t h =
      eta / m * deficit c xi t h := by
  rw [pathRegret, realizedCumulativeLoss_eq_common_sub_score,
    bestComparatorCumulativeLoss_eq_common_sub_top hm hmd]
  unfold deficit
  ring

/-- If an item is still active after a prefix, it was active at every earlier
round in that prefix. Consequently its score is its bit times all the noise. -/
theorem itemScore_eq_full_of_still_active {d m T : ℕ} (c : ℕ) (xi : Table d T)
    (i : Fin d) : ∀ t (h : History d m t), selectedCount i t h < (c : ℝ) →
      itemScore c xi t h i = bitValue (xi.1 i) * shapeSum xi t := by
  intro t
  induction t with
  | zero => intro h _; simp [itemScore, shapeSum]
  | succ t ih =>
    intro h hc
    have hp : selectedCount i t h.1 < (c : ℝ) := by
      change selectedCount i t h.1 + selectedIndicator i h.2.1 < (c : ℝ) at hc
      linarith [(selectedIndicator_mem_Icc i h.2.1).1]
    rw [itemScore, ih h.1 hp]
    simp only [activeVector, activeIndicator, hp, ite_true, one_mul,
      shapeSum, Finset.sum_range_succ]
    ring

/-- The paper uses activity just BEFORE the final round, not after it. -/
theorem itemScore_eq_shapeSum_of_final_active_bit {d m T : ℕ}
    (c : ℕ) (xi : Table d T) (t : ℕ) (h : History d m (t + 1)) (i : Fin d)
    (ha : selectedCount i t h.1 < (c : ℝ)) (hu : xi.1 i = true) :
    itemScore c xi (t + 1) h i = shapeSum xi (t + 1) := by
  rw [itemScore, itemScore_eq_full_of_still_active c xi i t h.1 ha]
  simp [activeVector, activeIndicator, ha, hu, bitValue, shapeSum, Finset.sum_range_succ]

def favorableActiveItems {d m T : ℕ} (c : ℕ) (xi : Table d T) (t : ℕ)
    (h : History d m t) : Finset (Fin d) :=
  Finset.univ.filter (fun i => xi.1 i = true ∧ selectedCount i t h < (c : ℝ))

/-- On the survival event at least m coordinates attain the common maximum;
this proves the equality of Top_m, not just a comparator lower estimate. -/
theorem topScore_eq_full_of_many_final_active {d m T : ℕ}
    (hmd : m ≤ d) (c : ℕ) (xi : Table d T) (t : ℕ) (h : History d m (t + 1))
    (hcount : m ≤ (favorableActiveItems c xi t h.1).card) :
    topScore m (itemScore c xi (t + 1) h) = (m : ℝ) * shapeSum xi (t + 1) := by
  obtain ⟨s, hs, hcard⟩ := Finset.exists_subset_card_eq hcount
  let a : MSetAction d m := ⟨s, hcard⟩
  have ha : actionLoss a (itemScore c xi (t + 1) h) =
      (m : ℝ) * shapeSum xi (t + 1) := by
    rw [actionLoss_eq_finset_sum]
    calc
      _ = ∑ _i ∈ a.val, shapeSum xi (t + 1) := by
        apply Finset.sum_congr rfl
        intro i hi
        have hgood : xi.1 i = true ∧ selectedCount i t h.1 < (c : ℝ) :=
          (Finset.mem_filter.mp (hs hi)).2
        exact itemScore_eq_shapeSum_of_final_active_bit c xi t h i hgood.2 hgood.1
      _ = _ := by simp [a.property]
  exact le_antisymm (topScore_mem_Icc hmd c xi (t + 1) h).2
    (ha ▸ actionLoss_le_topScore (itemScore c xi (t + 1) h) a)

end

end MsetsPaper.Lower.SparseCapped
