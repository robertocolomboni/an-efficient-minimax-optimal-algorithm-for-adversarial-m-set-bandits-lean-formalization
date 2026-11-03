import MsetsPaper.Lower.WJProcess
import MsetsPaper.Lower.SparseCappedComparatorMean
import MsetsPaper.Lower.Foundations

/-! # Pathwise regret in the introductory fixed-cardinality construction -/

namespace MsetsPaper.Lower.WJ

open MsetsLower MsetsLower.History MsetsLower.Feedback MsetsLower.Lower
open MeasureTheory ProbabilityTheory Set
open scoped BigOperators ENNReal ProbabilityTheory

noncomputable section

/-- The manuscript's `3K/4` active arms, for each individual history. -/
theorem historyActive_card_three_quarters {d c T : ℕ} (hd : 1 ≤ d)
    (hc : 0 < c) (hbudget : 4 * T ≤ c * d) (h : History d 1 T) :
    (3 : ℝ) / 4 * d ≤ (SparseCapped.historyActiveItems c T h).card := by
  let a0 := Classical.choice (nonempty_MSetAction hd)
  let A := SparseCapped.historyActions a0 T h
  have hcap := Sparse.cap_mul_inactive_card_le A c T
  have hpart := Sparse.active_card_add_inactive_card A c T
  have hsmall : 4 * (Sparse.inactiveItems A c T).card ≤ d := by
    apply Nat.le_of_mul_le_mul_left (c := c) _ hc
    nlinarith
  have hnat : 3 * d ≤ 4 * (Sparse.activeItems A c T).card := by omega
  have hreal : (3 : ℝ) * d ≤ 4 * ((Sparse.activeItems A c T).card : ℝ) := by
    exact_mod_cast hnat
  rw [SparseCapped.activeItems_historyActions] at hreal
  linarith

@[simp] theorem sum_bitsOfSet {d : ℕ} (S : Finset (Fin d)) :
    (∑ i : Fin d, SparseCapped.bitValue (bitsOfSet S i)) = (S.card : ℝ) := by
  classical
  simp [bitsOfSet, SparseCapped.bitValue]

/-- A full-noise table with a prescribed favorable set. -/
def fixedTable {d T : ℕ} (S : Finset (Fin d)) (Z : Fin T → SparseCapped.Noise) :
    SparseCapped.Table d T := (bitsOfSet S, Z)

theorem learnerScore_le_fixed_card {d T : ℕ} (hd : 1 ≤ d) (c : ℕ)
    (S : Finset (Fin d)) (Z : Fin T → SparseCapped.Noise) (h : History d 1 T) :
    SparseCapped.learnerScore c (fixedTable S Z) T h ≤ (c : ℝ) * S.card := by
  simpa only [fixedTable, sum_bitsOfSet] using
    SparseCapped.learnerScore_le_cap_mul_bits hd c (fixedTable S Z) T h

/-- Outside A, a literal singleton comparator receives every noise bonus. -/
theorem topScore_ge_shape_of_not_allInactive {d T : ℕ} (hd : 1 ≤ d) (c : ℕ)
    (S : Finset (Fin d)) (Z : Fin T → SparseCapped.Noise) (h : History d 1 T)
    (hA : h ∉ allInactive S c T) :
    SparseCapped.shapeSum (fixedTable S Z) T ≤
      SparseCapped.topScore 1 (SparseCapped.itemScore c (fixedTable S Z) T h) := by
  classical
  simp only [allInactive, Set.mem_ofPred_eq, not_forall] at hA
  obtain ⟨i, hi, hactive⟩ := hA
  have hfull := SparseCapped.itemScore_eq_full_of_still_active c
    (fixedTable S Z) i T h (lt_of_not_ge hactive)
  have hbit : SparseCapped.bitValue ((fixedTable S Z).1 i) = 1 := by
    simp [fixedTable, bitsOfSet, SparseCapped.bitValue, hi]
  rw [hbit, one_mul] at hfull
  let a : MSetAction d 1 := ⟨{i}, by simp⟩
  have htop := SparseCapped.actionLoss_le_topScore
    (SparseCapped.itemScore c (fixedTable S Z) T h) a
  simpa only [actionLoss_eq_finset_sum, a, Finset.sum_singleton, hfull] using htop

/-- The loss on A is bounded pointwise, so no independence of A and Z is used. -/
theorem deficit_ge_shape_sub_allInactive {d T : ℕ} (hd : 1 ≤ d) (c : ℕ)
    (S : Finset (Fin d)) (Z : Fin T → SparseCapped.Noise) (h : History d 1 T) :
    SparseCapped.shapeSum (fixedTable S Z) T -
      (T : ℝ) * (allInactive S c T).indicator (fun _ => (1 : ℝ)) h -
      (c : ℝ) * S.card ≤ SparseCapped.deficit c (fixedTable S Z) T h := by
  classical
  have hl := learnerScore_le_fixed_card hd c S Z h
  unfold SparseCapped.deficit
  by_cases hA : h ∈ allInactive S c T
  · rw [Set.indicator_of_mem hA]
    have hshape := (SparseCapped.shapeSum_mem_Icc (fixedTable S Z) T).2
    have htop := (SparseCapped.topScore_mem_Icc hd c (fixedTable S Z) T h).1
    linarith
  · rw [Set.indicator_of_notMem hA]
    have htop := topScore_ge_shape_of_not_allInactive hd c S Z h hA
    linarith

theorem pathRegret_le_epsilon_time {d T : ℕ} (hd : 1 ≤ d) (c : ℕ)
    (S : Finset (Fin d)) (Z : Fin T → SparseCapped.Noise)
    (epsilon : ℝ) (he : 0 ≤ epsilon) (hs : epsilon ≤ 1 / 16) (h : History d 1 T) :
    pathRegret ((SparseCapped.tableLossProcess (d := d) (m := 1) (by omega)
      c epsilon he hs T).at (fixedTable S Z)) T h ≤ epsilon * T := by
  rw [SparseCapped.pathRegret_eq_scaled_deficit (by omega) hd]
  simpa only [Nat.cast_one, div_one, one_mul] using
    mul_le_mul_of_nonneg_left (SparseCapped.deficit_le hd c (fixedTable S Z) T h) he

end

end MsetsPaper.Lower.WJ
