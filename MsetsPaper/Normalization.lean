import MsetsLower.Core.Protocol
import Mathlib.Tactic.NormNum

/-! A formal counterexample explaining the explicitly authorized introductory
correction. The mathematical setting uses action-level, not item-level bounds. -/

namespace MsetsPaper

open MsetsLower

theorem unit_item_losses_aggregate {d m : ℕ} (a : MSetAction d m) :
    actionLoss a (fun _ => (1 : ℝ)) = m := by
  rw [actionLoss_eq_finset_sum]
  simp

theorem item_normalization_counterexample :
    ∃ ell : Fin 3 → ℝ, (∀ i, |ell i| ≤ 1) ∧
      ∃ a : MSetAction 3 2, |actionLoss a ell| = 2 := by
  refine ⟨fun _ => 1, by norm_num, ?_⟩
  obtain ⟨a⟩ := nonempty_MSetAction (d := 3) (m := 2) (by norm_num)
  exact ⟨a, by rw [unit_item_losses_aggregate]; norm_num⟩

end MsetsPaper
