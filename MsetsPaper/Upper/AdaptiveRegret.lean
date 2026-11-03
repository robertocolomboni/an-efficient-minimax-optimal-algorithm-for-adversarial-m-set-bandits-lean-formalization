import MsetsPaper.Upper.MainAdaptiveEstimated
import MsetsPaper.Upper.MainGoodEvent
import Mathlib.Order.ConditionallyCompleteLattice.Finset

/-! # T1: actual path regret and best action in hindsight -/

noncomputable section
open MsetsLower MsetsPaper.Probability
open scoped BigOperators

namespace MsetsPaper.Upper

variable {d m : ℕ}

def adaptiveRealizedLoss
    (ell : (t : ℕ) → ActionTree (Action d m) t → Fin d → ℝ)
    (T : ℕ) (h : ActionTree (Action d m) T) : ℝ :=
  pathSum (fun t h a ↦ actionLoss a (ell t h)) T h

def adaptiveComparatorLoss
    (ell : (t : ℕ) → ActionTree (Action d m) t → Fin d → ℝ)
    (T : ℕ) (h : ActionTree (Action d m) T) (x : Action d m) : ℝ :=
  pathSum (fun t h _ ↦ actionLoss x (ell t h)) T h

def adaptiveRegret
    (ell : (t : ℕ) → ActionTree (Action d m) t → Fin d → ℝ)
    (T : ℕ) (h : ActionTree (Action d m) T) : ℝ :=
  adaptiveRealizedLoss ell T h - sInf (Set.range (adaptiveComparatorLoss ell T h))

theorem adaptive_best_action_exists
    (ell : (t : ℕ) → ActionTree (Action d m) t → Fin d → ℝ)
    (hmd : m ≤ d) (T : ℕ) (h : ActionTree (Action d m) T) :
    ∃ x : Action d m, adaptiveRegret ell T h =
      pathSum (fun t h a ↦ actionLoss a (ell t h) - actionLoss x (ell t h)) T h := by
  letI : Nonempty (Action d m) := nonempty_MSetAction hmd
  obtain ⟨x, hx⟩ := (Set.range_nonempty (adaptiveComparatorLoss ell T h)).csInf_mem
    (Set.finite_range _)
  refine ⟨x, ?_⟩
  rw [pathSum_sub]
  unfold adaptiveRegret adaptiveRealizedLoss adaptiveComparatorLoss at *
  rw [← hx]

theorem adaptiveRegret_le_of_forall
    (ell : (t : ℕ) → ActionTree (Action d m) t → Fin d → ℝ)
    (hmd : m ≤ d) (T : ℕ) (h : ActionTree (Action d m) T) {B : ℝ}
    (hB : ∀ x : Action d m,
      pathSum (fun t h a ↦ actionLoss a (ell t h) - actionLoss x (ell t h)) T h ≤ B) :
    adaptiveRegret ell T h ≤ B := by
  obtain ⟨x, hx⟩ := adaptive_best_action_exists ell hmd T h
  rw [hx]
  exact hB x

theorem adaptiveRegret_trivial
    (ell : (t : ℕ) → ActionTree (Action d m) t → Fin d → ℝ)
    (hmd : m ≤ d) (T : ℕ)
    (hloss : ∀ t < T, ∀ h (a : Action d m), |actionLoss a (ell t h)| ≤ 1)
    (h : ActionTree (Action d m) T) : adaptiveRegret ell T h ≤ 2 * T := by
  apply adaptiveRegret_le_of_forall ell hmd T h
  intro x
  have hp := pathSum_mono_upto
    (fun t h a ↦ actionLoss a (ell t h) - actionLoss x (ell t h))
    (fun _ _ _ ↦ (2 : ℝ)) T (fun t ht h a ↦ by
      linarith [(abs_le.mp (hloss t ht h a)).2, (abs_le.mp (hloss t ht h x)).1]) h
  simpa only [pathSum_const, mul_comm (T : ℝ) 2] using hp

theorem adaptive_smoothed_to_pure
    (ell : (t : ℕ) → ActionTree (Action d m) t → Fin d → ℝ)
    (T : ℕ) {lam : ℝ} (hlam : 0 ≤ lam)
    (hloss : ∀ t < T, ∀ h (a : Action d m), |actionLoss a (ell t h)| ≤ 1)
    (x : Action d m) (h : ActionTree (Action d m) T) :
    pathSum (fun t h a ↦ actionLoss a (ell t h) - actionLoss x (ell t h)) T h ≤
      pathSum (fun t h a ↦ actionLoss a (ell t h) -
        comparatorTrue (smoothedComparator lam x) (ell t h)) T h + 2 * lam * T := by
  have hp := pathSum_mono_upto
    (fun t h a ↦ actionLoss a (ell t h) - actionLoss x (ell t h))
    (fun t h a ↦ (actionLoss a (ell t h) -
      comparatorTrue (smoothedComparator lam x) (ell t h)) + 2 * lam) T
    (fun t ht h a ↦ by
      have hc := smoothedComparator_loss_cost hlam x (ell t h) (hloss t ht h)
      change comparatorTrue _ _ - _ ≤ _ at hc
      linarith) h
  simpa only [pathSum_add, pathSum_const, mul_comm (T : ℝ) (2 * lam)] using hp

end MsetsPaper.Upper
