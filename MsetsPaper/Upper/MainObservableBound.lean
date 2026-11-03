import MsetsPaper.Upper.MainConditionalBound
import MsetsPaper.Upper.AdaptiveExecutionConcentration

/-! # T1's conditional bound for the actual observable interaction

The observable regret recomputes losses from the actual past history, and
takes the minimum over fixed actions. It is not a statistic supplied with
the desired tail bound. The algorithmic P1 premises are still explicit.
-/

noncomputable section
open MeasureTheory MsetsLower MsetsLower.History MsetsPaper.Probability
open scoped BigOperators

namespace MsetsPaper.Upper

variable {d m : ℕ}

def observableSignedRegret (L : SignedLossProcess d m) (T : ℕ) (h : History d m T) : ℝ :=
  observablePathSum (fun t h a ↦ actionLoss a (L.itemLoss t h)) T h -
    sInf (Set.range (fun x : Action d m ↦
      observablePathSum (fun t h _ ↦ actionLoss x (L.itemLoss t h)) T h))

theorem observableSignedRegret_historyOfActions (L : SignedLossProcess d m)
    (T : ℕ) (h : ActionTree (Action d m) T) :
    observableSignedRegret L T (historyOfActions L T h) =
      adaptiveRegret (lossesOnActions L) T h := by
  unfold observableSignedRegret adaptiveRegret adaptiveRealizedLoss adaptiveComparatorLoss
  simp only [observablePathSum_historyOfActions]
  rfl

theorem observable_main_regret_high_probability_of_projection
    (theta : (t : ℕ) → History d m t → Fin d → ℝ)
    (htheta : ∀ t, Measurable (theta t)) (L : SignedLossProcess d m)
    (hmpos : 1 ≤ m) (hmtop : m ≤ d - 1) (T : ℕ) (hT : 0 < T)
    {delta : ℝ} (hdelta0 : 0 < delta) (hdelta1 : delta ≤ 1)
    (hzero : theta 0 () = 0)
    (hlo : ∀ t < T, ∀ h i,
      (128 * mainLearningRate d T (Nat.choose d m) delta * d / 2) * ((m : ℝ) / d) ≤
      weightedMarginal (m := m) (theta t h) i)
    (hhi : ∀ t < T, ∀ h i, weightedMarginal (m := m) (theta t h) i ≤
      1 - (128 * mainLearningRate d T (Nat.choose d m) delta * d / 2) * (1 - (m : ℝ) / d))
    (hprojection : ∀ (x : Action d m) t, t < T → ∀ h a,
      let eta := mainLearningRate d T (Nat.choose d m) delta
      let next := theta (t + 1) (h.snoc a (actionLoss a (L.itemLoss t h)))
      let unprojected := theta t h - eta • surrogateVector (theta t h) (L.itemLoss t h) eta a
      finiteKL (smoothedComparator (128 * eta * d) x) (weightedLaw (m := m) next) ≤
      finiteKL (smoothedComparator (128 * eta * d) x) (weightedLaw (m := m) unprojected) -
      finiteKL (weightedLaw (m := m) next) (weightedLaw (m := m) unprojected) + eta / T) :
    1 - delta ≤ (signedRunLaw (observableWeightedPolicy theta htheta (by omega)) L T).real
      {h | observableSignedRegret L T h ≤
        160 * Real.sqrt ((d : ℝ) * T * (Real.log (Nat.choose d m) + Real.log (1 / delta)))} := by
  rw [signedRunLaw_probability_eq_tree_all_sets]
  simp only [Set.mem_setOf_eq, observableSignedRegret_historyOfActions]
  apply main_regret_high_probability_of_projection (parametersOnActions theta L)
    (lossesOnActions L) hmpos hmtop T hT hdelta0 hdelta1
  · exact hzero
  · intro t _ h a
    exact L.action_abs_le_one t (historyOfActions L t h) a
  · intro t ht h i
    exact hlo t ht (historyOfActions L t h) i
  · intro t ht h i
    exact hhi t ht (historyOfActions L t h) i
  · intro x t ht h a
    exact hprojection x t ht (historyOfActions L t h) a

end MsetsPaper.Upper
