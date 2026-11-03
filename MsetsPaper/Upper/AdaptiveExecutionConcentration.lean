import MsetsPaper.Upper.AdaptiveExecution
import MsetsPaper.Upper.AdaptiveConcentration

/-!
# L5 and L6 for the actual observable interaction

The conclusions below concern the recursively generated Markov-kernel law,
not an independently postulated finite experiment.  Their statistics use
the real preceding observable histories.  Equality with the finite tree is
proved by deterministic feedback reconstruction.  Marginal invariants are
still explicit P1 obligations; none of these results asserts that the
algorithmic projection produces them.
-/

noncomputable section

open scoped BigOperators ProbabilityTheory
open MeasureTheory MsetsLower MsetsLower.History MsetsPaper.Probability

namespace MsetsPaper.Upper

variable {d m : ℕ}

def comparatorsOnActions
    (q : (t : ℕ) → History d m t → Action d m → ℝ) (L : SignedLossProcess d m)
    (t : ℕ) (h : ActionTree (Action d m) t) : Action d m → ℝ :=
  q t (historyOfActions L t h)

def lossesOnActions (L : SignedLossProcess d m)
    (t : ℕ) (h : ActionTree (Action d m) t) : Fin d → ℝ :=
  L.itemLoss t (historyOfActions L t h)

def observableComparatorDelta
    (theta : (t : ℕ) → History d m t → Fin d → ℝ)
    (q : (t : ℕ) → History d m t → Action d m → ℝ) (L : SignedLossProcess d m)
    (t : ℕ) (h : History d m t) (a : Action d m) : ℝ :=
  comparatorDelta (theta t h) (q t h) (L.itemLoss t h) a

def observableComparatorV
    (theta : (t : ℕ) → History d m t → Fin d → ℝ)
    (q : (t : ℕ) → History d m t → Action d m → ℝ)
    (t : ℕ) (h : History d m t) (_ : Action d m) : ℝ :=
  comparatorV (theta t h) (q t h)

def observablePhi (theta : (t : ℕ) → History d m t → Fin d → ℝ)
    (t : ℕ) (h : History d m t) (a : Action d m) : ℝ :=
  phi (weightedMarginal (m := m) (theta t h)) (fun i => selectedIndicator i a)

/-- L5 under the true signed observable-history run law, with exactly the
manuscript's eta/4 and log(2/rho)/eta constants. -/
theorem observable_comparator_high_probability
    (theta : (t : ℕ) → History d m t → Fin d → ℝ)
    (htheta : ∀ t, Measurable (theta t))
    (q : (t : ℕ) → History d m t → Action d m → ℝ) (L : SignedLossProcess d m)
    (hmpos : 1 ≤ m) (hmtop : m ≤ d - 1) (T : ℕ)
    {eta : ℝ} (heta : 0 < eta) (hsmall : eta ≤ 1 / 64)
    (hq : ∀ t < T, ∀ h b, 0 ≤ q t h b)
    (hqsum : ∀ t < T, ∀ h, ∑ b, q t h b = 1)
    (hlo : ∀ t < T, ∀ h i, (128 * eta * d / 2) * ((m : ℝ) / d) ≤
      weightedMarginal (m := m) (theta t h) i)
    (hhi : ∀ t < T, ∀ h i, weightedMarginal (m := m) (theta t h) i ≤
      1 - (128 * eta * d / 2) * (1 - (m : ℝ) / d))
    {rho : ℝ} (hrho : 0 < rho) :
    1 - rho ≤ (signedRunLaw (observableWeightedPolicy theta htheta (by omega)) L T).real
      {h | |observablePathSum (observableComparatorDelta theta q L) T h| ≤
        eta / 4 * observablePathSum (observableComparatorV theta q) T h +
          Real.log (2 / rho) / eta} := by
  rw [signedRunLaw_probability_eq_tree_all_sets]
  simp only [Set.mem_setOf_eq, observablePathSum_historyOfActions]
  exact adaptive_comparator_high_probability (parametersOnActions theta L)
    (comparatorsOnActions q L) (lossesOnActions L) hmpos hmtop T heta hsmall
    (fun t ht h b => hq t ht (historyOfActions L t h) b)
    (fun t ht h => hqsum t ht (historyOfActions L t h))
    (fun t ht h i => hlo t ht (historyOfActions L t h) i)
    (fun t ht h i => hhi t ht (historyOfActions L t h) i)
    (fun t _ h a => L.action_abs_le_one t (historyOfActions L t h) a) hrho

/-- The sharper displayed intermediate inequality in L6, transported without
changing either coefficient. -/
theorem observable_leverage_sharp_high_probability
    (theta : (t : ℕ) → History d m t → Fin d → ℝ)
    (htheta : ∀ t, Measurable (theta t)) (L : SignedLossProcess d m)
    (hmpos : 1 ≤ m) (hmtop : m ≤ d - 1) (T : ℕ)
    {lam : ℝ} (hlam : 0 < lam)
    (hlo : ∀ t < T, ∀ h i,
      (lam / 2) * ((m : ℝ) / d) ≤ weightedMarginal (m := m) (theta t h) i)
    (hhi : ∀ t < T, ∀ h i, weightedMarginal (m := m) (theta t h) i ≤
      1 - (lam / 2) * (1 - (m : ℝ) / d))
    {rho : ℝ} (hrho : 0 < rho) :
    1 - rho ≤ (signedRunLaw (observableWeightedPolicy theta htheta (by omega)) L T).real
      {h | observablePathSum (observablePhi theta) T h ≤
        (Real.exp 1 - 1) * ((d : ℝ) + 1) * T +
          (1 + 4 * d / lam) * Real.log (1 / rho)} := by
  rw [signedRunLaw_probability_eq_tree_all_sets]
  simp only [Set.mem_setOf_eq, observablePathSum_historyOfActions]
  apply nonnegative_bounded_sum_sharp_high_probability_upto
    (weightedBranchingLaw (parametersOnActions theta L) (by omega))
    (adaptivePhi (parametersOnActions theta L)) T (by positivity)
  · intro t ht h a
    exact adaptivePhi_range (parametersOnActions theta L) hmpos hmtop hlam t h
      (hlo t ht (historyOfActions L t h)) (hhi t ht (historyOfActions L t h)) a
  · intro t _ h
    exact adaptivePhi_mean (parametersOnActions theta L) hmpos hmtop t h
  · exact hrho

/-- The final, slightly relaxed constants stated in L6, under the true law. -/
theorem observable_leverage_high_probability
    (theta : (t : ℕ) → History d m t → Fin d → ℝ)
    (htheta : ∀ t, Measurable (theta t)) (L : SignedLossProcess d m)
    (hmpos : 1 ≤ m) (hmtop : m ≤ d - 1) (T : ℕ)
    {lam : ℝ} (hlam : 0 < lam)
    (hlo : ∀ t < T, ∀ h i,
      (lam / 2) * ((m : ℝ) / d) ≤ weightedMarginal (m := m) (theta t h) i)
    (hhi : ∀ t < T, ∀ h i, weightedMarginal (m := m) (theta t h) i ≤
      1 - (lam / 2) * (1 - (m : ℝ) / d))
    {rho : ℝ} (hrho : 0 < rho) (hrho1 : rho ≤ 1) :
    1 - rho ≤ (signedRunLaw (observableWeightedPolicy theta htheta (by omega)) L T).real
      {h | observablePathSum (observablePhi theta) T h ≤
        2 * ((d : ℝ) + 1) * T + 2 * (1 + 4 * d / lam) * Real.log (1 / rho)} := by
  rw [signedRunLaw_probability_eq_tree_all_sets]
  simp only [Set.mem_setOf_eq, observablePathSum_historyOfActions]
  exact adaptive_leverage_high_probability (parametersOnActions theta L) hmpos hmtop T hlam
    (fun t ht h i => hlo t ht (historyOfActions L t h) i)
    (fun t ht h i => hhi t ht (historyOfActions L t h) i) hrho hrho1

end MsetsPaper.Upper
