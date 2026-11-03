import MsetsPaper.Alignment.UpperAlgorithm

/-! The pathwise OMD inequality on the actual observable run, without an
assumption about invariants at impossible feedback histories. -/

noncomputable section

open MeasureTheory MsetsLower MsetsLower.History MsetsPaper.Probability MsetsPaper.Upper
open scoped BigOperators

namespace MsetsPaper.Alignment

variable {d m : ℕ}

def observableSurrogateDifference
    (theta : (t : ℕ) → History d m t → Fin d → ℝ)
    (L : SignedLossProcess d m) (eta : ℝ) (q : Action d m → ℝ)
    (t : ℕ) (h : History d m t) (a : Action d m) : ℝ :=
  finiteExpectation (weightedLaw (theta t h)) (surrogate (theta t h) (L.itemLoss t h) eta a) -
    finiteExpectation q (surrogate (theta t h) (L.itemLoss t h) eta a)

def observableSurrogateSecondMoment
    (theta : (t : ℕ) → History d m t → Fin d → ℝ)
    (L : SignedLossProcess d m) (eta : ℝ)
    (t : ℕ) (h : History d m t) (a : Action d m) : ℝ :=
  finiteExpectation (weightedLaw (theta t h))
    (fun b ↦ (surrogate (theta t h) (L.itemLoss t h) eta a b) ^ 2)

/-- The manuscript's pathwise stability statement holds almost surely under
the concrete feedback-only algorithm's law. Its stronger action-path version
is `upper_omd_stability`; reconstruction transfers it to observable histories. -/
theorem upper_omd_stability_observable
    (L : SignedLossProcess d m) (hmpos : 1 ≤ m) (hmtop : m ≤ d - 1)
    (T : ℕ) (hT : 0 < T) {delta : ℝ} (hdelta0 : 0 < delta) (hdelta1 : delta < 1)
    (q : Action d m → ℝ) (hq : ∀ a, 0 ≤ q a) (hqsum : ∑ a, q a = 1)
    (hqbox : ∀ i,
      128 * mainLearningRate d T (Nat.choose d m) delta * d * ((m : ℝ) / d) ≤ marginal q i ∧
      marginal q i ≤ 1 - 128 * mainLearningRate d T (Nat.choose d m) delta * d *
        (1 - (m : ℝ) / d)) :
    let eta := mainLearningRate d T (Nat.choose d m) delta
    let theta := ellipsoidAlgorithmParameters (d := d) (m := m) eta T
    ∀ᵐ h ∂signedRunLaw (mainAlgorithm T delta (by omega)) L T,
      observablePathSum (observableSurrogateDifference theta L eta q) T h ≤
        finiteKL q (weightedLaw (m := m) (0 : Fin d → ℝ)) / eta + 1 +
          2 * eta * observablePathSum (observableSurrogateSecondMoment theta L eta) T h := by
  let eta := mainLearningRate d T (Nat.choose d m) delta
  let theta := ellipsoidAlgorithmParameters (d := d) (m := m) eta T
  have hreconstruct := signedRunLaw_ae_history_reconstruction theta
    (measurable_ellipsoidAlgorithmParameters eta T) (show m ≤ d by omega) L T
  filter_upwards [hreconstruct] with h hh
  have hb := upper_omd_stability L hmpos hmtop T hT hdelta0 hdelta1
    q hq hqsum hqbox (actionsOfHistory T h)
  change observablePathSum (observableSurrogateDifference theta L eta q) T h ≤ _
  rw [← hh]
  simp only [observablePathSum_historyOfActions]
  exact hb

end MsetsPaper.Alignment
