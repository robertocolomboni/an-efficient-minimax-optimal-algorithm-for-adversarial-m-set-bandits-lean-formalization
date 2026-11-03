import MsetsPaper.Probability.FiniteTwoSided
import MsetsPaper.Upper.AdaptiveLeverage
import MsetsPaper.Upper.KWOneStep

/-!
# L5: comparator concentration for the actual adaptive weighted law

Both q_t and ell_t may depend on the entire action prefix. Each exponential
moment is derived from the actual estimator; only the legitimate marginal
and action-loss invariants are premises. The execution/P1 bridges remain
separate obligations, not hidden assumptions of this probability estimate.
-/

noncomputable section

open scoped BigOperators
open MsetsLower MsetsPaper.Probability

namespace MsetsPaper.Upper

variable {d m : ℕ}

def adaptiveComparatorDelta
    (theta : (t : ℕ) → ActionTree (Action d m) t → Fin d → ℝ)
    (q : (t : ℕ) → ActionTree (Action d m) t → Action d m → ℝ)
    (ell : (t : ℕ) → ActionTree (Action d m) t → Fin d → ℝ)
    (t : ℕ) (h : ActionTree (Action d m) t) (a : Action d m) : ℝ :=
  comparatorDelta (theta t h) (q t h) (ell t h) a

def adaptiveComparatorV
    (theta : (t : ℕ) → ActionTree (Action d m) t → Fin d → ℝ)
    (q : (t : ℕ) → ActionTree (Action d m) t → Action d m → ℝ)
    (t : ℕ) (h : ActionTree (Action d m) t) : ℝ :=
  comparatorV (theta t h) (q t h)

/-- The exact eta/4 and log(2/rho)/eta inequality from L5. -/
theorem adaptive_comparator_high_probability
    (theta : (t : ℕ) → ActionTree (Action d m) t → Fin d → ℝ)
    (q : (t : ℕ) → ActionTree (Action d m) t → Action d m → ℝ)
    (ell : (t : ℕ) → ActionTree (Action d m) t → Fin d → ℝ)
    (hmpos : 1 ≤ m) (hmtop : m ≤ d - 1) (T : ℕ)
    {eta : ℝ} (heta : 0 < eta) (hsmall : eta ≤ 1 / 64)
    (hq : ∀ t < T, ∀ h b, 0 ≤ q t h b)
    (hqsum : ∀ t < T, ∀ h, ∑ b, q t h b = 1)
    (hlo : ∀ t < T, ∀ h i, (128 * eta * d / 2) * ((m : ℝ) / d) ≤
      weightedMarginal (m := m) (theta t h) i)
    (hhi : ∀ t < T, ∀ h i, weightedMarginal (m := m) (theta t h) i ≤
      1 - (128 * eta * d / 2) * (1 - (m : ℝ) / d))
    (hloss : ∀ t < T, ∀ h (a : Action d m), |actionLoss a (ell t h)| ≤ 1)
    {rho : ℝ} (hrho : 0 < rho) :
    1 - rho ≤ (weightedBranchingLaw theta (by omega)).probability T {h |
      |pathSum (adaptiveComparatorDelta theta q ell) T h| ≤
        eta / 4 * pathSum (fun t h _ ↦ adaptiveComparatorV theta q t h) T h +
          Real.log (2 / rho) / eta} := by
  apply two_sided_predictable_high_probability
    (weightedBranchingLaw theta (by omega))
    (adaptiveComparatorDelta theta q ell) (adaptiveComparatorV theta q) T heta
  · intro t ht h s hs
    exact comparatorDelta_mgf_sign (theta t h) (q t h) (ell t h)
      (hq t ht h) (hqsum t ht h) hmpos hmtop heta hsmall
      (hlo t ht h) (hhi t ht h) (hloss t ht h) s hs
  · exact hrho

end MsetsPaper.Upper
