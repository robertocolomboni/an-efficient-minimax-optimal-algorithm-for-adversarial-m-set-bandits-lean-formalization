import MsetsPaper.Upper.Leverage
import MsetsPaper.Upper.MatrixBounds
import MsetsPaper.Upper.IncrementArithmetic

/-!
# Manuscript Lemma 3 for the actual estimator

This is a local one-round theorem, as in the paper. It neither presupposes
nor proves the algorithm's global membership invariant (Proposition 1).
The action loss normalization is used at its correct, aggregate level.
-/

noncomputable section

open MsetsLower MsetsLower.History
open scoped BigOperators

namespace MsetsPaper.Upper

variable {d m : ℕ}

def surrogate (theta ell : Fin d → ℝ) (eta : ℝ) (a b : Action d m) : ℝ :=
  estimateScalar theta a ell b -
    eta * actionLoss b (correction (m : ℝ) (weightedMarginal (m := m) theta))

theorem actionLoss_correction (theta : Fin d → ℝ)
    (hmpos : 1 ≤ m) (hmtop : m ≤ d - 1) (a : Action d m) :
    actionLoss a (correction (m : ℝ) (weightedMarginal (m := m) theta)) =
      4 * phi (weightedMarginal (m := m) theta) (fun i ↦ selectedIndicator i a) := by
  classical
  simpa [actionLoss, selectedIndicator, mul_ite] using
    weightedLaw_correction_dot theta hmpos hmtop a

/-- The actual range estimate used after setting `lam = 128*eta*d` and
assuming the true distribution belongs to `P_(lam/2)`. -/
theorem phi_range_half_parameter (theta : Fin d → ℝ)
    (hmpos : 1 ≤ m) (hmtop : m ≤ d - 1) {eta : ℝ} (heta : 0 < eta)
    (hlo : ∀ i, (128 * eta * d / 2) * ((m : ℝ) / d) ≤ weightedMarginal (m := m) theta i)
    (hhi : ∀ i, weightedMarginal (m := m) theta i ≤
      1 - (128 * eta * d / 2) * (1 - (m : ℝ) / d)) (a : Action d m) :
    0 ≤ phi (weightedMarginal (m := m) theta) (fun i ↦ selectedIndicator i a) ∧
      phi (weightedMarginal (m := m) theta) (fun i ↦ selectedIndicator i a) ≤
        1 + 4 * d / (128 * eta * d) := by
  have hd : 0 < (d : ℝ) := by exact_mod_cast (show 0 < d by omega)
  have h := weightedLaw_phi_range theta hmpos hmtop
    (show 0 < 128 * eta * d / 2 by positivity) hlo hhi a
  have heq : 1 + 2 * (d : ℝ) / (128 * eta * d / 2) =
      1 + 4 * d / (128 * eta * d) := by ring
  simpa only [heq] using h

/-- The stronger `51/1024` bound obtained in the proof of Lemma 3.
No estimator bound or leverage certificate is an input: both are proved.
The unused manuscript restriction `lam <= 1/2` is not needed for this local
inequality; it will instead be established for the algorithm's parameters. -/
theorem bounded_increments_strong (theta ell : Fin d → ℝ)
    (hmpos : 1 ≤ m) (hmtop : m ≤ d - 1)
    {eta : ℝ} (heta : 0 < eta) (hsmall : eta ≤ 1 / 64)
    (hloss : ∀ a : Action d m, |actionLoss a ell| ≤ 1)
    (hlo : ∀ i, (128 * eta * d / 2) * ((m : ℝ) / d) ≤ weightedMarginal (m := m) theta i)
    (hhi : ∀ i, weightedMarginal (m := m) theta i ≤
      1 - (128 * eta * d / 2) * (1 - (m : ℝ) / d)) (a b : Action d m) :
    eta * |surrogate theta ell eta a b| ≤ 51 / 1024 := by
  have hd : 0 < (d : ℝ) := by exact_mod_cast (show 0 < d by omega)
  have hrange := phi_range_half_parameter theta hmpos hmtop heta hlo hhi
  have hlev : ∀ c : Action d m, leverage theta c ≤ 1 + 4 * d / (128 * eta * d) :=
    fun c ↦ (leverage_le_phi theta hmpos hmtop c).trans (hrange c).2
  have hestimate := abs_estimateScalar_le_of_leverage_bound theta ell hmpos hmtop
    a b (hloss a) (hlev a) (hlev b)
  rw [surrogate, actionLoss_correction theta hmpos hmtop b]
  exact surrogate_increment_bound heta hsmall
    (eta_leverage_bound heta hd).le hestimate (hrange b).1 (hrange b).2

/-- Lemma 3's stated one-quarter bound. -/
theorem bounded_increments (theta ell : Fin d → ℝ)
    (hmpos : 1 ≤ m) (hmtop : m ≤ d - 1)
    {eta : ℝ} (heta : 0 < eta) (hsmall : eta ≤ 1 / 64)
    (hloss : ∀ a : Action d m, |actionLoss a ell| ≤ 1)
    (hlo : ∀ i, (128 * eta * d / 2) * ((m : ℝ) / d) ≤ weightedMarginal (m := m) theta i)
    (hhi : ∀ i, weightedMarginal (m := m) theta i ≤
      1 - (128 * eta * d / 2) * (1 - (m : ℝ) / d)) (a b : Action d m) :
    eta * |surrogate theta ell eta a b| ≤ 1 / 4 :=
  (bounded_increments_strong theta ell hmpos hmtop heta hsmall hloss hlo hhi a b).trans
    (by norm_num)

end MsetsPaper.Upper
