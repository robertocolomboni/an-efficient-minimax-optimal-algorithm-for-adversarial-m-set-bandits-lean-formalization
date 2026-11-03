import MsetsPaper.Probability.FiniteExponential
import MsetsPaper.Upper.Leverage

/-!
# L6 on the actual adaptive exponential action law

The next action is drawn from `weightedLaw (theta t h)`, not from an abstract
law supplied together with its desired mean or concentration conclusion.
The marginal invariant is an explicit input, to be discharged by P1.
The equivalence with observable-history execution is a separate bridge.
-/

noncomputable section

open scoped BigOperators
open MsetsLower MsetsLower.History MsetsPaper.Probability

namespace MsetsPaper.Upper

variable {d m : ℕ}

def weightedBranchingLaw (theta : (t : ℕ) → ActionTree (Action d m) t → Fin d → ℝ)
    (hmd : m ≤ d) : BranchingLaw (Action d m) where
  next t h := weightedLaw (theta t h)
  nonneg t h a := (weightedLaw_pos (theta t h) hmd a).le
  sum_one t h := sum_weightedLaw (theta t h) hmd

def adaptivePhi (theta : (t : ℕ) → ActionTree (Action d m) t → Fin d → ℝ)
    (t : ℕ) (h : ActionTree (Action d m) t) (a : Action d m) : ℝ :=
  phi (weightedMarginal (m := m) (theta t h)) (fun i ↦ selectedIndicator i a)

theorem adaptivePhi_mean
    (theta : (t : ℕ) → ActionTree (Action d m) t → Fin d → ℝ)
    (hmpos : 1 ≤ m) (hmtop : m ≤ d - 1) (t : ℕ) (h : ActionTree (Action d m) t) :
    ∑ a, (weightedBranchingLaw theta (by omega)).next t h a * adaptivePhi theta t h a =
      (d : ℝ) + 1 :=
  weightedLaw_phi_mean (theta t h) hmpos hmtop

theorem adaptivePhi_range
    (theta : (t : ℕ) → ActionTree (Action d m) t → Fin d → ℝ)
    (hmpos : 1 ≤ m) (hmtop : m ≤ d - 1) {lam : ℝ} (hlam : 0 < lam)
    (t : ℕ) (h : ActionTree (Action d m) t)
    (hlo : ∀ i, (lam / 2) * ((m : ℝ) / d) ≤ weightedMarginal (m := m) (theta t h) i)
    (hhi : ∀ i, weightedMarginal (m := m) (theta t h) i ≤
      1 - (lam / 2) * (1 - (m : ℝ) / d)) (a : Action d m) :
    0 ≤ adaptivePhi theta t h a ∧ adaptivePhi theta t h a ≤ 1 + 4 * d / lam := by
  have hb := weightedLaw_phi_range (theta t h) hmpos hmtop
    (show 0 < lam / 2 by positivity) hlo hhi a
  have heq : 1 + 2 * (d : ℝ) / (lam / 2) = 1 + 4 * d / lam := by ring
  simpa only [adaptivePhi, heq] using hb

/-- L6 with the manuscript constants, for any predictable parameter sequence
satisfying P_{lambda/2} through time T. This does not assert P1's invariant. -/
theorem adaptive_leverage_high_probability
    (theta : (t : ℕ) → ActionTree (Action d m) t → Fin d → ℝ)
    (hmpos : 1 ≤ m) (hmtop : m ≤ d - 1) (T : ℕ)
    {lam : ℝ} (hlam : 0 < lam)
    (hlo : ∀ t < T, ∀ h i,
      (lam / 2) * ((m : ℝ) / d) ≤ weightedMarginal (m := m) (theta t h) i)
    (hhi : ∀ t < T, ∀ h i, weightedMarginal (m := m) (theta t h) i ≤
      1 - (lam / 2) * (1 - (m : ℝ) / d))
    {rho : ℝ} (hrho : 0 < rho) (hrho1 : rho ≤ 1) :
    1 - rho ≤ (weightedBranchingLaw theta (by omega)).probability T
      {h | pathSum (adaptivePhi theta) T h ≤
        2 * ((d : ℝ) + 1) * T + 2 * (1 + 4 * d / lam) * Real.log (1 / rho)} := by
  have hsharp := nonnegative_bounded_sum_sharp_high_probability_upto
    (weightedBranchingLaw theta (show m ≤ d by omega)) (adaptivePhi theta) T
    (show 0 < 1 + 4 * (d : ℝ) / lam by positivity)
    (fun t ht h a ↦
      adaptivePhi_range theta hmpos hmtop hlam t h (hlo t ht h) (hhi t ht h) a)
    (fun t _ h ↦ adaptivePhi_mean theta hmpos hmtop t h) hrho
  apply hsharp.trans
  apply (weightedBranchingLaw theta (show m ≤ d by omega)).probability_mono
  intro h hh
  have hlog : 0 ≤ Real.log (1 / rho) := Real.log_nonneg ((one_le_div hrho).mpr hrho1)
  have hmean : 0 ≤ ((d : ℝ) + 1) * T := by positivity
  have hcoef := mul_le_mul_of_nonneg_right
    (show Real.exp 1 - 1 ≤ 2 by linarith [Real.exp_one_lt_three]) hmean
  have hlogterm : 0 ≤ (1 + 4 * (d : ℝ) / lam) * Real.log (1 / rho) :=
    mul_nonneg (by positivity) hlog
  change pathSum (adaptivePhi theta) T h ≤
    (Real.exp 1 - 1) * ((d : ℝ) + 1) * T +
      (1 + 4 * d / lam) * Real.log (1 / rho) at hh
  change pathSum (adaptivePhi theta) T h ≤
    2 * ((d : ℝ) + 1) * T + 2 * (1 + 4 * d / lam) * Real.log (1 / rho)
  nlinarith

end MsetsPaper.Upper
