import MsetsPaper.Upper.Algorithm
import MsetsPaper.Lower.OrdinaryNewRoute

/-! # The paper's strict comparison of upper and lower tail probabilities

The lower bound is applied at confidence `2 * delta` before comparison with
the upper guarantee at `delta`.  This file certifies the probabilistic rates;
computational efficiency is a separate resource refinement.
-/

noncomputable section
open MsetsLower MsetsLower.Lower MeasureTheory

namespace MsetsPaper

def regretRate (d m T : ℕ) (delta : ℝ) : ℝ :=
  Real.sqrt ((d : ℝ) * T * (Real.log (d.choose m : ℝ) + Real.log (1 / delta)))

theorem confidence_log_four {delta : ℝ} (hdelta : 0 < delta) (hsmall : delta ≤ 1 / 4) :
    2 * Real.log 2 ≤ Real.log (1 / delta) := by
  have harg : (4 : ℝ) ≤ 1 / delta := (le_div_iff₀ hdelta).mpr (by linarith)
  have hlog := Real.log_le_log (by norm_num : (0 : ℝ) < 4) harg
  have hid : Real.log (4 : ℝ) = 2 * Real.log 2 := by
    rw [show (4 : ℝ) = 2 ^ (2 : ℕ) by norm_num, Real.log_pow]
    norm_num
  rwa [hid] at hlog

theorem doubled_confidence_rate_comparison {d m T : ℕ} (hmd : m ≤ d)
    {delta : ℝ} (hdelta : 0 < delta) (hsmall : delta ≤ 1 / 4) :
    (2 : ℝ) ^ (-44 : ℤ) * regretRate d m T delta ≤
      (2 : ℝ) ^ (-43 : ℤ) * regretRate d m T (2 * delta) := by
  have hH := Lower.NewRoute.log_choose_nonneg hmd
  have hL := confidence_log_four hdelta hsmall
  have hlog2 : 0 ≤ Real.log (2 : ℝ) := Real.log_nonneg (by norm_num)
  have harg0 : 0 ≤ Real.log (d.choose m : ℝ) + Real.log (1 / delta) := by linarith
  have harg1 : 0 ≤ Real.log (d.choose m : ℝ) + Real.log (1 / delta) - Real.log 2 := by linarith
  have hD : (0 : ℝ) ≤ (d : ℝ) * T := by positivity
  have hscale := mul_le_mul_of_nonneg_left
    (show Real.log (d.choose m : ℝ) + Real.log (1 / delta) ≤
      4 * (Real.log (d.choose m : ℝ) + Real.log (1 / delta) - Real.log 2) by linarith) hD
  have hs0 := Real.sq_sqrt (mul_nonneg hD harg0)
  have hs1 := Real.sq_sqrt (mul_nonneg hD harg1)
  have hs : Real.sqrt ((d : ℝ) * T * (Real.log (d.choose m : ℝ) + Real.log (1 / delta))) ≤
      2 * Real.sqrt ((d : ℝ) * T * (Real.log (d.choose m : ℝ) + Real.log (1 / delta) - Real.log 2)) := by
    nlinarith [Real.sqrt_nonneg ((d : ℝ) * T * (Real.log (d.choose m : ℝ) + Real.log (1 / delta))),
      Real.sqrt_nonneg ((d : ℝ) * T * (Real.log (d.choose m : ℝ) + Real.log (1 / delta) - Real.log 2))]
  unfold regretRate
  rw [Lower.NewRoute.log_inverse_double hdelta]
  have heq : Real.log (d.choose m : ℝ) + (Real.log (1 / delta) - Real.log 2) =
      Real.log (d.choose m : ℝ) + Real.log (1 / delta) - Real.log 2 := by ring
  rw [heq]
  norm_num at hs ⊢
  linarith

theorem doubled_confidence_horizon_le (d m : ℕ) {delta : ℝ} (hdelta : 0 < delta) :
    Lower.NewRoute.horizon d m (2 * delta) ≤ Lower.NewRoute.horizon d m delta := by
  unfold Lower.NewRoute.horizon
  apply Nat.ceil_mono
  rw [Lower.NewRoute.log_inverse_double hdelta]
  have hlog2 : 0 ≤ Real.log (2 : ℝ) := Real.log_nonneg (by norm_num)
  have hcoeff : (0 : ℝ) ≤ 4 * (d : ℝ) * (min m (d - m) : ℕ) ^ 2 := by positivity
  nlinarith [mul_nonneg hcoeff hlog2]

/-- The two rate statements with strictly separated tail probabilities.
No claim that a lower event of probability exactly delta contradicts an upper
event of probability1-delta is made. -/
theorem matching_high_probability_rates {d m T : ℕ}
    (hm : 1 ≤ m) (hmtop : m ≤ d - 1) (hTpos : 0 < T)
    {delta : ℝ} (hdelta : 0 < delta) (hsmall : delta ≤ (2 : ℝ) ^ (-37 : ℤ))
    (hT : Lower.NewRoute.horizon d m delta ≤ T) :
    (∃ P : Policy d m, ∀ L : Upper.SignedLossProcess d m,
      1 - delta ≤ (Upper.signedRunLaw P L T).real
        {h | Upper.observableSignedRegret L T h ≤ 160 * regretRate d m T delta}) ∧
    (∀ P : Policy d m, ∃ L : LossProcess d m,
      delta < (runLaw P L T).real
        {h | (2 : ℝ) ^ (-44 : ℤ) * regretRate d m T delta ≤ pathRegret L T h}) := by
  have hmd : m ≤ d := by omega
  have hsmall1 : delta ≤ 1 := hsmall.trans (by norm_num)
  have hsmall4 : delta ≤ 1 / 4 := hsmall.trans (by norm_num)
  have hsmall2 : 2 * delta ≤ (2 : ℝ) ^ (-36 : ℤ) := by
    norm_num at hsmall ⊢
    linarith
  constructor
  · refine ⟨Upper.mainAlgorithm T delta hmd, ?_⟩
    intro L
    exact Upper.main_algorithm_regret_high_probability L hm hmtop T hTpos hdelta hsmall1
  · intro P
    obtain ⟨L, _hact, htail⟩ := Lower.NewRoute.lower_bound_explicit
      (by omega : 2 ≤ d) hm hmtop (by positivity : 0 < 2 * delta) hsmall2
      ((doubled_confidence_horizon_le d m hdelta).trans hT) P
    refine ⟨L, (show delta < 2 * delta by linarith).trans_le (htail.trans ?_)⟩
    apply ENNReal.toReal_mono (measure_ne_top _ _)
    apply measure_mono
    intro h hh
    exact (doubled_confidence_rate_comparison hmd hdelta hsmall4).trans hh

end MsetsPaper
