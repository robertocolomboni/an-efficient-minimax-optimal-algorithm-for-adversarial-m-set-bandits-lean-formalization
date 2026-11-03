import MsetsPaper.Alignment.UpperSketchBounds

/-! The introduction's unscaled O(dT) second-moment claim, in an explicit
large-horizon regime, and its O(sqrt(dT log(K/delta))) regret contribution. -/

noncomputable section
open MeasureTheory MsetsLower MsetsPaper.Upper MsetsPaper.Probability
open scoped BigOperators

namespace MsetsPaper.Alignment

theorem mainLearningRate_eq_sqrt_of_large_horizon {d T K delta : ℝ}
    (hd : 0 < d) (hT : 0 < T) (hK : 2 ≤ K)
    (hdelta0 : 0 < delta) (hdelta1 : delta ≤ 1)
    (hlarge : (256 ^ 2 / 320 : ℝ) * d * Real.log (12 * K / delta) ≤ T) :
    mainLearningRate d T K delta = Real.sqrt (Real.log (12 * K / delta) / (320 * d * T)) := by
  have hmul := mul_le_mul_of_nonneg_right hlarge (show 0 ≤ 320 * d by positivity)
  have hfrac : Real.log (12 * K / delta) / (320 * d * T) ≤ 1 / (65536 * d ^ 2) := by
    apply (div_le_div_iff₀ (by positivity) (by positivity)).mpr
    nlinarith
  have hroot : Real.sqrt (Real.log (12 * K / delta) / (320 * d * T)) ≤ 1 / (256 * d) := by
    apply Real.sqrt_le_iff.mpr
    refine ⟨by positivity, ?_⟩
    convert hfrac using 1 <;> ring
  exact min_eq_right hroot

theorem mainLearningRate_large_horizon_square {d T K delta : ℝ}
    (hd : 0 < d) (hT : 0 < T) (hK : 2 ≤ K)
    (hdelta0 : 0 < delta) (hdelta1 : delta ≤ 1)
    (hlarge : (256 ^ 2 / 320 : ℝ) * d * Real.log (12 * K / delta) ≤ T) :
    320 * (mainLearningRate d T K delta) ^ 2 * d * T = Real.log (12 * K / delta) := by
  have hs := Real.sq_sqrt (show 0 ≤ Real.log (12 * K / delta) / (320 * d * T) from
    div_nonneg (main_log_positive hK hdelta0 hdelta1).le (by positivity))
  rw [← mainLearningRate_eq_sqrt_of_large_horizon hd hT hK hdelta0 hdelta1 hlarge] at hs
  have he := (eq_div_iff (show (320 * d * T : ℝ) ≠ 0 by positivity)).mp hs
  nlinarith

theorem secondMoment_large_horizon_arithmetic {d T K delta Z : ℝ}
    (hd : 1 ≤ d) (hT : 1 ≤ T) (hK : 2 ≤ K)
    (hdelta0 : 0 < delta) (hdelta1 : delta ≤ 1)
    (hlarge : (256 ^ 2 / 320 : ℝ) * d * Real.log (12 * K / delta) ≤ T)
    (hZ : 2 * mainLearningRate d T K delta * Z ≤
      544 * mainLearningRate d T K delta * d * T + Real.log (1 / delta)) :
    Z ≤ 273 * d * T ∧
      2 * mainLearningRate d T K delta * Z ≤ 69 * Real.sqrt (d * T * Real.log (K / delta)) := by
  let eta := mainLearningRate d T K delta
  have heta : 0 < eta := mainLearningRate_pos (by linarith) (by linarith) hK hdelta0 hdelta1
  have hsmall : eta ≤ 1 / 256 := (mainLearningRate_le_cap _ _ _ _).trans
    (one_div_le_one_div_of_le (by norm_num : (0 : ℝ) < 256) (by linarith))
  have hs := mainLearningRate_large_horizon_square (by linarith : 0 < d)
    (by linarith : 0 < T) hK hdelta0 hdelta1 hlarge
  have hlog : Real.log (1 / delta) ≤ Real.log (12 * K / delta) := by
    apply Real.log_le_log (by positivity)
    exact div_le_div_of_nonneg_right (by linarith) hdelta0.le
  have hp := mul_le_mul_of_nonneg_right (show 320 * eta ≤ 2 by linarith)
    (show 0 ≤ eta * d * T by positivity)
  have habs : Real.log (1 / delta) ≤ 2 * eta * d * T := by
    dsimp [eta] at *
    nlinarith
  have hbudget : Z ≤ 273 * d * T := by
    apply (mul_le_mul_iff_left₀ (show 0 < 2 * eta by positivity)).mp
    dsimp [eta] at *
    nlinarith
  refine ⟨hbudget, ?_⟩
  have hLH := log_twelve_ratio_le_five hK hdelta0 hdelta1
  have hmul := mul_le_mul_of_nonneg_left hLH (show 0 ≤ d * T by positivity)
  have hs' := congrArg (fun r : ℝ ↦ r * (d * T)) hs
  have hsqrt := Real.sq_sqrt (show 0 ≤ d * T * Real.log (K / delta) by
    have hH : 0 ≤ Real.log (K / delta) := by
      apply Real.log_nonneg
      exact (le_div_iff₀ hdelta0).mpr (by linarith)
    positivity)
  have hscale : 8 * eta * d * T ≤ Real.sqrt (d * T * Real.log (K / delta)) := by
    apply (sq_le_sq₀ (by positivity) (Real.sqrt_nonneg _)).mp
    dsimp [eta] at *
    nlinarith
  have hscaled := mul_le_mul_of_nonneg_left hbudget (show 0 ≤ 2 * eta by positivity)
  change 2 * eta * Z ≤ _
  nlinarith [Real.sqrt_nonneg (d * T * Real.log (K / delta))]

/-- The unscaled moment sum and its actual OMD contribution are controlled
on the same event of probability at least1-delta/2 for the concrete algorithm. -/
theorem algorithm_secondMoment_large_horizon
    {d m : ℕ} (L : SignedLossProcess d m) (hmpos : 1 ≤ m) (hmtop : m ≤ d - 1)
    (T : ℕ) (hT : 0 < T) {delta : ℝ} (hdelta0 : 0 < delta) (hdelta1 : delta < 1)
    (hlarge : (256 ^ 2 / 320 : ℝ) * d * Real.log (12 * (Nat.choose d m : ℝ) / delta) ≤ T) :
    let eta := mainLearningRate d T (Nat.choose d m) delta
    let theta := ellipsoidAlgorithmParameters (d := d) (m := m) eta T
    1 - delta / 2 ≤ (signedRunLaw (mainAlgorithm T delta (by omega)) L T).real
      {h | observablePathSum (observableSurrogateSecondMoment theta L eta) T h ≤ 273 * d * T ∧
        2 * eta * observablePathSum (observableSurrogateSecondMoment theta L eta) T h ≤
          69 * Real.sqrt ((d : ℝ) * T * Real.log ((Nat.choose d m : ℝ) / delta))} := by
  have hb := UpperSketch.algorithm_sketch_estimated_loss_observable L hmpos hmtop T hT hdelta0 hdelta1
  apply hb.trans
  refine measureReal_mono ?_ (measure_ne_top _ _)
  intro h hh
  exact secondMoment_large_horizon_arithmetic
    (by exact_mod_cast (show 1 ≤ d by omega)) (by exact_mod_cast hT)
    (by exact_mod_cast action_count_ge_two hmpos hmtop)
    hdelta0 hdelta1.le hlarge hh.2.1

end MsetsPaper.Alignment
