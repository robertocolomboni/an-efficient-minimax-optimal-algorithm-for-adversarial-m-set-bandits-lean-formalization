import MsetsPaper.Upper.MainParameters

/-! # P1: exact lower bound on the chosen learning rate -/

namespace MsetsPaper.Upper

theorem mainLearningRate_lower {d T K delta : ℝ}
    (hd : 1 ≤ d) (hT : 1 ≤ T) (hK : 2 ≤ K)
    (hdelta0 : 0 < delta) (hdelta1 : delta ≤ 1) :
    1 / (256 * d * Real.sqrt T) ≤ mainLearningRate d T K delta := by
  have hd0 : 0 < d := by linarith
  have hT0 : 0 < T := by linarith
  have hsT : 0 < Real.sqrt T := Real.sqrt_pos.mpr hT0
  have hsT1 : 1 ≤ Real.sqrt T := by simpa using Real.sqrt_le_sqrt hT
  have hlog2 : 0 ≤ Real.log (2 / delta) := Real.log_nonneg ((le_div_iff₀ hdelta0).mpr (by linarith))
  have hL : 1 ≤ Real.log (12 * K / delta) := by
    linarith [(main_log_combinations hK hdelta0 hdelta1).2]
  have hs : 1 / (256 * d) ≤ Real.sqrt (Real.log (12 * K / delta) / (320 * d)) := by
    apply Real.le_sqrt_of_sq_le
    have hid : (1 / (256 * d)) ^ 2 = 1 / (65536 * d ^ 2) := by ring
    rw [hid]
    calc
      _ ≤ 1 / (320 * d) := one_div_le_one_div_of_le (by positivity)
        (by nlinarith [sq_nonneg (d - 1)])
      _ ≤ _ := div_le_div_of_nonneg_right hL (by positivity)
  unfold mainLearningRate
  apply le_min
  · apply one_div_le_one_div_of_le (by positivity)
    nlinarith
  · have h := div_le_div_of_nonneg_right hs hsT.le
    have hid : Real.log (12 * K / delta) / (320 * d * T) =
        (Real.log (12 * K / delta) / (320 * d)) / T := by ring
    rw [hid, Real.sqrt_div (by positivity)]
    convert h using 1 <;> ring

theorem mainLearningRate_dimension_time_lower {d T K delta : ℝ}
    (hd : 1 ≤ d) (hT : 1 ≤ T) (hK : 2 ≤ K)
    (hdelta0 : 0 < delta) (hdelta1 : delta ≤ 1) :
    1 / 256 ≤ mainLearningRate d T K delta * d * T := by
  have heta := mainLearningRate_lower hd hT hK hdelta0 hdelta1
  have hsq1 : 1 ≤ Real.sqrt T := Real.one_le_sqrt.mpr hT
  have hsq : Real.sqrt T ≤ T := by
    nlinarith [Real.sq_sqrt (show 0 ≤ T by linarith)]
  have hden : 0 < 256 * d * Real.sqrt T := by positivity
  have hmul := (div_le_iff₀ hden).mp heta
  have hepos := mainLearningRate_pos (by linarith) (by linarith) hK hdelta0 hdelta1
  have hlarge := mul_le_mul_of_nonneg_left hsq
    (mul_nonneg hepos.le (show 0 ≤ d by linarith))
  nlinarith

/-- An explicit witness for the sketch's absorption of its O(1) term.
This also handles delta arbitrarily close to one. -/
theorem main_sketch_constant_absorption {d T K delta : ℝ}
    (hd : 1 ≤ d) (hT : 1 ≤ T) (hK : 2 ≤ K)
    (hdelta0 : 0 < delta) (hdelta1 : delta ≤ 1) :
    1 + Real.log (2 / delta) ≤
      512 * (mainLearningRate d T K delta * d * T) + Real.log (1 / delta) := by
  have hlow := mainLearningRate_dimension_time_lower hd hT hK hdelta0 hdelta1
  have hlog2 : Real.log 2 ≤ 1 := by
    simpa only [show (2 : ℝ) - 1 = 1 by norm_num] using
      Real.log_le_sub_one_of_pos (by norm_num : (0 : ℝ) < 2)
  rw [show 2 / delta = 2 * (1 / delta) by ring,
    Real.log_mul (by norm_num) (by positivity : (1 / delta : ℝ) ≠ 0)]
  linarith

end MsetsPaper.Upper
