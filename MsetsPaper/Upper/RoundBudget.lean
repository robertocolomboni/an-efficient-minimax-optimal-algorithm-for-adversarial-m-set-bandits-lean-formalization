import MsetsPaper.Upper.AlgorithmParameters
import MsetsPaper.Upper.ProjectionProgram

/-! # The chosen learning rate removes confidence from the running-time bound

The constant 600 is deliberately conservative: it bounds only computational
work, not regret. The final budget is polynomial in d and log T, independently
of delta. No lower bound on delta is needed.
-/

namespace MsetsPaper.Upper.RoundProgram

noncomputable section

theorem projection_log_ratio_main (d : ℕ) (hd : 1 ≤ d) (T K delta : ℝ)
    (hT : 1 ≤ T) (hK : 2 ≤ K) (hd0 : 0 < delta) (hd1 : delta ≤ 1) :
    let eta := mainLearningRate d T K delta
    Real.log (projectionRadius d T /
      (projectionTolerance d eta T / (2 * Real.sqrt (d : ℝ)))) ≤
        600 + 6 * Real.log (d : ℝ) + 6 * Real.log T := by
  dsimp only
  let eta := mainLearningRate d T K delta
  have hdR : (1 : ℝ) ≤ d := by exact_mod_cast hd
  have hdpos : (0 : ℝ) < d := by linarith
  have hTpos : 0 < T := by linarith
  have heta : 0 < eta := mainLearningRate_pos hdpos hTpos hK hd0 hd1
  have hetamax : eta ≤ 1 / (256 * (d : ℝ)) := min_le_left _ _
  have hR : 0 < projectionRadius d T := by unfold projectionRadius; positivity
  have htau : 0 < projectionTolerance d eta T :=
    (projectionTolerance_pos_le_radius d hd eta T heta hetamax hT).1
  change Real.log (projectionRadius d T /
      (projectionTolerance d eta T / (2 * Real.sqrt (d : ℝ)))) ≤ _
  rw [projection_log_radius_ratio d hd _ _ hR htau]
  have hlo := mainLearningRate_lower hdR hT hK hd0 hd1
  have hden : 0 < 256 * (d : ℝ) * Real.sqrt T := by positivity
  have hlogeta := Real.log_le_log (one_div_pos.mpr hden) hlo
  rw [Real.log_div (by norm_num : (1 : ℝ) ≠ 0) hden.ne', Real.log_one,
    Real.log_mul (by positivity : 256 * (d : ℝ) ≠ 0) (by positivity : Real.sqrt T ≠ 0),
    Real.log_mul (by norm_num : (256 : ℝ) ≠ 0) hdpos.ne', Real.log_sqrt hTpos.le] at hlogeta
  have hlogR : Real.log (projectionRadius d T) =
      Real.log 4 + Real.log (d : ℝ) + Real.log T := by
    unfold projectionRadius
    rw [Real.log_mul (by positivity : 4 * (d : ℝ) ≠ 0) hTpos.ne',
      Real.log_mul (by norm_num : (4 : ℝ) ≠ 0) hdpos.ne']
  have hlogtau : Real.log (projectionTolerance d eta T) =
      2 * (Real.log eta - Real.log T) - (Real.log 2 + 2 * Real.log (projectionRadius d T)) := by
    unfold projectionTolerance
    rw [Real.log_div (by positivity : (eta / T)^2 ≠ 0)
        (by positivity : 2 * (projectionRadius d T)^2 ≠ 0),
      Real.log_pow, Real.log_div heta.ne' hTpos.ne',
      Real.log_mul (by norm_num : (2 : ℝ) ≠ 0) (by positivity : (projectionRadius d T)^2 ≠ 0),
      Real.log_pow]
    norm_num
  have h256 : Real.log 256 ≤ 255 := by
    linarith [Real.log_le_sub_one_of_pos (by norm_num : (0 : ℝ) < 256)]
  have h4 : Real.log 4 ≤ 3 := by
    linarith [Real.log_le_sub_one_of_pos (by norm_num : (0 : ℝ) < 4)]
  have h2 : Real.log 2 ≤ 1 := by
    linarith [Real.log_le_sub_one_of_pos (by norm_num : (0 : ℝ) < 2)]
  have hdlog : 0 ≤ Real.log (d : ℝ) := Real.log_nonneg hdR
  change _ ≤ Real.log eta at hlogeta
  rw [hlogtau, hlogR]
  linarith

theorem projectionOracleBudget_main_bound (d : ℕ) (hd : 1 ≤ d) (T K delta : ℝ)
    (hT : 1 ≤ T) (hK : 2 ≤ K) (hd0 : 0 < delta) (hd1 : delta ≤ 1) :
    (projectionOracleBudget d (mainLearningRate d T K delta) T : ℝ) ≤
      8 * (d : ℝ)^2 * (600 + 6 * Real.log (d : ℝ) + 6 * Real.log T) + 2 := by
  have hdpos : (0 : ℝ) < d := by exact_mod_cast (show 0 < d by omega)
  have heta := mainLearningRate_pos hdpos (by linarith : 0 < T) hK hd0 hd1
  have hb := projectionOracleBudget_bound d hd (mainLearningRate d T K delta) T
    heta (min_le_left _ _) hT
  have hl := projection_log_ratio_main d hd T K delta hT hK hd0 hd1
  have hm := mul_le_mul_of_nonneg_left hl (by positivity : 0 ≤ 8 * (d : ℝ)^2)
  linarith

/-- The literal pair of logarithms appearing in P1's computational paragraph. -/
theorem projection_log_parameters_main (d : ℕ) (hd : 1 ≤ d) (T K delta : ℝ)
    (hT : 1 ≤ T) (hK : 2 ≤ K) (hd0 : 0 < delta) (hd1 : delta ≤ 1) :
    Real.log (projectionRadius d T) +
      Real.log (1 / projectionTolerance d (mainLearningRate d T K delta) T) ≤
        600 + 6 * Real.log (d : ℝ) + 6 * Real.log T := by
  have hdR : (1 : ℝ) ≤ d := by exact_mod_cast hd
  have hdpos : (0 : ℝ) < d := by linarith
  have heta := mainLearningRate_pos hdpos (by linarith : 0 < T) hK hd0 hd1
  have htau := (projectionTolerance_pos_le_radius d hd _ T heta (min_le_left _ _) hT).1
  have hR : 0 < projectionRadius d T := by unfold projectionRadius; positivity
  have h := projection_log_ratio_main d hd T K delta hT hK hd0 hd1
  dsimp only at h
  rw [projection_log_radius_ratio d hd _ _ hR htau] at h
  rw [Real.log_div (by norm_num : (1 : ℝ) ≠ 0) htau.ne', Real.log_one]
  have h2 : 0 ≤ Real.log 2 := Real.log_nonneg (by norm_num)
  have hdlog := Real.log_nonneg hdR
  linarith

/-- Absorb log d into d so the final expression is literally a polynomial
in d and log T, not merely bounded by one. -/
theorem projectionOracleBudget_polynomial_bound (d : ℕ) (hd : 1 ≤ d) (T K delta : ℝ)
    (hT : 1 ≤ T) (hK : 2 ≤ K) (hd0 : 0 < delta) (hd1 : delta ≤ 1) :
    (projectionOracleBudget d (mainLearningRate d T K delta) T : ℝ) ≤
      8 * (d : ℝ)^2 * (600 + 6 * (d : ℝ) + 6 * Real.log T) + 2 := by
  have h := projectionOracleBudget_main_bound d hd T K delta hT hK hd0 hd1
  have hdpos : (0 : ℝ) < d := by exact_mod_cast (show 0 < d by omega)
  have hlog : Real.log (d : ℝ) ≤ d := by linarith [Real.log_le_sub_one_of_pos hdpos]
  have hm := mul_le_mul_of_nonneg_left hlog (by positivity : (0 : ℝ) ≤ 48 * (d : ℝ)^2)
  nlinarith

end

end MsetsPaper.Upper.RoundProgram
