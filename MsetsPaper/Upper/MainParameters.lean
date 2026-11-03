import Mathlib.Analysis.Real.Sqrt
import Mathlib.Analysis.Complex.ExponentialBounds
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Tactic

/-!
# T1: exact learning-rate case split and numerical constants

These are arithmetic implications used after the probabilistic regret bound,
not a certificate of that bound or of the algorithm. The two branches retain
the manuscript's constants 160 and 64.
-/

namespace MsetsPaper.Upper

noncomputable section

def mainLearningRate (d T K delta : ℝ) : ℝ :=
  min (1 / (256 * d)) (Real.sqrt (Real.log (12 * K / delta) / (320 * d * T)))

theorem action_count_ge_two {d m : ℕ} (hmpos : 1 ≤ m) (hmtop : m ≤ d - 1) :
    2 ≤ Nat.choose d m := by
  have h1 := Nat.choose_pos (show m - 1 ≤ d - 1 by omega)
  have h2 := Nat.choose_pos hmtop
  have heq : Nat.choose d m = Nat.choose (d - 1) (m - 1) + Nat.choose (d - 1) m := by
    have h := Nat.choose_succ_succ' (d - 1) (m - 1)
    simpa only [Nat.sub_add_cancel (show 1 ≤ d by omega), Nat.sub_add_cancel hmpos] using h
  omega

theorem log_twelve_ratio_le_five {K delta : ℝ} (hK : 2 ≤ K)
    (hd0 : 0 < delta) (hd1 : delta ≤ 1) :
    Real.log (12 * K / delta) ≤ 5 * Real.log (K / delta) := by
  have hK0 : 0 < K := by linarith
  have hr : 2 ≤ K / delta := (le_div_iff₀ hd0).mpr (by nlinarith)
  have hr0 : 0 < K / delta := by positivity
  have hfour : (12 : ℝ) ≤ (K / delta) ^ 4 := by
    nlinarith [sq_nonneg ((K / delta) ^ 2 - 4)]
  have hlog := Real.log_le_log (by norm_num : (0 : ℝ) < 12) hfour
  rw [Real.log_pow] at hlog
  have hid : 12 * K / delta = 12 * (K / delta) := by ring
  rw [hid, Real.log_mul (by norm_num) hr0.ne']
  norm_num at hlog
  linarith

theorem main_log_positive {K delta : ℝ} (hK : 2 ≤ K)
    (hd0 : 0 < delta) (hd1 : delta ≤ 1) :
    0 < Real.log (12 * K / delta) := by
  apply Real.log_pos
  apply (one_lt_div hd0).mpr
  nlinarith

theorem mainLearningRate_pos {d T K delta : ℝ} (hd : 0 < d) (hT : 0 < T)
    (hK : 2 ≤ K) (hdelta0 : 0 < delta) (hdelta1 : delta ≤ 1) :
    0 < mainLearningRate d T K delta := by
  have hL := main_log_positive hK hdelta0 hdelta1
  unfold mainLearningRate
  positivity

theorem mainLearningRate_le_cap (d T K delta : ℝ) :
    mainLearningRate d T K delta ≤ 1 / (256 * d) := min_le_left _ _

theorem mainLearningRate_parameter_constraints {d T K delta : ℝ}
    (hd : 1 ≤ d) (hT : 1 ≤ T) (hK : 2 ≤ K)
    (hdelta0 : 0 < delta) (hdelta1 : delta ≤ 1) :
    0 < mainLearningRate d T K delta ∧
    mainLearningRate d T K delta ≤ 1 / 64 ∧
    0 < 128 * mainLearningRate d T K delta * d ∧
    128 * mainLearningRate d T K delta * d ≤ 1 / 2 ∧
    0 < mainLearningRate d T K delta / T := by
  have hd0 : 0 < d := by linarith
  have hT0 : 0 < T := by linarith
  have heta := mainLearningRate_pos hd0 hT0 hK hdelta0 hdelta1
  have hcap := mainLearningRate_le_cap d T K delta
  have hsmall : mainLearningRate d T K delta ≤ 1 / 64 := by
    apply hcap.trans
    apply one_div_le_one_div_of_le (by norm_num : (0 : ℝ) < 64)
    linarith
  have hprod := (le_div_iff₀ (show 0 < 256 * d by positivity)).mp hcap
  exact ⟨heta, hsmall, by positivity, by nlinarith, by positivity⟩

theorem main_log_combinations {K delta : ℝ} (hK : 2 ≤ K)
    (hd0 : 0 < delta) (hd1 : delta ≤ 1) :
    Real.log K + Real.log (4 * K / delta) ≤ 2 * Real.log (12 * K / delta) ∧
      1 + Real.log (2 / delta) ≤ Real.log (12 * K / delta) := by
  have hK0 : 0 < K := by linarith
  constructor
  · have h1 : Real.log K ≤ Real.log (12 * K / delta) := by
      apply Real.log_le_log hK0
      apply (le_div_iff₀ hd0).mpr
      nlinarith
    have h2 : Real.log (4 * K / delta) ≤ Real.log (12 * K / delta) := by
      apply Real.log_le_log (by positivity)
      apply div_le_div_of_nonneg_right _ hd0.le
      nlinarith
    linarith
  · have he : Real.exp 1 * (2 / delta) ≤ 12 * K / delta := by
      rw [← mul_div_assoc]
      apply div_le_div_of_nonneg_right _ hd0.le
      nlinarith [Real.exp_one_lt_three]
    have h := Real.log_le_log (show 0 < Real.exp 1 * (2 / delta) by positivity) he
    rw [Real.log_mul (Real.exp_pos _).ne' (ne_of_gt (show 0 < 2 / delta by positivity)),
      Real.log_exp] at h
    exact h

theorem main_master_simplification {d T K delta eta R : ℝ}
    (hd : 0 ≤ d) (hT : 0 ≤ T) (hK : 2 ≤ K)
    (hdelta0 : 0 < delta) (hdelta1 : delta ≤ 1)
    (heta : 0 < eta) (heta1 : eta ≤ 1)
    (hR : R ≤ (Real.log K + Real.log (4 * K / delta)) / eta + 1 +
      286 * eta * d * T + Real.log (2 / delta)) :
    R ≤ 3 * Real.log (12 * K / delta) / eta + 320 * eta * d * T := by
  have hlogs := main_log_combinations hK hdelta0 hdelta1
  have hL := (main_log_positive hK hdelta0 hdelta1).le
  have hnum := div_le_div_of_nonneg_right hlogs.1 heta.le
  have hLeta : Real.log (12 * K / delta) ≤ Real.log (12 * K / delta) / eta := by
    apply (le_div_iff₀ heta).mpr
    nlinarith [mul_le_mul_of_nonneg_left heta1 hL]
  have hnonneg : 0 ≤ eta * d * T := by positivity
  have hid : 3 * Real.log (12 * K / delta) / eta =
      2 * Real.log (12 * K / delta) / eta + Real.log (12 * K / delta) / eta := by ring
  rw [hid]
  linarith

theorem sqrt_rate_expression {A L : ℝ} (hA : 0 < A) (hL : 0 < L) :
    3 * L / Real.sqrt (L / A) + A * Real.sqrt (L / A) =
      4 * Real.sqrt (A * L) := by
  rw [Real.sqrt_div hL.le]
  calc
    _ = 3 * (L / Real.sqrt L) * Real.sqrt A + (A / Real.sqrt A) * Real.sqrt L := by
      rw [div_div_eq_mul_div]
      ring
    _ = _ := by rw [Real.div_sqrt, Real.div_sqrt, Real.sqrt_mul hA.le]; ring

theorem main_sqrt_branch {d T L H R : ℝ} (hd : 0 < d) (hT : 0 < T)
    (hL : 0 < L) (hLH : L ≤ 5 * H)
    (hR : R ≤ 3 * L / Real.sqrt (L / (320 * d * T)) +
      320 * d * T * Real.sqrt (L / (320 * d * T))) :
    R ≤ 160 * Real.sqrt (d * T * H) := by
  rw [sqrt_rate_expression (by positivity) hL] at hR
  apply hR.trans
  have hH : 0 < H := by linarith
  have h1 := Real.sq_sqrt (show 0 ≤ 320 * d * T * L by positivity)
  have h2 := Real.sq_sqrt (show 0 ≤ d * T * H by positivity)
  have hprod := mul_le_mul_of_nonneg_left hLH (show 0 ≤ 5120 * d * T by positivity)
  nlinarith [Real.sqrt_nonneg (320 * d * T * L), Real.sqrt_nonneg (d * T * H)]

theorem cap_branch_horizon {d T L : ℝ} (hd : 0 < d) (hT : 0 < T) (hL : 0 < L)
    (hcap : 1 / (256 * d) ≤ Real.sqrt (L / (320 * d * T))) :
    T ≤ (256 ^ 2 / 320 : ℝ) * d * L := by
  have hsq : (1 / (256 * d)) ^ 2 ≤ L / (320 * d * T) := by
    nlinarith [Real.sq_sqrt (show 0 ≤ L / (320 * d * T) by positivity),
      Real.sqrt_nonneg (L / (320 * d * T)),
      show 0 < 1 / (256 * d) by positivity]
  have hid : (1 / (256 * d)) ^ 2 = 1 / (65536 * d ^ 2) := by ring
  rw [hid] at hsq
  have h := (div_le_div_iff₀ (show 0 < 65536 * d ^ 2 by positivity)
    (show 0 < 320 * d * T by positivity)).mp hsq
  apply (mul_le_mul_iff_right₀ (show 0 < 320 * d by positivity)).mp
  nlinarith

theorem main_cap_branch {d T L H R : ℝ} (hd : 0 < d) (hT : 0 < T)
    (hL : 0 < L) (hLH : L ≤ 5 * H)
    (hcap : 1 / (256 * d) ≤ Real.sqrt (L / (320 * d * T)))
    (hR : R ≤ 2 * T) : R ≤ 64 * Real.sqrt (d * T * H) := by
  have hTbound := cap_branch_horizon hd hT hL hcap
  have hH : 0 < H := by linarith
  have hLscaled := mul_le_mul_of_nonneg_left hLH (show 0 ≤ (256 ^ 2 / 320 : ℝ) * d by positivity)
  have hTfinal : T ≤ 1024 * d * H := by nlinarith
  have hmul := mul_le_mul_of_nonneg_right hTfinal hT.le
  have hsqrt := Real.sq_sqrt (show 0 ≤ d * T * H by positivity)
  apply hR.trans
  nlinarith [Real.sqrt_nonneg (d * T * H)]

/-- The cap branch's intermediate coefficient, before using L<=5H. -/
theorem main_cap_branch_intermediate {d T L R : ℝ} (hd : 0 < d) (hT : 0 < T)
    (hL : 0 < L) (hcap : 1 / (256 * d) ≤ Real.sqrt (L / (320 * d * T)))
    (hR : R ≤ 2 * T) : R ≤ (512 / Real.sqrt 320) * Real.sqrt (d * T * L) := by
  have hTbound := cap_branch_horizon hd hT hL hcap
  have hprod := mul_le_mul_of_nonneg_right hTbound hT.le
  have h320 := Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 320)
  have h320scaled := congrArg (fun z : ℝ ↦ 4 * T ^ 2 * z) h320
  have hsqrt := Real.sq_sqrt (show 0 ≤ d * T * L by positivity)
  have hs320 : 0 < Real.sqrt 320 := by positivity
  have hscaled : 2 * T * Real.sqrt 320 ≤ 512 * Real.sqrt (d * T * L) := by
    nlinarith [Real.sqrt_nonneg (d * T * L)]
  apply hR.trans
  rw [div_mul_eq_mul_div]
  exact (le_div_iff₀ hs320).mpr hscaled

theorem mainLearningRate_regret_constant {d T K delta R : ℝ}
    (hd : 0 < d) (hT : 0 < T) (hK : 2 ≤ K)
    (hdelta0 : 0 < delta) (hdelta1 : delta ≤ 1)
    (htrivial : R ≤ 2 * T)
    (hmaster : R ≤ 3 * Real.log (12 * K / delta) / mainLearningRate d T K delta +
      320 * mainLearningRate d T K delta * d * T) :
    R ≤ 160 * Real.sqrt (d * T * (Real.log K + Real.log (1 / delta))) := by
  have hL := main_log_positive hK hdelta0 hdelta1
  have hLH := log_twelve_ratio_le_five hK hdelta0 hdelta1
  have hfinal : R ≤ 160 * Real.sqrt (d * T * Real.log (K / delta)) := by
    by_cases hcap : 1 / (256 * d) ≤ Real.sqrt (Real.log (12 * K / delta) / (320 * d * T))
    · have h := main_cap_branch hd hT hL hLH hcap htrivial
      exact h.trans (by nlinarith [Real.sqrt_nonneg (d * T * Real.log (K / delta))])
    · have heq : mainLearningRate d T K delta =
          Real.sqrt (Real.log (12 * K / delta) / (320 * d * T)) :=
        min_eq_right (le_of_lt (lt_of_not_ge hcap))
      rw [heq] at hmaster
      apply main_sqrt_branch hd hT hL hLH
      nlinarith [hmaster]
  have hK0 : K ≠ 0 := by linarith
  simpa only [Real.log_div hK0 hdelta0.ne', one_div, Real.log_inv, sub_eq_add_neg] using hfinal

end

end MsetsPaper.Upper
