import MsetsPaper.Lower.WJCombinatorics
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Real

/-! Explicit parameters for the integer-valued W,J introductory experiment. -/

namespace MsetsPaper.Lower.WJ

noncomputable section

theorem cap_card_eq_time_eighth {d k c T : ℕ} (hd : d = 32 * k)
    (hcap : c * d = 4 * T) : (c : ℝ) * k = (T : ℝ) / 8 := by
  have hdR : (d : ℝ) = 32 * k := by exact_mod_cast hd
  have hcapR : (c : ℝ) * d = 4 * T := by exact_mod_cast hcap
  rw [hdR] at hcapR
  nlinarith

theorem horizon_pos {d k c T : ℕ} (hk : 1 ≤ k) (hd : d = 32 * k)
    (hc : 0 < c) (hcap : c * d = 4 * T) : 0 < T := by
  have hd0 : 0 < d := by omega
  have hp := Nat.mul_pos hc hd0
  omega

theorem log_marked_size_pos {k : ℕ} (hk : 1 ≤ k) : 0 < Real.log (k + 1 : ℕ) :=
  Real.log_pos (by exact_mod_cast (by omega : 1 < k + 1))

theorem log_marked_size_ge_eight_log_two {k : ℕ} (hk : 255 ≤ k) :
    8 * Real.log 2 ≤ Real.log (k + 1 : ℕ) := by
  have hsize : (256 : ℝ) ≤ (k + 1 : ℕ) := by exact_mod_cast (by omega : 256 ≤ k + 1)
  have hlog := Real.log_le_log (by norm_num : (0 : ℝ) < 256) hsize
  have heq : Real.log (256 : ℝ) = 8 * Real.log 2 := by
    rw [show (256 : ℝ) = 2 ^ (8 : ℕ) by norm_num, Real.log_pow]
    norm_num
  simpa only [heq] using hlog

theorem log_marked_size_ge_half_log_arms {d k : ℕ}
    (hk : 32 ≤ k) (hd : d = 32 * k) :
    Real.log d ≤ 2 * Real.log (k + 1 : ℕ) := by
  have hkR : (32 : ℝ) ≤ k := by exact_mod_cast hk
  have hdR : (d : ℝ) = 32 * k := by exact_mod_cast hd
  have hd0 : (0 : ℝ) < d := by rw [hdR]; positivity
  have hsize : (d : ℝ) ≤ ((k + 1 : ℕ) : ℝ) ^ 2 := by
    push_cast
    nlinarith
  have hlog := Real.log_le_log hd0 hsize
  rw [Real.log_pow] at hlog
  norm_num at hlog ⊢
  exact hlog

/-- This literal log(K) parameterization matches the choice in the TeX. -/
def epsilonDimension (d c : ℕ) : ℝ := Real.sqrt (Real.log d / (8192 * c))

theorem epsilonDimension_nonneg (d c : ℕ) : 0 ≤ epsilonDimension d c :=
  Real.sqrt_nonneg _

theorem epsilonDimension_pos {d c : ℕ} (hd : 1 < d) (hc : 0 < c) :
    0 < epsilonDimension d c := by
  exact Real.sqrt_pos.mpr (div_pos (Real.log_pos (by exact_mod_cast hd)) (by positivity))

theorem epsilonDimension_sq_mul_cap {d c : ℕ} (hd : 1 ≤ d) (hc : 0 < c) :
    8192 * epsilonDimension d c ^ 2 * c = Real.log d := by
  have hlog : 0 ≤ Real.log d := Real.log_nonneg (by exact_mod_cast hd)
  have hsq := Real.sq_sqrt (show 0 ≤ Real.log d / (8192 * c) from
    div_nonneg hlog (by positivity))
  change epsilonDimension d c ^ 2 = _ at hsq
  have hmul := (eq_div_iff (show (8192 * (c : ℝ)) ≠ 0 by positivity)).mp hsq
  nlinarith

theorem epsilonDimension_information_budget {d k c : ℕ}
    (hk : 255 ≤ k) (hd : d = 32 * k) (hc : 0 < c) :
    128 * epsilonDimension d c ^ 2 * c + Real.log 2 ≤
      (3 : ℝ) / 16 * Real.log (k + 1 : ℕ) := by
  have hsq := epsilonDimension_sq_mul_cap (by omega : 1 ≤ d) hc
  have hlog := log_marked_size_ge_eight_log_two hk
  have hcompare := log_marked_size_ge_half_log_arms (by omega : 32 ≤ k) hd
  have hpos := (log_marked_size_pos (by omega : 1 ≤ k)).le
  nlinarith

theorem epsilonDimension_small_of_horizon {d k c T : ℕ} (hk : 255 ≤ k)
    (hd : d = 32 * k) (hc : 0 < c) (hcap : c * d = 4 * T)
    (hT : (d : ℝ) * Real.log d ≤ T) : epsilonDimension d c ≤ 1 / 16 := by
  have hd0 : (0 : ℝ) < d := by exact_mod_cast (by omega : 0 < d)
  have hcR : (0 : ℝ) < c := by exact_mod_cast hc
  have hcapR : (c : ℝ) * d = 4 * T := by exact_mod_cast hcap
  have hclog : Real.log d ≤ (c : ℝ) / 4 := by nlinarith
  have hsq := epsilonDimension_sq_mul_cap (by omega : 1 ≤ d) hc
  have he := epsilonDimension_nonneg d c
  have hbound : epsilonDimension d c ^ 2 ≤ (1 : ℝ) / 256 := by nlinarith
  nlinarith

theorem epsilonDimension_regret_threshold {d k c T : ℕ} (hk : 255 ≤ k)
    (hd : d = 32 * k) (hc : 0 < c) (hcap : c * d = 4 * T) :
    (2 : ℝ) ^ (-14 : ℤ) * Real.sqrt ((d : ℝ) * T * Real.log d) ≤
      epsilonDimension d c * T / 8 := by
  have he := epsilonDimension_nonneg d c
  have hsq := epsilonDimension_sq_mul_cap (by omega : 1 ≤ d) hc
  have hd0 : (0 : ℝ) < d := by exact_mod_cast (by omega : 0 < d)
  have hd1 : (1 : ℝ) ≤ d := by exact_mod_cast (by omega : 1 ≤ d)
  have hT0 : (0 : ℝ) ≤ T := Nat.cast_nonneg T
  have hcapR : (c : ℝ) * d = 4 * T := by exact_mod_cast hcap
  have hmul := congrArg (fun x : ℝ => x * d) hsq
  have heq : 32768 * epsilonDimension d c ^ 2 * T = (d : ℝ) * Real.log d := by
    calc
      _ = 8192 * epsilonDimension d c ^ 2 * ((c : ℝ) * d) := by rw [hcapR]; ring
      _ = _ := by nlinarith [hmul]
  have hmulT := congrArg (fun x : ℝ => x * T) heq
  have hrad : 0 ≤ (d : ℝ) * T * Real.log d :=
    mul_nonneg (mul_nonneg hd0.le hT0) (Real.log_nonneg hd1)
  have hroot := Real.sq_sqrt hrad
  have hroot0 := Real.sqrt_nonneg ((d : ℝ) * T * Real.log d)
  have hproduct : 0 ≤ epsilonDimension d c * T := mul_nonneg he hT0
  have hrootbound : Real.sqrt ((d : ℝ) * T * Real.log d) ≤
      2048 * (epsilonDimension d c * T) := by
    nlinarith [sq_nonneg (epsilonDimension d c * T)]
  norm_num
  linarith

end
end MsetsPaper.Lower.WJ
