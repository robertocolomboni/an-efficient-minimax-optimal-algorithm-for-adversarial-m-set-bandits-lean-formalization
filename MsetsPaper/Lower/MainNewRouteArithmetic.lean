import MsetsPaper.Lower.Foundations
import MsetsPaper.Lower.ConfidenceObliviousParameters

/-! # Arithmetic of the new lower-bound assembly

These lemmas express the new manuscript's literal ceiling, minimum action
size, maximum of the two logarithmic terms, and polynomial threshold. They
do not invoke any earlier lower-bound endpoint.
-/

namespace MsetsPaper.Lower.NewRoute

open MsetsLower MsetsLower.Lower MeasureTheory Set
open scoped ENNReal

noncomputable section

def horizon (d m : ℕ) (delta : ℝ) : ℕ :=
  Nat.ceil (64 * (d : ℝ) ^ 2 +
    4 * (d : ℝ) * (min m (d - m) : ℕ) ^ 2 * Real.log (1 / delta))

def thresholdPolynomial (d : ℕ) (delta : ℝ) : ℝ :=
  1 + 64 * (d : ℝ) ^ 2 + 4 * (d : ℝ) ^ 3 * Real.log (1 / delta)

theorem min_size_bounds {d m : ℕ} (hm : 1 ≤ m) (hmtop : m ≤ d - 1) :
    1 ≤ min m (d - m) ∧ 2 * min m (d - m) ≤ d := by
  constructor
  · exact le_min hm (by omega)
  · have h₁ := min_le_left m (d - m)
    have h₂ := min_le_right m (d - m)
    omega

theorem choose_min_size {d m : ℕ} (hmd : m ≤ d) :
    d.choose (min m (d - m)) = d.choose m := by
  by_cases h : m ≤ d - m
  · rw [min_eq_left h]
  · rw [min_eq_right (le_of_not_ge h), Nat.choose_symm hmd]

theorem horizon_requirements {d m T : ℕ} {delta : ℝ}
    (hdelta : 0 < delta) (hsmall : delta ≤ (2 : ℝ) ^ (-36 : ℤ))
    (hT : horizon d m delta ≤ T) :
    64 * d ^ 2 ≤ T ∧
      4 * (d : ℝ) * (min m (d - m) : ℕ) ^ 2 * Real.log (1 / delta) ≤ T := by
  have hlog := (ConfidenceOblivious.log_inverse_positive hdelta hsmall).le
  have hceil := Nat.le_ceil
    (64 * (d : ℝ) ^ 2 +
      4 * (d : ℝ) * (min m (d - m) : ℕ) ^ 2 * Real.log (1 / delta))
  have hcast : (horizon d m delta : ℝ) ≤ T := by exact_mod_cast hT
  change 64 * (d : ℝ) ^ 2 +
    4 * (d : ℝ) * (min m (d - m) : ℕ) ^ 2 * Real.log (1 / delta) ≤
      (horizon d m delta : ℝ) at hceil
  have hsum := hceil.trans hcast
  have hconf : (0 : ℝ) ≤
    4 * (d : ℝ) * (min m (d - m) : ℕ) ^ 2 * Real.log (1 / delta) := by positivity
  constructor
  · have hreal : (64 : ℝ) * d ^ 2 ≤ T := by linarith
    exact_mod_cast hreal
  · linarith [sq_nonneg (d : ℝ)]

theorem half_sum_le_max (H L : ℝ) : (H + L) / 2 ≤ max H L := by
  have hH := le_max_left H L
  have hL := le_max_right H L
  linarith

/-- The last displayed threshold inequality of the new T3 proof. -/
theorem final_threshold_le_max {D H L : ℝ}
    (hD : 0 ≤ D) (hH : 0 ≤ H) (hL : 0 ≤ L) :
    (2 : ℝ) ^ (-43 : ℤ) * Real.sqrt (D * (H + L)) ≤
      (2 : ℝ) ^ (-42 : ℤ) * Real.sqrt (D * max H L) := by
  have hB : 0 ≤ max H L := hH.trans (le_max_left H L)
  have hhalf := half_sum_le_max H L
  have hs₁ := Real.sq_sqrt (show 0 ≤ D * (H + L) by positivity)
  have hs₂ := Real.sq_sqrt (show 0 ≤ D * max H L by positivity)
  have hcompare : D * (H + L) ≤ 4 * (D * max H L) := by
    have h := mul_le_mul_of_nonneg_left (show H + L ≤ 2 * max H L by linarith) hD
    nlinarith [mul_nonneg hD hB]
  have hsqrt : Real.sqrt (D * (H + L)) ≤ 2 * Real.sqrt (D * max H L) := by
    nlinarith [Real.sqrt_nonneg (D * (H + L)), Real.sqrt_nonneg (D * max H L)]
  norm_num
  linarith

theorem horizon_polynomial_bound {d m : ℕ} (hmd : m ≤ d) {delta : ℝ}
    (hdelta : 0 < delta) (hsmall : delta ≤ (2 : ℝ) ^ (-36 : ℤ)) :
    (horizon d m delta : ℝ) ≤ thresholdPolynomial d delta := by
  have hlog := (ConfidenceOblivious.log_inverse_positive hdelta hsmall).le
  have hs : ((min m (d - m) : ℕ) : ℝ) ≤ d := by
    exact_mod_cast (min_le_left m (d - m)).trans hmd
  have hs0 : (0 : ℝ) ≤ min m (d - m) := Nat.cast_nonneg _
  have hd0 : (0 : ℝ) ≤ d := Nat.cast_nonneg _
  have hsq : ((min m (d - m) : ℕ) : ℝ) ^ 2 ≤ (d : ℝ) ^ 2 := by nlinarith
  have hprod := mul_le_mul_of_nonneg_left hsq
    (show (0 : ℝ) ≤ 4 * (d : ℝ) * Real.log (1 / delta) by positivity)
  have hnonneg : (0 : ℝ) ≤ 64 * (d : ℝ) ^ 2 +
      4 * (d : ℝ) * (min m (d - m) : ℕ) ^ 2 * Real.log (1 / delta) := by positivity
  have hceil := (Nat.ceil_lt_add_one hnonneg).le
  change (horizon d m delta : ℝ) ≤ _ at hceil
  dsimp [thresholdPolynomial]
  nlinarith

theorem horizon_one {K : ℕ} (hK : 2 ≤ K) (delta : ℝ) :
    horizon K 1 delta = Nat.ceil
      (64 * (K : ℝ) ^ 2 + 4 * (K : ℝ) * Real.log (1 / delta)) := by
  simp [horizon, min_eq_left (by omega : 1 ≤ K - 1)]

/-- The confidence-level substitution mentioned after the headline theorem. -/
theorem log_inverse_double {delta : ℝ} (hdelta : 0 < delta) :
    Real.log (1 / (2 * delta)) = Real.log (1 / delta) - Real.log 2 := by
  rw [show 1 / (2 * delta) = (1 / delta) / 2 by ring,
    Real.log_div (by positivity : (1 / delta : ℝ) ≠ 0) (by norm_num)]

end

end MsetsPaper.Lower.NewRoute
