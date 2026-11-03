import MsetsLower.Prelude
import Mathlib.Analysis.Real.Sqrt

/-!
# Arithmetic for the confidence construction

This module records the numerical identities and deterministic inequalities in
the proof of `prop:lower-confidence`.  The probabilistic construction and the
sequential change of measure live in separate modules.
-/

namespace MsetsLower.Lower.Confidence

noncomputable section

/-- The constant `c₁=2⁻¹²` from `eq:lower-confidence-parameters`. -/
def confidenceConstant : Real := 1 / (2 : Real) ^ 12

/-- The planted gap from `eq:lower-confidence-parameters`. -/
def confidenceDelta (N L T : Real) : Real :=
  confidenceConstant * Real.sqrt (N * L / T)

/-- The stopping budget from `eq:lower-confidence-parameters`. -/
def confidenceBudget (N L T : Real) : Real :=
  confidenceDelta N L T * T / 16

/-- The three literal definitions in `eq:lower-confidence-parameters`, kept in
one theorem so the proof seam cannot be certified by mentioning only `Delta`.
-/
theorem lower_confidence_parameters (N L T : Real) :
    confidenceConstant = 1 / (2 : Real) ^ 12 ∧
      confidenceDelta N L T =
        confidenceConstant * Real.sqrt (N * L / T) ∧
      confidenceBudget N L T = confidenceDelta N L T * T / 16 := by
  exact ⟨rfl, rfl, rfl⟩

theorem confidenceConstant_pos : 0 < confidenceConstant := by
  norm_num [confidenceConstant]

theorem confidenceConstant_div_eight :
    confidenceConstant / 8 = 1 / (2 : Real) ^ 15 := by
  norm_num [confidenceConstant]

theorem confidenceConstant_sq_scaled :
    (2 : Real) ^ 16 * confidenceConstant ^ 2 = 1 / (2 : Real) ^ 8 := by
  norm_num [confidenceConstant]

/-- The two inequalities in `eq:lower-confidence-delta-small`, derived from
the horizon hypothesis and `N ≤ n`.  Variables are real-valued here so that
the result can be reused after coercing the discrete parameters. -/
theorem confidence_delta_small
    {n k N T L : Real}
    (hk : 1 ≤ k) (hNn : N ≤ n)
    (hT : 0 < T) (hL : 0 ≤ L)
    (hhorizon : 4 * n * k ^ 2 * L ≤ T) :
    k * confidenceDelta N L T ≤ confidenceConstant / 2 ∧
      confidenceDelta N L T ≤ 1 / (2 : Real) ^ 13 := by
  have hkpos : 0 < k := lt_of_lt_of_le zero_lt_one hk
  have hden : 0 < 4 * k ^ 2 := by positivity
  have hscaled : (N * L) * (4 * k ^ 2) ≤ T := by
    calc
      (N * L) * (4 * k ^ 2) ≤ (n * L) * (4 * k ^ 2) := by
        gcongr
      _ = 4 * n * k ^ 2 * L := by ring
      _ ≤ T := hhorizon
  have hdiv : N * L / T ≤ 1 / (4 * k ^ 2) := by
    apply (div_le_iff₀ hT).2
    calc
      N * L ≤ T / (4 * k ^ 2) := (le_div_iff₀ hden).2 hscaled
      _ = (1 / (4 * k ^ 2)) * T := by field_simp
  have hquarter : 1 / (4 * k ^ 2) = (1 / (2 * k)) ^ 2 := by
    field_simp
    ring
  have hsqrt : Real.sqrt (N * L / T) ≤ 1 / (2 * k) := by
    apply Real.sqrt_le_iff.mpr
    constructor
    · positivity
    · rwa [← hquarter]
  have hk_sqrt : k * Real.sqrt (N * L / T) ≤ 1 / 2 := by
    calc
      k * Real.sqrt (N * L / T) ≤ k * (1 / (2 * k)) :=
        mul_le_mul_of_nonneg_left hsqrt hkpos.le
      _ = 1 / 2 := by field_simp
  have hdelta_nonneg : 0 ≤ confidenceDelta N L T := by
    exact mul_nonneg confidenceConstant_pos.le (Real.sqrt_nonneg _)
  constructor
  · dsimp [confidenceDelta]
    calc
      k * (confidenceConstant * Real.sqrt (N * L / T)) =
          confidenceConstant * (k * Real.sqrt (N * L / T)) := by ring
      _ ≤ confidenceConstant * (1 / 2) :=
        mul_le_mul_of_nonneg_left hk_sqrt confidenceConstant_pos.le
      _ = confidenceConstant / 2 := by ring
  · have hdelta_le : confidenceDelta N L T ≤ confidenceConstant / 2 := by
      calc
        confidenceDelta N L T ≤ k * confidenceDelta N L T := by
          nlinarith
        _ ≤ confidenceConstant / 2 := by
          dsimp [confidenceDelta]
          calc
            k * (confidenceConstant * Real.sqrt (N * L / T)) =
                confidenceConstant * (k * Real.sqrt (N * L / T)) := by ring
            _ ≤ confidenceConstant * (1 / 2) :=
              mul_le_mul_of_nonneg_left hk_sqrt confidenceConstant_pos.le
            _ = confidenceConstant / 2 := by ring
    norm_num [confidenceConstant] at hdelta_le ⊢
    exact hdelta_le

/-- The elementary counting step below `eq:lower-confidence-average-score`:
an average at least `1/4`, with the displayed two-level upper bound, forces at
least a `2/15` fraction of large scores. -/
theorem large_score_fraction
    {alpha : Real}
    (haverage : (1 : Real) / 4 ≤
      alpha * ((17 : Real) / 16) + (1 - alpha) * ((1 : Real) / 8)) :
    (2 : Real) / 15 ≤ alpha := by
  linarith

/-- The manuscript deliberately spends a factor two instead of the sharper
`1/√2` when passing from `N ≥ n/2` to a square-root lower bound. -/
theorem half_sqrt_le_sqrt_of_half_le
    {n N q : Real}
    (hn : 0 ≤ n) (hq : 0 ≤ q) (hN : n / 2 ≤ N) :
    (1 / 2 : Real) * Real.sqrt (n * q) ≤ Real.sqrt (N * q) := by
  have hinside : (n * q) / 4 ≤ N * q := by
    nlinarith
  have hsqrt := Real.sqrt_le_sqrt hinside
  have hsqrt_div : Real.sqrt ((n * q) / 4) =
      (1 / 2 : Real) * Real.sqrt (n * q) := by
    rw [Real.sqrt_div (mul_nonneg hn hq)]
    have hsqrt_four : Real.sqrt (4 : Real) = 2 := by
      nlinarith [Real.sq_sqrt (by norm_num : (0 : Real) ≤ 4),
        Real.sqrt_nonneg (4 : Real)]
    rw [hsqrt_four]
    ring
  rwa [hsqrt_div] at hsqrt

/-- Constant conversion used in the first branch of the confidence proof. -/
theorem confidence_budget_dominates_target
    {n N T L : Real}
    (hn : 0 ≤ n) (hT : 0 ≤ T) (hL : 0 ≤ L) (hN : n / 2 ≤ N) :
    (1 / (2 : Real) ^ 17) * Real.sqrt (n * T * L) ≤
      confidenceConstant / 16 * Real.sqrt (N * T * L) := by
  have hsqrt : (1 / 2 : Real) * Real.sqrt (n * (T * L)) ≤
      Real.sqrt (N * (T * L)) :=
    half_sqrt_le_sqrt_of_half_le hn (mul_nonneg hT hL) hN
  have hc : confidenceConstant / 16 = 1 / (2 : Real) ^ 16 := by
    norm_num [confidenceConstant]
  rw [hc]
  have hsqrt' : (1 / 2 : Real) * Real.sqrt (n * T * L) ≤
      Real.sqrt (N * T * L) := by
    simpa only [mul_assoc] using hsqrt
  calc
    (1 / (2 : Real) ^ 17) * Real.sqrt (n * T * L) =
        (1 / (2 : Real) ^ 16) *
          ((1 / 2 : Real) * Real.sqrt (n * T * L)) := by ring
    _ ≤ (1 / (2 : Real) ^ 16) * Real.sqrt (N * T * L) :=
      mul_le_mul_of_nonneg_left hsqrt' (by norm_num)

/-- Constant conversion at the end of the planted-environment branch. -/
theorem confidence_score_dominates_target
    {n N T L : Real}
    (hn : 0 ≤ n) (hT : 0 ≤ T) (hL : 0 ≤ L) (hN : n / 2 ≤ N) :
    (1 / (2 : Real) ^ 16) * Real.sqrt (n * T * L) ≤
      confidenceConstant / 8 * Real.sqrt (N * T * L) := by
  have hsqrt : (1 / 2 : Real) * Real.sqrt (n * (T * L)) ≤
      Real.sqrt (N * (T * L)) :=
    half_sqrt_le_sqrt_of_half_le hn (mul_nonneg hT hL) hN
  rw [confidenceConstant_div_eight]
  have hsqrt' : (1 / 2 : Real) * Real.sqrt (n * T * L) ≤
      Real.sqrt (N * T * L) := by
    simpa only [mul_assoc] using hsqrt
  calc
    (1 / (2 : Real) ^ 16) * Real.sqrt (n * T * L) =
        (1 / (2 : Real) ^ 15) *
          ((1 / 2 : Real) * Real.sqrt (n * T * L)) := by ring
    _ ≤ (1 / (2 : Real) ^ 15) * Real.sqrt (N * T * L) :=
      mul_le_mul_of_nonneg_left hsqrt' (by norm_num)

end

end MsetsLower.Lower.Confidence

#print axioms MsetsLower.Lower.Confidence.lower_confidence_parameters
