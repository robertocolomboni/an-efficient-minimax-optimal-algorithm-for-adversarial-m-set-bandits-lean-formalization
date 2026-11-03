import MsetsLower.Lower.Confidence.Arithmetic

/-!
# Numerical KL budget in the confidence construction

This file certifies the displayed arithmetic chain in
`eq:lower-confidence-kl`, separately from the sequential probabilistic law.
-/

namespace MsetsLower.Lower.Confidence

noncomputable section

theorem confidenceDelta_sq_mul_time_div_candidates
    {N L T : Real} (hN : 0 < N) (hL : 0 ≤ L) (hT : 0 < T) :
    confidenceDelta N L T ^ 2 * T / N =
      confidenceConstant ^ 2 * L := by
  have hNLT : 0 ≤ N * L / T := by positivity
  rw [confidenceDelta, mul_pow, Real.sq_sqrt hNLT]
  field_simp [ne_of_gt hN, ne_of_gt hT]

/-- The four numerical lines of `eq:lower-confidence-kl`. -/
theorem lower_confidence_kl_arithmetic
    {k N L T Delta B expectedPulls : Real}
    (hN : 0 < N) (hL : 0 ≤ L) (hT : 0 < T)
    (hDelta : Delta = confidenceDelta N L T)
    (hB : B = Delta * T / 16)
    (hPulls : expectedPulls ≤
      (16 / N) * (T + 8 * k * B + k))
    (hkDelta : k * Delta / 2 ≤ 1 / (2 : Real) ^ 14)
    (hkT : k / T ≤ 1 / 8) :
    128 * (4 * Delta) ^ 2 * expectedPulls ≤
      (1 / (2 : Real) ^ 8) * L := by
  have hfactor0 : 0 ≤ 128 * (4 * Delta) ^ 2 := by positivity
  have hfirst :
      128 * (4 * Delta) ^ 2 * expectedPulls ≤
        (2 : Real) ^ 15 * (Delta ^ 2 / N) *
          (T + 8 * k * B + k) := by
    calc
      128 * (4 * Delta) ^ 2 * expectedPulls ≤
          128 * (4 * Delta) ^ 2 *
            ((16 / N) * (T + 8 * k * B + k)) :=
        mul_le_mul_of_nonneg_left hPulls hfactor0
      _ = (2 : Real) ^ 15 * (Delta ^ 2 / N) *
          (T + 8 * k * B + k) := by ring
  have hfactorization :
      (Delta ^ 2 / N) * (T + 8 * k * B + k) =
        (Delta ^ 2 * T / N) *
          (1 + k * Delta / 2 + k / T) := by
    rw [hB]
    field_simp [ne_of_gt hN, ne_of_gt hT]
    ring
  have hbracket : 1 + k * Delta / 2 + k / T ≤ 2 := by
    calc
      1 + k * Delta / 2 + k / T ≤
          1 + 1 / (2 : Real) ^ 14 + 1 / 8 := by linarith
      _ ≤ 2 := by norm_num
  have hsecond :
      (2 : Real) ^ 15 * (Delta ^ 2 / N) *
          (T + 8 * k * B + k) ≤
        (2 : Real) ^ 16 * (Delta ^ 2 * T / N) := by
    calc
      (2 : Real) ^ 15 * (Delta ^ 2 / N) *
          (T + 8 * k * B + k) =
        (2 : Real) ^ 15 *
          ((Delta ^ 2 / N) * (T + 8 * k * B + k)) := by ring
      _ = (2 : Real) ^ 15 * ((Delta ^ 2 * T / N) *
          (1 + k * Delta / 2 + k / T)) := by rw [hfactorization]
      _ = (2 : Real) ^ 15 * (Delta ^ 2 * T / N) *
          (1 + k * Delta / 2 + k / T) := by ring
      _ ≤ (2 : Real) ^ 15 * (Delta ^ 2 * T / N) * 2 :=
          mul_le_mul_of_nonneg_left hbracket (by positivity)
      _ = (2 : Real) ^ 16 * (Delta ^ 2 * T / N) := by ring
  calc
    128 * (4 * Delta) ^ 2 * expectedPulls ≤
        (2 : Real) ^ 15 * (Delta ^ 2 / N) *
          (T + 8 * k * B + k) := hfirst
    _ ≤ (2 : Real) ^ 16 * (Delta ^ 2 * T / N) := hsecond
    _ = (2 : Real) ^ 16 * confidenceConstant ^ 2 * L := by
      rw [hDelta, confidenceDelta_sq_mul_time_div_candidates hN hL hT]
      ring
    _ = (1 / (2 : Real) ^ 8) * L := by
      rw [confidenceConstant_sq_scaled]

end

end MsetsLower.Lower.Confidence

#print axioms MsetsLower.Lower.Confidence.confidenceDelta_sq_mul_time_div_candidates
#print axioms MsetsLower.Lower.Confidence.lower_confidence_kl_arithmetic
