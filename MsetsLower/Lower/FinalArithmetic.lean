import MsetsLower.Prelude

/-!
# Numerical assembly of the final lower bound

This file contains only the deterministic arithmetic used after the
action-count and confidence constructions have been proved.  Keeping it
separate prevents the final loss of a factor two from being hidden inside the
probabilistic arguments.
-/

namespace MsetsLower.Lower

noncomputable section

/-- The common constant after the sparse/dense action-count case split. -/
def actionCountConstant : Real := 1 / (2 : Real) ^ 38

/-- The literal constant in `thm:lower-bound-explicit`. -/
def finalLowerConstant : Real := 1 / (2 : Real) ^ 39

theorem actionCountConstant_eq_two_mul_final :
    actionCountConstant = 2 * finalLowerConstant := by
  norm_num [actionCountConstant, finalLowerConstant]

/-- If `B=max H L`, the `2^-38 sqrt(dTB)` bound implies the displayed
`2^-39 sqrt(dT(H+L))` bound of the explicit theorem. -/
theorem final_constant_sqrt_sum_le_sqrt_max
    {d T H L : Real}
    (hd : 0 ≤ d) (hT : 0 ≤ T) (hH : 0 ≤ H) (hL : 0 ≤ L) :
    finalLowerConstant * Real.sqrt (d * T * (H + L)) ≤
      actionCountConstant * Real.sqrt (d * T * max H L) := by
  let q : Real := d * T
  let B : Real := max H L
  have hq : 0 ≤ q := mul_nonneg hd hT
  have hB : 0 ≤ B := by
    dsimp [B]
    rcases le_total H L with hHL | hLH
    · rw [max_eq_right hHL]
      exact hL
    · rw [max_eq_left hLH]
      exact hH
  have hsum : H + L ≤ 2 * B := by
    have hHB : H ≤ B := le_max_left H L
    have hLB : L ≤ B := le_max_right H L
    linarith
  have hinside : q * (H + L) ≤ 4 * (q * B) := by
    calc
      q * (H + L) ≤ q * (2 * B) :=
        mul_le_mul_of_nonneg_left hsum hq
      _ ≤ 4 * (q * B) := by
        have hqB : 0 ≤ q * B := mul_nonneg hq hB
        nlinarith
  have hsqrt : Real.sqrt (q * (H + L)) ≤
      2 * Real.sqrt (q * B) := by
    calc
      Real.sqrt (q * (H + L)) ≤ Real.sqrt (4 * (q * B)) :=
        Real.sqrt_le_sqrt hinside
      _ = 2 * Real.sqrt (q * B) := by
        rw [Real.sqrt_mul (by norm_num : (0 : Real) ≤ 4)]
        have hsqrt_four : Real.sqrt (4 : Real) = 2 := by
          nlinarith [Real.sq_sqrt (by norm_num : (0 : Real) ≤ 4),
            Real.sqrt_nonneg (4 : Real)]
        rw [hsqrt_four]
  have hconstant : actionCountConstant = 2 * finalLowerConstant :=
    actionCountConstant_eq_two_mul_final
  have hfinal_nonneg : 0 ≤ finalLowerConstant := by
    norm_num [finalLowerConstant]
  dsimp [q, B] at hsqrt
  rw [hconstant]
  nlinarith

end

end MsetsLower.Lower
