import EffectiveResistance.PairTable

/-!
# Algebraic part of the three-slice estimate

The analytic input is the adjacent-rank curvature estimate on `χ`.  This file
checks all subsequent denominator manipulations and the lower bound on the
three-slice regression residual.
-/

namespace EffectiveResistance

noncomputable section

/-- The scalar inequality behind the weighted three-slice minimization.  If
`t² ≤ C x`, then the two nonnegative quadratic costs `x` and
`(2+t)²/D` cannot simultaneously be small. -/
theorem two_term_regression_lower_bound
    {D C x t : ℝ} (hD : 0 < D) (hC : 0 ≤ C) (hx : 0 ≤ x)
    (ht : t ^ 2 ≤ C * x) :
    4 / (D + C) ≤ x + (2 + t) ^ 2 / D := by
  have hDC : 0 < D + C := add_pos_of_pos_of_nonneg hD hC
  by_cases hC0 : C = 0
  · subst C
    have ht0 : t = 0 := by
      have : t ^ 2 ≤ 0 := by simpa using ht
      nlinarith [sq_nonneg t]
    subst t
    have hfour : 4 / D ≤ x + 4 / D := by linarith
    convert hfour using 1 <;> norm_num
  · have hCpos : 0 < C := lt_of_le_of_ne hC (Ne.symm hC0)
    have hmult := mul_le_mul_of_nonneg_left ht
      (mul_nonneg hD.le hDC.le)
    have hpoly :
        4 * D ≤ D * (D + C) * x + (D + C) * (2 + t) ^ 2 := by
      nlinarith [sq_nonneg ((D + C) * t + 2 * C)]
    apply (div_le_iff₀ hDC).2
    calc
      4 ≤ (D * (D + C) * x + (D + C) * (2 + t) ^ 2) / D :=
        (le_div_iff₀ hD).2 hpoly
      _ = (x + (2 + t) ^ 2 / D) * (D + C) := by
        field_simp [ne_of_gt hD]

namespace PairTable

variable (P : PairTable)

def sliceDenominator : ℝ := 1 / P.p11 + 4 / P.s + 1 / P.p00

theorem slice_table_identity :
    P.p00 * P.s + 4 * P.p11 * P.p00 + P.p11 * P.s + 2 * P.ω =
      P.vi + P.vj := by
  have hp00 : P.p00 = 1 - P.p11 - P.p10 - P.p01 := by
    linarith [P.total]
  simp only [s, μi, μj, vi, vj, ω]
  rw [hp00]
  ring

theorem sliceDenominator_pos
    (h11 : 0 < P.p11) (h10 : 0 < P.p10) (h00 : 0 < P.p00) :
    0 < P.sliceDenominator := by
  have hs : 0 < P.s := P.s_pos h10
  simp only [sliceDenominator]
  positivity

/-- The curvature bound on `χ` implies the precise denominator estimate used
in the three-slice lemma. -/
theorem three_slice_denominator_bound
    (h11 : 0 < P.p11) (h10 : 0 < P.p10) (h00 : 0 < P.p00)
    {χ : ℝ} (hχ : χ ≤ 2 * P.ω / (P.p11 * P.p00 * P.s)) :
    P.p11 * P.p00 * P.s * (P.sliceDenominator + χ) ≤
      P.vi + P.vj := by
  have hs : 0 < P.s := P.s_pos h10
  have hprod : 0 < P.p11 * P.p00 * P.s := by positivity
  have hscaled := mul_le_mul_of_nonneg_left hχ hprod.le
  have hcurv :
      (P.p11 * P.p00 * P.s) * χ ≤ 2 * P.ω := by
    calc
      (P.p11 * P.p00 * P.s) * χ ≤
          (P.p11 * P.p00 * P.s) *
            (2 * P.ω / (P.p11 * P.p00 * P.s)) := hscaled
      _ = 2 * P.ω := by
        field_simp [ne_of_gt h11, ne_of_gt h00, ne_of_gt hs]
  calc
    P.p11 * P.p00 * P.s * (P.sliceDenominator + χ) =
        P.p00 * P.s + 4 * P.p11 * P.p00 + P.p11 * P.s +
          (P.p11 * P.p00 * P.s) * χ := by
      simp only [sliceDenominator]
      field_simp [ne_of_gt h11, ne_of_gt h00, ne_of_gt hs]
    _ ≤ P.p00 * P.s + 4 * P.p11 * P.p00 + P.p11 * P.s +
        2 * P.ω := by linarith
    _ = P.vi + P.vj := P.slice_table_identity

/-- If the weighted least-squares residual is `4 / (D + χ)`, adjacent-rank
curvature gives the lower bound required by the main theorem. -/
theorem three_slice_residual_bound
    (h11 : 0 < P.p11) (h10 : 0 < P.p10) (h01 : 0 < P.p01)
    (h00 : 0 < P.p00) {χ ε : ℝ} (hχ0 : 0 ≤ χ)
    (hχ : χ ≤ 2 * P.ω / (P.p11 * P.p00 * P.s))
    (hε : ε = 4 / (P.sliceDenominator + χ)) :
    4 * P.p11 * P.p00 * P.s / (P.vi + P.vj) ≤ ε := by
  have hs : 0 < P.s := P.s_pos h10
  have hD : 0 < P.sliceDenominator := P.sliceDenominator_pos h11 h10 h00
  have hDχ : 0 < P.sliceDenominator + χ := add_pos_of_pos_of_nonneg hD hχ0
  have hvi : 0 < P.vi := P.vi_pos h11 h10 h01
  have hvj : 0 < P.vj := P.vj_pos h11 h10 h01
  have hv : 0 < P.vi + P.vj := add_pos hvi hvj
  rw [hε]
  apply (div_le_div_iff₀ hv hDχ).2
  have hden := P.three_slice_denominator_bound h11 h10 h00 hχ
  nlinarith [mul_pos (by positivity : 0 < (4 : ℝ))
    (mul_pos (mul_pos h11 h00) hs)]

/-- Direct variational form of the three-slice estimate.  It avoids naming a
pseudoinverse: a curvature estimate `t² ≤ Cx` is enough for every candidate
of the regression problem. -/
theorem three_slice_objective_bound
    (h11 : 0 < P.p11) (h10 : 0 < P.p10) (h01 : 0 < P.p01)
    (h00 : 0 < P.p00) (hω : 0 ≤ P.ω)
    {x t : ℝ} (hx : 0 ≤ x)
    (ht : t ^ 2 ≤
      (2 * P.ω / (P.p11 * P.p00 * P.s)) * x) :
    4 * P.p11 * P.p00 * P.s / (P.vi + P.vj) ≤
      x + (2 + t) ^ 2 / P.sliceDenominator := by
  have hs : 0 < P.s := P.s_pos h10
  have hC : 0 ≤ 2 * P.ω / (P.p11 * P.p00 * P.s) := by positivity
  have hD : 0 < P.sliceDenominator := P.sliceDenominator_pos h11 h10 h00
  have hlower := two_term_regression_lower_bound hD hC hx ht
  have hden := P.three_slice_denominator_bound h11 h10 h00
    (show 2 * P.ω / (P.p11 * P.p00 * P.s) ≤
        2 * P.ω / (P.p11 * P.p00 * P.s) from le_rfl)
  have hvi : 0 < P.vi := P.vi_pos h11 h10 h01
  have hvj : 0 < P.vj := P.vj_pos h11 h10 h01
  have hv : 0 < P.vi + P.vj := add_pos hvi hvj
  have hDC : 0 < P.sliceDenominator +
      2 * P.ω / (P.p11 * P.p00 * P.s) := add_pos_of_pos_of_nonneg hD hC
  have hfront :
      4 * P.p11 * P.p00 * P.s / (P.vi + P.vj) ≤
        4 / (P.sliceDenominator +
          2 * P.ω / (P.p11 * P.p00 * P.s)) := by
    apply (div_le_div_iff₀ hv hDC).2
    nlinarith [mul_pos (by norm_num : (0 : ℝ) < 4)
      (mul_pos (mul_pos h11 h00) hs)]
  exact hfront.trans hlower

end PairTable

end

end EffectiveResistance
