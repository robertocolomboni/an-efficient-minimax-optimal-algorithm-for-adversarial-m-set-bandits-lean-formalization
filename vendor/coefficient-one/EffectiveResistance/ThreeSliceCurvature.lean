import EffectiveResistance.ExternalFieldCurvature
import EffectiveResistance.ThreeSlice

/-!
# External-field curvature inside the three-slice mixture

This file combines the adjacent-rank inequality with the weighted covariance
mixture that occurs after fixing two endpoint coordinates.  The argument is
kept variational, so no matrix pseudoinverse is needed.
-/

open scoped BigOperators

namespace EffectiveResistance

noncomputable section

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

namespace PairTable

variable (P : PairTable)

def threeSliceQuadratic (w : ι → ℝ) (q : ℕ) (a : ι → ℝ) : ℝ :=
  P.p11 * quadraticForm (covarianceMatrix w q) a +
    P.s * quadraticForm (covarianceMatrix w (q + 1)) a +
      P.p00 * quadraticForm (covarianceMatrix w (q + 2)) a

theorem threeSliceQuadratic_nonnegative
    (w : ι → ℝ) (hw : ∀ i, 0 < w i) (q : ℕ)
    (hq : q + 2 ≤ Fintype.card ι) (a : ι → ℝ) :
    0 ≤ P.threeSliceQuadratic w q a := by
  have hq0 : q ≤ Fintype.card ι := by omega
  have hq1 : q + 1 ≤ Fintype.card ι := by omega
  unfold threeSliceQuadratic
  exact add_nonneg
    (add_nonneg
      (mul_nonneg P.nonneg11
        (covariance_quadratic_nonnegative w hw hq0 a))
      (mul_nonneg (add_nonneg P.nonneg10 P.nonneg01)
        (covariance_quadratic_nonnegative w hw hq1 a)))
    (mul_nonneg P.nonneg00
      (covariance_quadratic_nonnegative w hw hq a))

theorem middleSlice_le_threeSliceQuadratic
    (w : ι → ℝ) (hw : ∀ i, 0 < w i) (q : ℕ)
    (hq : q + 2 ≤ Fintype.card ι) (a : ι → ℝ) :
    P.s * quadraticForm (covarianceMatrix w (q + 1)) a ≤
      P.threeSliceQuadratic w q a := by
  have hq0 : q ≤ Fintype.card ι := by omega
  unfold threeSliceQuadratic
  have hleft : 0 ≤ P.p11 * quadraticForm (covarianceMatrix w q) a :=
    mul_nonneg P.nonneg11
      (covariance_quadratic_nonnegative w hw hq0 a)
  have hright : 0 ≤ P.p00 * quadraticForm (covarianceMatrix w (q + 2)) a :=
    mul_nonneg P.nonneg00
      (covariance_quadratic_nonnegative w hw hq a)
  linarith

theorem adjacentCoefficient_eq_tableCoefficient
    (h11 : 0 < P.p11) (h10 : 0 < P.p10) (h01 : 0 < P.p01)
    {theta : ℝ} (htheta : theta = P.p11 * P.p00 / (P.p10 * P.p01)) :
    2 * (1 - theta) / theta = 2 * P.ω / (P.p11 * P.p00) := by
  rw [htheta]
  simp only [ω]
  field_simp [ne_of_gt h11, ne_of_gt h10, ne_of_gt h01]

/-- Adjacent-rank curvature, strengthened from the middle covariance to the
full weighted three-slice covariance. -/
theorem rankCurvature_le_threeSliceQuadratic
    (w : ι → ℝ) (hw : ∀ i, 0 < w i) (q : ℕ)
    (hq : q + 2 ≤ Fintype.card ι)
    (h11 : 0 < P.p11) (h10 : 0 < P.p10) (h01 : 0 < P.p01)
    (h00 : 0 < P.p00)
    (hω : 0 ≤ P.ω)
    (htheta : adjacentTheta w q =
      P.p11 * P.p00 / (P.p10 * P.p01)) (a : ι → ℝ) :
    (∑ i, a i * rankCurvature w q i) ^ 2 ≤
      (2 * P.ω / (P.p11 * P.p00 * P.s)) *
        P.threeSliceQuadratic w q a := by
  have hs : 0 < P.s := P.s_pos h10
  have hmid := P.middleSlice_le_threeSliceQuadratic w hw q hq a
  have hmiddle : quadraticForm (covarianceMatrix w (q + 1)) a ≤
      P.threeSliceQuadratic w q a / P.s :=
    (le_div_iff₀ hs).2 (by simpa [mul_comm] using hmid)
  have hcurv := externalField_adjacent_rank_curvature w hw q hq a
  rw [P.adjacentCoefficient_eq_tableCoefficient h11 h10 h01 htheta] at hcurv
  have hcoef : 0 ≤ 2 * P.ω / (P.p11 * P.p00) := by positivity
  have hscaled := mul_le_mul_of_nonneg_left hmiddle hcoef
  calc
    (∑ i, a i * rankCurvature w q i) ^ 2 ≤
        (2 * P.ω / (P.p11 * P.p00)) *
          quadraticForm (covarianceMatrix w (q + 1)) a := hcurv
    _ ≤ (2 * P.ω / (P.p11 * P.p00)) *
        (P.threeSliceQuadratic w q a / P.s) := hscaled
    _ = (2 * P.ω / (P.p11 * P.p00 * P.s)) *
        P.threeSliceQuadratic w q a := by
      field_simp [ne_of_gt h11, ne_of_gt h00, ne_of_gt hs]

/-- Every vector in the external-field three-slice regression has cost at
least the endpoint-degree lower bound. -/
theorem externalField_threeSlice_objective_bound
    (w : ι → ℝ) (hw : ∀ i, 0 < w i) (q : ℕ)
    (hq : q + 2 ≤ Fintype.card ι)
    (h11 : 0 < P.p11) (h10 : 0 < P.p10) (h01 : 0 < P.p01)
    (h00 : 0 < P.p00) (hω : 0 ≤ P.ω)
    (htheta : adjacentTheta w q =
      P.p11 * P.p00 / (P.p10 * P.p01)) (a : ι → ℝ) :
    4 * P.p11 * P.p00 * P.s / (P.vi + P.vj) ≤
      P.threeSliceQuadratic w q a +
        (2 + ∑ i, a i * rankCurvature w q i) ^ 2 /
          P.sliceDenominator := by
  apply P.three_slice_objective_bound h11 h10 h01 h00 hω
  · exact P.threeSliceQuadratic_nonnegative w hw q hq a
  · exact P.rankCurvature_le_threeSliceQuadratic
      w hw q hq h11 h10 h01 h00 hω htheta a

end PairTable

end

end EffectiveResistance
