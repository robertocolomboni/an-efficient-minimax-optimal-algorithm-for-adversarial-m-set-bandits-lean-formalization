import CoefficientOne.WeightedLaplacian
import CoefficientOne.HyperplaneComparison
import CoefficientOne.CovarianceBridge

/-!
# Consequences of the positive matrix certificate

This file follows the manuscript immediately after `eq:R-squares`. For
`R = b b^T - K H - c t t^T`, positivity of `R`, positivity of `K`, and
nonnegativity of `c` imply that `H` is strictly negative on `b`'s orthogonal
hyperplane. The exact inertia theorem and the actual covariance comparison
follow from the corresponding generic lemmas.

These algebraic lemmas take the certificate identities and positivity as
hypotheses. `ConcreteCertificate` and the scalar bounds establish those
hypotheses for the external-field covariance; `Main` applies the resulting
comparison.
-/

open scoped BigOperators
open Matrix EffectiveResistance

namespace CoefficientOne

noncomputable section

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- The certificate is strictly negative on the normal's orthogonal
hyperplane, exactly as in the manuscript's last displayed certificate step. -/
theorem quadraticForm_neg_of_positive_certificate
    (H R : Matrix ι ι ℝ) (b t : ι → ℝ) (K c : ℝ)
    (hK : 0 < K) (hc : 0 ≤ c) (hR : R.PosDef)
    (hidentity : R = Matrix.vecMulVec b b - K • H - c • Matrix.vecMulVec t t)
    (z : ι → ℝ) (hz : z ≠ 0) (hbz : b ⬝ᵥ z = 0) :
    z ⬝ᵥ (H *ᵥ z) < 0 := by
  have hpositive : 0 < quadraticForm R z := by
    simpa only [quadraticForm, star_trivial] using hR.dotProduct_mulVec_pos hz
  rw [hidentity, quadraticForm_sub, quadraticForm_sub,
    quadraticForm_vecMulVec, quadraticForm_smul, quadraticForm_smul,
    quadraticForm_vecMulVec] at hpositive
  change (∑ i, b i * z i) = 0 at hbz
  rw [hbz] at hpositive
  have hnonneg : 0 ≤ c * (∑ i, t i * z i) ^ 2 :=
    mul_nonneg hc (sq_nonneg _)
  have hscaled : K * quadraticForm H z < 0 := by linarith
  exact neg_of_mul_neg_right hscaled hK.le

/-- The full square-decomposition route to the negative hyperplane. -/
theorem quadraticForm_neg_of_weighted_certificate
    (H R : Matrix ι ι ℝ) (a b t : ι → ℝ) (K c : ℝ)
    (hK : 0 < K) (hc : 0 ≤ c) (hRsymm : R.IsSymm)
    (ha : ∀ i, 0 < a i) (hoff : ∀ i j, i ≠ j → R i j ≤ 0)
    (hRa : ∀ i, 0 < (R *ᵥ a) i)
    (hidentity : R = Matrix.vecMulVec b b - K • H - c • Matrix.vecMulVec t t)
    (z : ι → ℝ) (hz : z ≠ 0) (hbz : b ⬝ᵥ z = 0) :
    z ⬝ᵥ (H *ᵥ z) < 0 := by
  exact quadraticForm_neg_of_positive_certificate H R b t K c hK hc
    (matrix_posDef_of_weighted_row_sums R a hRsymm ha hoff hRa) hidentity z hz hbz

/-- Exact inertia of a symmetric kernel matrix from the positive certificate
and one positive quadratic direction. -/
theorem inertia_of_positive_certificate
    (H R : Matrix ι ι ℝ) (hH : H.IsHermitian) (b t e : ι → ℝ) (K c : ℝ)
    (hK : 0 < K) (hc : 0 ≤ c) (hR : R.PosDef)
    (hidentity : R = Matrix.vecMulVec b b - K • H - c • Matrix.vecMulVec t t)
    (he : 0 < e ⬝ᵥ (H *ᵥ e)) :
    ∃ i, 0 < hH.eigenvalues i ∧ ∀ j, j ≠ i → hH.eigenvalues j < 0 := by
  apply unique_positive_eigenvalue_of_negative_hyperplane H hH b e
  · exact quadraticForm_neg_of_positive_certificate H R b t K c hK hc hR hidentity
  · exact he

/-- A diagonal congruence is the coordinate substitution `z_i ↦ w_i z_i`
in the quadratic form. -/
theorem quadraticForm_diagonal_congruence (H : Matrix ι ι ℝ) (w z : ι → ℝ) :
    z ⬝ᵥ ((Matrix.diagonal w * H * Matrix.diagonal w) *ᵥ z) =
      (w * z) ⬝ᵥ (H *ᵥ (w * z)) := by
  simp only [← Matrix.mulVec_mulVec]
  have hdiag : Matrix.diagonal w *ᵥ z = w * z := by
    ext i
    simp [Matrix.mulVec_diagonal]
  rw [hdiag]
  simp only [dotProduct, Matrix.mulVec_diagonal, Pi.mul_apply]
  apply Finset.sum_congr rfl
  intro i hi
  ring

/-- The negative hyperplane transforms by multiplying its normal by the
diagonal weights. No invertibility is needed for this nonpositive version. -/
theorem nonpositive_hyperplane_diagonal_congruence
    (H : Matrix ι ι ℝ) (b w : ι → ℝ) (c : ℝ) (hc : 0 ≤ c)
    (hneg : ∀ y : ι → ℝ, b ⬝ᵥ y = 0 → y ⬝ᵥ (H *ᵥ y) ≤ 0)
    (z : ι → ℝ) (hz : (b * w) ⬝ᵥ z = 0) :
    z ⬝ᵥ ((c • (Matrix.diagonal w * H * Matrix.diagonal w)) *ᵥ z) ≤ 0 := by
  have horth : b ⬝ᵥ (w * z) = 0 := by
    simpa only [dotProduct, Pi.mul_apply, mul_assoc] using hz
  rw [Matrix.smul_mulVec, dotProduct_smul, smul_eq_mul,
    quadraticForm_diagonal_congruence]
  exact mul_nonpos_of_nonneg_of_nonpos hc (hneg (w * z) horth)

/-- For the concrete finite law, the kernel's nonpositive hyperplane is
sufficient for the coefficient-one comparison. All probability identities,
row sums, variances, and the congruence are proved in `CovarianceBridge`. -/
theorem covariance_comparison_of_kernel_hyperplane
    (w : ι → ℝ) (hw : ∀ k, 0 < w k) (m : ℕ)
    (hmpos : 1 ≤ m) (hmtop : m ≤ Fintype.card ι - 1) (b : ι → ℝ)
    (hneg : ∀ y : ι → ℝ, b ⬝ᵥ y = 0 →
      y ⬝ᵥ (kernelMatrix w ((m : ℤ) - 1) *ᵥ y) ≤ 0) :
    LoewnerLE (comparisonMatrix (covarianceVariance w m)) (covarianceMatrix w m) := by
  have hmcard : m ≤ Fintype.card ι := hmtop.trans (Nat.sub_le _ _)
  apply covariance_comparison_of_nonpositive_hyperplane
    (covarianceMatrix w m) (covarianceVariance w m) (b * w)
    (covariance_isSymm w m) (covariance_mulVec_one_eq_zero w hw m hmcard)
    (covarianceVariance_sum_pos w hw m hmpos hmtop)
  intro z hz
  rw [covariance_complement_eq_kernel_congruence w hw m hmpos hmcard]
  exact nonpositive_hyperplane_diagonal_congruence
    (kernelMatrix w ((m : ℤ) - 1)) b w (1 / elementarySum w m ^ 2)
    (by positivity) hneg z hz

end

end CoefficientOne
