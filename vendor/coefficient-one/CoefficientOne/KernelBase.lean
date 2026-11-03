import CoefficientOne.MatrixCertificate

/-!
# The j = 0 kernel and the rank-one boundary case

This is the manuscript's explicit base case H_0 = 11^T-I. Its quadratic
form is strictly negative on the sum-zero hyperplane. The already proved
covariance bridge then gives coefficient one at rank m = 1.
-/

noncomputable section

namespace CoefficientOne

open Matrix EffectiveResistance Finset

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

theorem kernelMatrix_zero (w : ι → ℝ) :
    kernelMatrix w 0 = Matrix.vecMulVec (fun _ => 1) (fun _ => 1) - 1 := by
  ext i j
  by_cases hij : i = j <;>
    simp [kernelMatrix, kernelK_zero, Matrix.vecMulVec, Matrix.sub_apply,
      Matrix.one_apply, hij]

theorem kernelMatrix_zero_quadraticForm (w z : ι → ℝ) :
    quadraticForm (kernelMatrix w 0) z = (∑ i, z i) ^ 2 - z ⬝ᵥ z := by
  rw [kernelMatrix_zero, quadraticForm_sub, quadraticForm_vecMulVec]
  simp [quadraticForm]

theorem kernelMatrix_zero_neg_on_hyperplane (w z : ι → ℝ)
    (hz : z ≠ 0) (hsum : (fun _ => (1 : ℝ)) ⬝ᵥ z = 0) :
    z ⬝ᵥ (kernelMatrix w 0 *ᵥ z) < 0 := by
  change quadraticForm (kernelMatrix w 0) z < 0
  rw [kernelMatrix_zero_quadraticForm]
  have hs : ∑ i, z i = 0 := by simpa [dotProduct] using hsum
  rw [hs]
  have hnorm : 0 < z ⬝ᵥ z := by
    simpa only [star_trivial] using (dotProduct_self_star_pos_iff.mpr hz)
  nlinarith

theorem kernelMatrix_zero_nonpos_on_hyperplane (w z : ι → ℝ)
    (hsum : (fun _ => (1 : ℝ)) ⬝ᵥ z = 0) :
    z ⬝ᵥ (kernelMatrix w 0 *ᵥ z) ≤ 0 := by
  by_cases hz : z = 0
  · simp [hz]
  · exact (kernelMatrix_zero_neg_on_hyperplane w z hz hsum).le

theorem kernelMatrix_zero_isSymm (w : ι → ℝ) : (kernelMatrix w 0).IsSymm := by
  rw [kernelMatrix_zero]
  ext i j
  simp [Matrix.transpose_apply, Matrix.sub_apply, Matrix.vecMulVec,
    Matrix.one_apply, eq_comm]

theorem kernelMatrix_zero_positive_direction (w : ι → ℝ) (hcard : 2 ≤ Fintype.card ι) :
    0 < (fun _ => (1 : ℝ)) ⬝ᵥ (kernelMatrix w 0 *ᵥ (fun _ => 1)) := by
  change 0 < quadraticForm (kernelMatrix w 0) (fun _ => 1)
  rw [kernelMatrix_zero_quadraticForm]
  simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, mul_one,
    dotProduct, one_mul]
  have hcardR : (2 : ℝ) ≤ Fintype.card ι := by exact_mod_cast hcard
  nlinarith

theorem kernelMatrix_zero_inertia (w : ι → ℝ) (hcard : 2 ≤ Fintype.card ι) :
    ∃ i, 0 < (Matrix.isHermitian_iff_isSymm.mpr (kernelMatrix_zero_isSymm w)).eigenvalues i ∧
      ∀ j, j ≠ i →
        (Matrix.isHermitian_iff_isSymm.mpr (kernelMatrix_zero_isSymm w)).eigenvalues j < 0 := by
  apply unique_positive_eigenvalue_of_negative_hyperplane (kernelMatrix w 0)
    (Matrix.isHermitian_iff_isSymm.mpr (kernelMatrix_zero_isSymm w))
    (fun _ => 1) (fun _ => 1)
  · exact kernelMatrix_zero_neg_on_hyperplane w
  · exact kernelMatrix_zero_positive_direction w hcard

/-- The full coefficient-one covariance comparison at the first nontrivial rank. -/
theorem covariance_comparison_rankOne (w : ι → ℝ) (hw : ∀ i, 0 < w i)
    (hcard : 2 ≤ Fintype.card ι) :
    LoewnerLE (comparisonMatrix (covarianceVariance w 1)) (covarianceMatrix w 1) := by
  apply covariance_comparison_of_kernel_hyperplane w hw 1 (by decide) (by omega) (fun _ => 1)
  intro z hsum
  simpa using kernelMatrix_zero_nonpos_on_hyperplane w z hsum

end CoefficientOne
