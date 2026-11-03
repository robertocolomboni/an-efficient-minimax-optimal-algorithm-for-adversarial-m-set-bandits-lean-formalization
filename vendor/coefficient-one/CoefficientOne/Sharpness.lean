import Mathlib
import CoefficientOne.CovarianceBridge
import CoefficientOne.NormalizedSpectrum

/-!
# Explicit three-coordinate sharpness calculation

This follows the manuscript's rank-one three-coordinate example. The normalized
matrix has off-diagonal entries `-a,-a,-b`, where
`a = sqrt (epsilon / (1 + epsilon))` and `b = (1-epsilon)/(1+epsilon)`.
The three eigenvectors below provide the full displayed eigenvalue calculation.
The model is identified with the actual law below, and its eigenvector also proves sharpness of the original Loewner comparison.
-/

noncomputable section

namespace CoefficientOne

open Matrix

def sharpModelMatrix (a b : ℝ) : Matrix (Fin 3) (Fin 3) ℝ :=
  !![1, -a, -a; -a, 1, -b; -a, -b, 1]

def sharpKernelVector (a : ℝ) : Fin 3 → ℝ := ![2 * a, 1, 1]
def sharpAntisymmetricVector : Fin 3 → ℝ := ![0, 1, -1]
def sharpSymmetricVector (a : ℝ) : Fin 3 → ℝ := ![1, -a, -a]

theorem sharpModel_kernel (a b : ℝ) (hab : 2 * a ^ 2 = 1 - b) :
    sharpModelMatrix a b *ᵥ sharpKernelVector a = 0 := by
  ext i
  fin_cases i <;>
    simp [sharpModelMatrix, sharpKernelVector, Matrix.mulVec, dotProduct,
      Fin.sum_univ_succ] <;> nlinarith

theorem sharpModel_antisymmetric (a b : ℝ) :
    sharpModelMatrix a b *ᵥ sharpAntisymmetricVector =
      (1 + b) • sharpAntisymmetricVector := by
  ext i
  fin_cases i <;>
    simp [sharpModelMatrix, sharpAntisymmetricVector, Matrix.mulVec, dotProduct,
      Fin.sum_univ_succ] <;> ring

theorem sharpModel_symmetric (a b : ℝ) (hab : 2 * a ^ 2 = 1 - b) :
    sharpModelMatrix a b *ᵥ sharpSymmetricVector a =
      (2 - b) • sharpSymmetricVector a := by
  ext i
  fin_cases i <;>
    simp [sharpModelMatrix, sharpSymmetricVector, Matrix.mulVec, dotProduct,
      Fin.sum_univ_succ] <;> nlinarith

theorem sharpModel_kernel_ne_zero (a : ℝ) : sharpKernelVector a ≠ 0 := by
  intro h
  have := congrFun h 1
  norm_num [sharpKernelVector] at this

theorem sharpModel_antisymmetric_ne_zero : sharpAntisymmetricVector ≠ 0 := by
  intro h
  have := congrFun h 1
  norm_num [sharpAntisymmetricVector] at this

theorem sharpModel_symmetric_ne_zero (a : ℝ) : sharpSymmetricVector a ≠ 0 := by
  intro h
  have := congrFun h 0
  norm_num [sharpSymmetricVector] at this

theorem sharpModel_eigenvectors_orthogonal (a : ℝ) :
    dotProduct (sharpKernelVector a) (sharpSymmetricVector a) = 0 ∧
      dotProduct (sharpKernelVector a) sharpAntisymmetricVector = 0 ∧
      dotProduct (sharpSymmetricVector a) sharpAntisymmetricVector = 0 := by
  simp [sharpKernelVector, sharpSymmetricVector, sharpAntisymmetricVector,
    dotProduct, Fin.sum_univ_succ]
  ring

def sharpA (epsilon : ℝ) : ℝ := Real.sqrt (epsilon / (1 + epsilon))
def sharpB (epsilon : ℝ) : ℝ := (1 - epsilon) / (1 + epsilon)

theorem sharp_parameters_relation (epsilon : ℝ) (he : 0 ≤ epsilon) :
    2 * sharpA epsilon ^ 2 = 1 - sharpB epsilon := by
  have hd : 0 < 1 + epsilon := by linarith
  rw [sharpA, Real.sq_sqrt (div_nonneg he hd.le), sharpB]
  field_simp
  ring

theorem sharp_first_eigenvalue (epsilon : ℝ) (he : 0 ≤ epsilon) :
    1 + sharpB epsilon = 2 / (1 + epsilon) := by
  have hd : 1 + epsilon ≠ 0 := by linarith
  unfold sharpB
  field_simp
  ring

theorem sharp_second_eigenvalue (epsilon : ℝ) (he : 0 ≤ epsilon) :
    2 - sharpB epsilon = (1 + 3 * epsilon) / (1 + epsilon) := by
  have hd : 1 + epsilon ≠ 0 := by linarith
  unfold sharpB
  field_simp
  ring

theorem sharp_second_eigenvalue_pos (epsilon : ℝ) (he : 0 ≤ epsilon) :
    0 < (1 + 3 * epsilon) / (1 + epsilon) := by
  apply div_pos <;> linarith

theorem sharp_eigenvalue_limit :
    Filter.Tendsto (fun epsilon : ℝ => (1 + 3 * epsilon) / (1 + epsilon))
      (nhds 0) (nhds 1) := by
  have h : ContinuousAt (fun epsilon : ℝ => (1 + 3 * epsilon) / (1 + epsilon)) 0 :=
    (continuousAt_const.add (continuousAt_const.mul continuousAt_id)).div
      (continuousAt_const.add continuousAt_id) (by norm_num)
  simpa using h.tendsto

theorem sharpModel_shifted_determinant (a b lambda : ℝ)
    (hab : 2 * a ^ 2 = 1 - b) :
    Matrix.det (sharpModelMatrix a b - Matrix.diagonal (fun _ => lambda)) =
      -lambda * (1 + b - lambda) * (2 - b - lambda) := by
  simp [Matrix.det_fin_three, sharpModelMatrix]
  linear_combination -(1 + b - lambda) * hab

theorem exists_sharp_small_eigenvalue (c : ℝ) (hc : 1 < c) :
    ∃ epsilon : ℝ, 0 < epsilon ∧ epsilon < 1 ∧
      0 < (1 + 3 * epsilon) / (1 + epsilon) ∧
        (1 + 3 * epsilon) / (1 + epsilon) < c := by
  let epsilon : ℝ := min (1 / 2) ((c - 1) / 4)
  have he : 0 < epsilon := by
    apply lt_min <;> linarith
  have hehalf : epsilon ≤ 1 / 2 := min_le_left _ _
  have hec : epsilon ≤ (c - 1) / 4 := min_le_right _ _
  refine ⟨epsilon, he, by linarith, sharp_second_eigenvalue_pos epsilon he.le, ?_⟩
  apply (div_lt_iff₀ (by linarith : 0 < 1 + epsilon)).mpr
  have hce : 0 < c * epsilon := mul_pos (by linarith) he
  nlinarith
def sharpWeights (epsilon : ℝ) : Fin 3 → ℝ :=
  ![epsilon, (1 - epsilon) / 2, (1 - epsilon) / 2]

def sharpV0 (epsilon : ℝ) : ℝ := epsilon * (1 - epsilon)
def sharpV1 (epsilon : ℝ) : ℝ := (1 - epsilon ^ 2) / 4

def sharpCovariance (epsilon : ℝ) : Matrix (Fin 3) (Fin 3) ℝ :=
  !![sharpV0 epsilon, -(epsilon * (1 - epsilon) / 2), -(epsilon * (1 - epsilon) / 2);
     -(epsilon * (1 - epsilon) / 2), sharpV1 epsilon, -((1 - epsilon) ^ 2 / 4);
     -(epsilon * (1 - epsilon) / 2), -((1 - epsilon) ^ 2 / 4), sharpV1 epsilon]

theorem sharpWeights_pos (epsilon : ℝ) (he : 0 < epsilon) (he1 : epsilon < 1) :
    ∀ i, 0 < sharpWeights epsilon i := by
  intro i
  fin_cases i <;> simp [sharpWeights] <;> linarith

theorem sharpWeights_sum (epsilon : ℝ) : ∑ i, sharpWeights epsilon i = 1 := by
  simp [sharpWeights, Fin.sum_univ_succ]

theorem sharpWeights_normalizer (epsilon : ℝ) :
    EffectiveResistance.elementarySum (sharpWeights epsilon) 1 = 1 := by
  rw [elementarySum_one, sharpWeights_sum]

theorem sharpWeights_mean (epsilon : ℝ) :
    EffectiveResistance.inclusionMean (sharpWeights epsilon) 1 = sharpWeights epsilon := by
  ext i
  rw [inclusionMean_rankOne_eq_weight, sharpWeights_normalizer, div_one]

theorem sharp_covariance_actual (epsilon : ℝ) (he : 0 < epsilon) (he1 : epsilon < 1) :
    EffectiveResistance.covarianceMatrix (sharpWeights epsilon) 1 = sharpCovariance epsilon := by
  rw [EffectiveResistance.covarianceMatrix_rankOne (sharpWeights epsilon)
    (sharpWeights_pos epsilon he he1) (by decide), sharpWeights_mean]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [sharpWeights, sharpCovariance, sharpV0, sharpV1, Matrix.diagonal,
      Matrix.vecMulVec, Matrix.sub_apply] <;> ring

theorem sharp_variances_pos (epsilon : ℝ) (he : 0 < epsilon) (he1 : epsilon < 1) :
    0 < sharpV0 epsilon ∧ 0 < sharpV1 epsilon := by
  constructor
  · unfold sharpV0
    exact mul_pos he (by linarith)
  · unfold sharpV1
    have hs : epsilon ^ 2 < 1 := by nlinarith
    linarith

theorem sharp_normalization_A (epsilon : ℝ) (he : 0 < epsilon) (he1 : epsilon < 1) :
    (epsilon * (1 - epsilon) / 2) /
      (Real.sqrt (sharpV0 epsilon) * Real.sqrt (sharpV1 epsilon)) = sharpA epsilon := by
  obtain ⟨hv0, hv1⟩ := sharp_variances_pos epsilon he he1
  have hden : 0 < Real.sqrt (sharpV0 epsilon) * Real.sqrt (sharpV1 epsilon) :=
    mul_pos (Real.sqrt_pos.mpr hv0) (Real.sqrt_pos.mpr hv1)
  have hratio : 0 ≤ (epsilon * (1 - epsilon) / 2) /
      (Real.sqrt (sharpV0 epsilon) * Real.sqrt (sharpV1 epsilon)) := by positivity
  have hsquare : ((epsilon * (1 - epsilon) / 2) /
      (Real.sqrt (sharpV0 epsilon) * Real.sqrt (sharpV1 epsilon))) ^ 2 =
      epsilon / (1 + epsilon) := by
    rw [div_pow, mul_pow, Real.sq_sqrt hv0.le, Real.sq_sqrt hv1.le]
    unfold sharpV0 sharpV1
    have he0 : epsilon ≠ 0 := ne_of_gt he
    have heminus : 1 - epsilon ≠ 0 := by linarith
    have heplus : 1 + epsilon ≠ 0 := by linarith
    have hesq : 1 - epsilon ^ 2 ≠ 0 := by nlinarith
    field_simp
    ring
  have hroot := Real.sqrt_sq hratio
  rw [hsquare] at hroot
  exact hroot.symm

theorem sharp_normalization_B (epsilon : ℝ) (he : 0 < epsilon) (he1 : epsilon < 1) :
    ((1 - epsilon) ^ 2 / 4) / sharpV1 epsilon = sharpB epsilon := by
  unfold sharpV1 sharpB
  have heplus : 1 + epsilon ≠ 0 := by linarith
  have hesq : 1 - epsilon ^ 2 ≠ 0 := by nlinarith
  field_simp
  ring
theorem sharp_normalized_model (epsilon : ℝ) (he : 0 < epsilon) (he1 : epsilon < 1) :
    normalizedMatrix (sharpCovariance epsilon) =
      sharpModelMatrix (sharpA epsilon) (sharpB epsilon) := by
  obtain ⟨hv0, hv1⟩ := sharp_variances_pos epsilon he he1
  have hA := sharp_normalization_A epsilon he he1
  have hB := sharp_normalization_B epsilon he he1
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [normalizedMatrix, sharpCovariance, sharpModelMatrix,
      Real.mul_self_sqrt hv0.le, Real.mul_self_sqrt hv1.le,
      ne_of_gt hv0, ne_of_gt hv1, neg_div, hA, hB, mul_comm]

theorem sharp_normalized_actual (epsilon : ℝ) (he : 0 < epsilon) (he1 : epsilon < 1) :
    normalizedMatrix (EffectiveResistance.covarianceMatrix (sharpWeights epsilon) 1) =
      sharpModelMatrix (sharpA epsilon) (sharpB epsilon) := by
  rw [sharp_covariance_actual epsilon he he1, sharp_normalized_model epsilon he he1]

theorem sharp_actual_positive_eigenvector (epsilon : ℝ) (he : 0 < epsilon)
    (he1 : epsilon < 1) :
    normalizedMatrix (EffectiveResistance.covarianceMatrix (sharpWeights epsilon) 1) *ᵥ
        sharpSymmetricVector (sharpA epsilon) =
      ((1 + 3 * epsilon) / (1 + epsilon)) • sharpSymmetricVector (sharpA epsilon) := by
  rw [sharp_normalized_actual epsilon he he1]
  rw [← sharp_second_eigenvalue epsilon he.le]
  exact sharpModel_symmetric _ _ (sharp_parameters_relation epsilon he.le)

/-- Every proposed constant greater than one fails on an actual positive
three-coordinate rank-one law: its normalized covariance has a nonzero
vector with a positive eigenvalue strictly below that constant. -/
theorem normalized_covariance_constant_one_is_sharp (c : ℝ) (hc : 1 < c) :
    ∃ (w : Fin 3 → ℝ) (lambda : ℝ) (z : Fin 3 → ℝ),
      (∀ i, 0 < w i) ∧ 0 < lambda ∧ lambda < c ∧ z ≠ 0 ∧
        normalizedMatrix (EffectiveResistance.covarianceMatrix w 1) *ᵥ z = lambda • z := by
  obtain ⟨epsilon, he, he1, hlambda, hlambdac⟩ := exists_sharp_small_eigenvalue c hc
  refine ⟨sharpWeights epsilon, (1 + 3 * epsilon) / (1 + epsilon),
    sharpSymmetricVector (sharpA epsilon), sharpWeights_pos epsilon he he1,
    hlambda, hlambdac, sharpModel_symmetric_ne_zero _, ?_⟩
  exact sharp_actual_positive_eigenvector epsilon he he1
/-- No coefficient greater than one works uniformly in the original matrix
comparison. The same three-coordinate family proves this directly through
its explicit nonzero normalized eigenvector. -/
theorem covariance_comparison_constant_one_is_sharp (c : ℝ) (hc : 1 < c) :
    ∃ w : Fin 3 → ℝ, (∀ i, 0 < w i) ∧
      ¬ EffectiveResistance.LoewnerLE
        (c • EffectiveResistance.comparisonMatrix (covarianceVariance w 1))
        (EffectiveResistance.covarianceMatrix w 1) := by
  obtain ⟨w, lambda, z, hw, hlambda, hlambdac, hz, heig⟩ :=
    normalized_covariance_constant_one_is_sharp c hc
  refine ⟨w, hw, ?_⟩
  intro hcomparison
  have hdiag : ∀ i, 0 < EffectiveResistance.covarianceMatrix w 1 i i := by
    intro i
    exact covarianceVariance_pos w hw 1 (by decide) (by decide) i
  have hbound := normalized_eigenvalue_ge_of_scaled_comparison
    (EffectiveResistance.covarianceMatrix w 1)
    (EffectiveResistance.covariance_isSymm w 1) hdiag
    (covariance_mulVec_one_eq_zero w hw 1 (by decide)) c hcomparison
    lambda (ne_of_gt hlambda) z hz heig
  exact (not_le_of_gt hlambdac) hbound

end CoefficientOne
