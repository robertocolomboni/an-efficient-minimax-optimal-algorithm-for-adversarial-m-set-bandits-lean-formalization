import CoefficientOne.Sampling.Reindex
import CoefficientOne.Main

/-!
# The sharp covariance theorem on arbitrary finite coordinate sets

This is the reindexing bridge needed for every nonterminal residual law of
the sampler. Its application to conditional laws will use their explicitly
proved product-weight formula.
-/

open scoped BigOperators
open EffectiveResistance Matrix

namespace CoefficientOne.Sampling

noncomputable section

variable {ι κ : Type*} [Fintype ι] [Fintype κ] [DecidableEq ι] [DecidableEq κ]

theorem quadraticForm_submatrix_equiv (e : ι ≃ κ) (M : Matrix κ κ ℝ) (x : ι → ℝ) :
    quadraticForm M (fun b => x (e.symm b)) =
      quadraticForm (M.submatrix e e) x := by
  unfold quadraticForm Matrix.mulVec dotProduct
  rw [← e.sum_comp (fun b => x (e.symm b) *
    ∑ c, M b c * x (e.symm c))]
  simp only [e.symm_apply_apply, Matrix.submatrix_apply]
  apply Finset.sum_congr rfl
  intro i _
  rw [← e.sum_comp (fun c => M (e i) c * x (e.symm c))]
  simp only [e.symm_apply_apply]

theorem comparisonMatrix_reindex (e : ι ≃ κ) (v : ι → ℝ) :
    (comparisonMatrix (fun b => v (e.symm b))).submatrix e e = comparisonMatrix v := by
  have hsum : (∑ b, v (e.symm b)) = ∑ i, v i := e.symm.sum_comp v
  ext i j
  simp [comparisonMatrix, Matrix.diagonal_apply, Matrix.vecMulVec_apply, totalWeight, hsum,
    e.injective.eq_iff]

theorem covarianceVariance_reindex (e : ι ≃ κ) (w : ι → ℝ) (k : ℕ) :
    covarianceVariance (fun b => w (e.symm b)) k =
      fun b => covarianceVariance w k (e.symm b) := by
  funext b
  simpa only [e.apply_symm_apply, covarianceVariance] using
    covarianceMatrix_reindex e w k (e.symm b) (e.symm b)

/-- Coefficient one on any finite coordinate type, obtained by relabelling
the actual finite law; no covariance estimate is assumed. -/
theorem covariance_comparison_fintype (w : ι → ℝ) (hw : ∀ i, 0 < w i)
    (k : ℕ) (hkpos : 1 ≤ k) (hktop : k ≤ Fintype.card ι - 1) :
    LoewnerLE (comparisonMatrix (covarianceVariance w k)) (covarianceMatrix w k) := by
  let e : ι ≃ Fin (Fintype.card ι) := Fintype.equivFin ι
  have h := covariance_comparison_coefficient_one (fun b => w (e.symm b))
    (fun b => hw (e.symm b)) k hkpos hktop
  intro x
  have hx := h (fun b => x (e.symm b))
  rw [covarianceVariance_reindex, quadraticForm_submatrix_equiv,
    comparisonMatrix_reindex, quadraticForm_submatrix_equiv] at hx
  have hC : (covarianceMatrix (fun b => w (e.symm b)) k).submatrix e e =
      covarianceMatrix w k := by
    ext i j
    exact covarianceMatrix_reindex e w k i j
  rwa [hC] at hx

/-- Every nonzero normalized eigenvalue is at least one on an arbitrary
finite residual coordinate set. -/
theorem normalized_covariance_gap_fintype (w : ι → ℝ) (hw : ∀ i, 0 < w i)
    (k : ℕ) (hkpos : 1 ≤ k) (hktop : k ≤ Fintype.card ι - 1) :
    ∀ i, (Matrix.isHermitian_iff_isSymm.mpr
      (normalizedMatrix_isSymm (covarianceMatrix w k) (covariance_isSymm w k))).eigenvalues i ≠ 0 →
      1 ≤ (Matrix.isHermitian_iff_isSymm.mpr
        (normalizedMatrix_isSymm (covarianceMatrix w k) (covariance_isSymm w k))).eigenvalues i :=
  (externalField_comparison_iff_normalized_eigenvalue_gap w hw k hkpos hktop).mp
    (covariance_comparison_fintype w hw k hkpos hktop)

end
end CoefficientOne.Sampling
