import CoefficientOne.Sampling.ResidualCovariance

/-! # Zero-padded residual covariance Laplacians, including forced states -/

open scoped BigOperators
open EffectiveResistance Matrix
namespace CoefficientOne.Sampling
noncomputable section
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

theorem sum_eq_residual_subtype (R : Finset ι) (f : ι → ℝ)
    (hf : ∀ i ∉ R, f i = 0) : ∑ i, f i = ∑ i : R, f i.val := by
  have hs : ∑ i ∈ R, f i = ∑ i, f i :=
    Finset.sum_subset (Finset.subset_univ R) (fun i _ hi => hf i hi)
  rw [← hs]
  exact Finset.sum_subtype R (fun _ => Iff.rfl) f

theorem residualCovariance_mulVec_subtype (w : ι → ℝ) (R : Finset ι) (r : ℕ)
    (a : ι → ℝ) (i : R) :
    (residualCovariance w R r *ᵥ a) i.val =
      (covarianceMatrix (fun j : R => w j.val) r *ᵥ (fun j : R => a j.val)) i := by
  change (∑ j, residualCovariance w R r i.val j * a j) =
    ∑ j : R, covarianceMatrix (fun j : R => w j.val) r i j * a j.val
  rw [sum_eq_residual_subtype R _ (fun j hj => by
    rw [residualCovariance_notMem_right w R r i.val j hj, zero_mul])]
  simp_rw [residualCovariance_subtype]

theorem residualCovariance_mulVec_notMem (w : ι → ℝ) (R : Finset ι) (r : ℕ)
    (a : ι → ℝ) (i : ι) (hi : i ∉ R) :
    (residualCovariance w R r *ᵥ a) i = 0 := by
  simp [Matrix.mulVec, dotProduct, residualCovariance_notMem_left w R r i _ hi]

theorem residualCovariance_quadratic (w : ι → ℝ) (R : Finset ι) (r : ℕ) (a : ι → ℝ) :
    quadraticForm (residualCovariance w R r) a =
      quadraticForm (covarianceMatrix (fun i : R => w i.val) r) (fun i : R => a i.val) := by
  unfold quadraticForm dotProduct
  rw [sum_eq_residual_subtype R _ (fun i hi => by
    rw [residualCovariance_mulVec_notMem w R r a i hi, mul_zero])]
  simp_rw [residualCovariance_mulVec_subtype]

theorem residualVariance_eq_covariance (w : ι → ℝ) (hw : ∀ i, 0 < w i)
    (R : Finset ι) (r : ℕ) (hr : r ≤ R.card) (a : ι → ℝ) :
    residualVariance w hw R r hr a = quadraticForm (residualCovariance w R r) a := by
  rw [residualVariance_eq_subtype, residualCovariance_quadratic]

theorem residualCovariance_l1_mulVec (w : ι → ℝ) (R : Finset ι) (r : ℕ) (a : ι → ℝ) :
    l1Norm (residualCovariance w R r *ᵥ a) =
      l1Norm (covarianceMatrix (fun i : R => w i.val) r *ᵥ (fun i : R => a i.val)) := by
  unfold l1Norm
  rw [sum_eq_residual_subtype R _ (fun i hi => by
    rw [residualCovariance_mulVec_notMem w R r a i hi, abs_zero])]
  simp_rw [residualCovariance_mulVec_subtype]

theorem residualCovariance_rowSum_zero (w : ι → ℝ) (hw : ∀ i, 0 < w i)
    (R : Finset ι) (r : ℕ) (i : ι) : ∑ j, residualCovariance w R r i j = 0 := by
  by_cases hr : r ≤ R.card
  · by_cases hi : i ∈ R
    · rw [sum_eq_residual_subtype R _ (fun j hj => residualCovariance_notMem_right w R r i j hj)]
      change (∑ j : R, residualCovariance w R r (⟨i, hi⟩ : R).val j.val) = 0
      calc
        _ = ∑ j : R, covarianceMatrix (fun j : R => w j.val) r ⟨i, hi⟩ j :=
          Finset.sum_congr rfl (fun j _ => residualCovariance_subtype w R r ⟨i, hi⟩ j)
        _ = 0 := covariance_rowSum_zero (fun j : R => w j.val) (fun j => hw j.val)
          (by simpa using hr) ⟨i, hi⟩
    · simp [residualCovariance_notMem_left w R r i _ hi]
  · rw [residualCovariance_of_card_lt w R r (lt_of_not_ge hr)]
    simp

theorem residualCovariance_offdiag_nonpos (w : ι → ℝ) (hw : ∀ i, 0 < w i)
    (R : Finset ι) (r : ℕ) (i j : ι) (hij : i ≠ j) : residualCovariance w R r i j ≤ 0 := by
  by_cases h0 : r = 0
  · subst r; simp
  by_cases ht : r = R.card
  · subst r; simp [residualCovariance_full w hw]
  by_cases hr : r < R.card
  · by_cases hi : i ∈ R
    · by_cases hj : j ∈ R
      · change residualCovariance w R r (⟨i, hi⟩ : R).val (⟨j, hj⟩ : R).val ≤ 0
        rw [residualCovariance_subtype]
        exact (externalField_covariance_offDiagonal_neg (fun i : R => w i.val)
          (fun i => hw i.val) r (by omega) (by simpa using (show r ≤ R.card - 1 by omega))
          ⟨i, hi⟩ ⟨j, hj⟩ (fun he => hij (congrArg Subtype.val he))).le
      · rw [residualCovariance_notMem_right w R r i j hj]
    · rw [residualCovariance_notMem_left w R r i j hi]
  · rw [residualCovariance_of_card_lt w R r (by omega)]
    rfl

def residualNetwork (w : ι → ℝ) (hw : ∀ i, 0 < w i) (R : Finset ι) (r : ℕ) :
    ConductanceNetwork ι where
  conductance i j := if i = j then 0 else -residualCovariance w R r i j
  symmetric := by
    apply Matrix.IsSymm.ext
    intro i j
    by_cases h : i = j
    · subst j; simp
    · simp [h, Ne.symm h, residualCovariance_comm]
  nonnegative := by
    intro i j
    by_cases h : i = j
    · simp [h]
    · simp only [h, if_false]
      exact neg_nonneg.mpr (residualCovariance_offdiag_nonpos w hw R r i j h)
  diagonal_zero := by intro i; simp

theorem residualNetwork_degree (w : ι → ℝ) (hw : ∀ i, 0 < w i)
    (R : Finset ι) (r : ℕ) (i : ι) :
    (residualNetwork w hw R r).degree i = residualCovariance w R r i i := by
  have hr := residualCovariance_rowSum_zero w hw R r i
  unfold ConductanceNetwork.degree residualNetwork
  have he : (∑ j, if i = j then 0 else -residualCovariance w R r i j) =
      -(∑ j, residualCovariance w R r i j) + residualCovariance w R r i i := by
    calc
      _ = ∑ j, (-residualCovariance w R r i j +
          if j = i then residualCovariance w R r i i else 0) := by
        apply Finset.sum_congr rfl
        intro j _
        by_cases h : i = j
        · subst j; simp
        · simp [h, Ne.symm h]
      _ = _ := by rw [Finset.sum_add_distrib, Finset.sum_neg_distrib]; simp
  rw [he, hr]
  ring

theorem residualNetwork_laplacian (w : ι → ℝ) (hw : ∀ i, 0 < w i)
    (R : Finset ι) (r : ℕ) : (residualNetwork w hw R r).laplacian = residualCovariance w R r := by
  ext i j
  by_cases h : i = j
  · subst j
    simp only [ConductanceNetwork.laplacian, Matrix.sub_apply, Matrix.diagonal_apply_eq]
    rw [residualNetwork_degree]
    simp [residualNetwork]
  · rw [(residualNetwork w hw R r).laplacian_offDiagonal h]
    change -(if i = j then 0 else -residualCovariance w R r i j) = _
    simp [h]

end
end CoefficientOne.Sampling
