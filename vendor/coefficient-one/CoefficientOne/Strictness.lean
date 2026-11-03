import CoefficientOne.Main

/-!
# Strict covariance comparison and normalized spectrum

This module completes the paragraph `Strictness for positive weights`.
The strict negative hyperplane is transported through the invertible diagonal
congruence. The strict shifted-vector argument identifies the kernel of the
comparison defect. The normalized spectral conclusions use this same inertia
mechanism and the trace, rather than a new estimate.
-/

open scoped BigOperators
open Matrix EffectiveResistance

namespace CoefficientOne

noncomputable section

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- Strict negativity survives an invertible positive diagonal congruence. -/
theorem negative_hyperplane_diagonal_congruence
    (H : Matrix ι ι ℝ) (b w : ι → ℝ) (c : ℝ) (hc : 0 < c)
    (hw : ∀ i, w i ≠ 0)
    (hneg : ∀ y : ι → ℝ, y ≠ 0 → b ⬝ᵥ y = 0 → y ⬝ᵥ (H *ᵥ y) < 0)
    (z : ι → ℝ) (hz0 : z ≠ 0) (hz : (b * w) ⬝ᵥ z = 0) :
    z ⬝ᵥ ((c • (Matrix.diagonal w * H * Matrix.diagonal w)) *ᵥ z) < 0 := by
  have hne : w * z ≠ 0 := by
    intro hzero
    apply hz0
    ext i
    have hi := congrFun hzero i
    exact (mul_eq_zero.mp hi).resolve_left (hw i)
  have horth : b ⬝ᵥ (w * z) = 0 := by
    simpa only [dotProduct, Pi.mul_apply, mul_assoc] using hz
  rw [Matrix.smul_mulVec, dotProduct_smul, smul_eq_mul,
    quadraticForm_diagonal_congruence]
  exact mul_neg_of_pos_of_neg hc (hneg (w * z) hne horth)

/-- The strict form of the rank-one comparison away from the positive line. -/
theorem quadraticForm_lt_rankOne_of_negative_hyperplane
    (C : Matrix ι ι ℝ) (b e : ι → ℝ) (hC : C.IsSymm)
    (hneg : ∀ z : ι → ℝ, z ≠ 0 → b ⬝ᵥ z = 0 → z ⬝ᵥ (C *ᵥ z) < 0)
    (he : 0 < e ⬝ᵥ (C *ᵥ e)) (x : ι → ℝ)
    (hx : ¬ ∃ t : ℝ, x = t • e) :
    x ⬝ᵥ (C *ᵥ x) < (e ⬝ᵥ (C *ᵥ x)) ^ 2 / (e ⬝ᵥ (C *ᵥ e)) := by
  let s : ℝ := (e ⬝ᵥ (C *ᵥ x)) / (e ⬝ᵥ (C *ᵥ e))
  have horth : e ⬝ᵥ (C *ᵥ (x - s • e)) = 0 := by
    simp only [Matrix.mulVec_sub, Matrix.mulVec_smul, dotProduct_sub,
      dotProduct_smul, smul_eq_mul]
    dsimp [s]
    rw [div_mul_cancel₀ _ he.ne']
    ring
  have hne : x - s • e ≠ 0 := fun hz => hx ⟨s, sub_eq_zero.mp hz⟩
  have hstrict := quadraticForm_neg_on_bilinear_orthogonal C b e hC hneg he
    (x - s • e) hne horth
  rw [quadraticForm_sub_scalar_vector C hC x e s] at hstrict
  have hcompletion :
      x ⬝ᵥ (C *ᵥ x) - 2 * s * (e ⬝ᵥ (C *ᵥ x)) +
          s ^ 2 * (e ⬝ᵥ (C *ᵥ e)) =
        x ⬝ᵥ (C *ᵥ x) - (e ⬝ᵥ (C *ᵥ x)) ^ 2 / (e ⬝ᵥ (C *ᵥ e)) := by
    dsimp [s]
    field_simp [he.ne']
    ring
  rw [hcompletion] at hstrict
  exact sub_neg.mp hstrict

variable {n : ℕ}

/-- The strict negative hyperplane of the actual complementary covariance. -/
theorem covariance_complement_exists_negative_hyperplane
    (w : Fin n → ℝ) (hw : ∀ i, 0 < w i) (m : ℕ)
    (hmpos : 1 ≤ m) (hmtop : m ≤ n - 1) :
    ∃ b : Fin n → ℝ, ∀ z, z ≠ 0 → b ⬝ᵥ z = 0 →
      z ⬝ᵥ ((Matrix.diagonal (covarianceVariance w m) - covarianceMatrix w m) *ᵥ z) < 0 := by
  obtain ⟨b, hb⟩ := kernelMatrix_exists_negative_hyperplane w hw (m - 1) (by omega)
  refine ⟨b * w, ?_⟩
  intro z hz horth
  rw [covariance_complement_eq_kernel_congruence w hw m hmpos
    (by simpa only [Fintype.card_fin] using hmtop.trans (Nat.sub_le _ _))]
  have hidx : (m : ℤ) - 1 = ((m - 1 : ℕ) : ℤ) := by omega
  rw [hidx]
  apply negative_hyperplane_diagonal_congruence _ b w _ ?_
    (fun i => (hw i).ne') hb z hz horth
  exact div_pos (by norm_num) (sq_pos_of_pos
    (elementarySum_pos w hw (by simpa only [Fintype.card_fin] using hmtop.trans (Nat.sub_le _ _))))

/-- The comparison defect is strictly positive on every nonconstant vector. -/
theorem covariance_defect_quadratic_pos
    (w : Fin n → ℝ) (hw : ∀ i, 0 < w i) (m : ℕ)
    (hmpos : 1 ≤ m) (hmtop : m ≤ n - 1)
    (x : Fin n → ℝ) (hx : ¬ ∀ i j, x i = x j) :
    0 < quadraticForm
      (covarianceMatrix w m - comparisonMatrix (covarianceVariance w m)) x := by
  let v := covarianceVariance w m
  let C := Matrix.diagonal v - covarianceMatrix w m
  have hC : C.IsSymm := (Matrix.isSymm_diagonal v).sub (covariance_isSymm w m)
  have hrow : C *ᵥ (fun _ => 1) = v := covariance_complement_mulVec_one w hw m
    (by simpa only [Fintype.card_fin] using hmtop.trans (Nat.sub_le _ _))
  have hV : 0 < ∑ i, v i := covarianceVariance_sum_pos w hw m hmpos
    (by simpa only [Fintype.card_fin] using hmtop)
  have htotal : (fun _ => 1) ⬝ᵥ (C *ᵥ (fun _ => 1)) = ∑ i, v i := by
    rw [hrow]
    simp [dotProduct]
  have hbilinear : (fun _ => 1) ⬝ᵥ (C *ᵥ x) = v ⬝ᵥ x := by
    rw [symmetric_bilinear_swap C hC, hrow, dotProduct_comm]
  obtain ⟨b, hb⟩ := covariance_complement_exists_negative_hyperplane w hw m hmpos hmtop
  have hxline : ¬ ∃ t : ℝ, x = t • (fun _ : Fin n => (1 : ℝ)) := by
    rintro ⟨t, rfl⟩
    exact hx (by simp)
  have hstrict := quadraticForm_lt_rankOne_of_negative_hyperplane C b (fun _ => 1)
    hC hb (by simpa only [htotal] using hV) x hxline
  rw [hbilinear, htotal] at hstrict
  change quadraticForm (Matrix.diagonal v - covarianceMatrix w m) x <
    (v ⬝ᵥ x) ^ 2 / (∑ i, v i) at hstrict
  rw [quadraticForm_sub, quadraticForm_diagonal] at hstrict
  rw [quadraticForm_sub, quadraticForm_comparisonMatrix]
  change 0 < quadraticForm (covarianceMatrix w m) x -
    ((∑ i, v i * x i ^ 2) - (∑ i, v i * x i) ^ 2 / (∑ i, v i))
  simp only [dotProduct] at hstrict
  linarith

theorem comparisonMatrix_mulVec_one (v : ι → ℝ) (hV : totalWeight v ≠ 0) :
    comparisonMatrix v *ᵥ (fun _ => 1) = 0 := by
  rw [comparisonMatrix, Matrix.sub_mulVec, Matrix.smul_mulVec, Matrix.vecMulVec_mulVec]
  have hv : v ⬝ᵥ (fun _ => 1) = totalWeight v := by simp [dotProduct, totalWeight]
  rw [hv]
  ext i
  simp [Matrix.mulVec_diagonal, Pi.sub_apply, Pi.smul_apply, smul_eq_mul,
    ← mul_assoc, hV]

/-- Precisely the constants lie in the kernel of the comparison defect. -/
theorem covariance_defect_mulVec_eq_zero_iff_constant
    (w : Fin n → ℝ) (hw : ∀ i, 0 < w i) (m : ℕ)
    (hmpos : 1 ≤ m) (hmtop : m ≤ n - 1) (x : Fin n → ℝ) :
    (covarianceMatrix w m - comparisonMatrix (covarianceVariance w m)) *ᵥ x = 0 ↔
      ∀ i j, x i = x j := by
  constructor
  · intro hzero
    by_contra hnot
    have hpos := covariance_defect_quadratic_pos w hw m hmpos hmtop x hnot
    simp only [quadraticForm, hzero, dotProduct_zero] at hpos
    exact (lt_irrefl 0) hpos
  · intro hconstant
    let i₀ : Fin n := ⟨0, by omega⟩
    have hx : x = x i₀ • (fun _ : Fin n => (1 : ℝ)) := by
      ext i
      simpa using hconstant i i₀
    have hV : totalWeight (covarianceVariance w m) ≠ 0 :=
      (covarianceVariance_sum_pos w hw m hmpos
        (by simpa only [Fintype.card_fin] using hmtop)).ne'
    rw [hx, Matrix.mulVec_smul, Matrix.sub_mulVec,
      covariance_mulVec_one_eq_zero w hw m
        (by simpa only [Fintype.card_fin] using hmtop.trans (Nat.sub_le _ _)),
      comparisonMatrix_mulVec_one _ hV, sub_self, smul_zero]

/-- Equivalent quadratic characterization of the exact defect kernel. -/
theorem covariance_defect_quadratic_eq_zero_iff_constant
    (w : Fin n → ℝ) (hw : ∀ i, 0 < w i) (m : ℕ)
    (hmpos : 1 ≤ m) (hmtop : m ≤ n - 1) (x : Fin n → ℝ) :
    quadraticForm (covarianceMatrix w m - comparisonMatrix (covarianceVariance w m)) x = 0 ↔
      ∀ i j, x i = x j := by
  constructor
  · intro hz
    by_contra hnot
    have := covariance_defect_quadratic_pos w hw m hmpos hmtop x hnot
    exact (ne_of_gt this) hz
  · intro hx
    simp only [quadraticForm,
      (covariance_defect_mulVec_eq_zero_iff_constant w hw m hmpos hmtop x).mpr hx,
      dotProduct_zero]

end

end CoefficientOne
