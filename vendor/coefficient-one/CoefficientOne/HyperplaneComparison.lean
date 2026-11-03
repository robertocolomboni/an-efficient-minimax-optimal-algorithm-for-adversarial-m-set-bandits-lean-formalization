import Mathlib
import EffectiveResistance.MatrixOrder

/-!
# Rank-one comparison from a nonpositive hyperplane

This is a direct quadratic-form version of the final inertia argument in the
coefficient-one manuscript. If a symmetric form is nonpositive on one
hyperplane, and positive at a vector `e`, its value at `x` is at most
`(e^T C x)^2 / (e^T C e)`.

The proof explicitly subtracts multiples of `e` twice. First a vector
orthogonal to `e` for the bilinear form is moved into the given nonpositive
hyperplane. Then an arbitrary vector is reduced to this orthogonal case.
Only standard linear algebra and ordered-field algebra are used.

The covariance corollary takes `e = 1` and `C = Diag(v) - Sigma`.
-/

open scoped BigOperators
open Matrix

namespace CoefficientOne

noncomputable section

variable {ι : Type*} [Fintype ι]

/-- Symmetry of the bilinear form represented by a symmetric real matrix. -/
theorem symmetric_bilinear_swap (C : Matrix ι ι ℝ) (hC : C.IsSymm)
    (x y : ι → ℝ) : x ⬝ᵥ (C *ᵥ y) = y ⬝ᵥ (C *ᵥ x) := by
  simpa only [hC.eq] using Matrix.dotProduct_transpose_mulVec C x y

/-- Expansion after subtracting a multiple of a vector. -/
theorem quadraticForm_sub_scalar_vector (C : Matrix ι ι ℝ) (hC : C.IsSymm)
    (x e : ι → ℝ) (t : ℝ) :
    (x - t • e) ⬝ᵥ (C *ᵥ (x - t • e)) =
      x ⬝ᵥ (C *ᵥ x) - 2 * t * (e ⬝ᵥ (C *ᵥ x)) +
        t ^ 2 * (e ⬝ᵥ (C *ᵥ e)) := by
  simp only [Matrix.mulVec_sub, Matrix.mulVec_smul, dotProduct_sub,
    sub_dotProduct, dotProduct_smul, smul_dotProduct, smul_eq_mul]
  rw [symmetric_bilinear_swap C hC x e]
  ring

/-- A positive vector cannot lie in a hyperplane on which the form is
nonpositive. Thus the normal pairs nontrivially with that vector. -/
theorem hyperplane_normal_dot_ne_zero (C : Matrix ι ι ℝ) (b e : ι → ℝ)
    (hneg : ∀ z : ι → ℝ, b ⬝ᵥ z = 0 → z ⬝ᵥ (C *ᵥ z) ≤ 0)
    (he : 0 < e ⬝ᵥ (C *ᵥ e)) : b ⬝ᵥ e ≠ 0 := by
  intro hzero
  exact (not_le_of_gt he) (hneg e hzero)

/-- The form is nonpositive on the hyperplane orthogonal to a positive
vector for its own bilinear form. The proof explicitly moves `y` into the
original hyperplane, and the resulting correction is a nonnegative square. -/
theorem quadraticForm_nonpos_on_bilinear_orthogonal
    (C : Matrix ι ι ℝ) (b e : ι → ℝ) (hC : C.IsSymm)
    (hneg : ∀ z : ι → ℝ, b ⬝ᵥ z = 0 → z ⬝ᵥ (C *ᵥ z) ≤ 0)
    (he : 0 < e ⬝ᵥ (C *ᵥ e))
    (y : ι → ℝ) (hy : e ⬝ᵥ (C *ᵥ y) = 0) :
    y ⬝ᵥ (C *ᵥ y) ≤ 0 := by
  have hbe := hyperplane_normal_dot_ne_zero C b e hneg he
  let t : ℝ := (b ⬝ᵥ y) / (b ⬝ᵥ e)
  have hz : b ⬝ᵥ (y - t • e) = 0 := by
    simp only [dotProduct_sub, dotProduct_smul, smul_eq_mul]
    dsimp [t]
    rw [div_mul_cancel₀ _ hbe]
    ring
  have hquad := hneg (y - t • e) hz
  rw [quadraticForm_sub_scalar_vector C hC y e t, hy] at hquad
  have hcorrection : 0 ≤ t ^ 2 * (e ⬝ᵥ (C *ᵥ e)) :=
    mul_nonneg (sq_nonneg t) he.le
  linarith

/-- Rank-one upper bound for a form nonpositive on one hyperplane. -/
theorem quadraticForm_le_rankOne_of_nonpositive_hyperplane
    (C : Matrix ι ι ℝ) (b e : ι → ℝ) (hC : C.IsSymm)
    (hneg : ∀ z : ι → ℝ, b ⬝ᵥ z = 0 → z ⬝ᵥ (C *ᵥ z) ≤ 0)
    (he : 0 < e ⬝ᵥ (C *ᵥ e)) (x : ι → ℝ) :
    x ⬝ᵥ (C *ᵥ x) ≤ (e ⬝ᵥ (C *ᵥ x)) ^ 2 / (e ⬝ᵥ (C *ᵥ e)) := by
  let s : ℝ := (e ⬝ᵥ (C *ᵥ x)) / (e ⬝ᵥ (C *ᵥ e))
  have horth : e ⬝ᵥ (C *ᵥ (x - s • e)) = 0 := by
    simp only [Matrix.mulVec_sub, Matrix.mulVec_smul, dotProduct_sub,
      dotProduct_smul, smul_eq_mul]
    dsimp [s]
    rw [div_mul_cancel₀ _ he.ne']
    ring
  have hy := quadraticForm_nonpos_on_bilinear_orthogonal C b e hC hneg he
    (x - s • e) horth
  rw [quadraticForm_sub_scalar_vector C hC x e s] at hy
  have hcompletion :
      x ⬝ᵥ (C *ᵥ x) - 2 * s * (e ⬝ᵥ (C *ᵥ x)) +
          s ^ 2 * (e ⬝ᵥ (C *ᵥ e)) =
        x ⬝ᵥ (C *ᵥ x) - (e ⬝ᵥ (C *ᵥ x)) ^ 2 / (e ⬝ᵥ (C *ᵥ e)) := by
    dsimp [s]
    field_simp [he.ne']
    ring
  rw [hcompletion] at hy
  exact sub_nonpos.mp hy

/-- Taking the positive vector to be the all-ones vector yields the bound in
terms of the row-sum vector. Only the total row sum needs to be positive. -/
theorem quadraticForm_le_row_sum_rankOne
    (C : Matrix ι ι ℝ) (v b : ι → ℝ) (hC : C.IsSymm)
    (hv : C *ᵥ (fun _ => 1) = v) (hV : 0 < ∑ i, v i)
    (hneg : ∀ z : ι → ℝ, b ⬝ᵥ z = 0 → z ⬝ᵥ (C *ᵥ z) ≤ 0)
    (x : ι → ℝ) :
    x ⬝ᵥ (C *ᵥ x) ≤ (v ⬝ᵥ x) ^ 2 / (∑ i, v i) := by
  have htotal : (fun _ => 1) ⬝ᵥ (C *ᵥ (fun _ => 1)) = ∑ i, v i := by
    rw [hv]
    simp [dotProduct]
  have hbilinear : (fun _ => 1) ⬝ᵥ (C *ᵥ x) = v ⬝ᵥ x := by
    rw [symmetric_bilinear_swap C hC (fun _ => 1) x, hv, dotProduct_comm]
  have he : 0 < (fun _ => 1) ⬝ᵥ (C *ᵥ (fun _ => 1)) := by
    rw [htotal]
    exact hV
  have h := quadraticForm_le_rankOne_of_nonpositive_hyperplane
    C b (fun _ => 1) hC hneg he x
  simpa only [htotal, hbilinear] using h

/-- The row-sum bound as an inequality in the existing quadratic-form
definition of Loewner order. -/
theorem loewnerLE_rankOne_of_nonpositive_hyperplane [DecidableEq ι]
    (C : Matrix ι ι ℝ) (v b : ι → ℝ) (hC : C.IsSymm)
    (hv : C *ᵥ (fun _ => 1) = v) (hV : 0 < ∑ i, v i)
    (hneg : ∀ z : ι → ℝ, b ⬝ᵥ z = 0 → z ⬝ᵥ (C *ᵥ z) ≤ 0) :
    EffectiveResistance.LoewnerLE C
      ((∑ i, v i)⁻¹ • Matrix.vecMulVec v v) := by
  intro x
  rw [EffectiveResistance.quadraticForm_smul,
    EffectiveResistance.quadraticForm_vecMulVec]
  simpa only [EffectiveResistance.quadraticForm, dotProduct, div_eq_mul_inv,
    mul_comm] using quadraticForm_le_row_sum_rankOne C v b hC hv hV hneg x

/-- A zero-row-sum symmetric matrix obeys the coefficient-one covariance
comparison if its complementary matrix is nonpositive on one hyperplane.
This is the final manuscript comparison with `C = Diag(v) - Sigma`. -/
theorem covariance_comparison_of_nonpositive_hyperplane [DecidableEq ι]
    (Sigma : Matrix ι ι ℝ) (v b : ι → ℝ) (hSigma : Sigma.IsSymm)
    (hrow : Sigma *ᵥ (fun _ => 1) = 0) (hV : 0 < ∑ i, v i)
    (hneg : ∀ z : ι → ℝ, b ⬝ᵥ z = 0 →
      z ⬝ᵥ ((Matrix.diagonal v - Sigma) *ᵥ z) ≤ 0) :
    EffectiveResistance.LoewnerLE (EffectiveResistance.comparisonMatrix v) Sigma := by
  have hC : (Matrix.diagonal v - Sigma).IsSymm :=
    (Matrix.isSymm_diagonal v).sub hSigma
  have hv : (Matrix.diagonal v - Sigma) *ᵥ (fun _ => 1) = v := by
    rw [Matrix.sub_mulVec, hrow, sub_zero]
    ext i
    simp [Matrix.mulVec_diagonal]
  intro x
  have hupper := quadraticForm_le_row_sum_rankOne
    (Matrix.diagonal v - Sigma) v b hC hv hV hneg x
  change EffectiveResistance.quadraticForm (Matrix.diagonal v - Sigma) x ≤
    (v ⬝ᵥ x) ^ 2 / (∑ i, v i) at hupper
  rw [EffectiveResistance.quadraticForm_sub,
    EffectiveResistance.quadraticForm_diagonal] at hupper
  rw [EffectiveResistance.quadraticForm_comparisonMatrix]
  simp only [dotProduct] at hupper
  unfold EffectiveResistance.totalWeight
  linarith

/-- The strict version of the shifted-vector argument. A nonzero vector in
the bilinear orthogonal hyperplane remains nonzero after the correction. -/
theorem quadraticForm_neg_on_bilinear_orthogonal
    (C : Matrix ι ι ℝ) (b e : ι → ℝ) (hC : C.IsSymm)
    (hneg : ∀ z : ι → ℝ, z ≠ 0 → b ⬝ᵥ z = 0 → z ⬝ᵥ (C *ᵥ z) < 0)
    (he : 0 < e ⬝ᵥ (C *ᵥ e))
    (y : ι → ℝ) (hyne : y ≠ 0) (hy : e ⬝ᵥ (C *ᵥ y) = 0) :
    y ⬝ᵥ (C *ᵥ y) < 0 := by
  have hweak : ∀ z : ι → ℝ, b ⬝ᵥ z = 0 → z ⬝ᵥ (C *ᵥ z) ≤ 0 := by
    intro z hz
    by_cases hzero : z = 0
    · simp [hzero]
    · exact (hneg z hzero hz).le
  have hbe := hyperplane_normal_dot_ne_zero C b e hweak he
  let t : ℝ := (b ⬝ᵥ y) / (b ⬝ᵥ e)
  have hz : b ⬝ᵥ (y - t • e) = 0 := by
    simp only [dotProduct_sub, dotProduct_smul, smul_eq_mul]
    dsimp [t]
    rw [div_mul_cancel₀ _ hbe]
    ring
  have hzne : y - t • e ≠ 0 := by
    intro hzero
    have hyeq : y = t • e := sub_eq_zero.mp hzero
    have htzero : t = 0 := by
      rw [hyeq, Matrix.mulVec_smul, dotProduct_smul, smul_eq_mul] at hy
      exact (mul_eq_zero.mp hy).resolve_right he.ne'
    apply hyne
    rw [hyeq, htzero, zero_smul]
  have hquad := hneg (y - t • e) hzne hz
  rw [quadraticForm_sub_scalar_vector C hC y e t, hy] at hquad
  have hcorrection : 0 ≤ t ^ 2 * (e ⬝ᵥ (C *ᵥ e)) :=
    mul_nonneg (sq_nonneg t) he.le
  linarith

/-- A symmetric real matrix that is positive at some vector has a positive
eigenvalue. This uses the standard spectral theorem in mathlib. -/
theorem exists_positive_eigenvalue_of_quadraticForm_pos [DecidableEq ι]
    (C : Matrix ι ι ℝ) (hC : C.IsHermitian)
    (e : ι → ℝ) (he : 0 < e ⬝ᵥ (C *ᵥ e)) :
    ∃ i, 0 < hC.eigenvalues i := by
  by_contra! hnonpos
  have hdiag : (Matrix.diagonal (fun i => -hC.eigenvalues i)).PosSemidef :=
    Matrix.PosSemidef.diagonal (fun i => neg_nonneg.mpr (hnonpos i))
  have hminus : (-C).PosSemidef := by
    rw [hC.spectral_theorem, Unitary.conjStarAlgAut_apply]
    have hconj := hdiag.mul_mul_conjTranspose_same
      (hC.eigenvectorUnitary : Matrix ι ι ℝ)
    have hdiagEq : Matrix.diagonal (fun i => -hC.eigenvalues i) =
        -Matrix.diagonal hC.eigenvalues := (Matrix.diagonal_neg _).symm
    rw [hdiagEq, mul_neg, neg_mul] at hconj
    simpa [Function.comp_def, Matrix.star_eq_conjTranspose] using hconj
  have hn := hminus.dotProduct_mulVec_nonneg e
  simp only [star_trivial, Matrix.neg_mulVec, dotProduct_neg] at hn
  linarith
/-- Exact spectral inertia: strict negativity on one hyperplane and one
positive direction give a unique positive eigenvalue; every other eigenvalue
is strictly negative. Eigenvalues are counted with their multiplicities in
mathlib's orthonormal eigenvector basis. -/
theorem unique_positive_eigenvalue_of_negative_hyperplane [DecidableEq ι]
    (C : Matrix ι ι ℝ) (hC : C.IsHermitian) (b e : ι → ℝ)
    (hneg : ∀ z : ι → ℝ, z ≠ 0 → b ⬝ᵥ z = 0 → z ⬝ᵥ (C *ᵥ z) < 0)
    (he : 0 < e ⬝ᵥ (C *ᵥ e)) :
    ∃ i, 0 < hC.eigenvalues i ∧ ∀ j, j ≠ i → hC.eigenvalues j < 0 := by
  obtain ⟨i, hi⟩ := exists_positive_eigenvalue_of_quadraticForm_pos C hC e he
  refine ⟨i, hi, ?_⟩
  intro j hji
  let p : ι → ℝ := ⇑(hC.eigenvectorBasis i)
  let y : ι → ℝ := ⇑(hC.eigenvectorBasis j)
  have hquad (k : ι) :
      (⇑(hC.eigenvectorBasis k)) ⬝ᵥ (C *ᵥ ⇑(hC.eigenvectorBasis k)) =
        hC.eigenvalues k := by
    simpa using (hC.eigenvalues_eq k).symm
  have hp : 0 < p ⬝ᵥ (C *ᵥ p) := by
    simpa only [p, hquad] using hi
  have hyne : y ≠ 0 := by
    exact (WithLp.ofLp_eq_zero 2).ne.2 <| hC.eigenvectorBasis.orthonormal.ne_zero j
  have horth : p ⬝ᵥ (C *ᵥ y) = 0 := by
    dsimp [p, y]
    rw [hC.mulVec_eigenvectorBasis j, dotProduct_smul, smul_eq_mul]
    have hdot : (⇑(hC.eigenvectorBasis i)) ⬝ᵥ (⇑(hC.eigenvectorBasis j)) = 0 := by
      simpa only [EuclideanSpace.inner_eq_star_dotProduct, star_trivial] using
        hC.eigenvectorBasis.inner_eq_zero hji
    rw [hdot, mul_zero]
  have hn := quadraticForm_neg_on_bilinear_orthogonal C b p
    (Matrix.isHermitian_iff_isSymm.mp hC) hneg hp y hyne horth
  simpa only [y, hquad] using hn
end

end CoefficientOne
