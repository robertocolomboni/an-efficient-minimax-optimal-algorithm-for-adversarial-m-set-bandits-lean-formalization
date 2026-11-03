import CoefficientOne.NormalizedCovariance
import CoefficientOne.CovarianceBridge
import CoefficientOne.MatrixCertificate

/-!
# Normalized covariance and its spectral gap

This file proves both directions of the manuscript's spectral interpretation.
The first part treats a general symmetric matrix with a specified one-dimensional
kernel. The second part transports the comparison by its positive diagonal
normalization and specializes to the actual fixed-rank covariance.
-/

open scoped BigOperators
open Matrix EffectiveResistance

namespace CoefficientOne

noncomputable section

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- Orthogonal projection onto the perpendicular of a nonzero vector. -/
def perpendicularProjection (u : ι → ℝ) : Matrix ι ι ℝ :=
  1 - (u ⬝ᵥ u)⁻¹ • Matrix.vecMulVec u u

theorem perpendicularProjection_quadraticForm (u x : ι → ℝ) :
    quadraticForm (perpendicularProjection u) x =
      x ⬝ᵥ x - (u ⬝ᵥ x) ^ 2 / (u ⬝ᵥ u) := by
  rw [perpendicularProjection, quadraticForm_sub, quadraticForm_smul,
    quadraticForm_vecMulVec]
  simp [quadraticForm, dotProduct, div_eq_mul_inv, mul_comm]

theorem perpendicularProjection_mulVec_self (u : ι → ℝ) (hu : u ⬝ᵥ u ≠ 0) :
    perpendicularProjection u *ᵥ u = 0 := by
  simp [perpendicularProjection, Matrix.sub_mulVec, Matrix.smul_mulVec,
    Matrix.vecMulVec_mulVec, smul_smul, hu]

theorem perpendicularProjection_mulVec_of_orthogonal (u x : ι → ℝ)
    (hx : u ⬝ᵥ x = 0) : perpendicularProjection u *ᵥ x = x := by
  simp [perpendicularProjection, Matrix.sub_mulVec, Matrix.smul_mulVec,
    Matrix.vecMulVec_mulVec, hx]

theorem perpendicularProjection_isSymm (u : ι → ℝ) :
    (perpendicularProjection u).IsSymm := by
  apply Matrix.IsSymm.ext
  intro i j
  simp [perpendicularProjection, Matrix.vecMulVec, mul_comm]
  exact Matrix.isSymm_one.apply i j

/-- Every concrete eigenvalue occurs among mathlib's indexed eigenvalues. -/
theorem eigenvalue_eq_indexed_of_mulVec (N : Matrix ι ι ℝ) (hN : N.IsHermitian)
    (μ : ℝ) (x : ι → ℝ) (hx : x ≠ 0) (heig : N *ᵥ x = μ • x) :
    ∃ i, hN.eigenvalues i = μ := by
  have heigenvector : Module.End.HasEigenvector N.toLin' μ x := by
    refine ⟨Module.End.mem_eigenspace_iff.mpr ?_, hx⟩
    exact heig
  have hspectrum := (Module.End.hasEigenvalue_of_hasEigenvector heigenvector).mem_spectrum
  rw [Matrix.spectrum_toLin', hN.spectrum_real_eq_range_eigenvalues] at hspectrum
  exact hspectrum

omit [DecidableEq ι] in
/-- A nonzero-eigenvalue eigenvector is orthogonal to every kernel vector. -/
theorem kernel_dot_eigenvector_eq_zero (N : Matrix ι ι ℝ) (hN : N.IsSymm)
    (u x : ι → ℝ) (hNu : N *ᵥ u = 0) (μ : ℝ) (hμ : μ ≠ 0)
    (heig : N *ᵥ x = μ • x) : u ⬝ᵥ x = 0 := by
  have hswap := symmetric_bilinear_swap N hN u x
  rw [heig, hNu, dotProduct_zero, dotProduct_smul, smul_eq_mul] at hswap
  exact (mul_eq_zero.mp hswap).resolve_left hμ

/-- The projection comparison gives the lower bound on every nonzero
eigenvalue, by evaluation at a corresponding nonzero eigenvector. -/
theorem eigenvalue_one_le_of_projection_comparison
    (N : Matrix ι ι ℝ) (hN : N.IsSymm) (u : ι → ℝ) (hNu : N *ᵥ u = 0)
    (hcomparison : LoewnerLE (perpendicularProjection u) N)
    (μ : ℝ) (hμ : μ ≠ 0) (x : ι → ℝ) (hx : x ≠ 0)
    (heig : N *ᵥ x = μ • x) : 1 ≤ μ := by
  have horth := kernel_dot_eigenvector_eq_zero N hN u x hNu μ hμ heig
  have hbound := hcomparison x
  rw [perpendicularProjection_quadraticForm, horth] at hbound
  simp only [zero_pow (by decide : 2 ≠ 0), zero_div, sub_zero,
    quadraticForm, heig, dotProduct_smul, smul_eq_mul] at hbound
  have hnorm : 0 < x ⬝ᵥ x := by
    simpa only [star_trivial] using (dotProduct_self_star_pos_iff.mpr hx)
  nlinarith

/-- Conversely, if the kernel is exactly the stated line, a lower bound on
all nonzero eigenvalues gives the projection comparison. We diagonalize the
difference matrix and check the sign of each of its eigenvalues. -/
theorem projection_comparison_of_eigenvalue_gap
    (N : Matrix ι ι ℝ) (hN : N.IsHermitian) (u : ι → ℝ)
    (hu : 0 < u ⬝ᵥ u)
    (hker : ∀ x : ι → ℝ, N *ᵥ x = 0 ↔ ∃ c : ℝ, x = c • u)
    (hgap : ∀ μ : ℝ, μ ≠ 0 → ∀ x : ι → ℝ, x ≠ 0 →
      N *ᵥ x = μ • x → 1 ≤ μ) :
    LoewnerLE (perpendicularProjection u) N := by
  have hNu : N *ᵥ u = 0 := (hker u).mpr ⟨1, by simp⟩
  let A : Matrix ι ι ℝ := N - perpendicularProjection u
  have hA : A.IsHermitian := by
    apply Matrix.isHermitian_iff_isSymm.mpr
    exact (Matrix.isHermitian_iff_isSymm.mp hN).sub (perpendicularProjection_isSymm u)
  have hAu : A *ᵥ u = 0 := by
    simp [A, Matrix.sub_mulVec, hNu, perpendicularProjection_mulVec_self u hu.ne']
  have hApos : A.PosSemidef := by
    apply hA.posSemidef_iff_eigenvalues_nonneg.mpr
    intro i
    change (0 : ℝ) ≤ hA.eigenvalues i
    by_cases hzero : hA.eigenvalues i = 0
    · exact hzero.ge
    · let x : ι → ℝ := ⇑(hA.eigenvectorBasis i)
      have hx : x ≠ 0 :=
        (WithLp.ofLp_eq_zero 2).ne.2 (hA.eigenvectorBasis.orthonormal.ne_zero i)
      have heig : A *ᵥ x = hA.eigenvalues i • x := hA.mulVec_eigenvectorBasis i
      have horth : u ⬝ᵥ x = 0 := kernel_dot_eigenvector_eq_zero A
        (Matrix.isHermitian_iff_isSymm.mp hA) u x hAu (hA.eigenvalues i) hzero heig
      have heig' : N *ᵥ x - x = hA.eigenvalues i • x := by
        simpa only [A, Matrix.sub_mulVec,
          perpendicularProjection_mulVec_of_orthogonal u x horth] using heig
      have hNx : N *ᵥ x = (hA.eigenvalues i + 1) • x := by
        calc
          _ = (N *ᵥ x - x) + x := by abel
          _ = hA.eigenvalues i • x + x := by rw [heig']
          _ = _ := by rw [add_smul, one_smul]
      have hμ : hA.eigenvalues i + 1 ≠ 0 := by
        intro hμzero
        have hNxzero : N *ᵥ x = 0 := by simpa [hμzero] using hNx
        obtain ⟨c, hc⟩ := (hker x).mp hNxzero
        have hc0 : c = 0 := by
          rw [hc, dotProduct_smul, smul_eq_mul] at horth
          exact (mul_eq_zero.mp horth).resolve_right hu.ne'
        apply hx
        simp [hc, hc0]
      have hbound := hgap (hA.eigenvalues i + 1) hμ x hx hNx
      linarith
  intro x
  have hnonneg := hApos.dotProduct_mulVec_nonneg x
  change 0 ≤ star x ⬝ᵥ ((N - perpendicularProjection u) *ᵥ x) at hnonneg
  simpa only [star_trivial, Matrix.sub_mulVec, dotProduct_sub,
    quadraticForm, sub_nonneg] using hnonneg

/-- Exact equivalence between the projection comparison and the lower bound
on all nonzero indexed eigenvalues (including multiplicities). -/
theorem projection_comparison_iff_eigenvalue_gap
    (N : Matrix ι ι ℝ) (hN : N.IsHermitian) (u : ι → ℝ)
    (hu : 0 < u ⬝ᵥ u)
    (hker : ∀ x : ι → ℝ, N *ᵥ x = 0 ↔ ∃ c : ℝ, x = c • u) :
    LoewnerLE (perpendicularProjection u) N ↔
      ∀ i, hN.eigenvalues i ≠ 0 → 1 ≤ hN.eigenvalues i := by
  constructor
  · intro hcomparison i hi
    apply eigenvalue_one_le_of_projection_comparison N
      (Matrix.isHermitian_iff_isSymm.mp hN) u ((hker u).mpr ⟨1, by simp⟩)
      hcomparison (hN.eigenvalues i) hi (⇑(hN.eigenvectorBasis i))
      ((WithLp.ofLp_eq_zero 2).ne.2 (hN.eigenvectorBasis.orthonormal.ne_zero i))
      (hN.mulVec_eigenvectorBasis i)
  · intro hgap
    apply projection_comparison_of_eigenvalue_gap N hN u hu hker
    intro μ hμ x hx heig
    obtain ⟨i, hi⟩ := eigenvalue_eq_indexed_of_mulVec N hN μ x hx heig
    simpa only [hi] using hgap i (by simpa only [hi] using hμ)

/-- The canonical kernel vector after positive diagonal normalization. -/
def diagonalSqrtVector (M : Matrix ι ι ℝ) : ι → ℝ :=
  fun i => Real.sqrt (M i i)

omit [Fintype ι] [DecidableEq ι] in theorem diagonalSqrtVector_pos (M : Matrix ι ι ℝ) (hdiag : ∀ i, 0 < M i i)
    (i : ι) : 0 < diagonalSqrtVector M i := Real.sqrt_pos.mpr (hdiag i)

omit [DecidableEq ι] in theorem diagonalSqrtVector_dot_self (M : Matrix ι ι ℝ) (hdiag : ∀ i, 0 < M i i) :
    diagonalSqrtVector M ⬝ᵥ diagonalSqrtVector M = ∑ i, M i i := by
  apply Finset.sum_congr rfl
  intro i hi
  exact Real.mul_self_sqrt (hdiag i).le

/-- Entrywise expression for the normalized matrix acting on a vector. -/
theorem normalizedMatrix_mulVec_eq (M : Matrix ι ι ℝ) (x : ι → ℝ) :
    normalizedMatrix M *ᵥ x = (M *ᵥ (x / diagonalSqrtVector M)) / diagonalSqrtVector M := by
  rw [normalizedMatrix_eq_diagonal_mul]
  simp only [← Matrix.mulVec_mulVec]
  have hcoords : (Matrix.diagonal (fun i => (Real.sqrt (M i i))⁻¹)) *ᵥ x =
      x / diagonalSqrtVector M := by
    ext i
    simp [Matrix.mulVec_diagonal, diagonalSqrtVector, div_eq_mul_inv, mul_comm]
  rw [hcoords]
  ext i
  simp [Matrix.mulVec_diagonal, diagonalSqrtVector, div_eq_mul_inv, mul_comm]

/-- Congruence of the normalized quadratic form. -/
theorem normalizedMatrix_quadraticForm (M : Matrix ι ι ℝ) (x : ι → ℝ) :
    quadraticForm (normalizedMatrix M) x = quadraticForm M (x / diagonalSqrtVector M) := by
  unfold quadraticForm
  rw [normalizedMatrix_eq_diagonal_mul, quadraticForm_diagonal_congruence]
  have hcoords : (fun i => (Real.sqrt (M i i))⁻¹) * x = x / diagonalSqrtVector M := by
    ext i
    simp [diagonalSqrtVector, div_eq_mul_inv, mul_comm]
  rw [hcoords]

/-- Under positive diagonal rescaling, the weighted comparison becomes the
ordinary orthogonal projection onto the perpendicular of the square-root vector. -/
theorem comparisonMatrix_normalized_quadraticForm
    (M : Matrix ι ι ℝ) (hdiag : ∀ i, 0 < M i i) (x : ι → ℝ) :
    quadraticForm (comparisonMatrix (fun i => M i i)) (x / diagonalSqrtVector M) =
      quadraticForm (perpendicularProjection (diagonalSqrtVector M)) x := by
  rw [quadraticForm_comparisonMatrix, perpendicularProjection_quadraticForm]
  have hfirst : (∑ i, M i i * (x / diagonalSqrtVector M) i ^ 2) = x ⬝ᵥ x := by
    apply Finset.sum_congr rfl
    intro i hi
    simp only [Pi.div_apply, diagonalSqrtVector, div_pow, Real.sq_sqrt (hdiag i).le]
    field_simp [(hdiag i).ne']
  have hsecond : (∑ i, M i i * (x / diagonalSqrtVector M) i) =
      diagonalSqrtVector M ⬝ᵥ x := by
    apply Finset.sum_congr rfl
    intro i hi
    change M i i * (x i / Real.sqrt (M i i)) = Real.sqrt (M i i) * x i
    calc
      _ = (M i i / Real.sqrt (M i i)) * x i := by ring
      _ = _ := by rw [Real.div_sqrt]
  rw [hfirst, hsecond, diagonalSqrtVector_dot_self M hdiag]
  rfl

omit [Fintype ι] [DecidableEq ι] in
/-- Positive diagonal scaling is invertible on coordinates. -/
theorem mul_diagonalSqrtVector_div_self
    (M : Matrix ι ι ℝ) (hdiag : ∀ i, 0 < M i i) (x : ι → ℝ) :
    (diagonalSqrtVector M * x) / diagonalSqrtVector M = x := by
  ext i
  simp only [Pi.div_apply, Pi.mul_apply]
  exact mul_div_cancel_left₀ (x i) (diagonalSqrtVector_pos M hdiag i).ne'

/-- Equivalence of the original covariance comparison and its normalized
projection form. No spectral assertion is assumed in this algebraic step. -/
theorem comparison_iff_normalized_projection
    (M : Matrix ι ι ℝ) (hdiag : ∀ i, 0 < M i i) :
    LoewnerLE (comparisonMatrix (fun i => M i i)) M ↔
      LoewnerLE (perpendicularProjection (diagonalSqrtVector M)) (normalizedMatrix M) := by
  constructor
  · intro h x
    rw [← comparisonMatrix_normalized_quadraticForm M hdiag x,
      normalizedMatrix_quadraticForm]
    exact h (x / diagonalSqrtVector M)
  · intro h x
    have hbound := h (diagonalSqrtVector M * x)
    rw [← comparisonMatrix_normalized_quadraticForm M hdiag,
      normalizedMatrix_quadraticForm, mul_diagonalSqrtVector_div_self M hdiag x] at hbound
    exact hbound

/-- Exact transport of the kernel by diagonal normalization. -/
theorem normalizedMatrix_mulVec_eq_zero_iff
    (M : Matrix ι ι ℝ) (hdiag : ∀ i, 0 < M i i) (x : ι → ℝ) :
    normalizedMatrix M *ᵥ x = 0 ↔ M *ᵥ (x / diagonalSqrtVector M) = 0 := by
  rw [normalizedMatrix_mulVec_eq]
  constructor
  · intro hzero
    ext i
    have hi := congrFun hzero i
    simp only [Pi.div_apply, Pi.zero_apply] at hi
    exact (div_eq_zero_iff.mp hi).resolve_right (diagonalSqrtVector_pos M hdiag i).ne'
  · intro hzero
    ext i
    simp [hzero, Pi.div_apply]

/-- A matrix with kernel equal to the constant vectors normalizes to a
matrix with kernel equal to the line through its square-root diagonal. -/
theorem normalizedMatrix_kernel_line [Nonempty ι]
    (M : Matrix ι ι ℝ) (hdiag : ∀ i, 0 < M i i)
    (hker : ∀ x : ι → ℝ, M *ᵥ x = 0 ↔ ∀ i j, x i = x j) (x : ι → ℝ) :
    normalizedMatrix M *ᵥ x = 0 ↔ ∃ c : ℝ, x = c • diagonalSqrtVector M := by
  rw [normalizedMatrix_mulVec_eq_zero_iff M hdiag, hker]
  constructor
  · intro hconstant
    let i : ι := Classical.choice inferInstance
    refine ⟨x i / diagonalSqrtVector M i, ?_⟩
    ext j
    have hj := hconstant j i
    simp only [Pi.div_apply] at hj
    exact (div_eq_iff (diagonalSqrtVector_pos M hdiag j).ne').mp hj
  · rintro ⟨c, rfl⟩ i j
    simp [Pi.div_apply, Pi.smul_apply, smul_eq_mul,
      (diagonalSqrtVector_pos M hdiag i).ne', (diagonalSqrtVector_pos M hdiag j).ne']

/-- The complete generic spectral interpretation of coefficient one.
It applies to a symmetric matrix with positive diagonal and precisely the
constant vectors as its kernel. -/
theorem covariance_comparison_iff_normalized_eigenvalue_gap [Nonempty ι]
    (M : Matrix ι ι ℝ) (hM : M.IsSymm) (hdiag : ∀ i, 0 < M i i)
    (hker : ∀ x : ι → ℝ, M *ᵥ x = 0 ↔ ∀ i j, x i = x j) :
    LoewnerLE (comparisonMatrix (fun i => M i i)) M ↔
      ∀ i, (Matrix.isHermitian_iff_isSymm.mpr (normalizedMatrix_isSymm M hM)).eigenvalues i ≠ 0 →
        1 ≤ (Matrix.isHermitian_iff_isSymm.mpr (normalizedMatrix_isSymm M hM)).eigenvalues i := by
  rw [comparison_iff_normalized_projection M hdiag]
  apply projection_comparison_iff_eigenvalue_gap
  · rw [diagonalSqrtVector_dot_self M hdiag]
    exact Finset.sum_pos (fun i hi => hdiag i) Finset.univ_nonempty
  · exact normalizedMatrix_kernel_line M hdiag hker

/-- Both directions of the manuscript's equivalence, for the actual
fixed-rank external-field covariance and all nontrivial ranks. -/
theorem externalField_comparison_iff_normalized_eigenvalue_gap
    (w : ι → ℝ) (hw : ∀ k, 0 < w k) (m : ℕ)
    (hmpos : 1 ≤ m) (hmtop : m ≤ Fintype.card ι - 1) :
    LoewnerLE (comparisonMatrix (covarianceVariance w m)) (covarianceMatrix w m) ↔
      ∀ i, (Matrix.isHermitian_iff_isSymm.mpr
        (normalizedMatrix_isSymm (covarianceMatrix w m) (covariance_isSymm w m))).eigenvalues i ≠ 0 →
        1 ≤ (Matrix.isHermitian_iff_isSymm.mpr
          (normalizedMatrix_isSymm (covarianceMatrix w m) (covariance_isSymm w m))).eigenvalues i := by
  haveI : Nonempty ι := Fintype.card_pos_iff.mp (by omega)
  exact covariance_comparison_iff_normalized_eigenvalue_gap
    (covarianceMatrix w m) (covariance_isSymm w m)
    (covarianceVariance_pos w hw m hmpos hmtop)
    (covariance_mulVec_eq_zero_iff_constant w hw m hmpos hmtop)
/-- Diagonal normalization preserves positive semidefiniteness. -/
theorem normalizedMatrix_posSemidef (M : Matrix ι ι ℝ) (hM : M.PosSemidef) :
    (normalizedMatrix M).PosSemidef := by
  rw [normalizedMatrix_eq_diagonal_mul]
  simpa using hM.mul_mul_conjTranspose_same
    (Matrix.diagonal (fun i => (Real.sqrt (M i i))⁻¹))

/-- The actual normalized covariance is positive semidefinite. -/
theorem externalField_normalizedMatrix_posSemidef
    (w : ι → ℝ) (hw : ∀ k, 0 < w k) (m : ℕ)
    (hmcard : m ≤ Fintype.card ι) :
    (normalizedMatrix (covarianceMatrix w m)).PosSemidef := by
  exact normalizedMatrix_posSemidef _ (covarianceMatrix_posSemidef w hw m hmcard)
/-- The same Rayleigh-quotient implication for an arbitrary proposed constant,
useful when proving that coefficient one cannot be uniformly improved. -/
theorem eigenvalue_ge_of_scaled_projection_comparison
    (N : Matrix ι ι ℝ) (hN : N.IsSymm) (u : ι → ℝ) (hNu : N *ᵥ u = 0)
    (c : ℝ) (hcomparison : LoewnerLE (c • perpendicularProjection u) N)
    (μ : ℝ) (hμ : μ ≠ 0) (x : ι → ℝ) (hx : x ≠ 0)
    (heig : N *ᵥ x = μ • x) : c ≤ μ := by
  have horth := kernel_dot_eigenvector_eq_zero N hN u x hNu μ hμ heig
  have hbound := hcomparison x
  rw [quadraticForm_smul, perpendicularProjection_quadraticForm, horth] at hbound
  simp only [zero_pow (by decide : 2 ≠ 0), zero_div, sub_zero,
    quadraticForm, heig, dotProduct_smul, smul_eq_mul] at hbound
  have hnorm : 0 < x ⬝ᵥ x := by
    simpa only [star_trivial] using (dotProduct_self_star_pos_iff.mpr hx)
  nlinarith

/-- Any proposed coefficient in the original covariance comparison bounds
all concrete nonzero normalized eigenvalues from below. -/
theorem normalized_eigenvalue_ge_of_scaled_comparison
    (M : Matrix ι ι ℝ) (hM : M.IsSymm) (hdiag : ∀ i, 0 < M i i)
    (hrow : M *ᵥ (fun _ => 1) = 0) (c : ℝ)
    (hcomparison : LoewnerLE (c • comparisonMatrix (fun i => M i i)) M)
    (μ : ℝ) (hμ : μ ≠ 0) (x : ι → ℝ) (hx : x ≠ 0)
    (heig : normalizedMatrix M *ᵥ x = μ • x) : c ≤ μ := by
  have hNu : normalizedMatrix M *ᵥ diagonalSqrtVector M = 0 := by
    rw [normalizedMatrix_mulVec_eq]
    have hcoords : diagonalSqrtVector M / diagonalSqrtVector M = (fun _ => 1) := by
      ext i
      simp [Pi.div_apply, (diagonalSqrtVector_pos M hdiag i).ne']
    rw [hcoords, hrow]
    ext i
    simp [Pi.div_apply]
  apply eigenvalue_ge_of_scaled_projection_comparison
    (normalizedMatrix M) (normalizedMatrix_isSymm M hM) (diagonalSqrtVector M) hNu c
    ?_ μ hμ x hx heig
  intro z
  rw [quadraticForm_smul, ← comparisonMatrix_normalized_quadraticForm M hdiag z,
    normalizedMatrix_quadraticForm]
  simpa only [quadraticForm_smul] using hcomparison (z / diagonalSqrtVector M)
end

end CoefficientOne
