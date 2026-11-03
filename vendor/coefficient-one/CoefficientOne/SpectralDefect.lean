import CoefficientOne.StrictSpectrum

/-!
# The comparison defect from the strict normalized spectrum

This file follows the last part of the manuscript's strictness paragraph:
the nonzero eigenvalues of `N` exceed one, so `N - Π` is positive semidefinite
with kernel exactly the square-root variance line. Positive diagonal
congruence then gives the kernel and strict positivity of `Σ - P`.
-/

open scoped BigOperators
open Matrix EffectiveResistance

namespace CoefficientOne

noncomputable section

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

omit [DecidableEq ι] in
/-- A real positive semidefinite form vanishes exactly on its matrix kernel.
The discriminant proof is the standard polarization argument. -/
theorem quadraticForm_eq_zero_iff_mulVec_eq_zero
    (A : Matrix ι ι ℝ) (hA : A.IsSymm)
    (hpos : ∀ z, 0 ≤ quadraticForm A z) (x : ι → ℝ) :
    quadraticForm A x = 0 ↔ A *ᵥ x = 0 := by
  constructor
  · intro hx
    let e := A *ᵥ x
    have hdisc : discrim (quadraticForm A e) (-2 * (e ⬝ᵥ e)) 0 ≤ 0 := by
      apply discrim_le_zero
      intro t
      have ht := hpos (x - t • e)
      change 0 ≤ (x - t • e) ⬝ᵥ (A *ᵥ (x - t • e)) at ht
      rw [quadraticForm_sub_scalar_vector A hA] at ht
      change 0 ≤ quadraticForm A x - 2 * t * (e ⬝ᵥ e) +
        t ^ 2 * quadraticForm A e at ht
      rw [hx] at ht
      nlinarith
    have he : e ⬝ᵥ e = 0 := by
      simp only [discrim, mul_zero, sub_zero] at hdisc
      nlinarith [sq_nonneg (e ⬝ᵥ e)]
    exact (dotProduct_self_eq_zero.mp he)
  · intro hx
    simp [quadraticForm, hx]

theorem perpendicularProjection_mulVec_formula (u x : ι → ℝ) :
    perpendicularProjection u *ᵥ x = x - ((u ⬝ᵥ x) / (u ⬝ᵥ u)) • u := by
  simp [perpendicularProjection, Matrix.sub_mulVec, Matrix.smul_mulVec,
    Matrix.vecMulVec_mulVec, smul_smul, div_eq_mul_inv, mul_comm]

/-- A strict nonzero spectral gap excludes any additional kernel vector
of `N - Π`: its projection would otherwise be an eigenvector of `N` at one. -/
theorem spectral_defect_kernel_line
    (N : Matrix ι ι ℝ) (u : ι → ℝ) (hu : 0 < u ⬝ᵥ u)
    (hNu : N *ᵥ u = 0)
    (hgap : ∀ μ : ℝ, μ ≠ 0 → ∀ x : ι → ℝ, x ≠ 0 →
      N *ᵥ x = μ • x → 1 < μ) (x : ι → ℝ) :
    (N - perpendicularProjection u) *ᵥ x = 0 ↔ ∃ c : ℝ, x = c • u := by
  constructor
  · intro hx
    have hNx : N *ᵥ x = perpendicularProjection u *ᵥ x :=
      sub_eq_zero.mp (by simpa only [Matrix.sub_mulVec] using hx)
    have heig : N *ᵥ (perpendicularProjection u *ᵥ x) =
        (1 : ℝ) • (perpendicularProjection u *ᵥ x) := by
      rw [perpendicularProjection_mulVec_formula, Matrix.mulVec_sub,
        Matrix.mulVec_smul, hNu, smul_zero, sub_zero]
      simpa only [one_smul, perpendicularProjection_mulVec_formula] using hNx
    have hproj : perpendicularProjection u *ᵥ x = 0 := by
      by_contra hne
      have hbad := hgap 1 (by norm_num) _ hne heig
      exact (lt_irrefl 1) hbad
    refine ⟨(u ⬝ᵥ x) / (u ⬝ᵥ u), ?_⟩
    exact sub_eq_zero.mp (by simpa only [perpendicularProjection_mulVec_formula] using hproj)
  · rintro ⟨c, rfl⟩
    rw [Matrix.mulVec_smul, Matrix.sub_mulVec, hNu,
      perpendicularProjection_mulVec_self u hu.ne', sub_self, smul_zero]

/-- The strict spectral gap gives nonnegativity and the exact zero set of
the normalized comparison defect. -/
theorem spectral_defect_quadratic_pos
    (N : Matrix ι ι ℝ) (hN : N.IsHermitian) (u : ι → ℝ)
    (hu : 0 < u ⬝ᵥ u)
    (hker : ∀ x : ι → ℝ, N *ᵥ x = 0 ↔ ∃ c : ℝ, x = c • u)
    (hgap : ∀ μ : ℝ, μ ≠ 0 → ∀ x : ι → ℝ, x ≠ 0 →
      N *ᵥ x = μ • x → 1 < μ)
    (x : ι → ℝ) (hx : ¬ ∃ c : ℝ, x = c • u) :
    0 < quadraticForm (N - perpendicularProjection u) x := by
  have hcomp := projection_comparison_of_eigenvalue_gap N hN u hu hker
    (fun μ hμ z hz heig => (hgap μ hμ z hz heig).le)
  have hpos (z : ι → ℝ) : 0 ≤ quadraticForm (N - perpendicularProjection u) z := by
    rw [quadraticForm_sub]
    exact sub_nonneg.mpr (hcomp z)
  have hsymm : (N - perpendicularProjection u).IsSymm :=
    (Matrix.isHermitian_iff_isSymm.mp hN).sub (perpendicularProjection_isSymm u)
  have hNu : N *ᵥ u = 0 := (hker u).mpr ⟨1, by simp⟩
  apply lt_of_le_of_ne (hpos x)
  intro hz
  have hzero := (quadraticForm_eq_zero_iff_mulVec_eq_zero _ hsymm hpos x).mp hz.symm
  exact hx ((spectral_defect_kernel_line N u hu hNu hgap x).mp hzero)

variable {n : ℕ}

/-- The normalized defect has exactly the square-root variance line as kernel. -/
theorem normalized_covariance_defect_kernel
    (w : Fin n → ℝ) (hw : ∀ i, 0 < w i) (m : ℕ)
    (hmpos : 1 ≤ m) (hmtop : m ≤ n - 1) (x : Fin n → ℝ) :
    (normalizedMatrix (covarianceMatrix w m) -
      perpendicularProjection (diagonalSqrtVector (covarianceMatrix w m))) *ᵥ x = 0 ↔
        ∃ c : ℝ, x = c • diagonalSqrtVector (covarianceMatrix w m) := by
  exact spectral_defect_kernel_line _ _
    (normalized_covariance_kernel_vector_norm_pos w hw m hmpos hmtop)
    (normalized_covariance_kernel_vector w hw m hmpos hmtop)
    (normalized_covariance_eigenvector_gt_one w hw m hmpos hmtop) x

/-- The normalized defect is positive away from the square-root variance line. -/
theorem normalized_covariance_defect_quadratic_pos
    (w : Fin n → ℝ) (hw : ∀ i, 0 < w i) (m : ℕ)
    (hmpos : 1 ≤ m) (hmtop : m ≤ n - 1) (x : Fin n → ℝ)
    (hx : ¬ ∃ c : ℝ, x = c • diagonalSqrtVector (covarianceMatrix w m)) :
    0 < quadraticForm
      (normalizedMatrix (covarianceMatrix w m) -
        perpendicularProjection (diagonalSqrtVector (covarianceMatrix w m))) x := by
  haveI : Nonempty (Fin n) := ⟨⟨0, by omega⟩⟩
  apply spectral_defect_quadratic_pos _
    (Matrix.isHermitian_iff_isSymm.mpr
      (normalizedMatrix_isSymm _ (covariance_isSymm w m))) _
    (normalized_covariance_kernel_vector_norm_pos w hw m hmpos hmtop)
    (normalizedMatrix_kernel_line _
      (covarianceVariance_pos w hw m hmpos (by simpa using hmtop))
      (covariance_mulVec_eq_zero_iff_constant w hw m hmpos (by simpa using hmtop)))
    (normalized_covariance_eigenvector_gt_one w hw m hmpos hmtop) x hx

/-- In particular, the normalized defect is positive definite on `u`-perp. -/
theorem normalized_covariance_defect_pos_on_perpendicular
    (w : Fin n → ℝ) (hw : ∀ i, 0 < w i) (m : ℕ)
    (hmpos : 1 ≤ m) (hmtop : m ≤ n - 1) (x : Fin n → ℝ)
    (hx : x ≠ 0) (horth : diagonalSqrtVector (covarianceMatrix w m) ⬝ᵥ x = 0) :
    0 < quadraticForm
      (normalizedMatrix (covarianceMatrix w m) -
        perpendicularProjection (diagonalSqrtVector (covarianceMatrix w m))) x := by
  apply normalized_covariance_defect_quadratic_pos w hw m hmpos hmtop x
  rintro ⟨c, rfl⟩
  rw [dotProduct_smul, smul_eq_mul] at horth
  have hc : c = 0 := (mul_eq_zero.mp horth).resolve_right
    (normalized_covariance_kernel_vector_norm_pos w hw m hmpos hmtop).ne'
  exact hx (by simp [hc])

/-- Positive diagonal congruence transports the strict normalized defect
to the covariance defect. This is the spectral route used in the manuscript. -/
theorem covariance_defect_quadratic_pos_from_spectrum
    (w : Fin n → ℝ) (hw : ∀ i, 0 < w i) (m : ℕ)
    (hmpos : 1 ≤ m) (hmtop : m ≤ n - 1)
    (x : Fin n → ℝ) (hx : ¬ ∀ i j, x i = x j) :
    0 < quadraticForm
      (covarianceMatrix w m - comparisonMatrix (covarianceVariance w m)) x := by
  have hdiag : ∀ i, 0 < covarianceMatrix w m i i :=
    covarianceVariance_pos w hw m hmpos (by simpa using hmtop)
  have hnotline : ¬ ∃ c : ℝ,
      diagonalSqrtVector (covarianceMatrix w m) * x =
        c • diagonalSqrtVector (covarianceMatrix w m) := by
    rintro ⟨c, hc⟩
    have hconst (i : Fin n) : x i = c := by
      have hi := congrFun hc i
      change diagonalSqrtVector (covarianceMatrix w m) i * x i =
        c * diagonalSqrtVector (covarianceMatrix w m) i at hi
      have hu := (diagonalSqrtVector_pos _ hdiag i).ne'
      exact (mul_left_cancel₀ hu) (by simpa only [mul_comm c] using hi)
    exact hx (fun i j => (hconst i).trans (hconst j).symm)
  have hpos := normalized_covariance_defect_quadratic_pos w hw m hmpos hmtop
    (diagonalSqrtVector (covarianceMatrix w m) * x) hnotline
  rw [quadraticForm_sub, normalizedMatrix_quadraticForm,
    ← comparisonMatrix_normalized_quadraticForm _ hdiag,
    mul_diagonalSqrtVector_div_self _ hdiag] at hpos
  rw [quadraticForm_sub]
  exact hpos

/-- The spectral proof gives precisely the constant-vector kernel. -/
theorem covariance_defect_kernel_from_spectrum
    (w : Fin n → ℝ) (hw : ∀ i, 0 < w i) (m : ℕ)
    (hmpos : 1 ≤ m) (hmtop : m ≤ n - 1) (x : Fin n → ℝ) :
    (covarianceMatrix w m - comparisonMatrix (covarianceVariance w m)) *ᵥ x = 0 ↔
      ∀ i j, x i = x j := by
  constructor
  · intro hz
    by_contra hnonconst
    have hpos := covariance_defect_quadratic_pos_from_spectrum w hw m hmpos hmtop x hnonconst
    simp [quadraticForm, hz] at hpos
  · intro hc
    let i₀ : Fin n := ⟨0, by omega⟩
    have hx : x = x i₀ • (fun _ : Fin n => (1 : ℝ)) := by
      ext i
      simpa using hc i i₀
    have hV : totalWeight (covarianceVariance w m) ≠ 0 :=
      (covarianceVariance_sum_pos w hw m hmpos (by simpa using hmtop)).ne'
    rw [hx, Matrix.mulVec_smul, Matrix.sub_mulVec,
      covariance_mulVec_one_eq_zero w hw m
        (by simpa using hmtop.trans (Nat.sub_le _ _)),
      comparisonMatrix_mulVec_one _ hV, sub_self, smul_zero]

/-- The kernel statement in the paper, as equality of linear subspaces. -/
theorem covariance_defect_ker_eq_span_one_from_spectrum
    (w : Fin n → ℝ) (hw : ∀ i, 0 < w i) (m : ℕ)
    (hmpos : 1 ≤ m) (hmtop : m ≤ n - 1) :
    LinearMap.ker (covarianceMatrix w m - comparisonMatrix (covarianceVariance w m)).toLin' =
      Submodule.span ℝ {fun _ : Fin n => (1 : ℝ)} := by
  ext x
  rw [LinearMap.mem_ker, Matrix.toLin'_apply,
    covariance_defect_kernel_from_spectrum w hw m hmpos hmtop x,
    Submodule.mem_span_singleton]
  constructor
  · intro hc
    let i₀ : Fin n := ⟨0, by omega⟩
    refine ⟨x i₀, ?_⟩
    ext i
    simpa using (hc i₀ i)
  · rintro ⟨c, rfl⟩
    simp

end

end CoefficientOne
