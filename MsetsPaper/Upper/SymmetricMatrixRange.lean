import MsetsPaper.Upper.CovariancePseudoinverse
import Mathlib.Analysis.Matrix.Hermitian
import Mathlib.Analysis.InnerProductSpace.Adjoint

/-!
# The symmetric range/kernel step of manuscript Lemma 2

The range is the orthogonal complement of the kernel, by the adjoint theorem
for finite-dimensional inner-product spaces. A Moore--Penrose inverse solves
every right-hand side in that range by its first defining equation.
-/

noncomputable section

open Matrix
open scoped BigOperators

namespace MsetsPaper.Upper

variable {d : ℕ}

theorem symmetric_matrix_range_eq_kernel_orthogonal
    (A : Matrix (Fin d) (Fin d) ℝ) (hA : A.IsSymm) :
    LinearMap.range A.toEuclideanLin = (LinearMap.ker A.toEuclideanLin)ᗮ := by
  have hs : A.toEuclideanLin.IsSymmetric :=
    Matrix.isSymmetric_toEuclideanLin_iff.mpr (Matrix.isHermitian_iff_isSymm.mpr hA)
  simpa only [hs.adjoint_eq] using (LinearMap.orthogonal_ker A.toEuclideanLin).symm

/-- The same range/kernel identity in the paper's ordinary coordinate notation. -/
theorem symmetric_matrix_range_iff_kernel_orthogonal
    (A : Matrix (Fin d) (Fin d) ℝ) (hA : A.IsSymm) (y : Fin d → ℝ) :
    (∃ z, A *ᵥ z = y) ↔ ∀ x, A *ᵥ x = 0 → x ⬝ᵥ y = 0 := by
  have hrange := symmetric_matrix_range_eq_kernel_orthogonal A hA
  constructor
  · rintro ⟨z, rfl⟩ x hx
    have hmem : WithLp.toLp 2 (A *ᵥ z) ∈ LinearMap.range A.toEuclideanLin := by
      exact ⟨WithLp.toLp 2 z, by simp⟩
    rw [hrange] at hmem
    have hxker : WithLp.toLp 2 x ∈ LinearMap.ker A.toEuclideanLin := by
      simpa using hx
    have ho := Submodule.inner_right_of_mem_orthogonal hxker hmem
    simpa [EuclideanSpace.inner_toLp_toLp, dotProduct_comm] using ho
  · intro hy
    have horth : WithLp.toLp 2 y ∈ (LinearMap.ker A.toEuclideanLin)ᗮ := by
      intro x hx
      have hxker : A *ᵥ WithLp.ofLp x = 0 := by
        simpa using congrArg WithLp.ofLp hx
      simpa [EuclideanSpace.inner_eq_star_dotProduct, dotProduct_comm] using
        hy (WithLp.ofLp x) hxker
    rw [← hrange] at horth
    obtain ⟨z, hz⟩ := horth
    exact ⟨WithLp.ofLp z, by simpa using congrArg WithLp.ofLp hz⟩

/-- The first Penrose equation makes A B the identity on the range of A. -/
theorem IsMoorePenroseInverse.mulVec_eq_self_of_mem_range
    {A B : Matrix (Fin d) (Fin d) ℝ} (hAB : IsMoorePenroseInverse A B)
    {y : Fin d → ℝ} (hy : ∃ z, A *ᵥ z = y) :
    A *ᵥ (B *ᵥ y) = y := by
  obtain ⟨z, rfl⟩ := hy
  calc
    A *ᵥ (B *ᵥ (A *ᵥ z)) = (A * B * A) *ᵥ z := by
      simp only [Matrix.mulVec_mulVec, Matrix.mul_assoc]
    _ = A *ᵥ z := by rw [hAB.1]

end MsetsPaper.Upper
