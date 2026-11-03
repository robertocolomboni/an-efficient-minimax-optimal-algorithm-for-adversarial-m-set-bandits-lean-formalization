import Mathlib

noncomputable section

namespace CoefficientOne

/-- The usual `D^(-1/2) M D^(-1/2)`, with `D` the diagonal of `M`. -/
def normalizedMatrix {ι : Type*} (M : Matrix ι ι ℝ) : Matrix ι ι ℝ :=
  fun i j => M i j / (Real.sqrt (M i i) * Real.sqrt (M j j))

theorem normalizedMatrix_eq_diagonal_mul {ι : Type*} [Fintype ι] [DecidableEq ι]
    (M : Matrix ι ι ℝ) :
    normalizedMatrix M =
      Matrix.diagonal (fun i => (Real.sqrt (M i i))⁻¹) * M *
        Matrix.diagonal (fun i => (Real.sqrt (M i i))⁻¹) := by
  ext i j
  simp [normalizedMatrix, Matrix.mul_apply, Matrix.diagonal,
    div_eq_mul_inv, mul_comm, mul_left_comm, mul_assoc]

theorem normalizedMatrix_diagonal {ι : Type*} (M : Matrix ι ι ℝ) (i : ι)
    (hi : 0 < M i i) : normalizedMatrix M i i = 1 := by
  rw [normalizedMatrix, ← pow_two, Real.sq_sqrt hi.le]
  exact div_self (ne_of_gt hi)

theorem normalizedMatrix_isSymm {ι : Type*} (M : Matrix ι ι ℝ) (hM : M.IsSymm) :
    (normalizedMatrix M).IsSymm := by
  apply Matrix.IsSymm.ext
  intro i j
  simp only [normalizedMatrix, hM.apply i j, mul_comm]

end CoefficientOne
