import Mathlib.Data.Matrix.Basic
import Mathlib.Data.Real.Basic

/-!
# Quadratic-form order and the normalized comparison matrix

The paper uses the Loewner order only through real quadratic forms.  We make
that interpretation explicit, avoiding any dependence on a library-level
Moore--Penrose inverse.
-/

open scoped BigOperators
open Matrix

namespace EffectiveResistance

noncomputable section

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- The real quadratic form represented by a square matrix. -/
def quadraticForm (A : Matrix ι ι ℝ) (x : ι → ℝ) : ℝ :=
  x ⬝ᵥ (A *ᵥ x)

/-- Quadratic-form (Loewner) order on real matrices. -/
def LoewnerLE (A B : Matrix ι ι ℝ) : Prop :=
  ∀ x : ι → ℝ, quadraticForm A x ≤ quadraticForm B x

/-- The total mass of a vector of weights. -/
def totalWeight (v : ι → ℝ) : ℝ :=
  ∑ i, v i

/-- The rank-one corrected diagonal matrix appearing in the paper. -/
def comparisonMatrix (v : ι → ℝ) : Matrix ι ι ℝ :=
  Matrix.diagonal v - (totalWeight v)⁻¹ • Matrix.vecMulVec v v

theorem quadraticForm_diagonal (v x : ι → ℝ) :
    quadraticForm (Matrix.diagonal v) x = ∑ i, v i * (x i) ^ 2 := by
  simp [quadraticForm, dotProduct, Matrix.mulVec_diagonal, pow_two,
    mul_assoc, mul_left_comm]

theorem quadraticForm_vecMulVec (v x : ι → ℝ) :
    quadraticForm (Matrix.vecMulVec v v) x = (∑ i, v i * x i) ^ 2 := by
  simp [quadraticForm, dotProduct, Matrix.mulVec, Matrix.vecMulVec,
    Finset.mul_sum, Finset.sum_mul, pow_two, mul_assoc, mul_left_comm, mul_comm]

theorem quadraticForm_sub (A B : Matrix ι ι ℝ) (x : ι → ℝ) :
    quadraticForm (A - B) x = quadraticForm A x - quadraticForm B x := by
  simp [quadraticForm, Matrix.sub_mulVec, dotProduct_sub]

theorem quadraticForm_smul (a : ℝ) (A : Matrix ι ι ℝ) (x : ι → ℝ) :
    quadraticForm (a • A) x = a * quadraticForm A x := by
  simp [quadraticForm, Matrix.smul_mulVec, dotProduct_smul, mul_comm]

theorem quadraticForm_comparisonMatrix (v x : ι → ℝ) :
    quadraticForm (comparisonMatrix v) x =
      (∑ i, v i * (x i) ^ 2) -
        (∑ i, v i * x i) ^ 2 / totalWeight v := by
  rw [comparisonMatrix, quadraticForm_sub, quadraticForm_diagonal,
    quadraticForm_smul, quadraticForm_vecMulVec]
  simp [div_eq_mul_inv, mul_comm]

theorem loewnerLE_iff (A B : Matrix ι ι ℝ) :
    LoewnerLE A B ↔ ∀ x : ι → ℝ, quadraticForm A x ≤ quadraticForm B x :=
  Iff.rfl

end

end EffectiveResistance
