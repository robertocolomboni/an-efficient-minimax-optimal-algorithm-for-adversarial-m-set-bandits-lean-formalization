import Mathlib.LinearAlgebra.Matrix.PosDef
import Mathlib.Tactic

/-! # Scalar-pivot Schur elimination for positive-definite matrices

This is the algebraic specification of the solver. The operational program
must materialize each smaller matrix and right-hand side; the specification
alone does not assert a complexity bound.
-/

namespace MsetsPaper.Upper.SchurSolver

open Matrix
open scoped BigOperators

noncomputable section

variable {n : ℕ}

def schur (A : Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ) : Matrix (Fin n) (Fin n) ℝ :=
  fun i j ↦ A i.succ j.succ - A i.succ 0 * A 0 j.succ / A 0 0

def reducedRhs (A : Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ)
    (b : Fin (n + 1) → ℝ) : Fin n → ℝ :=
  fun i ↦ b i.succ - A i.succ 0 * b 0 / A 0 0

def reconstruct (A : Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ)
    (beta : ℝ) (x : Fin n → ℝ) : Fin (n + 1) → ℝ :=
  Fin.cons ((beta - ∑ j, A 0 j.succ * x j) / A 0 0) x

theorem mulVec_cons (A : Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ)
    (alpha : ℝ) (x : Fin n → ℝ) (i : Fin (n + 1)) :
    (A *ᵥ Fin.cons alpha x) i = A i 0 * alpha + ∑ j, A i j.succ * x j := by
  simp [Matrix.mulVec, dotProduct, Fin.sum_univ_succ]

theorem schur_mulVec (A : Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ)
    (x : Fin n → ℝ) (i : Fin n) :
    (schur A *ᵥ x) i =
      (∑ j, A i.succ j.succ * x j) - A i.succ 0 * (∑ j, A 0 j.succ * x j) / A 0 0 := by
  simp only [schur, Matrix.mulVec, dotProduct, sub_mul, Finset.sum_sub_distrib]
  congr 1
  rw [Finset.mul_sum, Finset.sum_div]
  apply Finset.sum_congr rfl
  intro j _
  ring

theorem reconstruct_head (A : Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ)
    (hp : A 0 0 ≠ 0) (beta : ℝ) (x : Fin n → ℝ) :
    (A *ᵥ reconstruct A beta x) 0 = beta := by
  rw [reconstruct, mulVec_cons]
  field_simp
  ring

theorem reconstruct_tail (A : Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ)
    (beta : ℝ) (x : Fin n → ℝ) (i : Fin n) :
    (A *ᵥ reconstruct A beta x) i.succ =
      (schur A *ᵥ x) i + A i.succ 0 * beta / A 0 0 := by
  rw [reconstruct, mulVec_cons, schur_mulVec]
  ring

/-- The Schur quadratic form is the original form evaluated at the
zero-head residual lift. The identity needs only a nonzero pivot. -/
theorem quadratic_lift (A : Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ)
    (hp : A 0 0 ≠ 0) (x : Fin n → ℝ) :
    reconstruct A 0 x ⬝ᵥ (A *ᵥ reconstruct A 0 x) = x ⬝ᵥ (schur A *ᵥ x) := by
  unfold dotProduct
  rw [Fin.sum_univ_succ]
  simp only [reconstruct_head A hp, mul_zero, zero_add, reconstruct_tail,
    mul_zero, zero_div, add_zero]
  apply Finset.sum_congr rfl
  intro i _
  simp [reconstruct]

theorem schur_posDef (A : Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ)
    (hA : A.PosDef) : (schur A).PosDef := by
  have hs : A.IsSymm := Matrix.isHermitian_iff_isSymm.mp hA.1
  have hsB : (schur A).IsSymm := by
    apply Matrix.IsSymm.ext
    intro i j
    dsimp [schur]
    rw [hs.apply i.succ j.succ, hs.apply 0 i.succ, hs.apply 0 j.succ]
    ring
  apply Matrix.PosDef.of_dotProduct_mulVec_pos (Matrix.isHermitian_iff_isSymm.mpr hsB)
  intro x hx
  have hlift : reconstruct A 0 x ≠ 0 := by
    intro hz
    apply hx
    ext i
    have hh := congrFun hz i.succ
    simpa [reconstruct] using hh
  have hpos := hA.dotProduct_mulVec_pos hlift
  simp only [star_trivial] at hpos ⊢
  rwa [quadratic_lift A (ne_of_gt hA.diag_pos)] at hpos

theorem reconstruct_solves (A : Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ)
    (hp : A 0 0 ≠ 0) (b : Fin (n + 1) → ℝ) (x : Fin n → ℝ)
    (hx : schur A *ᵥ x = reducedRhs A b) :
    A *ᵥ reconstruct A (b 0) x = b := by
  ext i
  refine Fin.cases ?_ (fun j ↦ ?_) i
  · exact reconstruct_head A hp (b 0) x
  · rw [reconstruct_tail, hx]
    simp [reducedRhs]

/-- Mathematical recursive specification, separate from the cached program. -/
def solveSpec : (n : ℕ) → Matrix (Fin n) (Fin n) ℝ → (Fin n → ℝ) → (Fin n → ℝ)
  | 0, _, _ => Fin.elim0
  | n + 1, A, b => reconstruct A (b 0) (solveSpec n (schur A) (reducedRhs A b))

theorem solveSpec_solves : ∀ (n : ℕ) (A : Matrix (Fin n) (Fin n) ℝ),
    A.PosDef → ∀ b, A *ᵥ solveSpec n A b = b := by
  intro n
  induction n with
  | zero => intro A hA b; ext i; exact Fin.elim0 i
  | succ n ih =>
    intro A hA b
    exact reconstruct_solves A (ne_of_gt hA.diag_pos) b _
      (ih (schur A) (schur_posDef A hA) (reducedRhs A b))

theorem solveSpec_eq_inverse (n : ℕ) (A : Matrix (Fin n) (Fin n) ℝ)
    (hA : A.PosDef) (b : Fin n → ℝ) : solveSpec n A b = A⁻¹ *ᵥ b := by
  letI := hA.isUnit.invertible
  symm
  apply Matrix.inv_mulVec_eq_vec
  exact (solveSpec_solves n A hA b).symm

end

end MsetsPaper.Upper.SchurSolver
