import CoefficientOne.HyperplaneComparison
import CoefficientOne.PseudoinverseIdentity
import EffectiveResistance.Resistance

/-!
# Reversing a pseudoinverse comparison

This file expands the inverse-order step used in the optimality proof of
the pseudoinverse corollary. On the zero-sum subspace, the inverse of
`comparisonMatrix v` has the same quadratic form as `diagonal (fun i => (v i)⁻¹)`.
The usual order reversal for positive definite inverses is proved by
completing the square, using an inverse on that subspace. No choice of
coordinates on the subspace or additional inverse matrix is needed.
-/

open scoped BigOperators
open Matrix EffectiveResistance

namespace CoefficientOne

noncomputable section

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

theorem inverseOrder_comparison_mulVec (v x : ι → ℝ) (i : ι) :
    (comparisonMatrix v *ᵥ x) i =
      v i * (x i - (v ⬝ᵥ x) / totalWeight v) := by
  simp [comparisonMatrix, Matrix.sub_mulVec, Matrix.smul_mulVec,
    Matrix.mulVec_diagonal, Matrix.vecMulVec_mulVec, div_eq_mul_inv]
  ring

theorem inverseOrder_comparison_zeroSum (v x : ι → ℝ)
    (hV : totalWeight v ≠ 0) :
    IsZeroSum (comparisonMatrix v *ᵥ x) := by
  unfold IsZeroSum
  simp only [inverseOrder_comparison_mulVec, mul_sub, Finset.sum_sub_distrib,
    ← Finset.sum_mul]
  change v ⬝ᵥ x - totalWeight v * ((v ⬝ᵥ x) / totalWeight v) = 0
  field_simp
  ring

/-- The inverse quadratic form of `P` evaluated at `P x` equals `xᵀ P x`.
This is the concrete identity `P D⁻¹ P = P`. -/
theorem inverseOrder_comparison_inverse_energy (v x : ι → ℝ)
    (hv : ∀ i, v i ≠ 0) (hV : totalWeight v ≠ 0) :
    (∑ i, (comparisonMatrix v *ᵥ x) i ^ 2 / v i) =
      quadraticForm (comparisonMatrix v) x := by
  have hz := inverseOrder_comparison_zeroSum v x hV
  change ∑ i, (comparisonMatrix v *ᵥ x) i = 0 at hz
  calc
    _ = ∑ i, (comparisonMatrix v *ᵥ x) i *
        (x i - (v ⬝ᵥ x) / totalWeight v) := by
      apply Finset.sum_congr rfl
      intro i hi
      rw [inverseOrder_comparison_mulVec]
      field_simp [hv i]
    _ = ∑ i, (comparisonMatrix v *ᵥ x) i * x i -
        (∑ i, (comparisonMatrix v *ᵥ x) i) *
          ((v ⬝ᵥ x) / totalWeight v) := by
      simp only [mul_sub, Finset.sum_sub_distrib, Finset.sum_mul]
    _ = _ := by
      rw [hz, zero_mul, sub_zero]
      exact dotProduct_comm _ _

/-- For positive diagonal weights, the kernel of `P` is exactly the line
of constant vectors. The nonzero hypotheses suffice for this algebraic step. -/
theorem inverseOrder_comparison_kernel (v : ι → ℝ)
    (hv : ∀ i, v i ≠ 0) (hV : totalWeight v ≠ 0) (x : ι → ℝ) :
    comparisonMatrix v *ᵥ x = 0 ↔ ∃ a : ℝ, x = fun _ => a := by
  constructor
  · intro hx
    refine ⟨(v ⬝ᵥ x) / totalWeight v, ?_⟩
    funext i
    have hi := congrFun hx i
    rw [inverseOrder_comparison_mulVec] at hi
    change v i * (x i - (v ⬝ᵥ x) / totalWeight v) = 0 at hi
    exact sub_eq_zero.mp ((mul_eq_zero.mp hi).resolve_left (hv i))
  · rintro ⟨a, rfl⟩
    ext i
    rw [inverseOrder_comparison_mulVec]
    have hdot : v ⬝ᵥ (fun _ : ι => a) = totalWeight v * a := by
      exact (Finset.sum_mul _ _ _).symm
    rw [hdot]
    simp [mul_div_cancel_left₀, hV]

/-- Two solutions to `P z = y` differ by a constant. In particular, the
diagonal inverse and any zero-sum inverse of `P` agree modulo its kernel. -/
theorem inverseOrder_diagonal_inverse_sub_solution_constant
    (v y z : ι → ℝ) (hv : ∀ i, v i ≠ 0)
    (hV : totalWeight v ≠ 0) (hy : IsZeroSum y)
    (hz : comparisonMatrix v *ᵥ z = y) :
    ∃ a : ℝ, (fun i => y i / v i) - z = fun _ => a := by
  apply (inverseOrder_comparison_kernel v hv hV _).mp
  rw [Matrix.mulVec_sub, comparison_div_mulVec v y hv hy, hz, sub_self]

/-- The identity `yᵀ P† y = yᵀ D⁻¹ y` from the manuscript. It holds for
any matrix solving the zero-sum equations for `P`, hence in particular for
its Moore-Penrose inverse. The proof uses the constant difference of the
two solutions and the zero-sum condition on `y`. -/
theorem inverseOrder_comparison_inverse_quadratic
    (v : ι → ℝ) (hv : ∀ i, v i ≠ 0) (hV : totalWeight v ≠ 0)
    (Kp : Matrix ι ι ℝ) (y : ι → ℝ) (hy : IsZeroSum y)
    (hsolve : comparisonMatrix v *ᵥ (Kp *ᵥ y) = y) :
    quadraticForm Kp y = ∑ i, y i ^ 2 / v i := by
  obtain ⟨a, ha⟩ := inverseOrder_diagonal_inverse_sub_solution_constant
    v y (Kp *ᵥ y) hv hV hy hsolve
  have hdot : y ⬝ᵥ ((fun i => y i / v i) - Kp *ᵥ y) = 0 := by
    rw [ha]
    change (∑ i, y i * a) = 0
    rw [← Finset.sum_mul]
    change (∑ i, y i) = 0 at hy
    rw [hy, zero_mul]
  rw [dotProduct_sub] at hdot
  have hdiag : y ⬝ᵥ (fun i => y i / v i) = ∑ i, y i ^ 2 / v i := by
    simp only [dotProduct, pow_two, mul_div_assoc]
  rw [hdiag] at hdot
  exact (sub_eq_zero.mp hdot).symm

/-- Reversal of inverse order on the zero-sum subspace, extended to the
whole space. The proof is the standard completion-of-squares proof for
positive definite inverses, written using the zero-sum inverse `K`.

At `y = P x`, the assumed inverse bound controls the last term in
`0 ≤ (x - c⁻¹ K y)ᵀ S (x - c⁻¹ K y)` and yields `c⁻¹ P ≤ S`. -/
theorem inverse_diagonal_bound_implies_comparison
    (S K : Matrix ι ι ℝ) (v : ι → ℝ) (hv : ∀ i, 0 < v i)
    (hV : totalWeight v ≠ 0)
    (hS : S.IsSymm) (hPSD : ∀ x, 0 ≤ quadraticForm S x)
    (hsolve : ∀ y, IsZeroSum y → S *ᵥ (K *ᵥ y) = y)
    (c : ℝ) (hc : 0 < c)
    (hbound : ∀ y, IsZeroSum y →
      quadraticForm K y ≤ c * ∑ i, y i ^ 2 / v i) :
    LoewnerLE (c⁻¹ • comparisonMatrix v) S := by
  intro x
  let y := comparisonMatrix v *ᵥ x
  have hy : IsZeroSum y := inverseOrder_comparison_zeroSum v x hV
  have hSy : S *ᵥ (K *ᵥ y) = y := hsolve y hy
  have henergy : ∑ i, y i ^ 2 / v i =
      quadraticForm (comparisonMatrix v) x :=
    inverseOrder_comparison_inverse_energy v x (fun i => (hv i).ne') hV
  have hbound' := hbound y hy
  rw [henergy] at hbound'
  have hcross : (K *ᵥ y) ⬝ᵥ (S *ᵥ x) =
      quadraticForm (comparisonMatrix v) x := by
    rw [symmetric_bilinear_swap S hS, hSy]
    rfl
  have hinverse : (K *ᵥ y) ⬝ᵥ (S *ᵥ (K *ᵥ y)) =
      quadraticForm K y := by
    rw [hSy]
    exact dotProduct_comm _ _
  have hsq := hPSD (x - c⁻¹ • (K *ᵥ y))
  change 0 ≤ (x - c⁻¹ • (K *ᵥ y)) ⬝ᵥ
    (S *ᵥ (x - c⁻¹ • (K *ᵥ y))) at hsq
  rw [quadraticForm_sub_scalar_vector S hS, hcross, hinverse] at hsq
  change 0 ≤ quadraticForm S x - 2 * c⁻¹ *
    quadraticForm (comparisonMatrix v) x + c⁻¹ ^ 2 * quadraticForm K y at hsq
  have hbound'' := mul_le_mul_of_nonneg_left hbound' (sq_nonneg c⁻¹)
  have hcancel : c⁻¹ ^ 2 * c = c⁻¹ := by field_simp
  rw [← mul_assoc, hcancel] at hbound''
  rw [quadraticForm_smul]
  linarith

end

end CoefficientOne
