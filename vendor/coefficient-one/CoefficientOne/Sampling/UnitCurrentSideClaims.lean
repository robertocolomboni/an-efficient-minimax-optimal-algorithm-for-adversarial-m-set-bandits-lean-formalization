import CoefficientOne.Sampling.UnitCurrentSetup

/-! Explicit reversible-chain side identities in the Gram argument. -/
open scoped BigOperators
open EffectiveResistance Matrix
namespace CoefficientOne.Sampling
noncomputable section
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

theorem transition_nonneg (N : ConductanceNetwork ι) (hd : ∀ i, 0 < N.degree i)
    (i j : ι) : 0 ≤ transitionMatrix N i j :=
  div_nonneg (N.nonnegative i j) (hd i).le

theorem transition_eq_one_sub_degree_inverse_laplacian (N : ConductanceNetwork ι)
    (hd : ∀ i, 0 < N.degree i) :
    transitionMatrix N = 1 - Matrix.diagonal (fun i => (N.degree i)⁻¹) * N.laplacian := by
  ext i j
  by_cases hij : i = j
  · subst j
    simp [Matrix.diagonal_mul, N.laplacian_diagonal, (hd i).ne']
  · simp [Matrix.diagonal_mul, Matrix.one_apply, hij, N.laplacian_offDiagonal hij,
      transitionMatrix, div_eq_mul_inv, mul_comm]

theorem currentGramMatrix_quadratic_identity (N : ConductanceNetwork ι)
    (hd : ∀ i, 0 < N.degree i) (x : ι → ℝ) :
    quadraticForm (currentGramMatrix N) x = (stationaryMass N ⬝ᵥ x) ^ 2 -
      ∑ i, stationaryMass N i * x i * (transitionMatrix N *ᵥ x) i := by
  have he (i j : ι) : currentGramMatrix N i j =
      stationaryMass N i * stationaryMass N j - stationaryMass N i * transitionMatrix N i j := by
    rw [stationary_transition N hd]
    rfl
  change (∑ i, x i * ∑ j, currentGramMatrix N i j * x j) =
    (∑ i, stationaryMass N i * x i) ^ 2 -
      ∑ i, stationaryMass N i * x i * ∑ j, transitionMatrix N i j * x j
  simp_rw [he, sub_mul, Finset.sum_sub_distrib, mul_sub]
  rw [Finset.sum_sub_distrib]
  congr 1
  · simp only [mul_assoc, ← Finset.mul_sum]
    simp only [← mul_assoc, ← Finset.sum_mul]
    rw [show (∑ i, x i * stationaryMass N i) = ∑ i, stationaryMass N i * x i by
      apply Finset.sum_congr rfl; intro i _; ring]
    ring
  · apply Finset.sum_congr rfl
    intro i _
    simp only [mul_assoc, ← Finset.mul_sum]
    ring

theorem transition_nonpositive_on_centered [Nonempty ι] (N : ConductanceNetwork ι)
    (hd : ∀ i, 0 < N.degree i) (hk : HasConstantKernel N) (hg : HasNormalizedGapOne N)
    (x : ι → ℝ) (hx : stationaryMass N ⬝ᵥ x = 0) :
    (∑ i, stationaryMass N i * x i * (transitionMatrix N *ᵥ x) i) ≤ 0 := by
  have hq := (Matrix.posSemidef_iff_dotProduct_mulVec.mp
    (currentGramMatrix_posSemidef N hd hk hg)).2 x
  simp only [star_trivial] at hq
  change 0 ≤ quadraticForm (currentGramMatrix N) x at hq
  rw [currentGramMatrix_quadratic_identity N hd x, hx] at hq
  nlinarith

end
end CoefficientOne.Sampling
