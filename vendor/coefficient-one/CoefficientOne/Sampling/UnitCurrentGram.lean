import CoefficientOne.Sampling.UnitCurrentSetup
import Mathlib.Analysis.Matrix.Order

/-! # The normalized Gram vectors in the unit-current proof -/

open scoped BigOperators MatrixOrder
open Matrix EffectiveResistance

namespace CoefficientOne.Sampling
noncomputable section

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- A Gram realization in the usual finite-dimensional real Euclidean space.
We write its inner product explicitly as `dotProduct`. -/
theorem exists_gram_vectors (Q : Matrix ι ι ℝ) (hQ : Q.PosSemidef) :
    ∃ z : ι → ι → ℝ, ∀ i j, z i ⬝ᵥ z j = Q i j := by
  obtain ⟨B, hB⟩ := CStarAlgebra.nonneg_iff_eq_star_mul_self.mp hQ.nonneg
  refine ⟨fun i k => B k i, ?_⟩
  intro i j
  rw [hB]
  simp [Matrix.mul_apply, Matrix.star_eq_conjTranspose, Matrix.conjTranspose_apply,
    dotProduct]

theorem gram_vectors_sum_zero (Q : Matrix ι ι ℝ)
    (z : ι → ι → ℝ) (hz : ∀ i j, z i ⬝ᵥ z j = Q i j)
    (hQ : Q *ᵥ (fun _ => 1) = 0) : ∑ i, z i = 0 := by
  have hnorm : (∑ i, z i) ⬝ᵥ (∑ j, z j) = 0 := by
    simp only [sum_dotProduct, dotProduct_sum, hz]
    rw [Finset.sum_comm]
    apply Finset.sum_eq_zero
    intro i _
    have hi := congrFun hQ i
    simpa [Matrix.mulVec, dotProduct] using hi
  exact dotProduct_self_eq_zero.mp hnorm

structure NormalizedGram (N : ConductanceNetwork ι) where
  vectors : ι → ι → ℝ
  unit : ∀ i, vectors i ⬝ᵥ vectors i = 1
  mean_zero : ∑ i, stationaryMass N i • vectors i = 0
  conductance : ∀ i j, normalizedConductance N i j =
    stationaryMass N i * stationaryMass N j * (1 - vectors i ⬝ᵥ vectors j)

theorem exists_normalizedGram [Nonempty ι] (N : ConductanceNetwork ι)
    (hd : ∀ i, 0 < N.degree i) (hk : HasConstantKernel N)
    (hg : HasNormalizedGapOne N) : Nonempty (NormalizedGram N) := by
  obtain ⟨z, hz⟩ := exists_gram_vectors _ (currentGramMatrix_posSemidef N hd hk hg)
  have hmean := gram_vectors_sum_zero _ z hz (currentGramMatrix_mulVec_one N hd)
  let r : ι → ι → ℝ := fun i => (stationaryMass N i)⁻¹ • z i
  have hr (i j : ι) : r i ⬝ᵥ r j =
      currentGramMatrix N i j / (stationaryMass N i * stationaryMass N j) := by
    simp [r, smul_dotProduct, dotProduct_smul, hz, div_eq_mul_inv,
      mul_comm, mul_left_comm, mul_assoc]
  refine ⟨⟨r, ?_, ?_, ?_⟩⟩
  · intro i
    rw [hr, currentGramMatrix_diagonal, pow_two]
    exact div_self (mul_ne_zero (stationaryMass_pos N hd i).ne'
      (stationaryMass_pos N hd i).ne')
  · have heq : ∀ i, stationaryMass N i • r i = z i := by
      intro i
      simp [r, smul_smul, (stationaryMass_pos N hd i).ne']
    simpa only [heq] using hmean
  · intro i j
    rw [hr]
    simp only [currentGramMatrix, Matrix.sub_apply, Matrix.vecMulVec_apply]
    field_simp [(stationaryMass_pos N hd i).ne', (stationaryMass_pos N hd j).ne']
    <;> ring

namespace NormalizedGram

variable {N : ConductanceNetwork ι} (G : NormalizedGram N)

theorem inner_le_one (i j : ι) : G.vectors i ⬝ᵥ G.vectors j ≤ 1 := by
  have h : 0 ≤ (G.vectors i - G.vectors j) ⬝ᵥ (G.vectors i - G.vectors j) :=
    Finset.sum_nonneg (fun _ _ => mul_self_nonneg _)
  simp only [sub_dotProduct, dotProduct_sub, G.unit] at h
  rw [dotProduct_comm (G.vectors j) (G.vectors i)] at h
  linarith

theorem neg_one_le_inner (i j : ι) : -1 ≤ G.vectors i ⬝ᵥ G.vectors j := by
  have h : 0 ≤ (G.vectors i + G.vectors j) ⬝ᵥ (G.vectors i + G.vectors j) :=
    Finset.sum_nonneg (fun _ _ => mul_self_nonneg _)
  simp only [add_dotProduct, dotProduct_add, G.unit] at h
  rw [dotProduct_comm (G.vectors j) (G.vectors i)] at h
  linarith

theorem difference_norm_sq_le_four (i j : ι) :
    (G.vectors i - G.vectors j) ⬝ᵥ (G.vectors i - G.vectors j) ≤ 4 := by
  have h := G.neg_one_le_inner i j
  simp only [sub_dotProduct, dotProduct_sub, G.unit]
  rw [dotProduct_comm (G.vectors j) (G.vectors i)]
  linarith

include G in
theorem conductance_le_two [Nonempty ι] (hd : ∀ i, 0 < N.degree i) (i j : ι) :
    normalizedConductance N i j ≤ 2 * (stationaryMass N i * stationaryMass N j) := by
  rw [G.conductance]
  have hp := mul_pos (stationaryMass_pos N hd i) (stationaryMass_pos N hd j)
  nlinarith [G.neg_one_le_inner i j]

end NormalizedGram
end
end CoefficientOne.Sampling
