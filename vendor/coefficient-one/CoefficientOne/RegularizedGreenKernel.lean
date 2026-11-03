import EffectiveResistance.AllRanks
import Mathlib

/-!
# An inverse formula for connected conductance networks

Adding the orthogonal projection onto constants makes the Laplacian
invertible. Its inverse solves every zero-sum demand, including for networks
with missing edges. This supplies a continuous matrix formula for the path
counterexample in Appendix E.3. The inverse need not vanish on constants;
its effective resistances agree with those of every Green kernel.
-/

open scoped BigOperators
open Matrix EffectiveResistance

namespace CoefficientOne

noncomputable section

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- Laplacian plus the orthogonal projection onto constants. -/
def regularizedLaplacian (N : ConductanceNetwork ι) : Matrix ι ι ℝ :=
  N.laplacian + Matrix.of (fun (_ _ : ι) => (Fintype.card ι : ℝ)⁻¹)

theorem regularizedLaplacian_isSymm (N : ConductanceNetwork ι) :
    (regularizedLaplacian N).IsSymm := by
  apply N.laplacian_isSymm.add
  apply Matrix.IsSymm.ext
  intro i j
  rfl

theorem regularizedLaplacian_mulVec (N : ConductanceNetwork ι) (x : ι → ℝ) :
    regularizedLaplacian N *ᵥ x =
      N.laplacian *ᵥ x + (fun _ => (∑ i, x i) / (Fintype.card ι : ℝ)) := by
  rw [regularizedLaplacian, Matrix.add_mulVec]
  congr 1
  ext i
  simp [Matrix.mulVec, dotProduct, Finset.sum_mul, div_eq_mul_inv, mul_comm]

theorem regularizedLaplacian_mulVec_of_zeroSum
    (N : ConductanceNetwork ι) (x : ι → ℝ) (hx : IsZeroSum x) :
    regularizedLaplacian N *ᵥ x = N.laplacian *ᵥ x := by
  rw [regularizedLaplacian_mulVec]
  change (∑ i, x i) = 0 at hx
  simp only [hx, zero_div]
  exact add_zero _

variable [Nonempty ι]

theorem regularizedLaplacian_sum_mulVec (N : ConductanceNetwork ι) (x : ι → ℝ) :
    (∑ i, (regularizedLaplacian N *ᵥ x) i) = ∑ i, x i := by
  have hL := N.laplacian_mulVec_zeroSum x
  have hcard : (Fintype.card ι : ℝ) ≠ 0 := by
    exact_mod_cast (Fintype.card_pos_iff.mpr (inferInstance : Nonempty ι)).ne'
  rw [regularizedLaplacian_mulVec]
  simp only [Pi.add_apply, Finset.sum_add_distrib]
  change (∑ i, (N.laplacian *ᵥ x) i) = 0 at hL
  rw [hL, zero_add]
  simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
  exact mul_div_cancel₀ _ hcard

/-- A connected Laplacian has no kernel after adding the constant projection. -/
theorem regularizedLaplacian_kernel
    (N : ConductanceNetwork ι)
    (hker : ∀ x : ι → ℝ, N.laplacian *ᵥ x = 0 → ∀ i j, x i = x j)
    (x : ι → ℝ) (hx : regularizedLaplacian N *ᵥ x = 0) : x = 0 := by
  have hxsum : IsZeroSum x := by
    have hs := regularizedLaplacian_sum_mulVec N x
    rw [hx] at hs
    simpa [IsZeroSum] using hs.symm
  have hLx : N.laplacian *ᵥ x = 0 := by
    rw [← regularizedLaplacian_mulVec_of_zeroSum N x hxsum]
    exact hx
  let i₀ : ι := Classical.choice inferInstance
  have hc := hker x hLx
  have hcard : (Fintype.card ι : ℝ) ≠ 0 := by
    exact_mod_cast (Fintype.card_pos_iff.mpr (inferInstance : Nonempty ι)).ne'
  have hbase : x i₀ = 0 := by
    have hs : (Fintype.card ι : ℝ) * x i₀ = 0 := by
      calc
        _ = ∑ _ : ι, x i₀ := by simp
        _ = ∑ i, x i := Finset.sum_congr rfl (fun i _ => (hc i i₀).symm)
        _ = 0 := hxsum
    exact (mul_eq_zero.mp hs).resolve_left hcard
  ext i
  exact (hc i i₀).trans hbase

theorem regularizedLaplacian_det_ne_zero
    (N : ConductanceNetwork ι)
    (hker : ∀ x : ι → ℝ, N.laplacian *ᵥ x = 0 → ∀ i j, x i = x j) :
    (regularizedLaplacian N).det ≠ 0 := by
  have hinj : Function.Injective (regularizedLaplacian N).mulVec := by
    intro x y hxy
    apply sub_eq_zero.mp
    apply regularizedLaplacian_kernel N hker (x - y)
    rw [Matrix.mulVec_sub, hxy, sub_self]
  exact isUnit_iff_ne_zero.mp ((Matrix.isUnit_iff_isUnit_det _).mp
    (Matrix.mulVec_injective_iff_isUnit.mp hinj))

/-- Inverse of the regularized Laplacian as a symmetric zero-sum solver. -/
def regularizedGreenKernel
    (N : ConductanceNetwork ι)
    (hker : ∀ x : ι → ℝ, N.laplacian *ᵥ x = 0 → ∀ i j, x i = x j) :
    GreenKernel N where
  kernel := (regularizedLaplacian N)⁻¹
  symmetric := (regularizedLaplacian_isSymm N).inv
  solves_zeroSum y hy := by
    let z := (regularizedLaplacian N)⁻¹ *ᵥ y
    have hAz : regularizedLaplacian N *ᵥ z = y := by
      rw [Matrix.mulVec_mulVec,
        Matrix.mul_nonsing_inv _ (isUnit_iff_ne_zero.mpr (regularizedLaplacian_det_ne_zero N hker)),
        Matrix.one_mulVec]
    have hz : IsZeroSum z := by
      have hs := regularizedLaplacian_sum_mulVec N z
      rw [hAz] at hs
      exact hs.symm.trans hy
    rw [← regularizedLaplacian_mulVec_of_zeroSum N z hz]
    exact hAz

theorem regularizedGreenKernel_effectiveResistance_formula
    (N : ConductanceNetwork ι)
    (hker : ∀ x : ι → ℝ, N.laplacian *ᵥ x = 0 → ∀ i j, x i = x j)
    (i j : ι) :
    (regularizedGreenKernel N hker).effectiveResistance i j =
      quadraticForm (regularizedLaplacian N)⁻¹ (pairDemand i j) := rfl

/-- The regularized inverse computes the same resistance as any Green kernel. -/
theorem regularizedGreenKernel_effectiveResistance_eq
    (N : ConductanceNetwork ι)
    (hker : ∀ x : ι → ℝ, N.laplacian *ᵥ x = 0 → ∀ i j, x i = x j)
    (G : GreenKernel N) (i j : ι) (hij : i ≠ j) :
    (regularizedGreenKernel N hker).effectiveResistance i j = G.effectiveResistance i j := by
  rw [(regularizedGreenKernel N hker).effectiveResistance_eq_solution_drop hij
    (G.potential (pairDemand i j)) (G.solves_pairDemand hij)]
  exact (G.effectiveResistance_eq_potential_sub i j).symm

end

end CoefficientOne
