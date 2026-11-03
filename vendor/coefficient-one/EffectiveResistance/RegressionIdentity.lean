import EffectiveResistance.EnergyCauchy
import EffectiveResistance.Resistance
import EffectiveResistance.Covariance
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith

/-!
# Effective resistance as a quadratic regression problem

This is the algebraic content of the resistance--regression identity.  The
constraint `c i - c j = 2` is the coefficient-space version of regressing
`X_i-X_j` on all remaining coordinates.
-/

open scoped BigOperators
open Matrix

namespace EffectiveResistance

noncomputable section

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

theorem pairDemand_dotProduct (i j : ι) (x : ι → ℝ) :
    pairDemand i j ⬝ᵥ x = x i - x j := by
  classical
  simp only [pairDemand, dotProduct, sub_mul, Finset.sum_sub_distrib]
  simp

namespace ConductanceNetwork

variable (N : ConductanceNetwork ι)

theorem energy_scale (a : ℝ) (x : ι → ℝ) :
    N.energy (fun i => a * x i) = a ^ 2 * N.energy x := by
  simp only [energy, energyPairing, dotProduct, Matrix.mulVec, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  ring

end ConductanceNetwork

namespace GreenKernel

variable {N : ConductanceNetwork ι} (G : GreenKernel N)

theorem effectiveResistance_eq_potential_sub
    (i j : ι) :
    G.effectiveResistance i j =
      G.potential (pairDemand i j) i - G.potential (pairDemand i j) j := by
  rw [effectiveResistance, pairDemand_dotProduct]

/-- A Green kernel that solves every zero-sum demand has strictly positive
effective resistance between distinct vertices. -/
theorem effectiveResistance_pos {i j : ι} (hij : i ≠ j) :
    0 < G.effectiveResistance i j := by
  have hnonneg := G.effectiveResistance_nonnegative hij
  by_contra hnot
  have hzero : G.effectiveResistance i j = 0 :=
    le_antisymm (le_of_not_gt hnot) hnonneg
  let h := G.potential (pairDemand i j)
  have hpairing : N.energyPairing (pairDemand i j) h = 2 := by
    rw [ConductanceNetwork.energyPairing]
    rw [show N.laplacian *ᵥ h = pairDemand i j by
      exact G.solves_pairDemand hij]
    rw [pairDemand_dotProduct, pairDemand_apply_left hij,
      pairDemand_apply_right hij]
    norm_num
  have hhenergy : N.energy h = G.effectiveResistance i j := by
    symm
    exact G.effectiveResistance_eq_energy hij
  have hcs := N.energyPairing_sq_le (pairDemand i j) h
  rw [hpairing, hhenergy, hzero] at hcs
  norm_num at hcs

/-- Any solution of the endpoint demand equation computes the same effective
resistance, even though the solution is only determined up to the Laplacian
kernel. -/
theorem effectiveResistance_eq_solution_drop
    {i j : ι} (hij : i ≠ j) (x : ι → ℝ)
    (hx : N.laplacian *ᵥ x = pairDemand i j) :
    G.effectiveResistance i j = x i - x j := by
  let h := G.potential (pairDemand i j)
  calc
    G.effectiveResistance i j = pairDemand i j ⬝ᵥ h := rfl
    _ = (N.laplacian *ᵥ x) ⬝ᵥ h := by rw [hx]
    _ = N.energyPairing h x := by
      rw [ConductanceNetwork.energyPairing]
      exact dotProduct_comm _ _
    _ = N.energyPairing x h := N.energyPairing_comm h x
    _ = x ⬝ᵥ pairDemand i j := by
      rw [ConductanceNetwork.energyPairing]
      rw [show N.laplacian *ᵥ h = pairDemand i j by
        exact G.solves_pairDemand hij]
    _ = pairDemand i j ⬝ᵥ x := dotProduct_comm _ _
    _ = x i - x j := pairDemand_dotProduct i j x

/-- Every coefficient vector with endpoint difference two has energy at least
`4/R_ij`. -/
theorem four_div_effectiveResistance_le_energy
    {i j : ι} (hij : i ≠ j) (hR : 0 < G.effectiveResistance i j)
    (c : ι → ℝ) (hc : c i - c j = 2) :
    4 / G.effectiveResistance i j ≤ N.energy c := by
  let h := G.potential (pairDemand i j)
  have hpairing : N.energyPairing c h = 2 := by
    rw [ConductanceNetwork.energyPairing]
    rw [show N.laplacian *ᵥ h = pairDemand i j by
      exact G.solves_pairDemand hij]
    rw [dotProduct_comm, pairDemand_dotProduct, hc]
  have hhenergy : N.energy h = G.effectiveResistance i j := by
    symm
    exact G.effectiveResistance_eq_energy hij
  have hcs := N.energyPairing_sq_le c h
  rw [hpairing, hhenergy] at hcs
  apply (div_le_iff₀ hR).2
  nlinarith

/-- The coefficient vector selected by the Green kernel. -/
def regressionMinimizer (i j : ι) : ι → ℝ :=
  fun k => (2 / G.effectiveResistance i j) *
    G.potential (pairDemand i j) k

theorem regressionMinimizer_endpoint_difference
    {i j : ι} (hR : 0 < G.effectiveResistance i j) :
    G.regressionMinimizer i j i - G.regressionMinimizer i j j = 2 := by
  unfold regressionMinimizer
  rw [← mul_sub]
  rw [← G.effectiveResistance_eq_potential_sub i j]
  field_simp [ne_of_gt hR]

theorem regressionMinimizer_energy
    {i j : ι} (hij : i ≠ j) (hR : 0 < G.effectiveResistance i j) :
    N.energy (G.regressionMinimizer i j) =
      4 / G.effectiveResistance i j := by
  unfold regressionMinimizer
  rw [N.energy_scale]
  rw [← G.effectiveResistance_eq_energy hij]
  field_simp [ne_of_gt hR]
  ring

/-- Exact variational resistance--regression identity. -/
theorem energy_regression_identity
    {i j : ι} (hij : i ≠ j) (hR : 0 < G.effectiveResistance i j) :
    (∀ c : ι → ℝ, c i - c j = 2 →
        4 / G.effectiveResistance i j ≤ N.energy c) ∧
      (G.regressionMinimizer i j i - G.regressionMinimizer i j j = 2 ∧
        N.energy (G.regressionMinimizer i j) =
          4 / G.effectiveResistance i j) := by
  exact ⟨fun c hc => G.four_div_effectiveResistance_le_energy hij hR c hc,
    G.regressionMinimizer_endpoint_difference hR,
    G.regressionMinimizer_energy hij hR⟩

/-- For an external-field covariance Laplacian, the Green-kernel minimizer
has centered second moment exactly `4/R_ij`. -/
theorem externalField_regressionMinimizer_secondMoment
    (w : ι → ℝ) (m : ℕ)
    (hL : N.laplacian = covarianceMatrix w m)
    {i j : ι} (hij : i ≠ j) (hR : 0 < G.effectiveResistance i j) :
    expectation w m (fun S =>
        (centeredLinearStatistic w m (G.regressionMinimizer i j) S) ^ 2) =
      4 / G.effectiveResistance i j := by
  rw [← quadraticForm_covariance]
  rw [← hL]
  change N.energy (G.regressionMinimizer i j) = _
  exact G.regressionMinimizer_energy hij hR

end GreenKernel

end

end EffectiveResistance
