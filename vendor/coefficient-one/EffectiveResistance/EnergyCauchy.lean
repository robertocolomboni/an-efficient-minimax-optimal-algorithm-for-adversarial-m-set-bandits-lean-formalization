import EffectiveResistance.Network
import Mathlib.Algebra.Order.BigOperators.Ring.Finset
import Mathlib.Tactic.Ring

/-!
# Cauchy--Schwarz for Laplacian energy
-/

open scoped BigOperators

namespace EffectiveResistance

noncomputable section

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

namespace ConductanceNetwork

variable (N : ConductanceNetwork ι)

/-- Twice the Laplacian bilinear form, written as an ordered edge sum. -/
def edgePairingSum (x y : ι → ℝ) : ℝ :=
  ∑ p : ι × ι,
    N.conductance p.1 p.2 * (x p.1 - x p.2) * (y p.1 - y p.2)

theorem energyPairing_eq_half_edgePairingSum (x y : ι → ℝ) :
    N.energyPairing x y = (2 : ℝ)⁻¹ * N.edgePairingSum x y := by
  rw [energyPairing_eq_sum]
  have hswap :
      (∑ i, ∑ j, x j * N.conductance i j * (y j - y i)) =
        ∑ i, ∑ j, x i * N.conductance i j * (y i - y j) := by
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro i _
    apply Finset.sum_congr rfl
    intro j _
    rw [N.conductance_comm]
  calc
    (∑ i, ∑ j, x i * N.conductance i j * (y i - y j)) =
        (2 : ℝ)⁻¹ *
          ((∑ i, ∑ j, x i * N.conductance i j * (y i - y j)) +
           (∑ i, ∑ j, x j * N.conductance i j * (y j - y i))) := by
            rw [hswap]
            ring
    _ = (2 : ℝ)⁻¹ * N.edgePairingSum x y := by
      congr 1
      rw [← Finset.sum_add_distrib]
      change _ = ∑ p : ι × ι,
        N.conductance p.1 p.2 * (x p.1 - x p.2) * (y p.1 - y p.2)
      rw [Fintype.sum_prod_type]
      apply Finset.sum_congr rfl
      intro i _
      rw [← Finset.sum_add_distrib]
      apply Finset.sum_congr rfl
      intro j _
      ring

theorem energy_eq_half_edgePairingSum (x : ι → ℝ) :
    N.energy x = (2 : ℝ)⁻¹ * N.edgePairingSum x x := by
  exact N.energyPairing_eq_half_edgePairingSum x x

/-- Cauchy--Schwarz in the positive semidefinite form induced by a Laplacian. -/
theorem energyPairing_sq_le (x y : ι → ℝ) :
    N.energyPairing x y ^ 2 ≤ N.energy x * N.energy y := by
  let r : ι × ι → ℝ := fun p =>
    N.conductance p.1 p.2 * (x p.1 - x p.2) * (y p.1 - y p.2)
  let f : ι × ι → ℝ := fun p =>
    N.conductance p.1 p.2 * (x p.1 - x p.2) ^ 2
  let g : ι × ι → ℝ := fun p =>
    N.conductance p.1 p.2 * (y p.1 - y p.2) ^ 2
  have hf : ∀ p ∈ (Finset.univ : Finset (ι × ι)), 0 ≤ f p := by
    intro p _
    exact mul_nonneg (N.nonnegative _ _) (sq_nonneg _)
  have hg : ∀ p ∈ (Finset.univ : Finset (ι × ι)), 0 ≤ g p := by
    intro p _
    exact mul_nonneg (N.nonnegative _ _) (sq_nonneg _)
  have hr : ∀ p ∈ (Finset.univ : Finset (ι × ι)),
      r p ^ 2 ≤ f p * g p := by
    intro p _
    dsimp [r, f, g]
    exact le_of_eq (by ring)
  have hcs : (∑ p, r p) ^ 2 ≤ (∑ p, f p) * ∑ p, g p :=
    Finset.sum_sq_le_sum_mul_sum_of_sq_le_mul Finset.univ hf hg hr
  have hr_sum : ∑ p, r p = N.edgePairingSum x y := by
    rfl
  have hf_sum : ∑ p, f p = N.edgePairingSum x x := by
    apply Finset.sum_congr rfl
    intro p _
    dsimp [f, edgePairingSum]
    ring
  have hg_sum : ∑ p, g p = N.edgePairingSum y y := by
    apply Finset.sum_congr rfl
    intro p _
    dsimp [g, edgePairingSum]
    ring
  rw [hr_sum, hf_sum, hg_sum] at hcs
  calc
    N.energyPairing x y ^ 2 =
        (4 : ℝ)⁻¹ * N.edgePairingSum x y ^ 2 := by
          rw [N.energyPairing_eq_half_edgePairingSum]
          ring
    _ ≤ (4 : ℝ)⁻¹ *
        (N.edgePairingSum x x * N.edgePairingSum y y) :=
          mul_le_mul_of_nonneg_left hcs
            (inv_nonneg.mpr (by norm_num : (0 : ℝ) ≤ 4))
    _ = N.energy x * N.energy y := by
          rw [N.energy_eq_half_edgePairingSum, N.energy_eq_half_edgePairingSum]
          ring

end ConductanceNetwork

end

end EffectiveResistance
