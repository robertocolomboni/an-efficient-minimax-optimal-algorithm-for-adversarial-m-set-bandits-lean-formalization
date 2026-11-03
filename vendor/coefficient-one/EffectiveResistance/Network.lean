import EffectiveResistance.MatrixOrder
import Mathlib.LinearAlgebra.Matrix.Symmetric
import Mathlib.Tactic.Ring

/-!
# Finite conductance networks

This file fixes the purely algebraic model behind the electrical terminology:
an edge conductance is a symmetric nonnegative matrix with zero diagonal, and
its Laplacian is `diagonal degree - conductance`.
-/

open scoped BigOperators
open Matrix

namespace EffectiveResistance

noncomputable section

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- A finite symmetric network of nonnegative conductances. -/
structure ConductanceNetwork (ι : Type*) [Fintype ι] [DecidableEq ι] where
  conductance : Matrix ι ι ℝ
  symmetric : conductance.IsSymm
  nonnegative : ∀ i j, 0 ≤ conductance i j
  diagonal_zero : ∀ i, conductance i i = 0

namespace ConductanceNetwork

variable (N : ConductanceNetwork ι)

/-- Total conductance incident to a vertex. -/
def degree (i : ι) : ℝ :=
  ∑ j, N.conductance i j

/-- Weighted graph Laplacian. -/
def laplacian : Matrix ι ι ℝ :=
  Matrix.diagonal N.degree - N.conductance

theorem conductance_comm (i j : ι) :
    N.conductance i j = N.conductance j i := by
  exact N.symmetric.apply j i

theorem laplacian_apply (i j : ι) :
    N.laplacian i j = if i = j then N.degree i else -N.conductance i j := by
  classical
  by_cases hij : i = j
  · subst j
    simp [laplacian, N.diagonal_zero]
  · simp [laplacian, hij]

theorem laplacian_diagonal (i : ι) :
    N.laplacian i i = N.degree i := by
  simp [laplacian_apply]

theorem laplacian_offDiagonal {i j : ι} (hij : i ≠ j) :
    N.laplacian i j = -N.conductance i j := by
  simp [laplacian_apply, hij]

theorem laplacian_mulVec (x : ι → ℝ) (i : ι) :
    (N.laplacian *ᵥ x) i =
      ∑ j, N.conductance i j * (x i - x j) := by
  rw [laplacian, Matrix.sub_mulVec]
  change (Matrix.diagonal N.degree *ᵥ x) i - (N.conductance *ᵥ x) i = _
  rw [Matrix.mulVec_diagonal]
  simp [degree, Matrix.mulVec, dotProduct, mul_sub, Finset.sum_sub_distrib,
    Finset.sum_mul]

theorem laplacian_mulVec_one :
    N.laplacian *ᵥ (fun _ : ι => (1 : ℝ)) = 0 := by
  funext i
  simp [laplacian_mulVec]

theorem laplacian_isSymm : N.laplacian.IsSymm := by
  exact (Matrix.isSymm_diagonal N.degree).sub N.symmetric

/-- Bilinear form represented by the Laplacian. -/
def energyPairing (x y : ι → ℝ) : ℝ :=
  x ⬝ᵥ (N.laplacian *ᵥ y)

/-- Dirichlet energy of a potential vector. -/
def energy (x : ι → ℝ) : ℝ :=
  N.energyPairing x x

theorem energy_eq_quadraticForm (x : ι → ℝ) :
    N.energy x = quadraticForm N.laplacian x :=
  rfl

theorem energyPairing_comm (x y : ι → ℝ) :
    N.energyPairing x y = N.energyPairing y x := by
  simp only [energyPairing, dotProduct, Matrix.mulVec, Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  rw [N.laplacian_isSymm.apply]
  ring

theorem energyPairing_eq_sum (x y : ι → ℝ) :
    N.energyPairing x y =
      ∑ i, ∑ j, x i * N.conductance i j * (y i - y j) := by
  simp [energyPairing, dotProduct, laplacian_mulVec, Finset.mul_sum, mul_assoc]

theorem energy_nonnegative (x : ι → ℝ) : 0 ≤ N.energy x := by
  rw [energy, energyPairing_eq_sum]
  have hpair :
      (∑ i, ∑ j, x i * N.conductance i j * (x i - x j)) =
        (2 : ℝ)⁻¹ * ∑ i, ∑ j,
          N.conductance i j * (x i - x j) ^ 2 := by
    calc
      (∑ i, ∑ j, x i * N.conductance i j * (x i - x j)) =
          (2 : ℝ)⁻¹ *
            ((∑ i, ∑ j, x i * N.conductance i j * (x i - x j)) +
             (∑ i, ∑ j, x j * N.conductance i j * (x j - x i))) := by
              have hswap :
                  (∑ i, ∑ j, x j * N.conductance i j * (x j - x i)) =
                    ∑ i, ∑ j, x i * N.conductance i j * (x i - x j) := by
                rw [Finset.sum_comm]
                apply Finset.sum_congr rfl
                intro i _
                apply Finset.sum_congr rfl
                intro j _
                rw [N.conductance_comm]
              rw [hswap]
              ring
      _ = (2 : ℝ)⁻¹ * ∑ i, ∑ j,
            N.conductance i j * (x i - x j) ^ 2 := by
              congr 1
              rw [← Finset.sum_add_distrib]
              apply Finset.sum_congr rfl
              intro i _
              rw [← Finset.sum_add_distrib]
              apply Finset.sum_congr rfl
              intro j _
              ring
  rw [hpair]
  exact mul_nonneg ((inv_pos.mpr (by norm_num : (0 : ℝ) < 2)).le)
    (Finset.sum_nonneg fun i _ =>
    Finset.sum_nonneg fun j _ => mul_nonneg (N.nonnegative i j) (sq_nonneg _))

end ConductanceNetwork

end

end EffectiveResistance
