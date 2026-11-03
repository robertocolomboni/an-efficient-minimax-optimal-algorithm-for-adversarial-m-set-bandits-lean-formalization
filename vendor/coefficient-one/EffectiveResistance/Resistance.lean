import EffectiveResistance.Network

/-!
# Green kernels and effective resistance

Mathlib does not currently expose a Moore--Penrose inverse for arbitrary
matrices.  For a graph Laplacian the paper only uses its inverse on the
zero-sum subspace.  `GreenKernel` records precisely that algebraic property.
-/

open scoped BigOperators
open Matrix

namespace EffectiveResistance

noncomputable section

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- A vector whose coordinates sum to zero. -/
def IsZeroSum (y : ι → ℝ) : Prop :=
  ∑ i, y i = 0

/-- Unit demand from `j` to `i`. -/
def pairDemand (i j : ι) : ι → ℝ :=
  fun k => (if k = i then 1 else 0) - (if k = j then 1 else 0)

theorem pairDemand_apply_left {i j : ι} (hij : i ≠ j) :
    pairDemand i j i = 1 := by
  simp [pairDemand, hij]

theorem pairDemand_apply_right {i j : ι} (hij : i ≠ j) :
    pairDemand i j j = -1 := by
  simp [pairDemand, hij, Ne.symm hij]

theorem pairDemand_zeroSum {i j : ι} (hij : i ≠ j) :
    IsZeroSum (pairDemand i j) := by
  classical
  simp [IsZeroSum, pairDemand, Finset.sum_sub_distrib]

/-- A symmetric generalized inverse of a Laplacian on the zero-sum subspace. -/
structure GreenKernel (N : ConductanceNetwork ι) where
  kernel : Matrix ι ι ℝ
  symmetric : kernel.IsSymm
  solves_zeroSum : ∀ y : ι → ℝ, IsZeroSum y →
    N.laplacian *ᵥ (kernel *ᵥ y) = y

namespace GreenKernel

variable {N : ConductanceNetwork ι} (G : GreenKernel N)

/-- Potential selected by the Green kernel for a prescribed demand. -/
def potential (y : ι → ℝ) : ι → ℝ :=
  G.kernel *ᵥ y

/-- Effective resistance, defined algebraically from the zero-sum inverse. -/
def effectiveResistance (i j : ι) : ℝ :=
  pairDemand i j ⬝ᵥ G.potential (pairDemand i j)

theorem solves_pairDemand {i j : ι} (hij : i ≠ j) :
    N.laplacian *ᵥ G.potential (pairDemand i j) = pairDemand i j := by
  exact G.solves_zeroSum _ (pairDemand_zeroSum hij)

theorem effectiveResistance_eq_energy {i j : ι} (hij : i ≠ j) :
    G.effectiveResistance i j = N.energy (G.potential (pairDemand i j)) := by
  rw [effectiveResistance, ConductanceNetwork.energy,
    ConductanceNetwork.energyPairing]
  rw [G.solves_pairDemand hij]
  exact dotProduct_comm _ _

theorem effectiveResistance_nonnegative {i j : ι} (hij : i ≠ j) :
    0 ≤ G.effectiveResistance i j := by
  rw [G.effectiveResistance_eq_energy hij]
  exact N.energy_nonnegative _

/-- The endpoint-degree resistance inequality from the main theorem. -/
def SatisfiesEndpointBound : Prop :=
  ∀ i j : ι, i ≠ j →
    G.effectiveResistance i j ≤ (N.degree i)⁻¹ + (N.degree j)⁻¹

end GreenKernel

end

end EffectiveResistance
