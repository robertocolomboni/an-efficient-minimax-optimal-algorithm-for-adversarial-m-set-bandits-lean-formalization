import EffectiveResistance.PairExchange
import EffectiveResistance.RegressionIdentity
import EffectiveResistance.CovarianceNetwork

/-!
# The interior-rank effective-resistance theorem

This file combines the covariance-energy estimate with the Green-kernel
variational identity.  The boundary ranks are treated separately.
-/

open scoped BigOperators
open Matrix

namespace EffectiveResistance

noncomputable section

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- Effective resistance is controlled by the two covariance diagonal entries
for ranks `m = q + 2` for which all four endpoint cells are nonempty. -/
theorem externalField_effectiveResistance_bound_interior
    (w : ι → ℝ) (hw : ∀ k, 0 < w k)
    (N : ConductanceNetwork ι) (G : GreenKernel N)
    (i j : ι) (hij : i ≠ j) (q : ℕ)
    (hm : q + 2 ≤ Fintype.card ι)
    (hq : q + 2 ≤ Fintype.card (PairComplement i j))
    (hL : N.laplacian = covarianceMatrix w (q + 2)) :
    G.effectiveResistance i j ≤
      1 / covarianceMatrix w (q + 2) i i +
        1 / covarianceMatrix w (q + 2) j j := by
  let P := externalFieldPairTable w hw hm i j
  have hcells := pairCells_pos_of_background_rank w hw i j hij q hq
  have hviP : 0 < P.vi := P.vi_pos hcells.1 hcells.2.1 hcells.2.2.1
  have hvjP : 0 < P.vj := P.vj_pos hcells.1 hcells.2.1 hcells.2.2.1
  have hviEq := externalFieldPairTable_vi_eq_covariance_diagonal
    w hw (q + 2) hm i j
  have hvjEq := externalFieldPairTable_vj_eq_covariance_diagonal
    w hw (q + 2) hm i j
  have hvi : 0 < covarianceMatrix w (q + 2) i i := by
    rw [← hviEq]
    exact hviP
  have hvj : 0 < covarianceMatrix w (q + 2) j j := by
    rw [← hvjEq]
    exact hvjP
  have hR : 0 < G.effectiveResistance i j := G.effectiveResistance_pos hij
  let c := G.regressionMinimizer i j
  have hc : c i - c j = 2 := G.regressionMinimizer_endpoint_difference hR
  have hquadratic := externalField_covariance_energy_lower_bound
    w hw i j hij q hm hq c hc
  have henergy :
      quadraticForm (covarianceMatrix w (q + 2)) c =
        4 / G.effectiveResistance i j := by
    rw [← hL]
    change N.energy c = 4 / G.effectiveResistance i j
    exact G.regressionMinimizer_energy hij hR
  rw [henergy] at hquadratic
  have hreciprocal :
      covarianceMatrix w (q + 2) i i *
          covarianceMatrix w (q + 2) j j /
        (covarianceMatrix w (q + 2) i i +
          covarianceMatrix w (q + 2) j j) ≤
        1 / G.effectiveResistance i j := by
    have hscaled :
        4 * (covarianceMatrix w (q + 2) i i *
            covarianceMatrix w (q + 2) j j /
          (covarianceMatrix w (q + 2) i i +
            covarianceMatrix w (q + 2) j j)) ≤
          4 * (1 / G.effectiveResistance i j) := by
      convert hquadratic using 1 <;> ring
    nlinarith [hscaled]
  have hsum : 0 < covarianceMatrix w (q + 2) i i +
      covarianceMatrix w (q + 2) j j := add_pos hvi hvj
  have hcross :
      covarianceMatrix w (q + 2) i i *
          covarianceMatrix w (q + 2) j j *
        G.effectiveResistance i j ≤
      covarianceMatrix w (q + 2) i i +
        covarianceMatrix w (q + 2) j j := by
    have h := (div_le_div_iff₀ hsum hR).mp hreciprocal
    nlinarith
  have hrhs :
      1 / covarianceMatrix w (q + 2) i i +
          1 / covarianceMatrix w (q + 2) j j =
        (covarianceMatrix w (q + 2) i i +
          covarianceMatrix w (q + 2) j j) /
        (covarianceMatrix w (q + 2) i i *
          covarianceMatrix w (q + 2) j j) := by
    field_simp [ne_of_gt hvi, ne_of_gt hvj]
    <;> ring
  rw [hrhs]
  exact (le_div_iff₀ (mul_pos hvi hvj)).2 (by
    nlinarith [hcross])

/-- The same theorem specialized to the canonical conductance network
`cᵢⱼ = -Σᵢⱼ`. -/
theorem externalFieldCovarianceNetwork_effectiveResistance_bound_interior
    (w : ι → ℝ) (hw : ∀ k, 0 < w k)
    (q : ℕ) (hm : q + 2 ≤ Fintype.card ι)
    (hinterior : q + 2 ≤ Fintype.card ι - 2)
    (G : GreenKernel
      (externalFieldCovarianceNetworkInterior w hw q hm hinterior))
    (i j : ι) (hij : i ≠ j) :
    G.effectiveResistance i j ≤
      1 / covarianceMatrix w (q + 2) i i +
        1 / covarianceMatrix w (q + 2) j j := by
  have hq : q + 2 ≤ Fintype.card (PairComplement i j) := by
    rw [card_pairComplement i j hij]
    exact hinterior
  exact externalField_effectiveResistance_bound_interior
    w hw (externalFieldCovarianceNetworkInterior w hw q hm hinterior) G
    i j hij q hm hq
    (externalFieldCovarianceNetworkInterior_laplacian
      w hw q hm hinterior)

end

end EffectiveResistance
