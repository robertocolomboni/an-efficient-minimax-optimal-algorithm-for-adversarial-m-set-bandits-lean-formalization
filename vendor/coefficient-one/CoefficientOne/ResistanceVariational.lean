import EffectiveResistance.RegressionIdentity
import Mathlib

/-!
# Variational estimates for effective resistance

The energy Cauchy--Schwarz inequality bounds resistance from below using
any test potential. These are supplementary network lemmas; the limiting
argument in `PathCounterexampleLimit` uses continuity of a regularized inverse.
-/

open scoped BigOperators
open Matrix EffectiveResistance

namespace CoefficientOne

noncomputable section

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

theorem endpoint_difference_sq_le_energy_mul_resistance
    (N : ConductanceNetwork ι) (G : GreenKernel N)
    (i j : ι) (hij : i ≠ j) (x : ι → ℝ) :
    (x i - x j) ^ 2 ≤ N.energy x * G.effectiveResistance i j := by
  have hcs := N.energyPairing_sq_le x (G.potential (pairDemand i j))
  have hpair : N.energyPairing x (G.potential (pairDemand i j)) = x i - x j := by
    rw [ConductanceNetwork.energyPairing, G.solves_pairDemand hij,
      dotProduct_comm, EffectiveResistance.pairDemand_dotProduct]
  rw [hpair, ← G.effectiveResistance_eq_energy hij] at hcs
  exact hcs

theorem endpoint_difference_sq_div_energy_le_resistance
    (N : ConductanceNetwork ι) (G : GreenKernel N)
    (i j : ι) (hij : i ≠ j) (x : ι → ℝ) (hx : 0 < N.energy x) :
    (x i - x j) ^ 2 / N.energy x ≤ G.effectiveResistance i j := by
  apply (div_le_iff₀ hx).mpr
  simpa only [mul_comm] using
    endpoint_difference_sq_le_energy_mul_resistance N G i j hij x

end

end CoefficientOne
