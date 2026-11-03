import MsetsPaper.Upper.ProjectionSetupArena
import MsetsPaper.Upper.RealArithmeticPrimitives

noncomputable section

namespace MsetsPaper.Upper

open ResourcePrograms (sqrtResource sqrtResource_values sqrtResource_bounds)

def projectionSetupExpLogArena (d : ℕ) (eta T : ℝ) : ResourceRun ProjectionSetup × ℕ :=
  let realD := (d : ℝ)
  let radius := 4 * realD * T
  let eps := eta / T
  let tolerance := (eps * eps) / (2 * (radius * radius))
  let root := sqrtResource realD
  let rho := tolerance / (2 * root.value)
  let lambda := 128 * eta * realD
  let target := 4 * realD * (realD + 1) * Real.log (radius / rho)
  let budget := ceilingArena target 0 0 0 0
  (⟨⟨radius, tolerance, rho, lambda, budget.1.value + 1⟩,
    budget.1.work + root.work + 24, budget.1.allocated + root.allocated + 29⟩,
    max budget.2 50)

theorem projectionSetupExpLogArena_values (d : ℕ) (eta T : ℝ) :
    (projectionSetupExpLogArena d eta T).1.value =
      ⟨projectionRadius d T, projectionTolerance d eta T,
        projectionTolerance d eta T / (2 * Real.sqrt (d : ℝ)),
        128 * eta * d, projectionOracleBudget d eta T⟩ := by
  simp only [projectionSetupExpLogArena, sqrtResource_values,
    (ceilingArena_correct _ 0 0 0 0 (Nat.zero_le _)).1,
    projectionRadius, projectionTolerance, projectionOracleBudget, ellipsoidIterationBudget, pow_two]

theorem projectionSetupExpLogArena_work (d : ℕ) (eta T : ℝ) :
    (projectionSetupExpLogArena d eta T).1.work ≤ 3 * projectionOracleBudget d eta T + 27 := by
  let x := 4 * (d : ℝ) * ((d : ℝ) + 1) * Real.log
    (projectionRadius d T / (projectionTolerance d eta T / (2 * Real.sqrt (d : ℝ))))
  have hc := ceilingArena_correct x 0 0 0 0 (Nat.zero_le _)
  have hr := sqrtResource_bounds (d : ℝ)
  simp only [x, projectionRadius, projectionTolerance, pow_two, Nat.sub_zero, Nat.zero_add] at hc
  simp only [projectionSetupExpLogArena, sqrtResource_values, projectionOracleBudget,
    ellipsoidIterationBudget, projectionRadius, projectionTolerance, pow_two]
  omega

theorem projectionSetupExpLogArena_allocated (d : ℕ) (eta T : ℝ) :
    (projectionSetupExpLogArena d eta T).1.allocated ≤ 2 * projectionOracleBudget d eta T + 32 := by
  let x := 4 * (d : ℝ) * ((d : ℝ) + 1) * Real.log
    (projectionRadius d T / (projectionTolerance d eta T / (2 * Real.sqrt (d : ℝ))))
  have hc := ceilingArena_correct x 0 0 0 0 (Nat.zero_le _)
  have hr := sqrtResource_bounds (d : ℝ)
  simp only [x, projectionRadius, projectionTolerance, pow_two, Nat.sub_zero, Nat.zero_add] at hc
  simp only [projectionSetupExpLogArena, sqrtResource_values, projectionOracleBudget,
    ellipsoidIterationBudget, projectionRadius, projectionTolerance, pow_two]
  omega

theorem projectionSetupExpLogArena_peak (d : ℕ) (eta T : ℝ) :
    (projectionSetupExpLogArena d eta T).2 = 50 := by
  dsimp only [projectionSetupExpLogArena]
  rw [(ceilingArena_correct _ 0 0 0 0 (Nat.zero_le _)).2.2.2]
  rfl

end MsetsPaper.Upper
