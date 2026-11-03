import MsetsPaper.Upper.StorageModel
import MsetsPaper.Upper.ProjectionProgram

noncomputable section

namespace MsetsPaper.Upper

/-- Natural ceiling implemented by successive integer comparisons. There is
no unit-cost floor/ceiling oracle: termination uses a proof erased at runtime.
Charging every retained frame gives a conservative space bound as well. -/
def ceilingResource (x : ℝ) (k : ℕ) : ResourceRun ℕ :=
  if h : x ≤ (k : ℝ) then ⟨k, 2, 1⟩ else
    let tail := ceilingResource x (k + 1)
    ⟨tail.value, tail.work + 3, tail.allocated + 2⟩
termination_by ⌈x⌉₊ - k
decreasing_by
  have hk : k < ⌈x⌉₊ := Nat.lt_ceil.mpr (lt_of_not_ge h)
  omega

theorem ceilingResource_correct (x : ℝ) (k : ℕ) (hk : k ≤ ⌈x⌉₊) :
    (ceilingResource x k).value = ⌈x⌉₊ ∧
    (ceilingResource x k).work = 3 * (⌈x⌉₊ - k) + 2 ∧
    (ceilingResource x k).allocated = 2 * (⌈x⌉₊ - k) + 1 := by
  rw [ceilingResource]
  split_ifs with h
  · have heq : k = ⌈x⌉₊ := Nat.le_antisymm hk (Nat.ceil_le.mpr h)
    simp [heq]
  · have hlt : k < ⌈x⌉₊ := Nat.lt_ceil.mpr (lt_of_not_ge h)
    have ih := ceilingResource_correct x (k + 1) (by omega)
    dsimp only
    exact ⟨ih.1, by omega, by omega⟩
termination_by ⌈x⌉₊ - k

structure ProjectionSetup where
  radius : ℝ
  tolerance : ℝ
  ballRadius : ℝ
  lambda : ℝ
  budget : ℕ

/-- Fixed-size real formula followed by the explicit ceiling loop. Casts,
scalar intermediates and the returned record are charged too. -/
def projectionSetupResource (d : ℕ) (eta T : ℝ) : ResourceRun ProjectionSetup :=
  let realD := (d : ℝ)
  let radius := 4 * realD * T
  let eps := eta / T
  let tolerance := (eps * eps) / (2 * (radius * radius))
  let rho := tolerance / (2 * Real.sqrt realD)
  let lambda := 128 * eta * realD
  let target := 4 * realD * (realD + 1) * Real.log (radius / rho)
  let budget := ceilingResource target 0
  ⟨⟨radius, tolerance, rho, lambda, budget.value + 1⟩,
    budget.work + 25, budget.allocated + 30⟩

theorem projectionSetupResource_values (d : ℕ) (eta T : ℝ) :
    (projectionSetupResource d eta T).value =
      ⟨projectionRadius d T, projectionTolerance d eta T,
        projectionTolerance d eta T / (2 * Real.sqrt (d : ℝ)),
        128 * eta * d, projectionOracleBudget d eta T⟩ := by
  simp only [projectionSetupResource, (ceilingResource_correct _ 0 (Nat.zero_le _)).1,
    projectionRadius, projectionTolerance, projectionOracleBudget, ellipsoidIterationBudget,
    pow_two]

theorem projectionSetupResource_counts (d : ℕ) (eta T : ℝ) :
    (projectionSetupResource d eta T).work = 3 * projectionOracleBudget d eta T + 24 ∧
    (projectionSetupResource d eta T).allocated = 2 * projectionOracleBudget d eta T + 29 := by
  let x := 4 * (d : ℝ) * ((d : ℝ) + 1) * Real.log
    (projectionRadius d T / (projectionTolerance d eta T / (2 * Real.sqrt (d : ℝ))))
  have hc := ceilingResource_correct x 0 (Nat.zero_le _)
  simp only [x, projectionRadius, projectionTolerance, pow_two, Nat.sub_zero] at hc
  simp only [projectionSetupResource, projectionOracleBudget, ellipsoidIterationBudget,
    projectionRadius, projectionTolerance, pow_two]
  constructor <;> omega

end MsetsPaper.Upper
