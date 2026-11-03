import MsetsPaper.Upper.ProjectionSetupResource

/-! Tail-transition implementation of the natural ceiling. Only the scalar
input, current integer and counters survive a transition. The max recurrence
charges four loop words; all fixed projection-setup temporaries fit in fifty
words. Exact reals and integer counters are word-RAM cells, not bit strings. -/

noncomputable section

namespace MsetsPaper.Upper

def ceilingArena (x : ℝ) (k work allocated peak : ℕ) : ResourceRun ℕ × ℕ :=
  if h : x ≤ (k : ℝ) then (⟨k, work + 2, allocated + 1⟩, max peak 4) else
    ceilingArena x (k + 1) (work + 3) (allocated + 2) (max peak 4)
termination_by ⌈x⌉₊ - k
decreasing_by
  have hk : k < ⌈x⌉₊ := Nat.lt_ceil.mpr (lt_of_not_ge h)
  omega

theorem ceilingArena_correct (x : ℝ) (k work allocated peak : ℕ) (hk : k ≤ ⌈x⌉₊) :
    (ceilingArena x k work allocated peak).1.value = ⌈x⌉₊ ∧
    (ceilingArena x k work allocated peak).1.work = work + 3 * (⌈x⌉₊ - k) + 2 ∧
    (ceilingArena x k work allocated peak).1.allocated = allocated + 2 * (⌈x⌉₊ - k) + 1 ∧
    (ceilingArena x k work allocated peak).2 = max peak 4 := by
  rw [ceilingArena]
  split_ifs with h
  · have heq : k = ⌈x⌉₊ := Nat.le_antisymm hk (Nat.ceil_le.mpr h)
    simp [heq]
  · have hlt : k < ⌈x⌉₊ := Nat.lt_ceil.mpr (lt_of_not_ge h)
    have ih := ceilingArena_correct x (k + 1) (work + 3) (allocated + 2) (max peak 4) (by omega)
    exact ⟨ih.1, by omega, by omega, by simpa only [max_self, max_assoc] using ih.2.2.2⟩
termination_by ⌈x⌉₊ - k

def projectionSetupArena (d : ℕ) (eta T : ℝ) : ResourceRun ProjectionSetup × ℕ :=
  let realD := (d : ℝ)
  let radius := 4 * realD * T
  let eps := eta / T
  let tolerance := (eps * eps) / (2 * (radius * radius))
  let rho := tolerance / (2 * Real.sqrt realD)
  let lambda := 128 * eta * realD
  let target := 4 * realD * (realD + 1) * Real.log (radius / rho)
  let budget := ceilingArena target 0 0 0 0
  (⟨⟨radius, tolerance, rho, lambda, budget.1.value + 1⟩,
    budget.1.work + 25, budget.1.allocated + 30⟩, max budget.2 50)

theorem projectionSetupArena_refines (d : ℕ) (eta T : ℝ) :
    (projectionSetupArena d eta T).1 = projectionSetupResource d eta T := by
  dsimp only [projectionSetupArena, projectionSetupResource]
  let x := 4 * (d : ℝ) * ((d : ℝ) + 1) * Real.log
    (projectionRadius d T / (projectionTolerance d eta T / (2 * Real.sqrt (d : ℝ))))
  have hc := ceilingArena_correct x 0 0 0 0 (Nat.zero_le _)
  have hr := ceilingResource_correct x 0 (Nat.zero_le _)
  simp only [x, projectionRadius, projectionTolerance, pow_two] at hc hr
  simp only [hc.1, hc.2.1, hc.2.2.1, hr.1, hr.2.1, hr.2.2, Nat.zero_add]

theorem projectionSetupArena_peak (d : ℕ) (eta T : ℝ) :
    (projectionSetupArena d eta T).2 = 50 := by
  dsimp only [projectionSetupArena]
  rw [(ceilingArena_correct _ 0 0 0 0 (Nat.zero_le _)).2.2.2]
  rfl

end MsetsPaper.Upper
