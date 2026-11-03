import MsetsPaper.Alignment.ImplementationDual
import MsetsPaper.Upper.ProjectionArena

/-! Definitive L8: one concrete output, its accuracy, full Pythagorean
inequality, operational work and peak storage. No optimizer or oracle
correctness premise is supplied by the caller. -/

noncomputable section
open scoped BigOperators
open MsetsPaper.Upper MsetsPaper.Upper.ResourcePrograms MsetsPaper.Upper.SchurSolver

namespace MsetsPaper.Alignment.Implementation

variable {d m : ℕ}

def storeParameter (theta : Fin d → ℝ) : StoredVector d :=
  ⟨List.ofFn theta, List.length_ofFn⟩

theorem storeParameter_values (theta : Fin d → ℝ) :
    storedVector (storeParameter theta) = theta := cachedRealVector_ofFn theta

def projectionTimeBound (d m : ℕ) (eta T : ℝ) : ℝ :=
  150 * ((d : ℝ) + 1) ^ 2 +
    (8 * (d : ℝ) ^ 2 * (Real.log (projectionRadius d T) -
      Real.log (projectionTolerance d eta T) + Real.log 2 + Real.log (d : ℝ) / 2) + 2) *
      ((searchStepBudget d m : ℝ) + 6) + 50

/-- The paper's L8, with explicit real-RAM resource bounds on the same
computed vector. `SmoothingPolytope` includes the probability-simplex
conditions, and the Pythagorean inequality quantifies over every competitor. -/
theorem approximate_projection (theta : Fin d → ℝ)
    (hm : 1 ≤ m) (hmtop : m ≤ d - 1) (eta T : ℝ)
    (heta : 0 < eta) (hcap : eta ≤ 1 / (256 * (d : ℝ))) (hT : 1 ≤ T)
    (hKL : finiteKL (weightedLaw (m := m) (0 : Fin d → ℝ)) (weightedLaw theta) ≤ T) :
    let run := projectionArena (storeParameter theta) m eta T
    let v := ellipsoidProjectionShift (m := m) theta eta T
    storedVector run.1.value = theta + v ∧
    coordinateL1 v ≤ projectionRadius d T ∧
    (∀ u, projectionDual (m := m) theta (projectionLower d m (128 * eta * d))
      (projectionUpper d m (128 * eta * d)) v ≤
      projectionDual (m := m) theta (projectionLower d m (128 * eta * d))
        (projectionUpper d m (128 * eta * d)) u + projectionTolerance d eta T) ∧
    SmoothingPolytope ((128 * eta * d) / 2)
      (weightedLaw (m := m) (storedVector run.1.value)) ∧
    (∀ q : Action d m → ℝ, SmoothingPolytope (128 * eta * d) q →
      finiteKL q (weightedLaw (m := m) (storedVector run.1.value)) +
        finiteKL (weightedLaw (m := m) (storedVector run.1.value)) (weightedLaw theta) ≤
          finiteKL q (weightedLaw theta) + eta / T) ∧
    (run.1.work : ℝ) ≤ projectionTimeBound d m eta T ∧
    run.2 ≤ projectionArenaSpace d m := by
  dsimp only
  have hstored := storeParameter_values theta
  have hinput : finiteKL (weightedLaw (m := m) (0 : Fin d → ℝ))
      (weightedLaw (storedVector (storeParameter theta))) ≤ T := by simpa only [hstored] using hKL
  have hcorrect := projectionArena_correct (storeParameter theta) hm hmtop eta T
    heta hcap hT hinput
  have haccuracy := ellipsoidProjectionShift_accuracy theta hm hmtop eta T heta hcap hT hKL
  refine ⟨?_, haccuracy.1, haccuracy.2,
    ⟨weightedLaw_probability _ (by omega), hcorrect.1⟩, ?_, ?_,
    projectionArena_peak _ m eta T⟩
  · rw [projectionArena_values _ hm, hstored]
    rfl
  · intro q hq
    simpa only [hstored] using hcorrect.2 q hq.1.1 hq.1.2 hq.2
  · exact projectionArena_polynomial_work _ (by omega) m eta T heta hcap hT

end MsetsPaper.Alignment.Implementation
