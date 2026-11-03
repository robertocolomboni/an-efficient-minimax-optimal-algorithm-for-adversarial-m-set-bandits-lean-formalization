import MsetsPaper.Upper.RoundExecutionResources
import MsetsPaper.Upper.RoundBudget
import MsetsPaper.Upper.LearningRateResource
import MsetsPaper.Upper.ProjectionArena

/-! # Complete operational round, including nested projection memory

All pre-projection temporary words may conservatively remain live throughout
the projection. The projection releases its own iteration-local words. The
returned parameter vector is copied before the outer round arena is reset.
Thus no projection iteration or round count occurs in the peak-space bound.
-/

namespace MsetsPaper.Upper.RoundProgram

open SchurSolver ResourcePrograms
open scoped unitInterval

noncomputable section

variable {d m : ℕ}

def roundArena (theta : StoredVector d) (eta T : ℝ) (hmd : m ≤ d)
    (u : Fin d → unitInterval) (Y : ℝ) : ResourceRun (StoredVector d) × ℕ :=
  let unprojected := unprojectedRoundResource theta eta hmd u Y
  let projected := projectionArena unprojected.value m eta T
  let copied := copyStoredVectorResource projected.1.value
  (⟨copied.value, unprojected.work + projected.1.work + copied.work + 3,
      unprojected.allocated + projected.1.allocated + copied.allocated + 3⟩,
    unprojected.allocated + projected.2 + copied.allocated + 3)

theorem roundArena_values (theta : StoredVector d) (eta T Y : ℝ)
    (hm : 1 ≤ m) (hmtop : m ≤ d - 1) (u : Fin d → unitInterval) :
    storedVector (roundArena theta eta T (by omega : m ≤ d) u Y).1.value =
      ellipsoidProjection (m := m)
        (unprojectedFromFeedback (storedVector theta) eta
          (sampleResource theta (by omega : m ≤ d) u).value.action Y) eta T := by
  simp only [roundArena, copyStoredVectorResource_values, projectionArena_values _ hm,
    unprojectedRoundResource_exact theta eta Y hm hmtop]

def roundWorkBase (d m : ℕ) : ℕ :=
  1000 * (d + m + 1)^4 + 150 * (d + 1)^2 + 3 * d + 55

def roundArenaSpace (d m : ℕ) : ℕ :=
  1000 * (d + m + 1)^4 + projectionArenaSpace d m + 4 * d + 5

theorem roundArena_work (theta : StoredVector d) (eta T Y : ℝ)
    (hmd : m ≤ d) (u : Fin d → unitInterval) :
    (roundArena theta eta T hmd u Y).1.work ≤
      roundWorkBase d m + projectionOracleBudget d eta T * (searchStepBudget d m + 6) := by
  have hu := (unprojectedRoundResource_bounds theta eta Y hmd u).1
  have hp := projectionArena_work (unprojectedRoundResource theta eta hmd u Y).value m eta T
  have hc := (copyStoredVectorResource_bounds
    (projectionArena (unprojectedRoundResource theta eta hmd u Y).value m eta T).1.value).1
  dsimp only [roundArena, roundWorkBase]
  omega

theorem roundArena_peak (theta : StoredVector d) (eta T Y : ℝ)
    (hmd : m ≤ d) (u : Fin d → unitInterval) :
    (roundArena theta eta T hmd u Y).2 ≤ roundArenaSpace d m := by
  have hu := (unprojectedRoundResource_bounds theta eta Y hmd u).2
  have hp := projectionArena_peak (unprojectedRoundResource theta eta hmd u Y).value m eta T
  have hc := (copyStoredVectorResource_bounds
    (projectionArena (unprojectedRoundResource theta eta hmd u Y).value m eta T).1.value).2
  dsimp only [roundArena, roundArenaSpace]
  omega

/-- An explicit time polynomial for the paper's selected learning rate.
Its only non-polynomial argument is log T; delta has disappeared. -/
def roundTimePolynomial (d m : ℕ) (T : ℝ) : ℝ :=
  roundWorkBase d m +
    (8 * (d : ℝ)^2 * (600 + 6 * (d : ℝ) + 6 * Real.log T) + 2) *
      ((searchStepBudget d m : ℝ) + 6)

theorem roundArena_main_work (theta : StoredVector d) (T K delta Y : ℝ)
    (hd : 1 ≤ d) (hT : 1 ≤ T) (hK : 2 ≤ K) (hdelta0 : 0 < delta) (hdelta1 : delta ≤ 1)
    (hmd : m ≤ d) (u : Fin d → unitInterval) :
    ((roundArena theta (mainLearningRate d T K delta) T hmd u Y).1.work : ℝ) ≤
      roundTimePolynomial d m T := by
  have hw : ((roundArena theta (mainLearningRate d T K delta) T hmd u Y).1.work : ℝ) ≤
      (roundWorkBase d m : ℝ) +
        (projectionOracleBudget d (mainLearningRate d T K delta) T : ℝ) *
          ((searchStepBudget d m : ℝ) + 6) := by
    exact_mod_cast roundArena_work theta (mainLearningRate d T K delta) T Y hmd u
  have hb := projectionOracleBudget_polynomial_bound d hd T K delta hT hK hdelta0 hdelta1
  have hp := mul_le_mul_of_nonneg_right hb
    (by positivity : (0 : ℝ) ≤ (searchStepBudget d m : ℝ) + 6)
  unfold roundTimePolynomial
  linarith

def parameterFootprint (theta : StoredVector d) : ℕ := 3 * theta.1.length + 1

theorem parameterFootprint_eq (theta : StoredVector d) : parameterFootprint theta = 3 * d + 1 := by
  simp only [parameterFootprint, theta.2]

/-- Streaming inputs are queried once per round. The driver does not retain a
list of past uniforms, observations, actions, or iterates. -/
def roundsArena (theta : StoredVector d) (eta T : ℝ) (hmd : m ≤ d)
    (u : ℕ → Fin d → unitInterval) (Y : ℕ → ℝ) (n : ℕ) :
    ResourceRun (StoredVector d) × ℕ :=
  nestedArenaProgram (fun t theta => roundArena theta eta T hmd (u t) (Y t))
    parameterFootprint n 0 theta 0 0 0

theorem roundsArena_work (theta : StoredVector d) (eta T : ℝ) (hmd : m ≤ d)
    (u : ℕ → Fin d → unitInterval) (Y : ℕ → ℝ) (n : ℕ) :
    (roundsArena theta eta T hmd u Y n).1.work ≤
      n * (roundWorkBase d m + projectionOracleBudget d eta T * (searchStepBudget d m + 6) + 3) + 1 := by
  simpa only [roundsArena, Nat.zero_add] using
    nestedArenaProgram_work _ parameterFootprint _
      (fun t theta => roundArena_work theta eta T (Y t) hmd (u t)) n 0 theta 0 0 0

theorem roundsArena_peak (theta : StoredVector d) (eta T : ℝ) (hmd : m ≤ d)
    (u : ℕ → Fin d → unitInterval) (Y : ℕ → ℝ) (n : ℕ) :
    (roundsArena theta eta T hmd u Y n).2 ≤ 3 * d + 1 + roundArenaSpace d m + 8 := by
  exact nestedArenaProgram_peak _ _ (3 * d + 1) (roundArenaSpace d m)
    (fun theta => (parameterFootprint_eq theta).le)
    (fun t theta => roundArena_peak theta eta T (Y t) hmd (u t)) n 0 theta 0 0 0 (by omega)

theorem roundsArena_values (theta : StoredVector d) (eta T : ℝ) (hmd : m ≤ d)
    (u : ℕ → Fin d → unitInterval) (Y : ℕ → ℝ) (n : ℕ) :
    (roundsArena theta eta T hmd u Y n).1.value =
      streamIterate (fun t theta => (roundArena theta eta T hmd (u t) (Y t)).1.value) n 0 theta :=
  nestedArenaProgram_values _ _ n 0 theta 0 0 0

end

end MsetsPaper.Upper.RoundProgram
