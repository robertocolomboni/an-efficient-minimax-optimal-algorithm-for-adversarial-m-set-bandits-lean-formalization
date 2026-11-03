import MsetsPaper.Upper.SPDSchurResources
import MsetsPaper.Upper.SPDWeightedSolve

/-! # Stored-data SPD solver: pivots, input footprint, and estimator instance

The resource bounds here concern the solve after its input data are stored.
`weightedSolveProgram_cost` separately includes the DP preprocessing arithmetic.
The word model stores a real/index/reference in one word and is not a claim
about bit complexity or finite-precision numerical error.
-/

namespace MsetsPaper.Upper.SchurSolver

open Matrix MsetsLower MsetsLower.History

noncomputable section

def PositivePivots : (n : ℕ) → StoredMatrix n → Prop
  | 0, _ => True
  | n + 1, A =>
    0 < (resourceMatrixRead A 0 0).value ∧
      PositivePivots n (resourceSchurMatrix A (resourceMatrixRead A 0 0).value).value

theorem positivePivots_of_posDef : ∀ (n : ℕ) (A : StoredMatrix n),
    (storedMatrix A).PosDef → PositivePivots n A := by
  intro n
  induction n with
  | zero => intro A hA; trivial
  | succ n ih =>
    intro A hA
    change 0 < (resourceMatrixRead A 0 0).value ∧ _
    rw [resourceMatrixRead_values]
    constructor
    · exact hA.diag_pos
    · apply ih
      rw [resourceSchurMatrix_exact]
      exact schur_posDef _ hA

theorem storedMatrix_cell_count {n : ℕ} (A : StoredMatrix n) :
    (A.1.map List.length).sum = n ^ 2 := by
  have heq : A.1.map List.length = A.1.map (fun _ ↦ n) := by
    apply List.map_congr_left
    intro row hrow
    exact A.2.2 row hrow
  rw [heq]
  simp [List.map_const', A.2.1, Nat.pow_two]

/-- Three words per input list cell, and two outer object headers. This
conservative count includes real cells, row references and vector cells. -/
def inputWordFootprint {n : ℕ} (A : StoredMatrix n) (b : StoredVector n) : ℕ :=
  3 * (A.1.map List.length).sum + 3 * A.1.length + 3 * b.1.length + 2

theorem inputWordFootprint_eq {n : ℕ} (A : StoredMatrix n) (b : StoredVector n) :
    inputWordFootprint A b = 3 * n ^ 2 + 6 * n + 2 := by
  simp only [inputWordFootprint, storedMatrix_cell_count, A.2.1, b.2]
  ring

/-- Input words plus every temporary word allocated during the recursive
call are polynomially bounded even if nothing is reclaimed during the call. -/
theorem profiledSolve_total_words (n : ℕ) (A : StoredMatrix n) (b : StoredVector n) :
    inputWordFootprint A b + (profiledSolve n A b).1.allocated ≤ 210 * (n + 1) ^ 4 := by
  rw [inputWordFootprint_eq, profiledSolve_resource]
  have h := (resourceSolve_bounds n A b).2
  nlinarith

def weightedMomentData {d : ℕ} (theta : Fin d → ℝ) (m : ℕ) : StoredMatrix d :=
  let weights := weightCells theta
  let w := cachedRealVector weights.1 (weightCells_length theta)
  let moments := momentRows w m
  ⟨moments.1, momentRows_length w m, momentRows_row_length w m⟩

theorem weightedMomentData_exact {d m : ℕ} (theta : Fin d → ℝ) (hm : 1 ≤ m) :
    storedMatrix (weightedMomentData theta m) = secondMoment (weightedLaw (m := m) theta) := by
  simp only [weightedMomentData, storedMatrix, momentRows_cached_formula, weightCells_cached,
    espPartitionProgram_correct, espPairProgram_correct theta hm]
  rfl

def feedbackData {d m : ℕ} (a : Action d m) (Y : ℝ) : StoredVector d :=
  ⟨(feedbackCells a Y).1, feedbackCells_length a Y⟩

theorem feedbackData_exact {d m : ℕ} (a : Action d m) (Y : ℝ) :
    storedVector (feedbackData a Y) = Y • (fun i ↦ selectedIndicator i a) :=
  feedbackCells_cached a Y

/-- Explicit instantiation on the DP-produced matrix and observed-feedback
vector. No invertibility or desired estimator identity is assumed. -/
theorem profiled_weighted_estimate {d m : ℕ} (theta : Fin d → ℝ) (a : Action d m)
    (ell : Fin d → ℝ) (hm : 1 ≤ m) (hmtop : m ≤ d - 1) :
    let A := weightedMomentData theta m
    let b := feedbackData a (actionLoss a ell)
    storedVector (profiledSolve d A b).1.value = estimateVector theta a ell ∧
      PositivePivots d A ∧
      (profiledSolve d A b).2 = d ^ 2 * (d + 1) ∧
      (profiledSolve d A b).1.work ≤ 200 * (d + 1) ^ 4 ∧
      inputWordFootprint A b + (profiledSolve d A b).1.allocated ≤ 210 * (d + 1) ^ 4 := by
  dsimp only
  have hA : (storedMatrix (weightedMomentData theta m)).PosDef := by
    rw [weightedMomentData_exact theta hm]
    exact secondMoment_posDef _ (weightedLaw_pos theta (by omega : m ≤ d)) hm hmtop
  have h := profiledSolve_correct_and_bounded d (weightedMomentData theta m)
    (feedbackData a (actionLoss a ell)) hA
  refine ⟨?_, positivePivots_of_posDef d _ hA, h.2.1, h.2.2.1, profiledSolve_total_words d _ _⟩
  rw [h.1, weightedMomentData_exact theta hm, feedbackData_exact, Matrix.mulVec_smul]
  rfl

end

end MsetsPaper.Upper.SchurSolver
