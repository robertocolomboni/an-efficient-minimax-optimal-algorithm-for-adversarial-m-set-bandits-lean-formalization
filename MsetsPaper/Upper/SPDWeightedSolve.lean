import MsetsPaper.Upper.SPDSchurProgram
import MsetsPaper.Upper.Estimator

/-! # Actual weighted-law estimator through cached DP and Schur elimination

Weights, denominator, moment entries, and feedback right-hand side are all
materialized. The algorithm never evaluates the action-space sum used in the
mathematical definition of the second moment. Arithmetic, access, and storage
costs remain distinct; this module certifies the arithmetic layer.
-/

namespace MsetsPaper.Upper.SchurSolver

open Matrix MsetsLower MsetsLower.History
open scoped BigOperators

noncomputable section

variable {d m : ℕ}

theorem countedMatrix_cost_le (f : Fin d → Fin d → ℝ × ℕ) (C : ℕ)
    (hcost : ∀ i j, (f i j).2 ≤ C) : (countedMatrix f).2 ≤ C * d * d := by
  unfold countedMatrix
  have hout := countedMap_cost_le
    (fun i ↦ countedMap (f i) (List.finRange d)) (List.finRange d) (C * d) (by
      intro i _
      simpa using countedMap_cost_le (f i) (List.finRange d) C (fun j _ ↦ hcost i j))
  simpa using hout

def weightCells (theta : Fin d → ℝ) : List ℝ × ℕ :=
  countedMap (fun i ↦ (Real.exp (theta i), 1)) (List.finRange d)

theorem weightCells_values (theta : Fin d → ℝ) :
    (weightCells theta).1 = List.ofFn (fun i ↦ Real.exp (theta i)) := by
  simp only [weightCells, countedMap_values, List.ofFn_eq_map]

theorem weightCells_length (theta : Fin d → ℝ) : (weightCells theta).1.length = d := by
  rw [weightCells_values, List.length_ofFn]

theorem weightCells_cached (theta : Fin d → ℝ) :
    cachedRealVector (weightCells theta).1 (weightCells_length theta) =
      fun i ↦ Real.exp (theta i) := by
  ext i
  simp [cachedRealVector, weightCells_values]

theorem weightCells_cost (theta : Fin d → ℝ) : (weightCells theta).2 = d := by
  simp [weightCells, countedMap_cost, List.map_const']

def momentRows (w : Fin d → ℝ) (m : ℕ) : List (List ℝ) × ℕ :=
  let denominator := espPartitionProgram w m
  let cells := countedMatrix (espPairProgram w m denominator.1)
  (cells.1, denominator.2 + cells.2)

theorem momentRows_length (w : Fin d → ℝ) (m : ℕ) :
    (momentRows w m).1.length = d := countedMatrix_length _

theorem momentRows_row_length (w : Fin d → ℝ) (m : ℕ)
    (row : List ℝ) (hrow : row ∈ (momentRows w m).1) : row.length = d :=
  countedMatrix_row_length _ row hrow

theorem momentRows_cached_formula (w : Fin d → ℝ) (m : ℕ) :
    cachedRealMatrix (momentRows w m).1 (momentRows_length w m) (momentRows_row_length w m) =
      fun i j ↦ (espPairProgram w m (espPartitionProgram w m).1 i j).1 :=
  countedMatrix_cached _

theorem momentRows_cached (theta : Fin d → ℝ) (hm : 1 ≤ m) :
    cachedRealMatrix (momentRows (fun i ↦ Real.exp (theta i)) m).1
      (momentRows_length _ _) (momentRows_row_length _ _) =
        secondMoment (weightedLaw (m := m) theta) := by
  change cachedRealMatrix
    (countedMatrix (espPairProgram (fun i ↦ Real.exp (theta i)) m
      (espPartitionProgram (fun i ↦ Real.exp (theta i)) m).1)).1 _ _ = _
  rw [countedMatrix_cached, espPartitionProgram_correct]
  ext i j
  exact espPairProgram_correct theta hm i j

theorem momentRows_cost (w : Fin d → ℝ) (m : ℕ) :
    (momentRows w m).2 ≤ 2 * m * d + (2 * m * d + 3) * d * d := by
  simp only [momentRows, espPartitionProgram_cost]
  exact Nat.add_le_add_left
    (countedMatrix_cost_le _ _ (fun i j ↦ espPairProgram_cost_le w m _ i j)) _

def feedbackCells (a : Action d m) (Y : ℝ) : List ℝ × ℕ :=
  countedMap (fun i ↦ (Y * selectedIndicator i a, 1)) (List.finRange d)

theorem feedbackCells_values (a : Action d m) (Y : ℝ) :
    (feedbackCells a Y).1 = List.ofFn (fun i ↦ Y * selectedIndicator i a) := by
  simp only [feedbackCells, countedMap_values, List.ofFn_eq_map]

theorem feedbackCells_length (a : Action d m) (Y : ℝ) :
    (feedbackCells a Y).1.length = d := by rw [feedbackCells_values, List.length_ofFn]

theorem feedbackCells_cached (a : Action d m) (Y : ℝ) :
    cachedRealVector (feedbackCells a Y).1 (feedbackCells_length a Y) =
      Y • (fun i ↦ selectedIndicator i a) := by
  ext i
  simp [cachedRealVector, feedbackCells_values]

theorem feedbackCells_cost (a : Action d m) (Y : ℝ) : (feedbackCells a Y).2 = d := by
  simp [feedbackCells, countedMap_cost, List.map_const']

def weightedSolveProgram (theta : Fin d → ℝ) (a : Action d m) (Y : ℝ) : SolveRun d :=
  let weights := weightCells theta
  let w := cachedRealVector weights.1 (weightCells_length theta)
  let moments := momentRows w m
  let M := cachedRealMatrix moments.1 (momentRows_length w m) (momentRows_row_length w m)
  let rhs := feedbackCells a Y
  let b := cachedRealVector rhs.1 (feedbackCells_length a Y)
  let solution := solveRun d M b
  ⟨solution.values, solution.length_eq, weights.2 + moments.2 + rhs.2 + solution.realOps⟩

theorem weightedSolveProgram_correct (theta : Fin d → ℝ) (a : Action d m) (Y : ℝ)
    (hm : 1 ≤ m) (hmtop : m ≤ d - 1) :
    (weightedSolveProgram theta a Y).vector =
      (secondMoment (weightedLaw (m := m) theta))⁻¹ *ᵥ
        (Y • (fun i ↦ selectedIndicator i a)) := by
  have hM := secondMoment_posDef (weightedLaw (m := m) theta)
    (weightedLaw_pos theta (by omega : m ≤ d)) hm hmtop
  change (solveRun d _ _).vector = _
  simp only [momentRows_cached_formula, weightCells_cached, espPartitionProgram_correct,
    espPairProgram_correct theta hm, feedbackCells_cached]
  exact solveRun_eq_inverse d _ hM _

theorem weightedSolveProgram_estimate (theta : Fin d → ℝ) (a : Action d m)
    (ell : Fin d → ℝ) (hm : 1 ≤ m) (hmtop : m ≤ d - 1) :
    (weightedSolveProgram theta a (actionLoss a ell)).vector = estimateVector theta a ell := by
  rw [weightedSolveProgram_correct theta a _ hm hmtop, Matrix.mulVec_smul]
  rfl

theorem weightedSolveProgram_cost (theta : Fin d → ℝ) (a : Action d m) (Y : ℝ) :
    (weightedSolveProgram theta a Y).realOps ≤
      2 * d + 2 * m * d + (2 * m * d + 3) * d * d + d ^ 2 * (d + 1) := by
  dsimp only [weightedSolveProgram]
  rw [weightCells_cost, feedbackCells_cost, solveRun_realOps]
  have h := momentRows_cost
    (cachedRealVector (weightCells theta).1 (weightCells_length theta)) m
  omega

end

end MsetsPaper.Upper.SchurSolver
