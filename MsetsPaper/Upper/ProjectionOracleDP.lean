import MsetsPaper.Upper.ESPAlgorithms
import MsetsPaper.Upper.ProjectionEllipsoid

/-! Non-enumerative refinements of the projection value and subgradient.

The operational counters count real arithmetic, real comparisons, exp and
log evaluations; each costs one in this explicitly stated oracle-RAM model.
List accesses/allocation and integer loop control are separate refinements.
Weights are materialized once in a d-cell list before the ESP programs run.
-/

noncomputable section
open scoped BigOperators

namespace MsetsPaper.Upper

def countedMap {α β : Type*} (f : α → β × ℕ) : List α → List β × ℕ
  | [] => ([], 0)
  | x :: xs =>
    let cell := f x
    let tail := countedMap f xs
    (cell.1 :: tail.1, cell.2 + tail.2)

theorem countedMap_values {α β : Type*} (f : α → β × ℕ) (xs : List α) :
    (countedMap f xs).1 = xs.map (fun x => (f x).1) := by
  induction xs with
  | nil => rfl
  | cons x xs ih => simp only [countedMap, ih, List.map_cons]

theorem countedMap_cost {α β : Type*} (f : α → β × ℕ) (xs : List α) :
    (countedMap f xs).2 = (xs.map (fun x => (f x).2)).sum := by
  induction xs with
  | nil => rfl
  | cons x xs ih => simp only [countedMap, ih, List.map_cons, List.sum_cons]

theorem countedMap_cost_le {α β : Type*} (f : α → β × ℕ) (xs : List α) (C : ℕ)
    (hC : ∀ x ∈ xs, (f x).2 ≤ C) : (countedMap f xs).2 ≤ C * xs.length := by
  induction xs with
  | nil => simp [countedMap]
  | cons x xs ih =>
    have hx := hC x (by simp)
    have ht := ih (fun y hy => hC y (by simp [hy]))
    simp only [countedMap, List.length_cons]
    nlinarith

def countedSum : List ℝ → ℝ × ℕ
  | [] => (0, 0)
  | x :: xs =>
    let tail := countedSum xs
    (x + tail.1, tail.2 + 1)

theorem countedSum_values (xs : List ℝ) : (countedSum xs).1 = xs.sum := by
  induction xs <;> simp_all [countedSum]

theorem countedSum_cost (xs : List ℝ) : (countedSum xs).2 = xs.length := by
  induction xs <;> simp_all [countedSum]

def cachedRealVector {d : ℕ} (xs : List ℝ) (h : xs.length = d) : Fin d → ℝ :=
  fun i => xs[i.val]'(by rw [h]; exact i.isLt)

theorem cachedRealVector_ofFn {d : ℕ} (f : Fin d → ℝ) :
    cachedRealVector (List.ofFn f) (List.length_ofFn) = f := by
  ext i
  simp [cachedRealVector]

variable {d m : ℕ}

def projectionWeightsProgram (theta v : Fin d → ℝ) : List ℝ × ℕ :=
  countedMap (fun i => (Real.exp (theta i + v i), 2)) (List.finRange d)

theorem projectionWeightsProgram_values (theta v : Fin d → ℝ) :
    (projectionWeightsProgram theta v).1 = List.ofFn (fun i => Real.exp (theta i + v i)) := by
  simp only [projectionWeightsProgram, countedMap_values, List.ofFn_eq_map]

theorem projectionWeightsProgram_length (theta v : Fin d → ℝ) :
    (projectionWeightsProgram theta v).1.length = d := by
  rw [projectionWeightsProgram_values, List.length_ofFn]

theorem projectionWeightsProgram_cost (theta v : Fin d → ℝ) :
    (projectionWeightsProgram theta v).2 = 2 * d := by
  simp [projectionWeightsProgram, countedMap_cost, List.map_const', Nat.mul_comm]

theorem projectionWeightsProgram_cached (theta v : Fin d → ℝ) :
    cachedRealVector (projectionWeightsProgram theta v).1 (projectionWeightsProgram_length theta v) =
      (fun i => Real.exp (theta i + v i)) := by
  ext i
  simp [cachedRealVector, projectionWeightsProgram_values]

def projectionGradientCellProgram (w : Fin d → ℝ) (m : ℕ) (Z : ℝ)
    (a b v : Fin d → ℝ) (i : Fin d) : ℝ × ℕ :=
  let mu := espMarginalProgram w m Z i
  if 0 < v i then (mu.1 - a i, mu.2 + 2)
  else if v i < 0 then (mu.1 - b i, mu.2 + 3)
  else (mu.1 - (a i + b i) / 2, mu.2 + 5)

theorem projectionGradientCellProgram_values (theta a b v : Fin d → ℝ)
    (hm : 1 ≤ m) (i : Fin d) :
    (projectionGradientCellProgram (fun j => Real.exp (theta j + v j)) m
      (partition (m := m) (theta + v)) a b v i).1 =
      projectionSubgradient (m := m) theta a b v i := by
  simp only [projectionGradientCellProgram, projectionSubgradient]
  have hmu := espMarginalProgram_correct (theta + v) hm i
  simp only [Pi.add_apply] at hmu
  split_ifs <;> simpa only [hmu]

theorem projectionGradientCellProgram_cost (w : Fin d → ℝ) (m : ℕ) (Z : ℝ)
    (a b v : Fin d → ℝ) (i : Fin d) :
    (projectionGradientCellProgram w m Z a b v i).2 ≤ 2 * m * d + 7 := by
  have h := espMarginalProgram_cost_le w m Z i
  dsimp only [projectionGradientCellProgram]
  split_ifs <;> dsimp only <;> omega

def projectionGradientProgram (theta a b v : Fin d → ℝ) (m : ℕ) : List ℝ × ℕ :=
  let weights := projectionWeightsProgram theta v
  let w := cachedRealVector weights.1 (projectionWeightsProgram_length theta v)
  let denominator := espPartitionProgram w m
  let cells := countedMap (projectionGradientCellProgram w m denominator.1 a b v) (List.finRange d)
  (cells.1, weights.2 + denominator.2 + cells.2)

theorem projectionGradientProgram_values (theta a b v : Fin d → ℝ) (hm : 1 ≤ m) :
    (projectionGradientProgram theta a b v m).1 =
      List.ofFn (projectionSubgradient (m := m) theta a b v) := by
  simp only [projectionGradientProgram, projectionWeightsProgram_cached,
    countedMap_values, List.ofFn_eq_map]
  have hZ := espPartitionProgram_correct (theta + v) m
  simp only [Pi.add_apply] at hZ
  rw [hZ]
  apply List.map_congr_left
  intro i _
  exact projectionGradientCellProgram_values theta a b v hm i

theorem projectionGradientProgram_length (theta a b v : Fin d → ℝ) (hm : 1 ≤ m) :
    (projectionGradientProgram theta a b v m).1.length = d := by
  rw [projectionGradientProgram_values theta a b v hm, List.length_ofFn]

theorem projectionGradientProgram_cost (theta a b v : Fin d → ℝ) (m : ℕ) :
    (projectionGradientProgram theta a b v m).2 ≤ 2 * d + 2 * m * d + (2 * m * d + 7) * d := by
  dsimp only [projectionGradientProgram]
  rw [projectionWeightsProgram_cost, espPartitionProgram_cost]
  let w := cachedRealVector (projectionWeightsProgram theta v).1 (projectionWeightsProgram_length theta v)
  have h := countedMap_cost_le
    (projectionGradientCellProgram w m (espPartitionProgram w m).1 a b v)
    (List.finRange d) (2 * m * d + 7)
    (fun i _ => projectionGradientCellProgram_cost w m (espPartitionProgram w m).1 a b v i)
  simpa only [List.length_finRange] using Nat.add_le_add_left h (2 * d + 2 * m * d)

def projectionPenaltyCellProgram (a b v : ℝ) : ℝ × ℕ :=
  (-a * max v 0 + b * max (-v) 0, 7)

def projectionPenaltyProgram (a b v : Fin d → ℝ) : ℝ × ℕ :=
  let cells := countedMap (fun i => projectionPenaltyCellProgram (a i) (b i) (v i)) (List.finRange d)
  let total := countedSum cells.1
  (total.1, cells.2 + total.2)

theorem projectionPenaltyProgram_values (a b v : Fin d → ℝ) :
    (projectionPenaltyProgram a b v).1 = projectionPenalty a b v := by
  simp only [projectionPenaltyProgram, countedSum_values, countedMap_values,
    projectionPenaltyCellProgram, ← List.ofFn_eq_map, List.sum_ofFn, projectionPenalty]

theorem projectionPenaltyProgram_cost (a b v : Fin d → ℝ) :
    (projectionPenaltyProgram a b v).2 = 8 * d := by
  simp [projectionPenaltyProgram, countedMap_cost, countedSum_cost,
    countedMap_values, projectionPenaltyCellProgram, List.map_const', Nat.mul_comm]
  omega

def projectionValueProgram (theta a b v : Fin d → ℝ) (m : ℕ) : ℝ × ℕ :=
  let weights := projectionWeightsProgram theta v
  let w := cachedRealVector weights.1 (projectionWeightsProgram_length theta v)
  let denominator := espPartitionProgram w m
  let penalty := projectionPenaltyProgram a b v
  (Real.log denominator.1 + penalty.1, weights.2 + denominator.2 + penalty.2 + 2)

theorem projectionValueProgram_values (theta a b v : Fin d → ℝ) (m : ℕ) :
    (projectionValueProgram theta a b v m).1 = projectionDual (m := m) theta a b v := by
  simp only [projectionValueProgram, projectionWeightsProgram_cached,
    projectionPenaltyProgram_values, projectionDual, logPartition]
  have hZ := espPartitionProgram_correct (theta + v) m
  simp only [Pi.add_apply] at hZ
  rw [hZ]

theorem projectionValueProgram_cost (theta a b v : Fin d → ℝ) (m : ℕ) :
    (projectionValueProgram theta a b v m).2 = 2 * m * d + 10 * d + 2 := by
  simp only [projectionValueProgram, projectionWeightsProgram_cost,
    espPartitionProgram_cost, projectionPenaltyProgram_cost]
  omega

end MsetsPaper.Upper
