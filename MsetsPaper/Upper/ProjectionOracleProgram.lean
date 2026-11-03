import MsetsPaper.Upper.ProjectionOracleDP
import MsetsPaper.Upper.ProjectionSearch

/-! A counted, finite-list implementation of both branches of the actual
projection oracle. It uses the ESP dynamic program, never action enumeration. -/

noncomputable section
open scoped BigOperators

namespace MsetsPaper.Upper

variable {d m : ℕ}

def projectionL1Program (v : Fin d → ℝ) : ℝ × ℕ :=
  let cells := countedMap (fun i => (|v i|, 1)) (List.finRange d)
  let total := countedSum cells.1
  (total.1, cells.2 + total.2)

theorem projectionL1Program_values (v : Fin d → ℝ) :
    (projectionL1Program v).1 = coordinateL1 v := by
  simp only [projectionL1Program, countedSum_values, countedMap_values,
    ← List.ofFn_eq_map, List.sum_ofFn, coordinateL1]

theorem projectionL1Program_cost (v : Fin d → ℝ) : (projectionL1Program v).2 = 2 * d := by
  simp [projectionL1Program, countedMap_cost, countedSum_cost,
    countedMap_values, List.map_const', two_mul]

def projectionSignProgram (v : Fin d → ℝ) : List ℝ × ℕ :=
  countedMap (fun i => (if 0 ≤ v i then (1 : ℝ) else -1, 1)) (List.finRange d)

theorem projectionSignProgram_values (v : Fin d → ℝ) :
    (projectionSignProgram v).1 = List.ofFn (l1Separator v) := by
  simp only [projectionSignProgram, countedMap_values, List.ofFn_eq_map, l1Separator]
  rfl

theorem projectionSignProgram_cost (v : Fin d → ℝ) : (projectionSignProgram v).2 = d := by
  simp [projectionSignProgram, countedMap_cost, List.map_const']

def projectionCutProgram (theta a b v : Fin d → ℝ) (R : ℝ) (m : ℕ) : List ℝ × ℕ :=
  let norm := projectionL1Program v
  if norm.1 ≤ R then
    let grad := projectionGradientProgram theta a b v m
    (grad.1, norm.2 + 1 + grad.2)
  else
    let sign := projectionSignProgram v
    (sign.1, norm.2 + 1 + sign.2)

theorem projectionCutProgram_values (theta a b v : Fin d → ℝ) (R : ℝ) (hm : 1 ≤ m) :
    (projectionCutProgram theta a b v R m).1 =
      List.ofFn (projectionEllipsoidOracle (m := m) theta a b R v) := by
  dsimp only [projectionCutProgram]
  rw [projectionL1Program_values]
  by_cases h : coordinateL1 v ≤ R
  · simp only [h, ↓reduceIte, projectionEllipsoidOracle,
      projectionGradientProgram_values theta a b v hm]
  · simp only [h, ↓reduceIte, projectionEllipsoidOracle, projectionSignProgram_values]

theorem projectionCutProgram_length (theta a b v : Fin d → ℝ) (R : ℝ) (hm : 1 ≤ m) :
    (projectionCutProgram theta a b v R m).1.length = d := by
  rw [projectionCutProgram_values theta a b v R hm, List.length_ofFn]

theorem projectionCutProgram_cost (theta a b v : Fin d → ℝ) (R : ℝ) (m : ℕ) :
    (projectionCutProgram theta a b v R m).2 ≤
      4 * d + 2 * m * d + (2 * m * d + 7) * d + 1 := by
  dsimp only [projectionCutProgram]
  split_ifs
  · have h := projectionGradientProgram_cost theta a b v m
    dsimp only
    rw [projectionL1Program_cost]
    omega
  · dsimp only
    rw [projectionL1Program_cost, projectionSignProgram_cost]
    omega

def projectionCutVector (theta a b v : Fin d → ℝ) (R : ℝ) (hm : 1 ≤ m) : Fin d → ℝ :=
  cachedRealVector (projectionCutProgram theta a b v R m).1
    (projectionCutProgram_length theta a b v R hm)

theorem projectionCutVector_eq (theta a b v : Fin d → ℝ) (R : ℝ) (hm : 1 ≤ m) :
    projectionCutVector theta a b v R hm = projectionEllipsoidOracle (m := m) theta a b R v := by
  ext i
  simp [projectionCutVector, cachedRealVector, projectionCutProgram_values theta a b v R hm]

def projectionRetainBestProgram (theta a b candidate best : Fin d → ℝ) (R : ℝ) (m : ℕ) :
    (Fin d → ℝ) × ℕ :=
  let norm := projectionL1Program candidate
  if norm.1 ≤ R then
    let candidateValue := projectionValueProgram theta a b candidate m
    let bestValue := projectionValueProgram theta a b best m
    if candidateValue.1 ≤ bestValue.1 then
      (candidate, norm.2 + candidateValue.2 + bestValue.2 + 2)
    else (best, norm.2 + candidateValue.2 + bestValue.2 + 2)
  else (best, norm.2 + 1)

theorem projectionRetainBestProgram_values (theta a b candidate best : Fin d → ℝ)
    (R : ℝ) (m : ℕ) :
    (projectionRetainBestProgram theta a b candidate best R m).1 =
      projectionRetainBest (m := m) theta a b R candidate best := by
  simp only [projectionRetainBestProgram, projectionL1Program_values,
    projectionValueProgram_values, projectionRetainBest]
  split_ifs <;> simp_all

theorem projectionRetainBestProgram_cost (theta a b candidate best : Fin d → ℝ)
    (R : ℝ) (m : ℕ) :
    (projectionRetainBestProgram theta a b candidate best R m).2 ≤
      4 * m * d + 22 * d + 6 := by
  dsimp only [projectionRetainBestProgram]
  split_ifs <;> dsimp only <;>
    simp only [projectionL1Program_cost, projectionValueProgram_cost] <;> nlinarith

end MsetsPaper.Upper
