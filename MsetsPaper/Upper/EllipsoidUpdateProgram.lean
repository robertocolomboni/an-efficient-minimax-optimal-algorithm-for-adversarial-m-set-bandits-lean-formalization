import MsetsPaper.Upper.ProjectionOracleDP

/-! Counted dense-list arithmetic for the actual center/shape update.
Access and allocation costs are not included in the real-operation counter.
The matrix-vector product is materialized once and reused in every cell. -/

noncomputable section
open scoped BigOperators
open Matrix

namespace MsetsPaper.Upper

variable {d : ℕ}

def countedDot (x y : Fin d → ℝ) : ℝ × ℕ :=
  let cells := countedMap (fun i => (x i * y i, 1)) (List.finRange d)
  let total := countedSum cells.1
  (total.1, cells.2 + total.2)

theorem countedDot_values (x y : Fin d → ℝ) : (countedDot x y).1 = x ⬝ᵥ y := by
  simp only [countedDot, countedSum_values, countedMap_values,
    ← List.ofFn_eq_map, List.sum_ofFn, dotProduct]

theorem countedDot_cost (x y : Fin d → ℝ) : (countedDot x y).2 = 2 * d := by
  simp [countedDot, countedMap_cost, countedSum_cost, countedMap_values, List.map_const', two_mul]

def countedMatVec (Q : Matrix (Fin d) (Fin d) ℝ) (g : Fin d → ℝ) : List ℝ × ℕ :=
  countedMap (fun i => countedDot (Q i) g) (List.finRange d)

theorem countedMatVec_values (Q : Matrix (Fin d) (Fin d) ℝ) (g : Fin d → ℝ) :
    (countedMatVec Q g).1 = List.ofFn (Q *ᵥ g) := by
  simp only [countedMatVec, countedMap_values, countedDot_values, List.ofFn_eq_map]
  rfl

theorem countedMatVec_length (Q : Matrix (Fin d) (Fin d) ℝ) (g : Fin d → ℝ) :
    (countedMatVec Q g).1.length = d := by rw [countedMatVec_values, List.length_ofFn]

theorem countedMatVec_cached (Q : Matrix (Fin d) (Fin d) ℝ) (g : Fin d → ℝ) :
    cachedRealVector (countedMatVec Q g).1 (countedMatVec_length Q g) = Q *ᵥ g := by
  ext i
  simp [cachedRealVector, countedMatVec_values]

theorem countedMatVec_cost (Q : Matrix (Fin d) (Fin d) ℝ) (g : Fin d → ℝ) :
    (countedMatVec Q g).2 = 2 * d * d := by
  simp [countedMatVec, countedMap_cost, countedDot_cost, List.map_const', Nat.mul_comm]

def countedMatrix (f : Fin d → Fin d → ℝ × ℕ) : List (List ℝ) × ℕ :=
  countedMap (fun i => countedMap (f i) (List.finRange d)) (List.finRange d)

theorem countedMatrix_values (f : Fin d → Fin d → ℝ × ℕ) :
    (countedMatrix f).1 = List.ofFn (fun i => List.ofFn (fun j => (f i j).1)) := by
  simp only [countedMatrix, countedMap_values, List.ofFn_eq_map]

theorem countedMatrix_length (f : Fin d → Fin d → ℝ × ℕ) :
    (countedMatrix f).1.length = d := by rw [countedMatrix_values, List.length_ofFn]

theorem countedMatrix_row_length (f : Fin d → Fin d → ℝ × ℕ)
    (row : List ℝ) (hrow : row ∈ (countedMatrix f).1) : row.length = d := by
  rw [countedMatrix_values, List.mem_ofFn] at hrow
  obtain ⟨i, rfl⟩ := hrow
  exact List.length_ofFn

def cachedRealMatrix (rows : List (List ℝ)) (houter : rows.length = d)
    (hinner : ∀ row ∈ rows, row.length = d) : Matrix (Fin d) (Fin d) ℝ :=
  fun i j =>
    let row := rows[i.val]'(by rw [houter]; exact i.isLt)
    row[j.val]'(by rw [hinner row (List.getElem_mem _)]; exact j.isLt)

theorem countedMatrix_cached (f : Fin d → Fin d → ℝ × ℕ) :
    cachedRealMatrix (countedMatrix f).1 (countedMatrix_length f)
      (countedMatrix_row_length f) = fun i j => (f i j).1 := by
  ext i j
  simp [cachedRealMatrix, countedMatrix_values]

theorem countedMatrix_cost (f : Fin d → Fin d → ℝ × ℕ) (C : ℕ)
    (hcost : ∀ i j, (f i j).2 = C) : (countedMatrix f).2 = C * d * d := by
  simp only [countedMatrix, countedMap_cost, hcost]
  simp [List.map_const', Nat.mul_comm, Nat.mul_assoc]

def ellipsoidCenterCells (c u : Fin d → ℝ) (k : ℝ) : List ℝ × ℕ :=
  countedMap (fun i => (c i - k * u i, 2)) (List.finRange d)

theorem ellipsoidCenterCells_values (c u : Fin d → ℝ) (k : ℝ) :
    (ellipsoidCenterCells c u k).1 = List.ofFn (fun i => c i - k * u i) := by
  simp only [ellipsoidCenterCells, countedMap_values, List.ofFn_eq_map]

theorem ellipsoidCenterCells_length (c u : Fin d → ℝ) (k : ℝ) :
    (ellipsoidCenterCells c u k).1.length = d := by
  rw [ellipsoidCenterCells_values, List.length_ofFn]

theorem ellipsoidCenterCells_cached (c u : Fin d → ℝ) (k : ℝ) :
    cachedRealVector (ellipsoidCenterCells c u k).1 (ellipsoidCenterCells_length c u k) =
      c - k • u := by
  ext i
  simp [cachedRealVector, ellipsoidCenterCells_values]

theorem ellipsoidCenterCells_cost (c u : Fin d → ℝ) (k : ℝ) :
    (ellipsoidCenterCells c u k).2 = 2 * d := by
  simp [ellipsoidCenterCells, countedMap_cost, List.map_const', Nat.mul_comm]

def ellipsoidUpdateProgram (c : Fin d → ℝ) (Q : Matrix (Fin d) (Fin d) ℝ)
    (g : Fin d → ℝ) : EllipsoidState d × ℕ :=
  let product := countedMatVec Q g
  let u := cachedRealVector product.1 (countedMatVec_length Q g)
  let quad := countedDot g u
  let nplus := (d : ℝ) + 1
  let nsq := (d : ℝ) * d
  let a := nsq / (nsq - 1)
  let b := (2 / nplus) / quad.1
  let k := 1 / (nplus * Real.sqrt quad.1)
  let center := ellipsoidCenterCells c u k
  let shapeCell := fun i j => (a * (Q i j - b * (u i * u j)), 4)
  let shape := countedMatrix shapeCell
  (⟨cachedRealVector center.1 (ellipsoidCenterCells_length c u k),
      cachedRealMatrix shape.1 (countedMatrix_length shapeCell) (countedMatrix_row_length shapeCell)⟩,
    product.2 + quad.2 + 9 + center.2 + shape.2)

theorem ellipsoidUpdateProgram_values (c : Fin d → ℝ) (Q : Matrix (Fin d) (Fin d) ℝ)
    (g : Fin d → ℝ) :
    (ellipsoidUpdateProgram c Q g).1 = ⟨ellipsoidNextCenter c g Q, ellipsoidNextShape Q g⟩ := by
  simp only [ellipsoidUpdateProgram, countedMatVec_cached, countedDot_values,
    ellipsoidCenterCells_cached, countedMatrix_cached]
  congr 1
  ext i j
  simp only [ellipsoidNextShape, ellipsoidRankOneDowndate, Matrix.smul_apply,
    Matrix.sub_apply, Matrix.vecMulVec_apply, smul_eq_mul, ellipsoidQuadratic, pow_two]

theorem ellipsoidUpdateProgram_cost (c : Fin d → ℝ) (Q : Matrix (Fin d) (Fin d) ℝ)
    (g : Fin d → ℝ) :
    (ellipsoidUpdateProgram c Q g).2 = 6 * d * d + 4 * d + 9 := by
  simp only [ellipsoidUpdateProgram, countedMatVec_cost, countedDot_cost, ellipsoidCenterCells_cost]
  rw [countedMatrix_cost _ 4 (fun _ _ => rfl)]
  ring

end MsetsPaper.Upper
