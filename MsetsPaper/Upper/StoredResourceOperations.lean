import MsetsPaper.Upper.SPDSchurResources
import MsetsPaper.Upper.ResourceCombinators

noncomputable section
open scoped BigOperators
open Matrix

namespace MsetsPaper.Upper.ResourcePrograms

open SchurSolver (StoredVector StoredMatrix storedVector storedMatrix
  resourceVectorRead resourceVectorRead_values resourceVectorRead_bounds
  resourceMatrixRead resourceMatrixRead_values resourceMatrixRead_bounds
  resourceTabulate resourceTabulate_values resourceTabulate_bounds)

variable {d : ℕ}

def vectorProgram (f : Fin d → ResourceRun ℝ) : ResourceRun (StoredVector d) :=
  let cells := resourceTabulate d f
  ⟨⟨cells.value, by simp [cells, resourceTabulate_values]⟩,
    cells.work + 1, cells.allocated + 1⟩

theorem vectorProgram_values (f : Fin d → ResourceRun ℝ) :
    storedVector (vectorProgram f).value = fun i => (f i).value := by
  ext i
  simp [vectorProgram, storedVector, cachedRealVector, resourceTabulate_values]

theorem vectorProgram_bounds (f : Fin d → ResourceRun ℝ) (W A : ℕ)
    (h : ∀ i, (f i).work ≤ W ∧ (f i).allocated ≤ A) :
    (vectorProgram f).work ≤ (W + 2) * d + 2 ∧
      (vectorProgram f).allocated ≤ (A + 4) * d + 2 := by
  have ht := resourceTabulate_bounds d f W A h
  dsimp only [vectorProgram]
  constructor <;> omega

def matrixProgram (f : Fin d → Fin d → ResourceRun ℝ) : ResourceRun (StoredMatrix d) :=
  let rows := resourceTabulate d (fun i => resourceTabulate d (f i))
  ⟨⟨rows.value, by
      constructor
      · simp [rows, resourceTabulate_values]
      · intro row hrow
        simp only [rows, resourceTabulate_values, List.mem_ofFn] at hrow
        obtain ⟨i, rfl⟩ := hrow
        simp⟩, rows.work + 1, rows.allocated + 1⟩

theorem matrixProgram_values (f : Fin d → Fin d → ResourceRun ℝ) :
    storedMatrix (matrixProgram f).value = fun i j => (f i j).value := by
  ext i j
  simp [matrixProgram, storedMatrix, cachedRealMatrix, resourceTabulate_values]

theorem matrixProgram_bounds (f : Fin d → Fin d → ResourceRun ℝ) (W A : ℕ)
    (h : ∀ i j, (f i j).work ≤ W ∧ (f i j).allocated ≤ A) :
    (matrixProgram f).work ≤ ((W + 2) * d + 3) * d + 2 ∧
      (matrixProgram f).allocated ≤ ((A + 4) * d + 5) * d + 2 := by
  have ht := resourceTabulate_bounds d (fun i => resourceTabulate d (f i))
    ((W + 2) * d + 1) ((A + 4) * d + 1)
    (fun i => resourceTabulate_bounds d (f i) W A (h i))
  dsimp only [matrixProgram]
  constructor <;> nlinarith [ht.1, ht.2]

def sumProgram (f : Fin d → ResourceRun ℝ) : ResourceRun ℝ :=
  let cells := resourceTabulate d f
  let total := MsetsPaper.Upper.resourceSum cells.value
  ⟨total.value, cells.work + total.work + 1, cells.allocated + total.allocated + 2⟩

theorem sumProgram_values (f : Fin d → ResourceRun ℝ) :
    (sumProgram f).value = ∑ i, (f i).value := by
  simp only [sumProgram, MsetsPaper.Upper.resourceSum_values, resourceTabulate_values,
    List.sum_ofFn]

theorem sumProgram_bounds (f : Fin d → ResourceRun ℝ) (W A : ℕ)
    (h : ∀ i, (f i).work ≤ W ∧ (f i).allocated ≤ A) :
    (sumProgram f).work ≤ (W + 5) * d + 3 ∧
      (sumProgram f).allocated ≤ (A + 6) * d + 4 := by
  have ht := resourceTabulate_bounds d f W A h
  have hs := MsetsPaper.Upper.resourceSum_counts (resourceTabulate d f).value
  have hlen : (resourceTabulate d f).value.length = d := by
    simp only [resourceTabulate_values, List.length_ofFn]
  rw [hlen] at hs
  dsimp only [sumProgram]
  constructor <;> nlinarith [ht.1, ht.2, hs.1, hs.2]

def vectorProductCell (x y : StoredVector d) (i : Fin d) : ResourceRun ℝ :=
  let a := resourceVectorRead x i
  let b := resourceVectorRead y i
  ⟨a.value * b.value, a.work + b.work + 1, a.allocated + b.allocated + 1⟩

theorem vectorProductCell_values (x y : StoredVector d) (i : Fin d) :
    (vectorProductCell x y i).value = storedVector x i * storedVector y i := by
  simp only [vectorProductCell, resourceVectorRead_values]

theorem vectorProductCell_bounds (x y : StoredVector d) (i : Fin d) :
    (vectorProductCell x y i).work ≤ 2 * d + 5 ∧
      (vectorProductCell x y i).allocated ≤ 4 * d + 7 := by
  have hx := resourceVectorRead_bounds x i
  have hy := resourceVectorRead_bounds y i
  dsimp only [vectorProductCell]
  constructor <;> omega

def dotProgram (x y : StoredVector d) : ResourceRun ℝ := sumProgram (vectorProductCell x y)

theorem dotProgram_values (x y : StoredVector d) :
    (dotProgram x y).value = storedVector x ⬝ᵥ storedVector y := by
  simp only [dotProgram, sumProgram_values, vectorProductCell_values, dotProduct]

theorem dotProgram_bounds (x y : StoredVector d) :
    (dotProgram x y).work ≤ (2 * d + 10) * d + 3 ∧
      (dotProgram x y).allocated ≤ (4 * d + 13) * d + 4 := by
  exact sumProgram_bounds _ (2 * d + 5) (4 * d + 7) (vectorProductCell_bounds x y)

def matVecProductCell (Q : StoredMatrix d) (g : StoredVector d) (i j : Fin d) : ResourceRun ℝ :=
  let a := resourceMatrixRead Q i j
  let b := resourceVectorRead g j
  ⟨a.value * b.value, a.work + b.work + 1, a.allocated + b.allocated + 1⟩

theorem matVecProductCell_values (Q : StoredMatrix d) (g : StoredVector d) (i j : Fin d) :
    (matVecProductCell Q g i j).value = storedMatrix Q i j * storedVector g j := by
  simp only [matVecProductCell, resourceMatrixRead_values, resourceVectorRead_values]

theorem matVecProductCell_bounds (Q : StoredMatrix d) (g : StoredVector d) (i j : Fin d) :
    (matVecProductCell Q g i j).work ≤ 3 * d + 7 ∧
      (matVecProductCell Q g i j).allocated ≤ 6 * d + 10 := by
  have hx := resourceMatrixRead_bounds Q i j
  have hy := resourceVectorRead_bounds g j
  dsimp only [matVecProductCell]
  constructor <;> omega

def matVecProgram (Q : StoredMatrix d) (g : StoredVector d) : ResourceRun (StoredVector d) :=
  vectorProgram (fun i => sumProgram (matVecProductCell Q g i))

theorem matVecProgram_values (Q : StoredMatrix d) (g : StoredVector d) :
    storedVector (matVecProgram Q g).value = storedMatrix Q *ᵥ storedVector g := by
  ext i
  simp only [matVecProgram, vectorProgram_values, sumProgram_values,
    matVecProductCell_values, Matrix.mulVec, dotProduct]

theorem matVecProgram_bounds (Q : StoredMatrix d) (g : StoredVector d) :
    (matVecProgram Q g).work ≤ ((3 * d + 12) * d + 5) * d + 2 ∧
      (matVecProgram Q g).allocated ≤ ((6 * d + 16) * d + 8) * d + 2 := by
  exact vectorProgram_bounds _ ((3 * d + 12) * d + 3) ((6 * d + 16) * d + 4)
    (fun i => sumProgram_bounds _ (3 * d + 7) (6 * d + 10) (matVecProductCell_bounds Q g i))

end MsetsPaper.Upper.ResourcePrograms
