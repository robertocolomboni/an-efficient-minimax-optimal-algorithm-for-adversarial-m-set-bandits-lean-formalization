import MsetsPaper.Upper.SPDSchurProgram
import MsetsPaper.Upper.StorageModel
import MsetsPaper.Upper.SPDSchurRAMCache

/-! # Explicit list access and allocation for scalar Schur elimination

This resource refinement counts list traversal, output cells, scalar
intermediates and recursive control frames. Before each quadratic Schur
update it copies the matrix sequentially to indexed RAM rows. Both copying
and indexed reads are charged. All temporary allocations are conservatively
retained until the solver returns, so total allocation bounds space.
-/

namespace MsetsPaper.Upper.SchurSolver

open Matrix
open scoped BigOperators

noncomputable section

abbrev StoredVector (n : ℕ) := {xs : List ℝ // xs.length = n}
abbrev StoredMatrix (n : ℕ) :=
  {rows : List (List ℝ) // rows.length = n ∧ ∀ row ∈ rows, row.length = n}

def storedVector {n : ℕ} (x : StoredVector n) : Fin n → ℝ := cachedRealVector x.1 x.2
def storedMatrix {n : ℕ} (A : StoredMatrix n) : Matrix (Fin n) (Fin n) ℝ :=
  cachedRealMatrix A.1 A.2.1 A.2.2

def resourceVectorRead {n : ℕ} (x : StoredVector n) (i : Fin n) : ResourceRun ℝ :=
  resourceListRead 0 x.1 i.val

theorem resourceVectorRead_values {n : ℕ} (x : StoredVector n) (i : Fin n) :
    (resourceVectorRead x i).value = storedVector x i := by
  have hi : i.val < x.1.length := by rw [x.2]; exact i.isLt
  simp [resourceVectorRead, resourceListRead_values, List.getElem?_eq_getElem hi,
    storedVector, cachedRealVector]

theorem resourceVectorRead_bounds {n : ℕ} (x : StoredVector n) (i : Fin n) :
    (resourceVectorRead x i).work ≤ n + 2 ∧
      (resourceVectorRead x i).allocated ≤ 2 * n + 3 := by
  simpa only [resourceVectorRead, x.2] using resourceListRead_bounds 0 x.1 i.val

def resourceMatrixRead {n : ℕ} (A : StoredMatrix n) (i j : Fin n) : ResourceRun ℝ :=
  let row := resourceListRead [] A.1 i.val
  let cell := resourceListRead 0 row.value j.val
  ⟨cell.value, row.work + cell.work, row.allocated + cell.allocated⟩

theorem resourceMatrixRead_values {n : ℕ} (A : StoredMatrix n) (i j : Fin n) :
    (resourceMatrixRead A i j).value = storedMatrix A i j := by
  have hi : i.val < A.1.length := by rw [A.2.1]; exact i.isLt
  have hrow : (resourceListRead [] A.1 i.val).value = A.1[i.val] := by
    simp [resourceListRead_values, List.getElem?_eq_getElem hi]
  have hj : j.val < A.1[i.val].length := by
    rw [A.2.2 _ (List.getElem_mem hi)]; exact j.isLt
  simp [resourceMatrixRead, hrow, resourceListRead_values, List.getElem?_eq_getElem hj,
    storedMatrix, cachedRealMatrix]

theorem resourceMatrixRead_bounds {n : ℕ} (A : StoredMatrix n) (i j : Fin n) :
    (resourceMatrixRead A i j).work ≤ 2 * n + 4 ∧
      (resourceMatrixRead A i j).allocated ≤ 4 * n + 6 := by
  have hi : i.val < A.1.length := by rw [A.2.1]; exact i.isLt
  have hrow : (resourceListRead [] A.1 i.val).value = A.1[i.val] := by
    simp [resourceListRead_values, List.getElem?_eq_getElem hi]
  have hlen : (resourceListRead [] A.1 i.val).value.length = n := by
    rw [hrow]; exact A.2.2 _ (List.getElem_mem hi)
  have h₁ := resourceListRead_bounds ([] : List ℝ) A.1 i.val
  have h₂ := resourceListRead_bounds 0 (resourceListRead [] A.1 i.val).value j.val
  rw [A.2.1] at h₁
  rw [hlen] at h₂
  dsimp only [resourceMatrixRead]
  constructor <;> omega

/-- Explicit tabulation; no uncounted index-list construction is needed. -/
def resourceTabulate {α : Type*} : (n : ℕ) → (Fin n → ResourceRun α) → ResourceRun (List α)
  | 0, _ => ⟨[], 1, 1⟩
  | n + 1, f =>
    let head := f 0
    let tail := resourceTabulate n (fun i ↦ f i.succ)
    ⟨head.value :: tail.value, head.work + tail.work + 2,
      head.allocated + tail.allocated + 4⟩

theorem resourceTabulate_values {α : Type*} :
    ∀ (n : ℕ) (f : Fin n → ResourceRun α),
      (resourceTabulate n f).value = List.ofFn (fun i ↦ (f i).value) := by
  intro n
  induction n with
  | zero => intro f; simp [resourceTabulate]
  | succ n ih => intro f; simp [resourceTabulate, List.ofFn_succ, ih]

theorem resourceTabulate_bounds {α : Type*} :
    ∀ (n : ℕ) (f : Fin n → ResourceRun α) (W A : ℕ),
      (∀ i, (f i).work ≤ W ∧ (f i).allocated ≤ A) →
      (resourceTabulate n f).work ≤ (W + 2) * n + 1 ∧
        (resourceTabulate n f).allocated ≤ (A + 4) * n + 1 := by
  intro n
  induction n with
  | zero => intro f W A h; simp [resourceTabulate]
  | succ n ih =>
    intro f W A h
    have hhead := h 0
    have htail := ih (fun i ↦ f i.succ) W A (fun i ↦ h i.succ)
    dsimp only [resourceTabulate]
    constructor <;> nlinarith

def resourceSum : List ℝ → ResourceRun ℝ
  | [] => ⟨0, 1, 1⟩
  | x :: xs =>
    let tail := resourceSum xs
    ⟨x + tail.value, tail.work + 2, tail.allocated + 4⟩

theorem resourceSum_values (xs : List ℝ) : (resourceSum xs).value = xs.sum := by
  induction xs <;> simp_all [resourceSum]

theorem resourceSum_counts (xs : List ℝ) :
    (resourceSum xs).work = 2 * xs.length + 1 ∧
      (resourceSum xs).allocated = 4 * xs.length + 1 := by
  induction xs with
  | nil => simp [resourceSum]
  | cons x xs ih => simp only [resourceSum, List.length_cons]; constructor <;> omega

def resourceSchurCell {n : ℕ} (A : StoredMatrix (n + 1)) (p : ℝ) (i j : Fin n) :
    ResourceRun ℝ :=
  let a := resourceMatrixRead A i.succ j.succ
  let c := resourceMatrixRead A i.succ 0
  let r := resourceMatrixRead A 0 j.succ
  ⟨a.value - c.value * r.value / p,
    a.work + c.work + r.work + 3, a.allocated + c.allocated + r.allocated + 3⟩

theorem resourceSchurCell_values {n : ℕ} (A : StoredMatrix (n + 1)) (p : ℝ) (i j : Fin n) :
    (resourceSchurCell A p i j).value =
      storedMatrix A i.succ j.succ - storedMatrix A i.succ 0 * storedMatrix A 0 j.succ / p := by
  simp only [resourceSchurCell, resourceMatrixRead_values]

theorem resourceSchurCell_bounds {n : ℕ} (A : StoredMatrix (n + 1)) (p : ℝ) (i j : Fin n) :
    (resourceSchurCell A p i j).work ≤ 6 * n + 21 ∧
      (resourceSchurCell A p i j).allocated ≤ 12 * n + 33 := by
  have h₁ := resourceMatrixRead_bounds A i.succ j.succ
  have h₂ := resourceMatrixRead_bounds A i.succ 0
  have h₃ := resourceMatrixRead_bounds A 0 j.succ
  dsimp only [resourceSchurCell]
  constructor <;> omega

def cachedSchurCell {n : ℕ} (A : Array (Array ℝ)) (p : ℝ) (i j : Fin n) :
    ResourceRun ℝ :=
  let a := RAMPrograms.matrixReadRAM A i.succ.val j.succ.val
  let c := RAMPrograms.matrixReadRAM A i.succ.val 0
  let r := RAMPrograms.matrixReadRAM A 0 j.succ.val
  ⟨a.value - c.value * r.value / p,
    a.work + c.work + r.work + 3, a.allocated + c.allocated + r.allocated + 3⟩

theorem cachedSchurCell_values {n : ℕ} (A : StoredMatrix (n + 1)) (p : ℝ)
    (i j : Fin n) :
    (cachedSchurCell (RAMPrograms.packRowsRAM A.1).value p i j).value =
      storedMatrix A i.succ j.succ - storedMatrix A i.succ 0 * storedMatrix A 0 j.succ / p := by
  have hread (i j : Fin (n + 1)) :
      (RAMPrograms.matrixReadRAM (RAMPrograms.packRowsRAM A.1).value i.val j.val).value =
        storedMatrix A i j := by
    rw [RAMPrograms.packRowsRAM_read]
    have hi : i.val < A.1.length := by rw [A.2.1]; exact i.isLt
    have hj : j.val < A.1[i.val].length := by
      rw [A.2.2 _ (List.getElem_mem hi)]; exact j.isLt
    simp [List.getElem?_eq_getElem hi, List.getElem?_eq_getElem hj,
      storedMatrix, cachedRealMatrix]
  have hc := hread i.succ 0
  have hr := hread 0 j.succ
  simp only [Fin.val_zero] at hc hr
  simp only [cachedSchurCell, hread i.succ j.succ, hc, hr]

theorem cachedSchurCell_counts {n : ℕ} (A : Array (Array ℝ)) (p : ℝ) (i j : Fin n) :
    (cachedSchurCell A p i j).work = 9 ∧
      (cachedSchurCell A p i j).allocated = 9 := ⟨rfl, rfl⟩

def resourceSchurMatrix {n : ℕ} (A : StoredMatrix (n + 1)) (p : ℝ) :
    ResourceRun (StoredMatrix n) :=
  let cached := RAMPrograms.packRowsRAM A.1
  let rows := resourceTabulate n (fun i ↦ resourceTabulate n (cachedSchurCell cached.value p i))
  ⟨⟨rows.value, by
      constructor
      · simp [rows, resourceTabulate_values]
      · intro row hrow
        simp only [rows, resourceTabulate_values, List.mem_ofFn] at hrow
        obtain ⟨i, rfl⟩ := hrow
        simp⟩,
    cached.work + rows.work + 1, cached.allocated + rows.allocated + 1⟩

theorem resourceSchurMatrix_exact {n : ℕ} (A : StoredMatrix (n + 1)) :
    storedMatrix (resourceSchurMatrix A (storedMatrix A 0 0)).value = schur (storedMatrix A) := by
  ext i j
  simp [storedMatrix, cachedRealMatrix, resourceSchurMatrix, resourceTabulate_values,
    cachedSchurCell_values, schur]

/-- The complete Schur update, including its sequential RAM copy and all
accesses, is quadratic. The solver consequently has cubic total work. -/
theorem resourceSchurMatrix_quadratic {n : ℕ} (A : StoredMatrix (n + 1)) (p : ℝ) :
    (resourceSchurMatrix A p).work ≤ 50 * (n + 1) ^ 2 ∧
      (resourceSchurMatrix A p).allocated ≤ 50 * (n + 1) ^ 2 := by
  have hcache := RAMPrograms.packRowsRAM_bounds A.1 (n + 1) A.2.1 A.2.2
  have hrows := resourceTabulate_bounds n
    (fun i ↦ resourceTabulate n (cachedSchurCell (RAMPrograms.packRowsRAM A.1).value p i))
    (11 * n + 1) (13 * n + 1) (by
      intro i
      exact resourceTabulate_bounds n
        (cachedSchurCell (RAMPrograms.packRowsRAM A.1).value p i) 9 9
        (fun j => ⟨(cachedSchurCell_counts _ _ i j).1.le,
          (cachedSchurCell_counts _ _ i j).2.le⟩))
  dsimp only [resourceSchurMatrix]
  constructor <;> nlinarith [hcache.1, hcache.2, hrows.1, hrows.2]

theorem resourceSchurMatrix_bounds {n : ℕ} (A : StoredMatrix (n + 1)) (p : ℝ) :
    (resourceSchurMatrix A p).work ≤ 50 * (n + 1) ^ 3 ∧
      (resourceSchurMatrix A p).allocated ≤ 50 * (n + 1) ^ 3 := by
  have h := resourceSchurMatrix_quadratic A p
  have hpow : (n + 1) ^ 2 ≤ (n + 1) ^ 3 := by
    calc
      _ = (n + 1) ^ 2 * 1 := by omega
      _ ≤ (n + 1) ^ 2 * (n + 1) := Nat.mul_le_mul_left _ (by omega)
      _ = _ := by ring
  constructor <;> nlinarith [h.1, h.2]

def resourceRhsCell {n : ℕ} (A : StoredMatrix (n + 1)) (b : StoredVector (n + 1))
    (p beta : ℝ) (i : Fin n) : ResourceRun ℝ :=
  let a := resourceMatrixRead A i.succ 0
  let v := resourceVectorRead b i.succ
  ⟨v.value - a.value * beta / p, a.work + v.work + 3, a.allocated + v.allocated + 3⟩

theorem resourceRhsCell_values {n : ℕ} (A : StoredMatrix (n + 1)) (b : StoredVector (n + 1))
    (p beta : ℝ) (i : Fin n) :
    (resourceRhsCell A b p beta i).value =
      storedVector b i.succ - storedMatrix A i.succ 0 * beta / p := by
  simp only [resourceRhsCell, resourceMatrixRead_values, resourceVectorRead_values]

theorem resourceRhsCell_bounds {n : ℕ} (A : StoredMatrix (n + 1)) (b : StoredVector (n + 1))
    (p beta : ℝ) (i : Fin n) :
    (resourceRhsCell A b p beta i).work ≤ 3 * n + 12 ∧
      (resourceRhsCell A b p beta i).allocated ≤ 6 * n + 18 := by
  have h₁ := resourceMatrixRead_bounds A i.succ 0
  have h₂ := resourceVectorRead_bounds b i.succ
  dsimp only [resourceRhsCell]
  constructor <;> omega

def resourceReducedRhs {n : ℕ} (A : StoredMatrix (n + 1)) (b : StoredVector (n + 1))
    (p beta : ℝ) : ResourceRun (StoredVector n) :=
  let row := resourceTabulate n (resourceRhsCell A b p beta)
  ⟨⟨row.value, by simp [row, resourceTabulate_values]⟩, row.work + 1, row.allocated + 1⟩

theorem resourceReducedRhs_exact {n : ℕ} (A : StoredMatrix (n + 1)) (b : StoredVector (n + 1)) :
    storedVector (resourceReducedRhs A b (storedMatrix A 0 0) (storedVector b 0)).value =
      reducedRhs (storedMatrix A) (storedVector b) := by
  ext i
  simp [storedVector, cachedRealVector, resourceReducedRhs, resourceTabulate_values,
    resourceRhsCell_values, reducedRhs]

theorem resourceReducedRhs_bounds {n : ℕ} (A : StoredMatrix (n + 1)) (b : StoredVector (n + 1))
    (p beta : ℝ) :
    (resourceReducedRhs A b p beta).work ≤ 40 * (n + 1) ^ 2 ∧
      (resourceReducedRhs A b p beta).allocated ≤ 40 * (n + 1) ^ 2 := by
  have hrow := resourceTabulate_bounds n (resourceRhsCell A b p beta)
    (3 * n + 12) (6 * n + 18) (resourceRhsCell_bounds A b p beta)
  dsimp only [resourceReducedRhs]
  constructor <;> nlinarith

def resourceDotCell {n : ℕ} (A : StoredMatrix (n + 1)) (x : StoredVector n)
    (i : Fin n) : ResourceRun ℝ :=
  let a := resourceMatrixRead A 0 i.succ
  let v := resourceVectorRead x i
  ⟨a.value * v.value, a.work + v.work + 1, a.allocated + v.allocated + 1⟩

theorem resourceDotCell_values {n : ℕ} (A : StoredMatrix (n + 1)) (x : StoredVector n)
    (i : Fin n) :
    (resourceDotCell A x i).value = storedMatrix A 0 i.succ * storedVector x i := by
  simp only [resourceDotCell, resourceMatrixRead_values, resourceVectorRead_values]

theorem resourceDotCell_bounds {n : ℕ} (A : StoredMatrix (n + 1)) (x : StoredVector n)
    (i : Fin n) :
    (resourceDotCell A x i).work ≤ 3 * n + 9 ∧
      (resourceDotCell A x i).allocated ≤ 6 * n + 14 := by
  have h₁ := resourceMatrixRead_bounds A 0 i.succ
  have h₂ := resourceVectorRead_bounds x i
  dsimp only [resourceDotCell]
  constructor <;> omega

def resourceHeadDot {n : ℕ} (A : StoredMatrix (n + 1)) (x : StoredVector n) : ResourceRun ℝ :=
  let cells := resourceTabulate n (resourceDotCell A x)
  let total := resourceSum cells.value
  ⟨total.value, cells.work + total.work + 1, cells.allocated + total.allocated + 1⟩

theorem resourceHeadDot_values {n : ℕ} (A : StoredMatrix (n + 1)) (x : StoredVector n) :
    (resourceHeadDot A x).value = ∑ i, storedMatrix A 0 i.succ * storedVector x i := by
  simp only [resourceHeadDot, resourceSum_values, resourceTabulate_values,
    resourceDotCell_values, List.sum_ofFn]

theorem resourceHeadDot_bounds {n : ℕ} (A : StoredMatrix (n + 1)) (x : StoredVector n) :
    (resourceHeadDot A x).work ≤ 40 * (n + 1) ^ 2 ∧
      (resourceHeadDot A x).allocated ≤ 40 * (n + 1) ^ 2 := by
  have hc := resourceTabulate_bounds n (resourceDotCell A x) (3 * n + 9) (6 * n + 14)
    (resourceDotCell_bounds A x)
  have hs := resourceSum_counts (resourceTabulate n (resourceDotCell A x)).value
  have hlen : (resourceTabulate n (resourceDotCell A x)).value.length = n := by
    rw [resourceTabulate_values, List.length_ofFn]
  rw [hlen] at hs
  dsimp only [resourceHeadDot]
  constructor <;> nlinarith

/-- A resource-counted solver with a RAM cache for each quadratic Schur
update. The remaining list traversals are at most quadratic per level.
Pivot and head right-hand side are read once per level. -/
def resourceSolve : (n : ℕ) → StoredMatrix n → StoredVector n → ResourceRun (StoredVector n)
  | 0, _, _ => ⟨⟨[], rfl⟩, 1, 1⟩
  | n + 1, A, b =>
    let pivot := resourceMatrixRead A 0 0
    let beta := resourceVectorRead b 0
    let B := resourceSchurMatrix A pivot.value
    let c := resourceReducedRhs A b pivot.value beta.value
    let tail := resourceSolve n B.value c.value
    let dot := resourceHeadDot A tail.value
    ⟨⟨((beta.value - dot.value) / pivot.value) :: tail.value.1,
      by simp only [List.length_cons, tail.value.2]⟩,
      pivot.work + beta.work + B.work + c.work + tail.work + dot.work + 4,
      pivot.allocated + beta.allocated + B.allocated + c.allocated +
        tail.allocated + dot.allocated + 10⟩

theorem resourceSolve_values : ∀ (n : ℕ) (A : StoredMatrix n) (b : StoredVector n),
    storedVector (resourceSolve n A b).value = solveSpec n (storedMatrix A) (storedVector b) := by
  intro n
  induction n with
  | zero => intro A b; ext i; exact Fin.elim0 i
  | succ n ih =>
    intro A b
    have ht := ih
      (resourceSchurMatrix A (storedMatrix A 0 0)).value
      (resourceReducedRhs A b (storedMatrix A 0 0) (storedVector b 0)).value
    rw [resourceSchurMatrix_exact, resourceReducedRhs_exact] at ht
    simp only [resourceSolve, resourceMatrixRead_values, resourceVectorRead_values,
      resourceHeadDot_values]
    rw [solveSpec]
    ext i
    refine Fin.cases ?_ (fun j ↦ ?_) i
    · simp only [storedVector, cachedRealVector, Fin.val_zero, List.getElem_cons_zero,
        reconstruct, Fin.cons_zero]
      congr 1
      congr 1
      apply Finset.sum_congr rfl
      intro j _
      exact congrArg (fun z ↦ storedMatrix A 0 j.succ * z) (congrFun ht j)
    · have hj := congrFun ht j
      simpa [storedVector, cachedRealVector, reconstruct] using hj

/-- Conservative polynomial bounds including list traversal and all retained
temporary words. These are distinct from the tighter cubic real-op count. -/
theorem resourceSolve_bounds : ∀ (n : ℕ) (A : StoredMatrix n) (b : StoredVector n),
    (resourceSolve n A b).work ≤ 200 * (n + 1) ^ 4 ∧
      (resourceSolve n A b).allocated ≤ 200 * (n + 1) ^ 4 := by
  intro n
  induction n with
  | zero => intro A b; simp [resourceSolve]
  | succ n ih =>
    intro A b
    let p := resourceMatrixRead A 0 0
    let beta := resourceVectorRead b 0
    let B := resourceSchurMatrix A p.value
    let c := resourceReducedRhs A b p.value beta.value
    let tail := resourceSolve n B.value c.value
    have hp := resourceMatrixRead_bounds A 0 0
    have hb := resourceVectorRead_bounds b 0
    have hB := resourceSchurMatrix_bounds A p.value
    have hc := resourceReducedRhs_bounds A b p.value beta.value
    have ht := ih B.value c.value
    have hd := resourceHeadDot_bounds A tail.value
    change p.work + beta.work + B.work + c.work + tail.work +
        (resourceHeadDot A tail.value).work + 4 ≤ 200 * (n + 1 + 1) ^ 4 ∧
      p.allocated + beta.allocated + B.allocated + c.allocated + tail.allocated +
        (resourceHeadDot A tail.value).allocated + 10 ≤ 200 * (n + 1 + 1) ^ 4
    change p.work ≤ _ ∧ p.allocated ≤ _ at hp
    change beta.work ≤ _ ∧ beta.allocated ≤ _ at hb
    change B.work ≤ _ ∧ B.allocated ≤ _ at hB
    change c.work ≤ _ ∧ c.allocated ≤ _ at hc
    change tail.work ≤ _ ∧ tail.allocated ≤ _ at ht
    constructor <;> nlinarith

/-- Cubic total operational work for this same solver, including sequential
cache construction, list/vector access, control and allocation. -/
theorem resourceSolve_cubic : ∀ (n : ℕ) (A : StoredMatrix n) (b : StoredVector n),
    (resourceSolve n A b).work ≤ 200 * (n + 1) ^ 3 ∧
      (resourceSolve n A b).allocated ≤ 200 * (n + 1) ^ 3 := by
  intro n
  induction n with
  | zero => intro A b; simp [resourceSolve]
  | succ n ih =>
    intro A b
    let p := resourceMatrixRead A 0 0
    let beta := resourceVectorRead b 0
    let B := resourceSchurMatrix A p.value
    let c := resourceReducedRhs A b p.value beta.value
    let tail := resourceSolve n B.value c.value
    have hp := resourceMatrixRead_bounds A 0 0
    have hb := resourceVectorRead_bounds b 0
    have hB := resourceSchurMatrix_quadratic A p.value
    have hc := resourceReducedRhs_bounds A b p.value beta.value
    have ht := ih B.value c.value
    have hd := resourceHeadDot_bounds A tail.value
    change p.work + beta.work + B.work + c.work + tail.work +
        (resourceHeadDot A tail.value).work + 4 ≤ 200 * (n + 1 + 1) ^ 3 ∧
      p.allocated + beta.allocated + B.allocated + c.allocated + tail.allocated +
        (resourceHeadDot A tail.value).allocated + 10 ≤ 200 * (n + 1 + 1) ^ 3
    change p.work ≤ _ ∧ p.allocated ≤ _ at hp
    change beta.work ≤ _ ∧ beta.allocated ≤ _ at hb
    change B.work ≤ _ ∧ B.allocated ≤ _ at hB
    change c.work ≤ _ ∧ c.allocated ≤ _ at hc
    change tail.work ≤ _ ∧ tail.allocated ≤ _ at ht
    constructor <;> nlinarith

theorem resourceSolve_eq_inverse (n : ℕ) (A : StoredMatrix n) (b : StoredVector n)
    (hA : (storedMatrix A).PosDef) :
    storedVector (resourceSolve n A b).value = (storedMatrix A)⁻¹ *ᵥ storedVector b := by
  rw [resourceSolve_values]
  exact solveSpec_eq_inverse n _ hA _

theorem resourceSolve_refines (n : ℕ) (A : StoredMatrix n) (b : StoredVector n) :
    storedVector (resourceSolve n A b).value =
      (solveRun n (storedMatrix A) (storedVector b)).vector := by
  rw [resourceSolve_values, solveRun_vector]

/-- The same resource program with a separate real-arithmetic counter.
Per level, tabulation performs 3 operations at each of n² Schur cells,
3 at each of n RHS cells, 2n in the dot product, and 2 for the head solve.
Reads, control frames and allocation are charged in the first component. -/
def profiledSolve : (n : ℕ) → StoredMatrix n → StoredVector n →
    ResourceRun (StoredVector n) × ℕ
  | 0, _, _ => (⟨⟨[], rfl⟩, 1, 1⟩, 0)
  | n + 1, A, b =>
    let pivot := resourceMatrixRead A 0 0
    let beta := resourceVectorRead b 0
    let B := resourceSchurMatrix A pivot.value
    let c := resourceReducedRhs A b pivot.value beta.value
    let tail := profiledSolve n B.value c.value
    let dot := resourceHeadDot A tail.1.value
    (⟨⟨((beta.value - dot.value) / pivot.value) :: tail.1.value.1,
      by simp only [List.length_cons, tail.1.value.2]⟩,
      pivot.work + beta.work + B.work + c.work + tail.1.work + dot.work + 4,
      pivot.allocated + beta.allocated + B.allocated + c.allocated +
        tail.1.allocated + dot.allocated + 10⟩,
      tail.2 + 3 * n * n + 3 * n + 2 * n + 2)

theorem profiledSolve_resource : ∀ (n : ℕ) (A : StoredMatrix n) (b : StoredVector n),
    (profiledSolve n A b).1 = resourceSolve n A b := by
  intro n
  induction n with
  | zero => intro A b; rfl
  | succ n ih => intro A b; simp only [profiledSolve, resourceSolve, ih]

theorem profiledSolve_total_cubic (n : ℕ) (A : StoredMatrix n) (b : StoredVector n) :
    (profiledSolve n A b).1.work ≤ 200 * (n + 1) ^ 3 ∧
      (profiledSolve n A b).1.allocated ≤ 200 * (n + 1) ^ 3 := by
  rw [profiledSolve_resource]
  exact resourceSolve_cubic n A b

theorem profiledSolve_realOps : ∀ (n : ℕ) (A : StoredMatrix n) (b : StoredVector n),
    (profiledSolve n A b).2 = n ^ 2 * (n + 1) := by
  intro n
  induction n with
  | zero => intro A b; rfl
  | succ n ih => intro A b; simp only [profiledSolve, ih]; ring

/-- One concrete stored-data solver with exact output and all three resource
bounds. Allocated words include conservatively retained recursive temporaries;
the input matrix/vector occupy an additional polynomial number of words. -/
theorem profiledSolve_correct_and_bounded (n : ℕ) (A : StoredMatrix n) (b : StoredVector n)
    (hA : (storedMatrix A).PosDef) :
    storedVector (profiledSolve n A b).1.value = (storedMatrix A)⁻¹ *ᵥ storedVector b ∧
      (profiledSolve n A b).2 = n ^ 2 * (n + 1) ∧
      (profiledSolve n A b).1.work ≤ 200 * (n + 1) ^ 4 ∧
      (profiledSolve n A b).1.allocated ≤ 200 * (n + 1) ^ 4 := by
  rw [profiledSolve_resource, profiledSolve_realOps]
  exact ⟨resourceSolve_eq_inverse n A b hA, rfl, resourceSolve_bounds n A b⟩

end

end MsetsPaper.Upper.SchurSolver
