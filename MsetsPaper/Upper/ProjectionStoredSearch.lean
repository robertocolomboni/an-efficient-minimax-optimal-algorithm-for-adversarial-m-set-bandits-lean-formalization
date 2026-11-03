import MsetsPaper.Upper.ProjectionStoredOracle
import MsetsPaper.Upper.EllipsoidStoredProgram
import MsetsPaper.Upper.ResourceArenaProgram

/-! The retained search state contains only three finite scalar lists (one
nested for the matrix) and a word counter. Every transition deep-copies all
returned lists into the retained arena, including zero-cut/unchanged-best
branches. The old arena and all temporary DP/update data can then be released.
No closure or old-list pointer survives in the stated word-RAM semantics.
-/

noncomputable section
-- Large nested stored-program terms require a deeper reducibility stack.
set_option maxRecDepth 4096
open scoped BigOperators

namespace MsetsPaper.Upper.ResourcePrograms

open SchurSolver (StoredVector StoredMatrix storedVector storedMatrix
  resourceVectorRead resourceVectorRead_values resourceVectorRead_bounds
  resourceMatrixRead resourceMatrixRead_values resourceMatrixRead_bounds)

variable {d m : ℕ}

structure StoredSearch (d : ℕ) where
  ellipsoid : StoredEllipsoid d
  best : StoredVector d
  queries : ℕ

def StoredSearch.decode (s : StoredSearch d) : ProjectionSearchState d :=
  ⟨s.ellipsoid.decode, storedVector s.best, s.queries⟩

/-- Scalars and list-link words are counted even when aliasing could save
space. Eight additional record/control slots make this a safe overcount. -/
def StoredSearch.footprint (s : StoredSearch d) : ℕ :=
  (2 * s.ellipsoid.center.val.length + 1) +
    ((s.ellipsoid.shape.val.map (fun row => 2 * row.length + 1)).sum +
      2 * s.ellipsoid.shape.val.length + 1) +
    (2 * s.best.val.length + 1) + 8

theorem StoredSearch.footprint_eq (s : StoredSearch d) :
    s.footprint = 2 * d ^ 2 + 7 * d + 11 := by
  have hmap : s.ellipsoid.shape.val.map (fun row => 2 * row.length + 1) =
      s.ellipsoid.shape.val.map (fun _ => 2 * d + 1) := by
    apply List.map_congr_left
    intro row hrow
    rw [s.ellipsoid.shape.property.2 row hrow]
  simp only [StoredSearch.footprint, s.ellipsoid.center.property,
    s.ellipsoid.shape.property.1, s.best.property, hmap, List.map_const', List.sum_replicate]
  simp only [s.ellipsoid.shape.property.1, smul_eq_mul]
  ring

/-- Explicit full copy, rather than retaining a pointer into a discarded
temporary arena. Array/list contents are scalar words, never computations. -/
def copySearchResource (s : StoredSearch d) : ResourceRun (StoredSearch d) :=
  let center := vectorProgram (resourceVectorRead s.ellipsoid.center)
  let shape := matrixProgram (resourceMatrixRead s.ellipsoid.shape)
  let best := vectorProgram (resourceVectorRead s.best)
  ⟨⟨⟨center.value, shape.value⟩, best.value, s.queries⟩,
    center.work + shape.work + best.work + 5,
    center.allocated + shape.allocated + best.allocated + 8⟩

theorem copySearchResource_values (s : StoredSearch d) :
    (copySearchResource s).value.decode = s.decode := by
  simp only [copySearchResource, StoredSearch.decode, StoredEllipsoid.decode,
    vectorProgram_values, matrixProgram_values, resourceVectorRead_values, resourceMatrixRead_values]

theorem copySearchResource_bounds (s : StoredSearch d) :
    (copySearchResource s).work ≤ 100 * (d + 1) ^ 3 ∧
      (copySearchResource s).allocated ≤ 100 * (d + 1) ^ 3 := by
  have hc := vectorProgram_bounds (resourceVectorRead s.ellipsoid.center)
    (d + 2) (2 * d + 3) (resourceVectorRead_bounds s.ellipsoid.center)
  have hb := vectorProgram_bounds (resourceVectorRead s.best)
    (d + 2) (2 * d + 3) (resourceVectorRead_bounds s.best)
  have hQ := matrixProgram_bounds (resourceMatrixRead s.ellipsoid.shape)
    (2 * d + 4) (4 * d + 6) (resourceMatrixRead_bounds s.ellipsoid.shape)
  dsimp only [copySearchResource]
  constructor <;> nlinarith [hc.1, hc.2, hb.1, hb.2, hQ.1, hQ.2]

def searchStepResource (theta a b : StoredVector d) (m : ℕ) (R : ℝ) (s : StoredSearch d) :
    ResourceRun (StoredSearch d) :=
  let cut := cutResource theta a b s.ellipsoid.center m R
  let next := ellipsoidStepResource s.ellipsoid cut.value
  let best := retainResource theta a b s.ellipsoid.center s.best m R
  let copied := copySearchResource ⟨next.value, best.value, s.queries + 1⟩
  ⟨copied.value, cut.work + next.work + best.work + copied.work + 5,
    cut.allocated + next.allocated + best.allocated + copied.allocated + 8⟩

theorem searchStepResource_values (theta a b : StoredVector d) (hm : 1 ≤ m)
    (R : ℝ) (s : StoredSearch d) :
    (searchStepResource theta a b m R s).value.decode =
      projectionSearchStep (m := m) (storedVector theta) (storedVector a)
        (storedVector b) R s.decode := by
  dsimp only [searchStepResource]
  rw [copySearchResource_values]
  change (⟨(ellipsoidStepResource s.ellipsoid
    (cutResource theta a b s.ellipsoid.center m R).value).value.decode,
    storedVector (retainResource theta a b s.ellipsoid.center s.best m R).value,
    s.queries + 1⟩ : ProjectionSearchState d) = _
  rw [ellipsoidStepResource_values, cutResource_values theta a b s.ellipsoid.center hm R,
    retainResource_values]
  rfl

def searchStepBudget (d m : ℕ) : ℕ :=
  cutBudget d m + 204 * (d + 1) ^ 3 + 700 * (d + m + 1) ^ 2 + 38

theorem searchStepResource_bounds (theta a b : StoredVector d) (m : ℕ)
    (R : ℝ) (s : StoredSearch d) :
    (searchStepResource theta a b m R s).work ≤ searchStepBudget d m ∧
      (searchStepResource theta a b m R s).allocated ≤ searchStepBudget d m := by
  let cut := cutResource theta a b s.ellipsoid.center m R
  let next := ellipsoidStepResource s.ellipsoid cut.value
  let best := retainResource theta a b s.ellipsoid.center s.best m R
  have hg := cutResource_bounds theta a b s.ellipsoid.center m R
  have hn := ellipsoidStepResource_bounds s.ellipsoid cut.value
  have hb := retainResource_bounds theta a b s.ellipsoid.center s.best m R
  have hc := copySearchResource_bounds (⟨next.value, best.value, s.queries + 1⟩ : StoredSearch d)
  dsimp only [searchStepResource, searchStepBudget]
  dsimp only [cut, next, best] at hn hc
  constructor <;> omega

def initialSearchResource (d : ℕ) (R : ℝ) : ResourceRun (StoredSearch d) :=
  let zero := vectorProgram (fun _ : Fin d => (⟨0, 1, 1⟩ : ResourceRun ℝ))
  let radiusSq := R * R
  let shape := matrixProgram (fun i j : Fin d =>
    (⟨if i = j then radiusSq else 0, 1, 1⟩ : ResourceRun ℝ))
  ⟨⟨⟨zero.value, shape.value⟩, zero.value, 0⟩,
    zero.work + shape.work + 5, zero.allocated + shape.allocated + 8⟩

theorem initialSearchResource_values (theta a b : StoredVector d) (R : ℝ) (m : ℕ) :
    (initialSearchResource d R).value.decode =
      projectionSearchRun (m := m) (storedVector theta) (storedVector a) (storedVector b) R 0 := by
  simp only [initialSearchResource, StoredSearch.decode, StoredEllipsoid.decode,
    vectorProgram_values, matrixProgram_values, projectionSearchRun, ellipsoidInitial]
  congr 2
  ext i j
  simp [Matrix.smul_apply, Matrix.one_apply, pow_two]

theorem initialSearchResource_bounds (d : ℕ) (R : ℝ) :
    (initialSearchResource d R).work ≤ 30 * (d + 1) ^ 2 ∧
      (initialSearchResource d R).allocated ≤ 30 * (d + 1) ^ 2 := by
  have hz := vectorProgram_bounds (fun _ : Fin d => (⟨0, 1, 1⟩ : ResourceRun ℝ))
    1 1 (fun _ => ⟨le_rfl, le_rfl⟩)
  have hQ := matrixProgram_bounds (fun i j : Fin d =>
    (⟨if i = j then R * R else 0, 1, 1⟩ : ResourceRun ℝ)) 1 1 (fun _ _ => ⟨le_rfl, le_rfl⟩)
  dsimp only [initialSearchResource]
  constructor <;> nlinarith [hz.1, hz.2, hQ.1, hQ.2]

def searchArena (theta a b : StoredVector d) (m : ℕ) (R : ℝ) (N : ℕ) :
    ResourceRun (StoredSearch d) × ℕ :=
  let initial := initialSearchResource d R
  arenaProgram (searchStepResource theta a b m R) StoredSearch.footprint N initial.value
    initial.work initial.allocated initial.allocated

theorem searchArena_values (theta a b : StoredVector d) (hm : 1 ≤ m)
    (R : ℝ) (N : ℕ) :
    (searchArena theta a b m R N).1.value.decode =
      projectionSearchRun (m := m) (storedVector theta) (storedVector a) (storedVector b) R N := by
  have hiter (n : ℕ) :
      ((fun s => (searchStepResource theta a b m R s).value)^[n]
        (initialSearchResource d R).value).decode =
      projectionSearchRun (m := m) (storedVector theta) (storedVector a) (storedVector b) R n := by
    induction n with
    | zero => exact initialSearchResource_values theta a b R m
    | succ n ih =>
      rw [Function.iterate_succ_apply', searchStepResource_values theta a b hm R, ih]
      rfl
  dsimp only [searchArena]
  rw [arenaProgram_values]
  exact hiter N

theorem searchArena_work (theta a b : StoredVector d) (m : ℕ) (R : ℝ) (N : ℕ) :
    (searchArena theta a b m R N).1.work ≤
      30 * (d + 1) ^ 2 + N * (searchStepBudget d m + 3) + 1 := by
  have h := arenaProgram_work (searchStepResource theta a b m R) StoredSearch.footprint
    (searchStepBudget d m) (fun s => (searchStepResource_bounds theta a b m R s).1)
    N (initialSearchResource d R).value (initialSearchResource d R).work
      (initialSearchResource d R).allocated (initialSearchResource d R).allocated
  have hi := initialSearchResource_bounds d R
  exact h.trans (by omega)

def searchArenaSpace (d m : ℕ) : ℕ := 2 * d ^ 2 + 7 * d + 19 + searchStepBudget d m

/-- Peak live storage is independent of the iteration budget N. The three
read-only input vectors are charged separately by the caller. -/
theorem searchArena_peak (theta a b : StoredVector d) (m : ℕ) (R : ℝ) (N : ℕ) :
    (searchArena theta a b m R N).2 ≤ searchArenaSpace d m := by
  have hi := (initialSearchResource_bounds d R).2
  have hbase : 30 * (d + 1) ^ 2 ≤ searchStepBudget d m := by
    unfold searchStepBudget
    nlinarith [Nat.zero_le (cutBudget d m), Nat.zero_le (d ^ 2), Nat.zero_le (d ^ 3),
      Nat.zero_le ((d + m + 1) ^ 2)]
  have h := arenaProgram_peak (searchStepResource theta a b m R) StoredSearch.footprint
    (2 * d ^ 2 + 7 * d + 11) (searchStepBudget d m)
    (fun s => (StoredSearch.footprint_eq s).le)
    (fun s => (searchStepResource_bounds theta a b m R s).2)
    N (initialSearchResource d R).value (initialSearchResource d R).work
      (initialSearchResource d R).allocated (initialSearchResource d R).allocated (by omega)
  change (searchArena theta a b m R N).2 ≤
    2 * d ^ 2 + 7 * d + 11 + searchStepBudget d m + 8 at h
  unfold searchArenaSpace
  omega

end MsetsPaper.Upper.ResourcePrograms
