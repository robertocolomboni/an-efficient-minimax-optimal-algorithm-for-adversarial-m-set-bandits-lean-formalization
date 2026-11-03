import MsetsPaper.Upper.StorageModel

/-! # Explicit random-access memory primitives for the real-RAM layer

An array is the logical snapshot of an owned indexed RAM buffer. A load costs
one operation and returns one scalar/reference word; a store costs one and
overwrites one cell, allocating no new RAM words. `Array.set!` is the pure
snapshot semantics of that store, NOT a cost claim about Lean's persistent
arrays or its compiler. Callers must retain/count simultaneously live buffers.
Bulk initialization is charged linearly, including the array header.
-/

namespace MsetsPaper.Upper.RAMPrograms
noncomputable section

def realLoad (a : Array ℝ) (i : ℕ) : ResourceRun ℝ :=
  ⟨a[i]?.getD 0, 1, 1⟩

def rowLoad (a : Array (Array ℝ)) (i : ℕ) : ResourceRun (Array ℝ) :=
  ⟨a[i]?.getD #[], 1, 1⟩

def realStore (a : Array ℝ) (i : ℕ) (x : ℝ) : ResourceRun (Array ℝ) :=
  ⟨a.set! i x, 1, 0⟩

def rowStore (a : Array (Array ℝ)) (i : ℕ) (x : Array ℝ) : ResourceRun (Array (Array ℝ)) :=
  ⟨a.set! i x, 1, 0⟩

def realBuffer (n : ℕ) (x : ℝ) : ResourceRun (Array ℝ) :=
  ⟨Array.replicate n x, n + 1, n + 1⟩

/-- The entries are references to the supplied row. This does not allocate
n independent copies of that row; callers creating mutable rows must do so. -/
def rowBuffer (n : ℕ) (x : Array ℝ := #[]) : ResourceRun (Array (Array ℝ)) :=
  ⟨Array.replicate n x, n + 1, n + 1⟩

@[simp] theorem realLoad_values (a : Array ℝ) (i : ℕ) :
    (realLoad a i).value = a[i]?.getD 0 := rfl
@[simp] theorem rowLoad_values (a : Array (Array ℝ)) (i : ℕ) :
    (rowLoad a i).value = a[i]?.getD #[] := rfl
@[simp] theorem realStore_values (a : Array ℝ) (i : ℕ) (x : ℝ) :
    (realStore a i x).value = a.set! i x := rfl
@[simp] theorem rowStore_values (a : Array (Array ℝ)) (i : ℕ) (x : Array ℝ) :
    (rowStore a i x).value = a.set! i x := rfl
@[simp] theorem realBuffer_values (n : ℕ) (x : ℝ) :
    (realBuffer n x).value = Array.replicate n x := rfl
@[simp] theorem rowBuffer_values (n : ℕ) (x : Array ℝ) :
    (rowBuffer n x).value = Array.replicate n x := rfl

theorem realLoad_counts (a : Array ℝ) (i : ℕ) :
    (realLoad a i).work = 1 ∧ (realLoad a i).allocated = 1 := ⟨rfl, rfl⟩
theorem rowLoad_counts (a : Array (Array ℝ)) (i : ℕ) :
    (rowLoad a i).work = 1 ∧ (rowLoad a i).allocated = 1 := ⟨rfl, rfl⟩
theorem realStore_counts (a : Array ℝ) (i : ℕ) (x : ℝ) :
    (realStore a i x).work = 1 ∧ (realStore a i x).allocated = 0 := ⟨rfl, rfl⟩
theorem rowStore_counts (a : Array (Array ℝ)) (i : ℕ) (x : Array ℝ) :
    (rowStore a i x).work = 1 ∧ (rowStore a i x).allocated = 0 := ⟨rfl, rfl⟩
theorem realBuffer_counts (n : ℕ) (x : ℝ) :
    (realBuffer n x).work = n + 1 ∧ (realBuffer n x).allocated = n + 1 := ⟨rfl, rfl⟩
theorem rowBuffer_counts (n : ℕ) (x : Array ℝ) :
    (rowBuffer n x).work = n + 1 ∧ (rowBuffer n x).allocated = n + 1 := ⟨rfl, rfl⟩

end
end MsetsPaper.Upper.RAMPrograms
