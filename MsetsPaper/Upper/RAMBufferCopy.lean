import MsetsPaper.Upper.RAMMemory
import MsetsPaper.Upper.ResourceCombinators

/-! # Linear copying into fresh owned RAM buffers

The polymorphic entries below are word payloads (real scalars or references).
The routine first counts its input list, initializes a fresh buffer, and fills
it by explicit in-place stores. No amortized constant-time dynamic-array push
or unit-cost whole-list conversion is assumed. Each new buffer has one owner;
the old snapshot is not retained by the fill loop.
-/

namespace MsetsPaper.Upper.RAMPrograms
noncomputable section

def wordStore {α : Type*} (a : Array α) (i : ℕ) (x : α) : ResourceRun (Array α) :=
  ⟨a.set! i x, 1, 0⟩

def wordBuffer {α : Type*} (n : ℕ) (x : α) : ResourceRun (Array α) :=
  ⟨Array.replicate n x, n + 1, n + 1⟩

def bufferFill {α : Type*} (a : Array α) (cursor : ℕ) : List α → ResourceRun (Array α)
  | [] => ⟨a, 1, 1⟩
  | x :: tail =>
    let written := wordStore a cursor x
    let next := bufferFill written.value (cursor + 1) tail
    ⟨next.value, written.work + next.work + 3, written.allocated + next.allocated + 2⟩

theorem bufferFill_counts {α : Type*} (xs : List α) (a : Array α) (cursor : ℕ) :
    (bufferFill a cursor xs).work = 4 * xs.length + 1 ∧
      (bufferFill a cursor xs).allocated = 2 * xs.length + 1 := by
  induction xs generalizing a cursor with
  | nil => simp [bufferFill]
  | cons x xs ih =>
    have h := ih (a.set! cursor x) (cursor + 1)
    simp only [bufferFill, wordStore, List.length_cons]
    constructor <;> omega

theorem bufferFill_prefix {α : Type*} (fallback : α) (xs : List α)
    (a : Array α) (pref : List α)
    (ha : a.toList = pref ++ List.replicate xs.length fallback) :
    (bufferFill a pref.length xs).value.toList = pref ++ xs := by
  induction xs generalizing a pref with
  | nil => simpa [bufferFill] using ha
  | cons x xs ih =>
    have ha' : (a.set! pref.length x).toList =
        (pref ++ [x]) ++ List.replicate xs.length fallback := by
      rw [Array.toList_set!, ha]
      simp [List.set_append_right, List.replicate_succ, List.append_assoc]
    have h := ih (a.set! pref.length x) (pref ++ [x]) ha'
    simpa [bufferFill, wordStore, List.append_assoc] using h

def copyListToArray {α : Type*} (fallback : α) (xs : List α) : ResourceRun (Array α) :=
  let len := resourceLength xs
  let buffer := wordBuffer len.value fallback
  let filled := bufferFill buffer.value 0 xs
  ⟨filled.value, len.work + buffer.work + filled.work + 2,
    len.allocated + buffer.allocated + filled.allocated + 2⟩

theorem copyListToArray_toList {α : Type*} (fallback : α) (xs : List α) :
    (copyListToArray fallback xs).value.toList = xs := by
  simp only [copyListToArray, resourceLength_values, wordBuffer]
  simpa using bufferFill_prefix fallback xs (Array.replicate xs.length fallback) [] (by simp)

theorem copyListToArray_values {α : Type*} (fallback : α) (xs : List α) :
    (copyListToArray fallback xs).value = xs.toArray := by
  apply Array.toList_inj.mp
  rw [copyListToArray_toList, List.toList_toArray]

theorem copyListToArray_size {α : Type*} (fallback : α) (xs : List α) :
    (copyListToArray fallback xs).value.size = xs.length := by
  rw [copyListToArray_values]
  simp

theorem copyListToArray_counts {α : Type*} (fallback : α) (xs : List α) :
    (copyListToArray fallback xs).work = 7 * xs.length + 5 ∧
      (copyListToArray fallback xs).allocated = 5 * xs.length + 5 := by
  have hl := resourceLength_counts xs
  have hf := bufferFill_counts xs (Array.replicate xs.length fallback) 0
  simp only [copyListToArray, resourceLength_values, wordBuffer]
  constructor <;> omega

abbrev realListToArray (xs : List ℝ) : ResourceRun (Array ℝ) := copyListToArray 0 xs
abbrev rowListToArray (rows : List (Array ℝ)) : ResourceRun (Array (Array ℝ)) :=
  copyListToArray #[] rows

end
end MsetsPaper.Upper.RAMPrograms
