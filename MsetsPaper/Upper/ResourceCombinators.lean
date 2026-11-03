import MsetsPaper.Upper.StorageModel

noncomputable section

namespace MsetsPaper.Upper

def resourceMap {α β : Type*} (f : α → ResourceRun β) : List α → ResourceRun (List β)
  | [] => ⟨[], 1, 1⟩
  | x :: xs =>
    let cell := f x
    let tail := resourceMap f xs
    ⟨cell.value :: tail.value, cell.work + tail.work + 2,
      cell.allocated + tail.allocated + 3⟩

theorem resourceMap_values {α β : Type*} (f : α → ResourceRun β) (xs : List α) :
    (resourceMap f xs).value = xs.map (fun x => (f x).value) := by
  induction xs with
  | nil => rfl
  | cons x xs ih => simp only [resourceMap, ih, List.map_cons]

theorem resourceMap_bounds {α β : Type*} (f : α → ResourceRun β) (xs : List α) (W A : ℕ)
    (hbound : ∀ x ∈ xs, (f x).work ≤ W ∧ (f x).allocated ≤ A) :
    (resourceMap f xs).work ≤ 1 + xs.length * (W + 2) ∧
      (resourceMap f xs).allocated ≤ 1 + xs.length * (A + 3) := by
  induction xs with
  | nil => simp [resourceMap]
  | cons x xs ih =>
    have hx := hbound x (by simp)
    have ht := ih (fun y hy => hbound y (by simp [hy]))
    simp only [resourceMap, List.length_cons]
    constructor <;> nlinarith [hx.1, hx.2, ht.1, ht.2]

def resourceSum : List ℝ → ResourceRun ℝ
  | [] => ⟨0, 1, 1⟩
  | x :: xs =>
    let tail := resourceSum xs
    ⟨x + tail.value, tail.work + 3, tail.allocated + 2⟩

theorem resourceSum_values (xs : List ℝ) : (resourceSum xs).value = xs.sum := by
  induction xs <;> simp_all [resourceSum]

theorem resourceSum_counts (xs : List ℝ) :
    (resourceSum xs).work = 3 * xs.length + 1 ∧
      (resourceSum xs).allocated = 2 * xs.length + 1 := by
  induction xs with
  | nil => simp [resourceSum]
  | cons x xs ih => simp only [resourceSum, List.length_cons]; constructor <;> omega

def resourceLength {α : Type*} : List α → ResourceRun ℕ
  | [] => ⟨0, 1, 1⟩
  | _ :: xs =>
    let tail := resourceLength xs
    ⟨tail.value + 1, tail.work + 2, tail.allocated + 2⟩

theorem resourceLength_values {α : Type*} (xs : List α) :
    (resourceLength xs).value = xs.length := by
  induction xs <;> simp_all [resourceLength]

theorem resourceLength_counts {α : Type*} (xs : List α) :
    (resourceLength xs).work = 2 * xs.length + 1 ∧
      (resourceLength xs).allocated = 2 * xs.length + 1 := by
  induction xs with
  | nil => simp [resourceLength]
  | cons x xs ih => simp only [resourceLength, List.length_cons]; constructor <;> omega

theorem resourceListRead_work_le_index {α : Type*} (fallback : α) (xs : List α) (k : ℕ) :
    (resourceListRead fallback xs k).work ≤ k + 2 := by
  simp only [resourceListRead, resourceListGet_work, countedListGet_cost]
  omega

theorem resourceListRead_allocated_le_index {α : Type*} (fallback : α) (xs : List α) (k : ℕ) :
    (resourceListRead fallback xs k).allocated ≤ 2 * k + 3 := by
  have h := resourceListGet_allocated_le xs k
  rw [resourceListGet_work, countedListGet_cost] at h
  simp only [resourceListRead]
  omega

theorem resourceListRead_property {α : Type*} (fallback : α) (xs : List α) (k : ℕ)
    (P : α → Prop) (hfallback : P fallback) (hxs : ∀ x ∈ xs, P x) :
    P (resourceListRead fallback xs k).value := by
  rw [resourceListRead_values]
  induction xs generalizing k with
  | nil => simpa using hfallback
  | cons x xs ih =>
    cases k with
    | zero => simpa using hxs x (by simp)
    | succ k =>
      simpa only [List.getElem?_cons_succ] using ih k (fun y hy => hxs y (by simp [hy]))

def resourceFilter {α : Type*} (predicate : α → ResourceRun Bool) :
    List α → ResourceRun (List α)
  | [] => ⟨[], 1, 1⟩
  | x :: xs =>
    let test := predicate x
    let tail := resourceFilter predicate xs
    if test.value then
      ⟨x :: tail.value, test.work + tail.work + 3, test.allocated + tail.allocated + 3⟩
    else ⟨tail.value, test.work + tail.work + 2, test.allocated + tail.allocated + 2⟩

theorem resourceFilter_values {α : Type*} (predicate : α → ResourceRun Bool) (xs : List α) :
    (resourceFilter predicate xs).value = xs.filter (fun x => (predicate x).value) := by
  induction xs with
  | nil => rfl
  | cons x xs ih =>
    simp only [resourceFilter, List.filter_cons]
    split_ifs <;> simp only [ih]

theorem resourceFilter_bounds {α : Type*} (predicate : α → ResourceRun Bool)
    (xs : List α) (W A : ℕ)
    (hbound : ∀ x ∈ xs, (predicate x).work ≤ W ∧ (predicate x).allocated ≤ A) :
    (resourceFilter predicate xs).work ≤ 1 + xs.length * (W + 3) ∧
      (resourceFilter predicate xs).allocated ≤ 1 + xs.length * (A + 3) := by
  induction xs with
  | nil => simp [resourceFilter]
  | cons x xs ih =>
    have hx := hbound x (by simp)
    have ht := ih (fun y hy => hbound y (by simp [hy]))
    simp only [resourceFilter, List.length_cons]
    split_ifs <;> constructor <;> nlinarith [hx.1, hx.2, ht.1, ht.2]

end MsetsPaper.Upper
