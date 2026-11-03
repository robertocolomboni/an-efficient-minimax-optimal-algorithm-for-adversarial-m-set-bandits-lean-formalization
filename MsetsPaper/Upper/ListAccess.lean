import MsetsPaper.Upper.EllipsoidUpdateProgram

/-! Operational list access rather than a unit-time indexing assumption.
One unit is charged for each examined list constructor. The lookup returns
the same optional value as List.getElem?; no finite-set enumeration is used. -/

noncomputable section

namespace MsetsPaper.Upper

def countedListGet {α : Type*} : List α → ℕ → Option α × ℕ
  | [], _ => (none, 1)
  | x :: _, 0 => (some x, 1)
  | _ :: xs, k + 1 =>
    let tail := countedListGet xs k
    (tail.1, tail.2 + 1)

theorem countedListGet_values {α : Type*} (xs : List α) (k : ℕ) :
    (countedListGet xs k).1 = xs[k]? := by
  induction xs generalizing k with
  | nil => simp [countedListGet]
  | cons x xs ih => cases k <;> simp [countedListGet, ih]

theorem countedListGet_cost {α : Type*} (xs : List α) (k : ℕ) :
    (countedListGet xs k).2 = min (k + 1) (xs.length + 1) := by
  induction xs generalizing k with
  | nil => simp [countedListGet]
  | cons x xs ih =>
    cases k with
    | zero => simp [countedListGet]
    | succ k => simp only [countedListGet, ih, List.length_cons]; omega

theorem countedListGet_cost_le_length {α : Type*} (xs : List α) (k : ℕ) :
    (countedListGet xs k).2 ≤ xs.length + 1 := by
  rw [countedListGet_cost]
  exact min_le_right _ _

theorem countedListGet_cost_valid {α : Type*} (xs : List α) (k : ℕ) (hk : k < xs.length) :
    (countedListGet xs k).2 = k + 1 := by
  rw [countedListGet_cost, min_eq_left (by omega)]

def countedListRead {α : Type*} (fallback : α) (xs : List α) (k : ℕ) : α × ℕ :=
  let lookup := countedListGet xs k
  (lookup.1.getD fallback, lookup.2 + 1)

theorem countedListRead_values {α : Type*} (fallback : α) (xs : List α) (k : ℕ) :
    (countedListRead fallback xs k).1 = xs[k]?.getD fallback := by
  simp only [countedListRead, countedListGet_values]

theorem countedListRead_cost_le {α : Type*} (fallback : α) (xs : List α) (k : ℕ) :
    (countedListRead fallback xs k).2 ≤ xs.length + 2 := by
  dsimp only [countedListRead]
  have := countedListGet_cost_le_length xs k
  omega

theorem countedListRead_valid {α : Type*} (fallback : α) (xs : List α)
    (k : ℕ) (hk : k < xs.length) :
    (countedListRead fallback xs k).1 = xs[k] ∧
      (countedListRead fallback xs k).2 = k + 2 := by
  constructor
  · rw [countedListRead_values, List.getElem?_eq_getElem hk, Option.getD_some]
  · change (countedListGet xs k).2 + 1 = k + 2
    rw [countedListGet_cost_valid xs k hk]

variable {d : ℕ}

def countedCachedVectorRead (xs : List ℝ) (i : Fin d) : ℝ × ℕ := countedListRead 0 xs i.val

theorem countedCachedVectorRead_values (xs : List ℝ) (hlen : xs.length = d) (i : Fin d) :
    (countedCachedVectorRead xs i).1 = cachedRealVector xs hlen i := by
  exact (countedListRead_valid 0 xs i.val (by rw [hlen]; exact i.isLt)).1

theorem countedCachedVectorRead_cost (xs : List ℝ) (hlen : xs.length = d) (i : Fin d) :
    (countedCachedVectorRead xs i).2 ≤ d + 1 := by
  have h := (countedListRead_valid 0 xs i.val (by rw [hlen]; exact i.isLt)).2
  change (countedListRead 0 xs i.val).2 ≤ _
  rw [h]
  omega

def countedCachedMatrixRead (rows : List (List ℝ)) (i j : Fin d) : ℝ × ℕ :=
  let row := countedListRead [] rows i.val
  let cell := countedListRead 0 row.1 j.val
  (cell.1, row.2 + cell.2)

theorem countedCachedMatrixRead_values (rows : List (List ℝ)) (houter : rows.length = d)
    (hinner : ∀ row ∈ rows, row.length = d) (i j : Fin d) :
    (countedCachedMatrixRead rows i j).1 = cachedRealMatrix rows houter hinner i j := by
  have hi : i.val < rows.length := by rw [houter]; exact i.isLt
  have hrow := (countedListRead_valid [] rows i.val hi).1
  have hj : j.val < rows[i.val].length := by rw [hinner _ (List.getElem_mem hi)]; exact j.isLt
  simp only [countedCachedMatrixRead, hrow]
  exact (countedListRead_valid 0 rows[i.val] j.val hj).1

theorem countedCachedMatrixRead_cost (rows : List (List ℝ)) (houter : rows.length = d)
    (hinner : ∀ row ∈ rows, row.length = d) (i j : Fin d) :
    (countedCachedMatrixRead rows i j).2 ≤ 2 * d + 2 := by
  have hi : i.val < rows.length := by rw [houter]; exact i.isLt
  have hrow := countedListRead_valid [] rows i.val hi
  have hj : j.val < rows[i.val].length := by rw [hinner _ (List.getElem_mem hi)]; exact j.isLt
  have hcell := (countedListRead_valid 0 rows[i.val] j.val hj).2
  dsimp only [countedCachedMatrixRead]
  rw [hrow.1, hrow.2, hcell]
  omega

end MsetsPaper.Upper
