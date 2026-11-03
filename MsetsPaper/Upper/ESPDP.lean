import MsetsPaper.Upper.ESP

/-!
# A non-enumerative, counted elementary-symmetric dynamic program

The code scans a row once, doing one multiplication and one addition per
positive-degree cell. `espDP` computes each previous row once and reuses its
stored list; it never calls `powersetCard` or enumerates the action space.
The counter is an operational arithmetic-cost semantics (real addition and
multiplication each cost one); it does not assert bit complexity for reals.
-/

noncomputable section
open scoped BigOperators

namespace MsetsPaper.Upper

/-- The actual inner loop, instrumented at each multiplication/addition. -/
def espZip (w : ℝ) : List ℝ → List ℝ → List ℝ × ℕ
  | x :: xs, y :: ys =>
    let next := espZip w xs ys
    ((x + w * y) :: next.1, next.2 + 2)
  | _, _ => ([], 0)

theorem espZip_values (w : ℝ) (xs ys : List ℝ) :
    (espZip w xs ys).1 = List.zipWith (fun x y => x + w * y) xs ys := by
  induction xs generalizing ys with
  | nil => rfl
  | cons x xs ih => cases ys <;> simp [espZip, ih]

theorem espZip_cost (w : ℝ) (xs ys : List ℝ) :
    (espZip w xs ys).2 = 2 * min xs.length ys.length := by
  induction xs generalizing ys with
  | nil => simp [espZip]
  | cons x xs ih =>
    cases ys with
    | nil => simp [espZip]
    | cons y ys => simp [espZip, ih, Nat.mul_add, min_add_add_right]

/-- One complete row update; degree zero is copied without arithmetic. -/
def espStep (w : ℝ) : List ℝ → List ℝ × ℕ
  | [] => ([], 0)
  | x :: xs =>
    let next := espZip w xs (x :: xs)
    (x :: next.1, next.2)

theorem espStep_length (w : ℝ) (row : List ℝ) :
    (espStep w row).1.length = row.length := by
  cases row <;> simp [espStep, espZip_values, List.length_zipWith]

theorem espStep_cost (w : ℝ) (row : List ℝ) :
    (espStep w row).2 = 2 * (row.length - 1) := by
  cases row <;> simp [espStep, espZip_cost]

theorem espStep_get_zero (w : ℝ) (row : List ℝ) (h : 0 < row.length) :
    (espStep w row).1[0]'(by rw [espStep_length]; exact h) = row[0] := by
  cases row with
  | nil => simp at h
  | cons x xs => rfl

theorem espStep_get_succ (w : ℝ) (row : List ℝ) (k : ℕ) (h : k + 1 < row.length) :
    (espStep w row).1[k + 1]'(by rw [espStep_length]; exact h) =
      row[k + 1] + w * row[k] := by
  cases row with
  | nil => simp at h
  | cons x xs => simp [espStep, espZip_values, List.getElem_zipWith]

/-- The empty prefix has coefficients 1,0,...,0. -/
def espInitial (m : ℕ) : List ℝ := 1 :: List.replicate m 0

@[simp] theorem espInitial_length (m : ℕ) : (espInitial m).length = m + 1 := by
  simp [espInitial]

/-- Bottom-up suffix DP: each preceding row is evaluated exactly once. -/
def espDP {ι : Type*} (w : ι → ℝ) (m : ℕ) : List ι → List ℝ × ℕ
  | [] => (espInitial m, 0)
  | i :: tail =>
    let previous := espDP w m tail
    let current := espStep (w i) previous.1
    (current.1, previous.2 + current.2)

theorem espDP_length {ι : Type*} (w : ι → ℝ) (m : ℕ) (order : List ι) :
    (espDP w m order).1.length = m + 1 := by
  induction order with
  | nil => exact espInitial_length m
  | cons i tail ih => simpa [espDP, espStep_length] using ih

/-- Exactly two arithmetic operations for each of the m cells at each item. -/
theorem espDP_cost {ι : Type*} (w : ι → ℝ) (m : ℕ) (order : List ι) :
    (espDP w m order).2 = 2 * m * order.length := by
  induction order with
  | nil => simp [espDP]
  | cons i tail ih =>
    simp only [espDP, ih, espStep_cost, espDP_length, Nat.add_sub_cancel,
      List.length_cons]
    ring

/-- Every stored cell equals the finite subset specification; no recurrence
correctness is supplied as a premise. -/
theorem espDP_correct {ι : Type*} [DecidableEq ι] (w : ι → ℝ) (m : ℕ)
    (order : List ι) (hn : order.Nodup) (k : ℕ) (hk : k ≤ m) :
    (espDP w m order).1[k]'(by rw [espDP_length]; omega) = esp w order.toFinset k := by
  induction order generalizing k with
  | nil =>
    cases k with
    | zero => simp [espDP, espInitial]
    | succ k => simp [espDP, espInitial, esp_empty_succ]
  | cons i tail ih =>
    obtain ⟨hi, ht⟩ := List.nodup_cons.mp hn
    cases k with
    | zero =>
      have hp : 0 < (espDP w m tail).1.length := by rw [espDP_length]; omega
      have hc : 0 < (espStep (w i) (espDP w m tail).1).1.length := by
        rw [espStep_length]; exact hp
      change (espStep (w i) (espDP w m tail).1).1[0]'hc = _
      rw [espStep_get_zero _ _ hp, ih ht 0 (by omega), esp_zero, esp_zero]
    | succ k =>
      have hp : k + 1 < (espDP w m tail).1.length := by rw [espDP_length]; omega
      have hc : k + 1 < (espStep (w i) (espDP w m tail).1).1.length := by
        rw [espStep_length]; exact hp
      change (espStep (w i) (espDP w m tail).1).1[k + 1]'hc = _
      rw [espStep_get_succ _ _ _ hp, ih ht (k + 1) hk, ih ht k (by omega)]
      simpa only [List.toFinset_cons] using
        (esp_insert_succ w tail.toFinset i (by simpa using hi) k).symm

/-- A single coefficient, together with the cost of the actual DP run. -/
def espEvaluate {ι : Type*} (w : ι → ℝ) (order : List ι) (k : ℕ) : ℝ × ℕ :=
  let result := espDP w k order
  (result.1[k]'(by dsimp [result]; rw [espDP_length]; omega), result.2)

theorem espEvaluate_correct {ι : Type*} [DecidableEq ι] (w : ι → ℝ)
    (order : List ι) (hn : order.Nodup) (k : ℕ) :
    (espEvaluate w order k).1 = esp w order.toFinset k :=
  espDP_correct w k order hn k le_rfl

theorem espEvaluate_cost {ι : Type*} (w : ι → ℝ) (order : List ι) (k : ℕ) :
    (espEvaluate w order k).2 = 2 * k * order.length := espDP_cost w k order

/-- The stored rows for suffix preprocessing. The `head` field is a reference
to the first stored row, rather than a recomputation of its coefficients. -/
structure ESPTable where
  head : List ℝ
  rows : List (List ℝ)
  arithmetic : ℕ

def espSuffixTable {ι : Type*} (w : ι → ℝ) (m : ℕ) : List ι → ESPTable
  | [] => ⟨espInitial m, [espInitial m], 0⟩
  | i :: tail =>
    let previous := espSuffixTable w m tail
    let current := espStep (w i) previous.head
    ⟨current.1, current.1 :: previous.rows, previous.arithmetic + current.2⟩

theorem espSuffixTable_head {ι : Type*} (w : ι → ℝ) (m : ℕ) (order : List ι) :
    (espSuffixTable w m order).head = (espDP w m order).1 := by
  induction order with
  | nil => rfl
  | cons i tail ih => simp only [espSuffixTable, espDP, ih]

theorem espSuffixTable_cost {ι : Type*} (w : ι → ℝ) (m : ℕ) (order : List ι) :
    (espSuffixTable w m order).arithmetic = 2 * m * order.length := by
  induction order with
  | nil => simp [espSuffixTable]
  | cons i tail ih =>
    simp only [espSuffixTable, espSuffixTable_head, espStep_cost,
      espDP_length, Nat.add_sub_cancel, ih, List.length_cons]
    ring

theorem espSuffixTable_rows_length {ι : Type*} (w : ι → ℝ) (m : ℕ) (order : List ι) :
    (espSuffixTable w m order).rows.length = order.length + 1 := by
  induction order with
  | nil => rfl
  | cons i tail ih => simpa [espSuffixTable] using congrArg Nat.succ ih

/-- This is an exact bound on stored coefficient cells, not a declaration of
an asymptotic running time detached from the implementation. -/
theorem espSuffixTable_cells {ι : Type*} (w : ι → ℝ) (m : ℕ) (order : List ι) :
    ((espSuffixTable w m order).rows.map List.length).sum =
      (order.length + 1) * (m + 1) := by
  induction order with
  | nil => simp [espSuffixTable, espInitial]
  | cons i tail ih =>
    simp only [espSuffixTable, List.map_cons, List.sum_cons, espStep_length,
      espSuffixTable_head, espDP_length, ih, List.length_cons]
    ring

theorem espSuffixTable_row {ι : Type*} (w : ι → ℝ) (m : ℕ) (order : List ι)
    (j : ℕ) (hj : j ≤ order.length) :
    (espSuffixTable w m order).rows[j]'(by rw [espSuffixTable_rows_length]; omega) =
      (espDP w m (order.drop j)).1 := by
  induction order generalizing j with
  | nil =>
    have : j = 0 := by simpa using hj
    subst j
    rfl
  | cons i tail ih =>
    cases j with
    | zero => simp [espSuffixTable, espDP, espSuffixTable_head]
    | succ j =>
      have hj' : j ≤ tail.length := by simpa using hj
      simpa only [espSuffixTable, List.getElem_cons_succ, List.drop_succ_cons] using ih j hj'

/-- Execute several deletion problems, accumulating the inner program's cost. -/
def espBatch {ι : Type*} (w : ι → ℝ) : List (List ι × ℕ) → List ℝ × ℕ
  | [] => ([], 0)
  | (order, k) :: tail =>
    let current := espEvaluate w order k
    let remaining := espBatch w tail
    (current.1 :: remaining.1, current.2 + remaining.2)

theorem espBatch_cost_le {ι : Type*} (w : ι → ℝ) (jobs : List (List ι × ℕ))
    (d m : ℕ) (hjobs : ∀ job ∈ jobs, job.1.length ≤ d ∧ job.2 ≤ m) :
    (espBatch w jobs).2 ≤ 2 * m * d * jobs.length := by
  induction jobs with
  | nil => simp [espBatch]
  | cons job jobs ih =>
    obtain ⟨order, k⟩ := job
    have hcur := hjobs (order, k) (by simp)
    have htail := ih (fun job hj => hjobs job (by simp [hj]))
    have hc : 2 * k * order.length ≤ 2 * m * d :=
      Nat.mul_le_mul (Nat.mul_le_mul_left 2 hcur.2) hcur.1
    simp only [espBatch, espEvaluate_cost, List.length_cons]
    nlinarith

end MsetsPaper.Upper
