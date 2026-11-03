import MsetsPaper.Upper.ESPRAM
import MsetsPaper.Upper.SamplerStoredProgram

/-! Sequential moment evaluation with an explicit temporary-arena reset.
After evaluating one deleted coefficient, only its returned scalar and two
counters are retained, never its coefficient rows. The next call therefore
uses the same temporary arena. Ten word slots conservatively cover the
scalar/counters, record/frame metadata, continuation pointer and output cell.
-/

noncomputable section

namespace MsetsPaper.Upper.RAMPrograms

variable {d : ℕ}

def appendResource {α : Type*} : List α → List α → ResourceRun (List α)
  | [], ys => ⟨ys, 1, 1⟩
  | x :: xs, ys =>
    let tail := appendResource xs ys
    ⟨x :: tail.value, tail.work + 2, tail.allocated + 3⟩

theorem appendResource_values {α : Type*} (xs ys : List α) :
    (appendResource xs ys).value = xs ++ ys := by
  induction xs <;> simp_all [appendResource]

theorem appendResource_counts {α : Type*} (xs ys : List α) :
    (appendResource xs ys).work = 2 * xs.length + 1 ∧
      (appendResource xs ys).allocated = 3 * xs.length + 1 := by
  induction xs with
  | nil => simp [appendResource]
  | cons x xs ih => simp only [appendResource, List.length_cons]; constructor <;> omega

def pairJobsRows (inner : List (Fin d)) : List (Fin d) → ResourceRun (List (Fin d × Fin d))
  | [] => ⟨[], 1, 1⟩
  | i :: tail =>
    let row := resourceMap (fun j => (⟨(i,j), 3, 3⟩ : ResourceRun (Fin d × Fin d))) inner
    let remaining := pairJobsRows inner tail
    let joined := appendResource row.value remaining.value
    ⟨joined.value, row.work + remaining.work + joined.work + 2,
      row.allocated + remaining.allocated + joined.allocated + 4⟩

theorem pairJobsRows_values (inner outer : List (Fin d)) :
    (pairJobsRows inner outer).value = outer.product inner := by
  induction outer with
  | nil => rfl
  | cons i tail ih =>
    simp only [pairJobsRows, resourceMap_values, appendResource_values, ih]
    rfl

theorem pairJobsRows_bounds (inner outer : List (Fin d)) :
    (pairJobsRows inner outer).work ≤ 1 + outer.length * (7 * inner.length + 4) ∧
      (pairJobsRows inner outer).allocated ≤ 1 + outer.length * (9 * inner.length + 6) := by
  induction outer with
  | nil => simp [pairJobsRows]
  | cons i tail ih =>
    let f := fun j => (⟨(i,j), 3, 3⟩ : ResourceRun (Fin d × Fin d))
    have hr := resourceMap_bounds f inner 3 3 (fun _ _ => ⟨le_rfl, le_rfl⟩)
    have hj := appendResource_counts (resourceMap f inner).value (pairJobsRows inner tail).value
    have hlen : (resourceMap f inner).value.length = inner.length := by simp [resourceMap_values]
    rw [hlen] at hj
    dsimp only [pairJobsRows]
    dsimp only [f] at hr hj
    simp only [List.length_cons]
    constructor <;> nlinarith [hr.1, hr.2, hj.1, hj.2, ih.1, ih.2]

structure MomentBatchResult where
  values : List ℝ
  work : ℕ
  allocated : ℕ
  peak : ℕ

def momentBatchRAM (weights : Array ℝ) (order : List (Fin d)) (m : ℕ) (Z : ℝ) :
    List (Fin d × Fin d) → MomentBatchResult
  | [] => ⟨[], 1, 1, 1⟩
  | (i,j) :: jobs =>
    let current := pairRAM weights order m Z i j
    let remaining := momentBatchRAM weights order m Z jobs
    ⟨current.value :: remaining.values,
      current.work + remaining.work + 4,
      current.allocated + remaining.allocated + 10,
      max (current.allocated + 10) (remaining.peak + 10)⟩

theorem momentBatchRAM_values (weights : Array ℝ) (order : List (Fin d)) (m : ℕ) (Z : ℝ)
    (jobs : List (Fin d × Fin d)) :
    (momentBatchRAM weights order m Z jobs).values =
      jobs.map (fun ij => (pairRAM weights order m Z ij.1 ij.2).value) := by
  induction jobs with
  | nil => rfl
  | cons ij jobs ih => cases ij; simp [momentBatchRAM, ih]

theorem momentBatchRAM_length (weights : Array ℝ) (order : List (Fin d)) (m : ℕ) (Z : ℝ)
    (jobs : List (Fin d × Fin d)) :
    (momentBatchRAM weights order m Z jobs).values.length = jobs.length := by
  rw [momentBatchRAM_values, List.length_map]

theorem momentBatchRAM_bounds (weights : Array ℝ) (order : List (Fin d)) (m : ℕ) (Z : ℝ)
    (jobs : List (Fin d × Fin d)) :
    let C := 4 * m + 23 + order.length * (7 * m + 16)
    (momentBatchRAM weights order m Z jobs).work ≤ 1 + jobs.length * (C + 4) ∧
    (momentBatchRAM weights order m Z jobs).allocated ≤ 1 + jobs.length * (C + 10) ∧
    (momentBatchRAM weights order m Z jobs).peak ≤ C + 10 * jobs.length + 1 := by
  dsimp only
  induction jobs with
  | nil => simp [momentBatchRAM]
  | cons ij jobs ih =>
    obtain ⟨i,j⟩ := ij
    have hc := pairRAM_bounds weights order m Z i j
    dsimp only [momentBatchRAM]
    simp only [List.length_cons]
    refine ⟨?_, ?_, ?_⟩
    · nlinarith [hc.1, ih.1]
    · nlinarith [hc.2, ih.2.1]
    · apply max_le <;> omega

theorem momentBatchRAM_correct (theta : Fin d → ℝ) (weights : Array ℝ)
    (hw : ∀ i : Fin d, weights[i.val]?.getD 0 = Real.exp (theta i))
    (m : ℕ) (hm : 1 ≤ m) (jobs : List (Fin d × Fin d)) :
    (momentBatchRAM weights (List.finRange d) m (partition (m := m) theta) jobs).values =
      jobs.map (fun ij => secondMoment (weightedLaw (m := m) theta) ij.1 ij.2) := by
  rw [momentBatchRAM_values]
  apply List.map_congr_left
  intro ij hij
  rw [pairRAM_values]
  simp only [hw]
  exact espPairProgram_correct theta hm ij.1 ij.2

theorem momentBatchRAM_sharp_resources (weights : Array ℝ) (m : ℕ) (Z : ℝ)
    (hd : 1 ≤ d) (hm : 1 ≤ m) :
    (momentBatchRAM weights (List.finRange d) m Z (espMatrixCells d)).work ≤ 60 * d ^ 3 * m ∧
    (momentBatchRAM weights (List.finRange d) m Z (espMatrixCells d)).peak ≤
      50 * d * m + 10 * d ^ 2 + 1 := by
  have h := momentBatchRAM_bounds weights (List.finRange d) m Z (espMatrixCells d)
  simp only [List.length_finRange, espMatrixCells_length] at h
  have hdm : d ≤ d * m := by nlinarith
  have hmd : m ≤ d * m := by nlinarith
  have hC : 4 * m + 23 + d * (7 * m + 16) ≤ 50 * d * m := by nlinarith
  have hmul := Nat.mul_le_mul_left (d * d) hC
  have hd2 : 1 ≤ d * d := by nlinarith
  have hd3 : d * d ≤ d ^ 3 * m := by nlinarith
  constructor
  · nlinarith [h.1]
  · nlinarith [h.2.2]

end MsetsPaper.Upper.RAMPrograms
