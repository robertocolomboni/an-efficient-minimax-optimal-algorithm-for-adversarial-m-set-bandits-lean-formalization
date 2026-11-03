import MsetsPaper.Upper.ESPRAMBatch

noncomputable section

namespace MsetsPaper.Upper.RAMPrograms

open ESPSampling (samplerOrderResource samplerOrderResource_values samplerOrderResource_bounds)
variable {d m : ℕ}

/-- Complete denominator-once/moments computation. The pair-job list is
materialized and counted. During the batch only one deleted-list DP arena
is live, while its scalar output and the moment table are retained. -/
def momentTableRAM (weights : Array ℝ) (d m : ℕ) : MomentBatchResult :=
  let order := samplerOrderResource d
  let jobs := pairJobsRows order.value order.value
  let denominator := espEvaluateRAM weights order.value m
  let run := momentBatchRAM weights order.value m denominator.value jobs.value
  ⟨run.values, order.work + jobs.work + denominator.work + run.work + 6,
    order.allocated + jobs.allocated + denominator.allocated + run.allocated + 8,
    max (weights.size + order.allocated + jobs.allocated + denominator.allocated + 20)
      (weights.size + 2 * order.value.length + 6 * jobs.value.length + run.peak + 20)⟩

theorem momentTableRAM_values (theta : Fin d → ℝ) (weights : Array ℝ)
    (hw : ∀ i : Fin d, weights[i.val]?.getD 0 = Real.exp (theta i)) (hm : 1 ≤ m) :
    (momentTableRAM weights d m).values =
      (espMatrixCells d).map (fun ij => secondMoment (weightedLaw (m := m) theta) ij.1 ij.2) := by
  dsimp only [momentTableRAM]
  rw [samplerOrderResource_values, pairJobsRows_values, espEvaluateRAM_values]
  simp only [hw]
  have hZ := espPartitionProgram_correct theta m
  change (espEvaluate (fun i => Real.exp (theta i)) (List.finRange d) m).1 = _ at hZ
  rw [hZ]
  exact momentBatchRAM_correct theta weights hw m hm (espMatrixCells d)

theorem momentTableRAM_length (weights : Array ℝ) (d m : ℕ) :
    (momentTableRAM weights d m).values.length = d * d := by
  simp only [momentTableRAM, momentBatchRAM_length, pairJobsRows_values,
    samplerOrderResource_values]
  exact espMatrixCells_length d

theorem momentTableRAM_work (weights : Array ℝ) (d m : ℕ) (hd : 1 ≤ d) (hm : 1 ≤ m) :
    (momentTableRAM weights d m).work ≤ 200 * d ^ 3 * m := by
  let order := (samplerOrderResource d).value
  let jobs := (pairJobsRows order order).value
  let Z := (espEvaluateRAM weights order m).value
  have ho := (samplerOrderResource_bounds d).1
  have hj := (pairJobsRows_bounds order order).1
  have hz := (espEvaluateRAM_bounds weights order m).1
  have hr := (momentBatchRAM_sharp_resources weights m Z hd hm).1
  have horder : order = List.finRange d := samplerOrderResource_values d
  have hjobs : jobs = espMatrixCells d := by simp only [jobs, pairJobsRows_values, horder, espMatrixCells]
  rw [← hjobs, ← horder] at hr
  have hlen : order.length = d := by simp [horder]
  rw [hlen] at hj hz
  have hdm : d ≤ d * m := by nlinarith
  have hmd : m ≤ d * m := by nlinarith
  have hd2 : 1 ≤ d ^ 2 := by nlinarith
  have hbig : d * m ≤ d ^ 3 * m := by nlinarith
  have hd2big : d ^ 2 ≤ d ^ 3 * m := by nlinarith
  dsimp only [momentTableRAM]
  dsimp only [order, jobs, Z] at hj hz hr
  nlinarith

/-- This is the literal O(dm+d^2) peak-space bound, not total allocations
over all deletion jobs. The actual batch reset retains scalar results only. -/
theorem momentTableRAM_peak (weights : Array ℝ) (hsize : weights.size = d)
    (m : ℕ) (hd : 1 ≤ d) (hm : 1 ≤ m) :
    (momentTableRAM weights d m).peak ≤ 200 * (d * m + d ^ 2 + 1) := by
  let order := (samplerOrderResource d).value
  let jobs := (pairJobsRows order order).value
  let Z := (espEvaluateRAM weights order m).value
  have ho := (samplerOrderResource_bounds d).2
  have hj := (pairJobsRows_bounds order order).2
  have hz := (espEvaluateRAM_bounds weights order m).2
  have hr := (momentBatchRAM_sharp_resources weights m Z hd hm).2
  have horder : order = List.finRange d := samplerOrderResource_values d
  have hjobs : jobs = espMatrixCells d := by simp only [jobs, pairJobsRows_values, horder, espMatrixCells]
  rw [← hjobs, ← horder] at hr
  have hlen : order.length = d := by simp [horder]
  have hjlen : jobs.length = d * d := by rw [hjobs, espMatrixCells_length]
  rw [hlen] at hj hz
  have hdm : d ≤ d * m := by nlinarith
  have hmd : m ≤ d * m := by nlinarith
  dsimp only [momentTableRAM]
  dsimp only [order, jobs, Z] at hj hz hr hlen hjlen
  rw [hsize, hlen, hjlen]
  apply max_le <;> nlinarith

end MsetsPaper.Upper.RAMPrograms
