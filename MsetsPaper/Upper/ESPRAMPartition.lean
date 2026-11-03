import MsetsPaper.Upper.SamplerRAMCache

noncomputable section

namespace MsetsPaper.Upper.RAMPrograms

open ESPSampling (samplerOrderResource samplerOrderResource_values samplerOrderResource_bounds)

def logPartitionRAM (theta : Array ℝ) (d m : ℕ) : ResourceRun ℝ :=
  let weights := weightsRAM theta d
  let order := samplerOrderResource d
  let denominator := espEvaluateRAM weights.value order.value m
  ⟨Real.log denominator.value, weights.work + order.work + denominator.work + 3,
    weights.allocated + order.allocated + denominator.allocated + 5⟩

theorem logPartitionRAM_values (theta : Array ℝ) (d m : ℕ) :
    (logPartitionRAM theta d m).value =
      logPartition (m := m) (fun i : Fin d => theta[i.val]?.getD 0) := by
  simp only [logPartitionRAM, samplerOrderResource_values, espEvaluateRAM_values,
    logPartition]
  have hw : (fun i : Fin d => (weightsRAM theta d).value[i.val]?.getD 0) =
      fun i : Fin d => Real.exp (theta[i.val]?.getD 0) := funext (weightsRAM_values theta d)
  rw [hw]
  congr 1
  exact espPartitionProgram_correct (fun i : Fin d => theta[i.val]?.getD 0) m

theorem logPartitionRAM_bounds (theta : Array ℝ) (d m : ℕ) (hd : 1 ≤ d) (hm : 1 ≤ m) :
    (logPartitionRAM theta d m).work ≤ 128 * d * m ∧
      (logPartitionRAM theta d m).allocated ≤ 128 * d * m := by
  have hw := weightsRAM_bounds theta d
  have ho := samplerOrderResource_bounds d
  have hz := espEvaluateRAM_bounds (weightsRAM theta d).value (samplerOrderResource d).value m
  have hlen : (samplerOrderResource d).value.length = d := by simp [samplerOrderResource_values]
  rw [hlen] at hz
  have hdm : d ≤ d * m := by nlinarith
  have hmd : m ≤ d * m := by nlinarith
  dsimp only [logPartitionRAM]
  constructor <;> nlinarith [hw.1, hw.2, ho.1, ho.2, hz.1, hz.2]

/-- Even retaining every temporary allocation, the input plus all live
words is O(dm). No reuse or constant-cost conversion is assumed here. -/
theorem logPartitionRAM_all_words (theta : Array ℝ) {d : ℕ} (hsize : theta.size = d)
    (m : ℕ) (hd : 1 ≤ d) (hm : 1 ≤ m) :
    theta.size + (logPartitionRAM theta d m).allocated + 10 ≤ 150 * d * m := by
  have h := (logPartitionRAM_bounds theta d m hd hm).2
  have hdm : d ≤ d * m := by nlinarith
  rw [hsize]
  nlinarith

end MsetsPaper.Upper.RAMPrograms
