import MsetsPaper.Upper.ESPRAMPartition
import MsetsPaper.Upper.ESPRAMMomentsFromTheta
import MsetsPaper.Upper.SamplerRAMComplete

/-! Definitive L9. Correctness and complexity refer to the same explicit
array programs, with a cached sampler separating preprocessing from draws.
The action sums below are specifications, not enumerations performed by
these programs. The real-RAM model counts exp/log and independent uniform
draws as primitive operations, as in the manuscript. -/

noncomputable section
open MsetsPaper.Upper MsetsPaper.Upper.RAMPrograms MsetsPaper.Upper.ESPSampling

namespace MsetsPaper.Alignment.Implementation

structure ESPRoutineCertificate (theta : Array ℝ) (d m : ℕ) : Prop where
  partition_value : (logPartitionRAM theta d m).value =
    logPartition (m := m) (fun i : Fin d => theta[i.val]?.getD 0)
  partition_work : (logPartitionRAM theta d m).work ≤ 128 * d * m
  partition_space : theta.size + (logPartitionRAM theta d m).allocated + 10 ≤ 150 * d * m
  moment_values : (momentTableFromThetaRAM theta d m).values =
    (espMatrixCells d).map (fun ij => secondMoment
      (weightedLaw (m := m) (fun i : Fin d => theta[i.val]?.getD 0)) ij.1 ij.2)
  moment_length : (momentTableFromThetaRAM theta d m).values.length = d * d
  marginal_values : ∀ (i : Fin d) (k : ℕ), (espMatrixCells d)[k]? = some (i, i) →
    (momentTableFromThetaRAM theta d m).values[k]? =
      some (weightedMarginal (m := m) (fun j : Fin d => theta[j.val]?.getD 0) i)
  moment_work : (momentTableFromThetaRAM theta d m).work ≤ 400 * d ^ 3 * m
  moment_space : (momentTableFromThetaRAM theta d m).peak ≤ 800 * (d * m + d ^ 2)
  preprocessing_work : (samplerCacheRAM theta d m).work ≤ 128 * d * m
  draw_work : ∀ u : Fin d → unitInterval,
    (cachedSamplerRAM (samplerCacheRAM theta d m).value m u).1.work ≤ 25 * d + 3 ∧
    (cachedSamplerRAM (samplerCacheRAM theta d m).value m u).2 ≤ d
  sampling_space : ∀ u : Fin d → unitInterval,
    theta.size + 1 + (samplerFromThetaRAM theta d m u).1.allocated ≤ 160 * d * m
  sampling_cardinality : ∀ u : Fin d → unitInterval,
    (samplerFromThetaRAM theta d m u).1.value.length = m ∧
    (samplerFromThetaRAM theta d m u).1.value.Nodup
  sampling_law : ∀ a : Action d m,
    uniformCube (Fin d) {u | (samplerFromThetaRAM theta d m u).1.value.toFinset = a.val} =
      ENNReal.ofReal (weightedLaw (fun i : Fin d => (realLoad theta i.val).value) a)

/-- A caller provides only a stored parameter vector and the dimension
conditions; the table identities and sampling law are proved internally. -/
theorem esp_routines (theta : Array ℝ) {d m : ℕ} (hsize : theta.size = d)
    (hm : 1 ≤ m) (hmd : m ≤ d) : ESPRoutineCertificate theta d m where
  partition_value := logPartitionRAM_values theta d m
  partition_work := (logPartitionRAM_bounds theta d m (by omega) hm).1
  partition_space := logPartitionRAM_all_words theta hsize m (by omega) hm
  moment_values := momentTableFromThetaRAM_values theta d m hm
  moment_length := momentTableFromThetaRAM_length theta d m
  marginal_values := momentTableFromThetaRAM_diagonal theta d m hm
  moment_work := momentTableFromThetaRAM_work theta d m (by omega) hm
  moment_space := momentTableFromThetaRAM_peak_order theta hsize m (by omega) hm
  preprocessing_work := (samplerCacheRAM_linear theta d m (by omega) hm).1
  draw_work := fun u => ⟨(cachedSamplerRAM_linear theta d m u).1,
    (cachedSamplerRAM_linear theta d m u).2.2⟩
  sampling_space := samplerFromThetaRAM_peak_with_input theta d m hsize (by omega) hm
  sampling_cardinality := samplerFromThetaRAM_card_nodup theta d m hmd
  sampling_law := samplerFromThetaRAM_probability theta d m hmd

end MsetsPaper.Alignment.Implementation
