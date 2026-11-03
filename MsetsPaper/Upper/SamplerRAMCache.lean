import MsetsPaper.Upper.RAMBufferCopy
import MsetsPaper.Upper.SamplerRAMDraws
import MsetsPaper.Upper.ESPRAM
import MsetsPaper.Upper.SamplerStoredProgram

/-! Actual suffix-cache preprocessing. Every row is copied into an owned RAM
buffer and the outer reference array is also constructed explicitly. The
bound includes parameter reads, exponentials, order generation, DP, and both
levels of conversion. Total allocation already bounds peak temporary words;
no reset or hidden free conversion is required for this preprocessing pass. -/

namespace MsetsPaper.Upper.RAMPrograms
open ESPSampling SchurSolver
open scoped unitInterval
noncomputable section

theorem rowCopies_counts (rows : List (List ℝ)) :
    (resourceMap realListToArray rows).work =
      7 * (rows.map List.length).sum + 7 * rows.length + 1 ∧
    (resourceMap realListToArray rows).allocated =
      5 * (rows.map List.length).sum + 8 * rows.length + 1 := by
  induction rows with
  | nil => simp [resourceMap]
  | cons row rows ih =>
    have hc := copyListToArray_counts (0 : ℝ) row
    simp only [resourceMap, List.map_cons, List.sum_cons, List.length_cons]
    change _ ∧ _
    constructor <;> dsimp only [realListToArray] at * <;> omega

def nestedRowsRAM (rows : List (List ℝ)) : ResourceRun (Array (Array ℝ)) :=
  let inner := resourceMap realListToArray rows
  let outer := rowListToArray inner.value
  ⟨outer.value, inner.work + outer.work + 2, inner.allocated + outer.allocated + 2⟩

theorem nestedRowsRAM_values (rows : List (List ℝ)) :
    decodeRows (nestedRowsRAM rows).value = rows := by
  change ((copyListToArray (#[] : Array ℝ) _).value.toList.map Array.toList) = rows
  rw [copyListToArray_toList, resourceMap_values]
  simp only [List.map_map, Function.comp_def, realListToArray, copyListToArray_toList]
  change List.map id rows = rows
  exact List.map_id rows

theorem nestedRowsRAM_counts (rows : List (List ℝ)) :
    (nestedRowsRAM rows).work =
      7 * (rows.map List.length).sum + 14 * rows.length + 8 ∧
    (nestedRowsRAM rows).allocated =
      5 * (rows.map List.length).sum + 13 * rows.length + 8 := by
  have hi := rowCopies_counts rows
  have ho := copyListToArray_counts (#[] : Array ℝ) (resourceMap realListToArray rows).value
  have hl : (resourceMap realListToArray rows).value.length = rows.length := by
    simp only [resourceMap_values, List.length_map]
  rw [hl] at ho
  dsimp only [nestedRowsRAM, rowListToArray]
  constructor <;> omega

def weightsRAM (theta : Array ℝ) (d : ℕ) : ResourceRun (Array ℝ) :=
  let scalars := resourceTabulate d (fun i =>
    let x := realLoad theta i.val
    (⟨Real.exp x.value, x.work + 1, x.allocated + 1⟩ : ResourceRun ℝ))
  let copied := realListToArray scalars.value
  ⟨copied.value, scalars.work + copied.work + 2,
    scalars.allocated + copied.allocated + 2⟩

theorem weightsRAM_values (theta : Array ℝ) (d : ℕ) (i : Fin d) :
    (realLoad (weightsRAM theta d).value i.val).value =
      Real.exp ((realLoad theta i.val).value) := by
  simp only [weightsRAM, realListToArray, copyListToArray_values,
    resourceTabulate_values, realLoad_values]
  simp

theorem weightsRAM_size (theta : Array ℝ) (d : ℕ) :
    (weightsRAM theta d).value.size = d := by
  simp only [weightsRAM, realListToArray, copyListToArray_size,
    resourceTabulate_values, List.length_ofFn]

theorem weightsRAM_bounds (theta : Array ℝ) (d : ℕ) :
    (weightsRAM theta d).work ≤ 11 * d + 8 ∧
      (weightsRAM theta d).allocated ≤ 11 * d + 8 := by
  let f := fun i : Fin d =>
    (⟨Real.exp (realLoad theta i.val).value, 2, 2⟩ : ResourceRun ℝ)
  have ht := resourceTabulate_bounds d f 2 2 (fun _ => ⟨le_rfl, le_rfl⟩)
  have hc := copyListToArray_counts (0 : ℝ) (resourceTabulate d f).value
  have hl : (resourceTabulate d f).value.length = d := by
    simp only [resourceTabulate_values, List.length_ofFn]
  rw [hl] at hc
  change (resourceTabulate d f).work +
      (copyListToArray 0 (resourceTabulate d f).value).work + 2 ≤ _ ∧
    (resourceTabulate d f).allocated +
      (copyListToArray 0 (resourceTabulate d f).value).allocated + 2 ≤ _
  constructor <;> omega

structure RAMSamplerCache (d : ℕ) where
  weights : Array ℝ
  rows : Array (Array ℝ)
  order : List (Fin d)

def samplerCacheRAM (theta : Array ℝ) (d m : ℕ) : ResourceRun (RAMSamplerCache d) :=
  let weights := weightsRAM theta d
  let order := samplerOrderResource d
  let table := espSuffixRAM weights.value m order.value
  let copied := nestedRowsRAM table.value.rows
  ⟨⟨weights.value, copied.value, order.value⟩,
    weights.work + order.work + table.work + copied.work + 4,
    weights.allocated + order.allocated + table.allocated + copied.allocated + 4⟩

theorem samplerCacheRAM_order (theta : Array ℝ) (d m : ℕ) :
    (samplerCacheRAM theta d m).value.order = List.finRange d :=
  samplerOrderResource_values d

theorem samplerCacheRAM_weights (theta : Array ℝ) (d m : ℕ) (i : Fin d) :
    (realLoad (samplerCacheRAM theta d m).value.weights i.val).value =
      Real.exp ((realLoad theta i.val).value) := weightsRAM_values theta d i

theorem samplerCacheRAM_rows (theta : Array ℝ) (d m : ℕ) :
    decodeRows (samplerCacheRAM theta d m).value.rows =
      (espSuffixTable (fun i : Fin d => Real.exp (realLoad theta i.val).value)
        m (List.finRange d)).rows := by
  change decodeRows (nestedRowsRAM _).value = _
  rw [nestedRowsRAM_values, espSuffixRAM_values, samplerOrderResource_values]
  congr 2
  funext i
  exact weightsRAM_values theta d i

set_option maxHeartbeats 800000 in
theorem samplerCacheRAM_linear (theta : Array ℝ) (d m : ℕ)
    (hd : 1 ≤ d) (hm : 1 ≤ m) :
    (samplerCacheRAM theta d m).work ≤ 128 * d * m ∧
      (samplerCacheRAM theta d m).allocated ≤ 128 * d * m := by
  have hw := weightsRAM_bounds theta d
  have ho := samplerOrderResource_bounds d
  have ht := espSuffixRAM_linear (weightsRAM theta d).value m hd hm
  have hc := nestedRowsRAM_counts
    (espSuffixRAM (weightsRAM theta d).value m (List.finRange d)).value.rows
  have hl : (espSuffixRAM (weightsRAM theta d).value m (List.finRange d)).value.rows.length =
      d + 1 := by rw [espSuffixRAM_values, espSuffixTable_rows_length, List.length_finRange]
  have hs : ((espSuffixRAM (weightsRAM theta d).value m (List.finRange d)).value.rows.map
      List.length).sum = (d + 1) * (m + 1) := by
    rw [espSuffixRAM_values, espSuffixTable_cells, List.length_finRange]
  rw [hl, hs] at hc
  have hdm : d ≤ d * m := by nlinarith
  have hmd : m ≤ d * m := by nlinarith
  have hprod : 1 ≤ d * m := by nlinarith
  dsimp only [samplerCacheRAM]
  rw [samplerOrderResource_values]
  constructor
  · nlinarith only [hw.1, ho.1, ht.1, hc.1, hdm, hmd, hprod]
  · nlinarith only [hw.2, ho.2, ht.2, hc.2, hdm, hmd, hprod]

def cachedSamplerRAM {d : ℕ} (cache : RAMSamplerCache d) (m : ℕ)
    (u : Fin d → unitInterval) : ResourceRun (List (Fin d)) × ℕ :=
  randomSamplerRAM cache.weights u cache.rows cache.order d m 0

theorem cachedSamplerRAM_linear (theta : Array ℝ) (d m : ℕ)
    (u : Fin d → unitInterval) :
    (cachedSamplerRAM (samplerCacheRAM theta d m).value m u).1.work ≤ 25 * d + 3 ∧
    (cachedSamplerRAM (samplerCacheRAM theta d m).value m u).1.allocated ≤ 25 * d + 3 ∧
    (cachedSamplerRAM (samplerCacheRAM theta d m).value m u).2 ≤ d := by
  simp only [cachedSamplerRAM, samplerCacheRAM_order]
  exact randomSamplerRAM_postprocessing_linear _ u _ m

theorem cachedSamplerRAM_probability (theta : Array ℝ) (d m : ℕ) (hmd : m ≤ d)
    (a : Action d m) :
    uniformCube (Fin d) {u | (cachedSamplerRAM (samplerCacheRAM theta d m).value m u).1.value.toFinset = a.val} =
      ENNReal.ofReal (weightedLaw (fun i : Fin d => (realLoad theta i.val).value) a) := by
  simp only [cachedSamplerRAM, samplerCacheRAM_order]
  exact randomSamplerRAM_weighted_probability _ _ _ hmd
    (samplerCacheRAM_weights theta d m) (samplerCacheRAM_rows theta d m) a

end
end MsetsPaper.Upper.RAMPrograms
