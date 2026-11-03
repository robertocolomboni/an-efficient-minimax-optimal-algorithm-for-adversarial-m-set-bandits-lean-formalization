import MsetsPaper.Upper.ESPResources
import MsetsPaper.Upper.ResourceCombinators
import MsetsPaper.Upper.ESPSamplerDP

/-! Resource refinement of the actual suffix-table sampler. The output is a
sublist of its input order, so no implicit set deduplication is needed. All
list traversals (including the quota length test) are charged. A reader for
the uniform variate specifies explicitly whether draws or cached reads are
being used; no assumption of cost-free coordinate access is made. -/

noncomputable section
set_option maxHeartbeats 1000000
open scoped BigOperators unitInterval ENNReal
open MeasureTheory ProbabilityTheory

namespace MsetsPaper.Upper.ESPSampling

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

def thresholdResource (readWeight : ι → ResourceRun ℝ)
    (rows : List (List ℝ)) (r : ℕ) (i : ι) : ResourceRun ℝ :=
  let nextRow := resourceListRead [] rows 1
  let currentRow := resourceListRead [] rows 0
  let numerator := resourceListRead 0 nextRow.value (r - 1)
  let denominator := resourceListRead 0 currentRow.value r
  let weight := readWeight i
  ⟨weight.value * numerator.value / denominator.value,
    nextRow.work + currentRow.work + numerator.work + denominator.work + weight.work + 3,
    nextRow.allocated + currentRow.allocated + numerator.allocated + denominator.allocated +
      weight.allocated + 5⟩

theorem thresholdResource_values (readWeight : ι → ResourceRun ℝ)
    (rows : List (List ℝ)) (r : ℕ) (i : ι) :
    (thresholdResource readWeight rows r i).value =
      tableThreshold (fun j => (readWeight j).value) rows r i := by
  simp only [thresholdResource, resourceListRead_values, tableThreshold, readCell]

theorem thresholdResource_bounds (readWeight : ι → ResourceRun ℝ)
    (rows : List (List ℝ)) (r m W A : ℕ) (i : ι) (hr : r ≤ m)
    (hi : (readWeight i).work ≤ W ∧ (readWeight i).allocated ≤ A) :
    (thresholdResource readWeight rows r i).work ≤ W + 2 * m + 16 ∧
    (thresholdResource readWeight rows r i).allocated ≤ A + 4 * m + 24 := by
  have hw1 := resourceListRead_work_le_index ([] : List ℝ) rows 1
  have hw0 := resourceListRead_work_le_index ([] : List ℝ) rows 0
  have hwn := resourceListRead_work_le_index 0 (resourceListRead [] rows 1).value (r - 1)
  have hwd := resourceListRead_work_le_index 0 (resourceListRead [] rows 0).value r
  have ha1 := resourceListRead_allocated_le_index ([] : List ℝ) rows 1
  have ha0 := resourceListRead_allocated_le_index ([] : List ℝ) rows 0
  have han := resourceListRead_allocated_le_index 0 (resourceListRead [] rows 1).value (r - 1)
  have had := resourceListRead_allocated_le_index 0 (resourceListRead [] rows 0).value r
  simp only [thresholdResource]
  constructor <;> omega

def samplerListResource (readWeight readUniform : ι → ResourceRun ℝ) :
    List ι → ℕ → List (List ℝ) → ResourceRun (List ι)
  | [], _, _ => ⟨[], 1, 1⟩
  | i :: tail, r, rows =>
    if r = 0 then ⟨[], 2, 2⟩ else
    let len := resourceLength (i :: tail)
    if r = len.value then ⟨i :: tail, len.work + 3, len.allocated + 3⟩ else
    let uniform := readUniform i
    let threshold := thresholdResource readWeight rows r i
    if uniform.value ≤ threshold.value then
      let next := samplerListResource readWeight readUniform tail (r - 1) rows.tail
      ⟨i :: next.value, len.work + uniform.work + threshold.work + next.work + 8,
        len.allocated + uniform.allocated + threshold.allocated + next.allocated + 12⟩
    else
      let next := samplerListResource readWeight readUniform tail r rows.tail
      ⟨next.value, len.work + uniform.work + threshold.work + next.work + 8,
        len.allocated + uniform.allocated + threshold.allocated + next.allocated + 12⟩

theorem samplerListResource_values (readWeight readUniform : ι → ResourceRun ℝ)
    (order : List ι) (r : ℕ) (rows : List (List ℝ)) :
    (samplerListResource readWeight readUniform order r rows).value.toFinset =
      (tableSampler (fun i => (readWeight i).value) (fun i => (readUniform i).value)
        order r rows).output := by
  induction order generalizing r rows with
  | nil => rfl
  | cons i tail ih =>
    simp only [samplerListResource, tableSampler, resourceLength_values,
      thresholdResource_values]
    split_ifs <;> simp only [List.toFinset_nil, List.toFinset_cons, ih]

theorem samplerListResource_sublist (readWeight readUniform : ι → ResourceRun ℝ)
    (order : List ι) (r : ℕ) (rows : List (List ℝ)) :
    (samplerListResource readWeight readUniform order r rows).value.Sublist order := by
  induction order generalizing r rows with
  | nil => exact List.Sublist.refl []
  | cons i tail ih =>
    simp only [samplerListResource]
    split_ifs
    · exact List.nil_sublist _
    · exact List.Sublist.refl _
    · exact (ih (r - 1) rows.tail).cons_cons i
    · exact (ih r rows.tail).cons i

theorem samplerListResource_nodup (readWeight readUniform : ι → ResourceRun ℝ)
    (order : List ι) (hn : order.Nodup) (r : ℕ) (rows : List (List ℝ)) :
    (samplerListResource readWeight readUniform order r rows).value.Nodup :=
  (samplerListResource_sublist readWeight readUniform order r rows).nodup hn

theorem samplerListResource_bounds (readWeight readUniform : ι → ResourceRun ℝ)
    (order : List ι) (r : ℕ) (rows : List (List ℝ)) (D m W A U B : ℕ)
    (hD : order.length ≤ D) (hr : r ≤ m)
    (hweight : ∀ i ∈ order, (readWeight i).work ≤ W ∧ (readWeight i).allocated ≤ A)
    (huniform : ∀ i ∈ order, (readUniform i).work ≤ U ∧ (readUniform i).allocated ≤ B) :
    (samplerListResource readWeight readUniform order r rows).work ≤
      1 + order.length * (2 * D + W + U + 2 * m + 30) ∧
    (samplerListResource readWeight readUniform order r rows).allocated ≤
      1 + order.length * (2 * D + A + B + 4 * m + 42) := by
  induction order generalizing r rows with
  | nil => simp [samplerListResource]
  | cons i tail ih =>
    have htailD : tail.length ≤ D := by simpa only [List.length_cons] using
      (Nat.le_trans (Nat.le_succ tail.length) hD)
    have hwi := hweight i (by simp)
    have hui := huniform i (by simp)
    have hwt := fun j hj => hweight j (List.mem_cons_of_mem i hj)
    have hut := fun j hj => huniform j (List.mem_cons_of_mem i hj)
    have ht := thresholdResource_bounds readWeight rows r m W A i hr hwi
    have hl := resourceLength_counts (i :: tail)
    simp only [List.length_cons] at hl hD ⊢
    simp only [samplerListResource]
    split_ifs <;> dsimp only
    · constructor <;> nlinarith only [Nat.zero_le (tail.length * (2 * D + W + U + 2 * m + 30)),
        Nat.zero_le (tail.length * (2 * D + A + B + 4 * m + 42))]
    · constructor <;> nlinarith [hl.1, hl.2]
    · have hn := ih (r - 1) rows.tail htailD (by omega) hwt hut
      constructor <;> nlinarith [hl.1, hl.2, ht.1, ht.2, hn.1, hn.2, hui.1, hui.2]
    · have hn := ih r rows.tail htailD hr hwt hut
      constructor <;> nlinarith [hl.1, hl.2, ht.1, ht.2, hn.1, hn.2, hui.1, hui.2]

end MsetsPaper.Upper.ESPSampling
