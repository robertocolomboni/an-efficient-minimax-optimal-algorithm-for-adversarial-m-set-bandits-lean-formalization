import MsetsPaper.Upper.SamplerStoredProgram

noncomputable section

namespace MsetsPaper.Upper.ResourcePrograms

open SchurSolver (StoredVector storedVector resourceVectorRead resourceVectorRead_values
  resourceVectorRead_bounds)
open ESPSampling (samplerOrderResource samplerOrderResource_values samplerOrderResource_bounds)

variable {d : ℕ}

def partitionResource (weights : StoredVector d) (m : ℕ) : ResourceRun ℝ :=
  let order := samplerOrderResource d
  let run := espEvaluateResource (resourceVectorRead weights) order.value m
  ⟨run.value, order.work + run.work + 2, order.allocated + run.allocated + 4⟩

theorem partitionResource_values (weights : StoredVector d) (m : ℕ) :
    (partitionResource weights m).value = (espPartitionProgram (storedVector weights) m).1 := by
  simp only [partitionResource, samplerOrderResource_values, espEvaluateResource_values,
    resourceVectorRead_values, espPartitionProgram]

theorem partitionResource_bounds (weights : StoredVector d) (m : ℕ) :
    (partitionResource weights m).work ≤ 3 * m + 8 + d * (d + 5 * m + 11) ∧
    (partitionResource weights m).allocated ≤ 4 * m + 14 + d * (2 * d + 7 * m + 17) := by
  have ho := samplerOrderResource_bounds d
  have he := espEvaluateResource_bounds (resourceVectorRead weights)
    (samplerOrderResource d).value m (d + 2) (2 * d + 3)
    (fun i _ => resourceVectorRead_bounds weights i)
  have hlen : (samplerOrderResource d).value.length = d := by
    simp [samplerOrderResource_values]
  rw [hlen] at he
  dsimp only [partitionResource]
  constructor <;> nlinarith [ho.1, ho.2, he.1, he.2]

/-- Two explicit index comparisons and their conjunction. Taking i=j also
implements a single-coordinate deletion, with the same conservative charge. -/
def deletedResource (weights : StoredVector d) (k : ℕ) (i j : Fin d) : ResourceRun ℝ :=
  let order := samplerOrderResource d
  let filtered := resourceFilter
    (fun x => (⟨decide (x ≠ i ∧ x ≠ j), 3, 3⟩ : ResourceRun Bool)) order.value
  let run := espEvaluateResource (resourceVectorRead weights) filtered.value k
  ⟨run.value, order.work + filtered.work + run.work + 2,
    order.allocated + filtered.allocated + run.allocated + 4⟩

theorem deletedResource_values (weights : StoredVector d) (k : ℕ) (i j : Fin d) :
    (deletedResource weights k i j).value =
      (espEvaluate (storedVector weights) (espDeletedOrder d {i, j}) k).1 := by
  simp only [deletedResource, samplerOrderResource_values, resourceFilter_values,
    espEvaluateResource_values, resourceVectorRead_values, espDeletedOrder]
  congr 2
  apply List.filter_congr
  intro x hx
  simp

theorem deletedResource_bounds (weights : StoredVector d) (k : ℕ) (i j : Fin d) :
    (deletedResource weights k i j).work ≤ 3 * k + 9 + d * (d + 5 * k + 17) ∧
    (deletedResource weights k i j).allocated ≤ 4 * k + 15 + d * (2 * d + 7 * k + 23) := by
  let order := (samplerOrderResource d).value
  let predicate := fun x => (⟨decide (x ≠ i ∧ x ≠ j), 3, 3⟩ : ResourceRun Bool)
  have ho := samplerOrderResource_bounds d
  have hf := resourceFilter_bounds predicate order 3 3 (fun _ _ => ⟨le_rfl, le_rfl⟩)
  have he := espEvaluateResource_bounds (resourceVectorRead weights)
    (resourceFilter predicate order).value k (d + 2) (2 * d + 3)
    (fun x _ => resourceVectorRead_bounds weights x)
  have horder : order.length = d := by simp [order, samplerOrderResource_values]
  have hfiltered : (resourceFilter predicate order).value.length ≤ d := by
    rw [resourceFilter_values]
    exact (List.length_filter_le _ _).trans horder.le
  rw [horder] at hf
  have hw := Nat.mul_le_mul_right (d + 2 + 5 * k + 6) hfiltered
  have ha := Nat.mul_le_mul_right (2 * d + 3 + 7 * k + 9) hfiltered
  dsimp only [deletedResource]
  change _ ≤ _ ∧ _ ≤ _
  dsimp only [predicate, order] at he hf hw ha
  constructor <;> nlinarith [ho.1, ho.2, hf.1, hf.2, he.1, he.2]

def marginalResource (weights : StoredVector d) (m : ℕ) (Z : ℝ) (i : Fin d) : ResourceRun ℝ :=
  let numerator := deletedResource weights (m - 1) i i
  let weight := resourceVectorRead weights i
  ⟨weight.value * numerator.value / Z, numerator.work + weight.work + 2,
    numerator.allocated + weight.allocated + 4⟩

theorem marginalResource_values (weights : StoredVector d) (m : ℕ) (Z : ℝ) (i : Fin d) :
    (marginalResource weights m Z i).value = (espMarginalProgram (storedVector weights) m Z i).1 := by
  simp only [marginalResource, deletedResource_values, resourceVectorRead_values,
    Finset.insert_eq_of_mem (Finset.mem_singleton_self i), espMarginalProgram]

theorem marginalResource_bounds (weights : StoredVector d) (m : ℕ) (Z : ℝ) (i : Fin d) :
    (marginalResource weights m Z i).work ≤ 100 * (d + m + 1) ^ 2 ∧
    (marginalResource weights m Z i).allocated ≤ 100 * (d + m + 1) ^ 2 := by
  have hn := deletedResource_bounds weights (m - 1) i i
  have hw := resourceVectorRead_bounds weights i
  have hk : m - 1 ≤ m := Nat.sub_le _ _
  have hkm := Nat.mul_le_mul_left d hk
  dsimp only [marginalResource]
  constructor <;> nlinarith [hn.1, hn.2, hw.1, hw.2]

def pairResource (weights : StoredVector d) (m : ℕ) (Z : ℝ) (i j : Fin d) : ResourceRun ℝ :=
  if i = j then
    let run := marginalResource weights m Z i
    ⟨run.value, run.work + 1, run.allocated + 1⟩
  else if m < 2 then ⟨0, 2, 2⟩ else
    let numerator := deletedResource weights (m - 2) i j
    let wi := resourceVectorRead weights i
    let wj := resourceVectorRead weights j
    ⟨wi.value * wj.value * numerator.value / Z,
      numerator.work + wi.work + wj.work + 5,
      numerator.allocated + wi.allocated + wj.allocated + 7⟩

theorem pairResource_values (weights : StoredVector d) (m : ℕ) (Z : ℝ) (i j : Fin d) :
    (pairResource weights m Z i j).value = (espPairProgram (storedVector weights) m Z i j).1 := by
  simp only [pairResource, espPairProgram, marginalResource_values,
    deletedResource_values, resourceVectorRead_values]
  split_ifs <;> rfl

theorem pairResource_bounds (weights : StoredVector d) (m : ℕ) (Z : ℝ) (i j : Fin d) :
    (pairResource weights m Z i j).work ≤ 101 * (d + m + 1) ^ 2 ∧
    (pairResource weights m Z i j).allocated ≤ 101 * (d + m + 1) ^ 2 := by
  have hm := marginalResource_bounds weights m Z i
  have hn := deletedResource_bounds weights (m - 2) i j
  have hi := resourceVectorRead_bounds weights i
  have hj := resourceVectorRead_bounds weights j
  have hk : m - 2 ≤ m := Nat.sub_le _ _
  have hkm := Nat.mul_le_mul_left d hk
  dsimp only [pairResource]
  split_ifs <;> dsimp only <;> constructor <;>
    nlinarith [hm.1, hm.2, hn.1, hn.2, hi.1, hi.2, hj.1, hj.2]

end MsetsPaper.Upper.ResourcePrograms
