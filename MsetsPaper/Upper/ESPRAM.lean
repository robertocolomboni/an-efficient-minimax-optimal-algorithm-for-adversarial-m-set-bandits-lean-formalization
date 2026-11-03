import MsetsPaper.Upper.RAMMemory
import MsetsPaper.Upper.ESPResources
import MsetsPaper.Upper.ResourceCombinators

/-! ESP rows are scanned sequentially; only weights need indexed RAM reads.
Consequently the already operational list-DP has linear dm work and even
TOTAL allocation. This does not assert constant-time List indexing.
-/

noncomputable section

namespace MsetsPaper.Upper.RAMPrograms

variable {d : ℕ}

def espEvaluateRAM (weights : Array ℝ) (order : List (Fin d)) (k : ℕ) : ResourceRun ℝ :=
  espEvaluateResource (fun i => realLoad weights i.val) order k

theorem espEvaluateRAM_values (weights : Array ℝ) (order : List (Fin d)) (k : ℕ) :
    (espEvaluateRAM weights order k).value =
      (espEvaluate (fun i => weights[i.val]?.getD 0) order k).1 := by
  simp only [espEvaluateRAM, espEvaluateResource_values, realLoad_values]

theorem espEvaluateRAM_bounds (weights : Array ℝ) (order : List (Fin d)) (k : ℕ) :
    (espEvaluateRAM weights order k).work ≤ 3 * k + 5 + order.length * (5 * k + 7) ∧
    (espEvaluateRAM weights order k).allocated ≤ 4 * k + 9 + order.length * (7 * k + 10) := by
  have h := espEvaluateResource_bounds (fun i : Fin d => realLoad weights i.val)
    order k 1 1 (fun _ _ => ⟨le_rfl, le_rfl⟩)
  dsimp only [espEvaluateRAM]
  constructor <;> nlinarith [h.1, h.2]

def espSuffixRAM (weights : Array ℝ) (m : ℕ) (order : List (Fin d)) : ResourceRun ESPTable :=
  espSuffixResource (fun i => realLoad weights i.val) m order

theorem espSuffixRAM_values (weights : Array ℝ) (m : ℕ) (order : List (Fin d)) :
    (espSuffixRAM weights m order).value =
      espSuffixTable (fun i => weights[i.val]?.getD 0) m order := by
  simp only [espSuffixRAM, espSuffixResource_values, realLoad_values]

theorem espSuffixRAM_bounds (weights : Array ℝ) (m : ℕ) (order : List (Fin d)) :
    (espSuffixRAM weights m order).work ≤ 2 * m + 4 + order.length * (5 * m + 10) ∧
    (espSuffixRAM weights m order).allocated ≤ 2 * m + 6 + order.length * (7 * m + 14) := by
  have h := espSuffixResource_bounds (fun i : Fin d => realLoad weights i.val) m order
    1 1 (fun _ _ => ⟨le_rfl, le_rfl⟩)
  dsimp only [espSuffixRAM]
  constructor <;> nlinarith [h.1, h.2]

theorem espSuffixRAM_linear (weights : Array ℝ) (m : ℕ) (hd : 1 ≤ d) (hm : 1 ≤ m) :
    (espSuffixRAM weights m (List.finRange d)).work ≤ 30 * d * m ∧
    (espSuffixRAM weights m (List.finRange d)).allocated ≤ 30 * d * m := by
  have h := espSuffixRAM_bounds weights m (List.finRange d)
  simp only [List.length_finRange] at h
  have hdm : d ≤ d * m := by nlinarith
  have hmd : m ≤ d * m := by nlinarith
  constructor <;> nlinarith [h.1, h.2]

/-- A two-comparison deleted list, then a sequential row DP. The list itself
is constructed and charged; the weight-array reads cost one RAM access. -/
def deletedRAM (weights : Array ℝ) (order : List (Fin d)) (k : ℕ) (i j : Fin d) :
    ResourceRun ℝ :=
  let filtered := resourceFilter
    (fun x => (⟨decide (x ≠ i ∧ x ≠ j), 3, 3⟩ : ResourceRun Bool)) order
  let run := espEvaluateRAM weights filtered.value k
  ⟨run.value, filtered.work + run.work + 2, filtered.allocated + run.allocated + 4⟩

theorem deletedRAM_values (weights : Array ℝ) (k : ℕ) (i j : Fin d) :
    (deletedRAM weights (List.finRange d) k i j).value =
      (espEvaluate (fun x : Fin d => weights[x.val]?.getD 0) (espDeletedOrder d {i,j}) k).1 := by
  simp only [deletedRAM, espEvaluateRAM_values, resourceFilter_values, espDeletedOrder]
  congr 2
  apply List.filter_congr
  intro x hx
  simp

theorem deletedRAM_bounds (weights : Array ℝ) (order : List (Fin d)) (k : ℕ) (i j : Fin d) :
    (deletedRAM weights order k i j).work ≤ 3 * k + 8 + order.length * (5 * k + 13) ∧
    (deletedRAM weights order k i j).allocated ≤ 4 * k + 14 + order.length * (7 * k + 16) := by
  let p := fun x => (⟨decide (x ≠ i ∧ x ≠ j), 3, 3⟩ : ResourceRun Bool)
  have hf := resourceFilter_bounds p order 3 3 (fun _ _ => ⟨le_rfl, le_rfl⟩)
  have he := espEvaluateRAM_bounds weights (resourceFilter p order).value k
  have hlen : (resourceFilter p order).value.length ≤ order.length := by
    rw [resourceFilter_values]
    exact List.length_filter_le _ _
  have hw := Nat.mul_le_mul_right (5 * k + 7) hlen
  have ha := Nat.mul_le_mul_right (7 * k + 10) hlen
  dsimp only [deletedRAM]
  dsimp only [p] at hf he hw ha
  constructor <;> nlinarith [hf.1, hf.2, he.1, he.2]

def marginalRAM (weights : Array ℝ) (order : List (Fin d)) (m : ℕ) (Z : ℝ) (i : Fin d) :
    ResourceRun ℝ :=
  let numerator := deletedRAM weights order (m - 1) i i
  let weight := realLoad weights i.val
  ⟨weight.value * numerator.value / Z, numerator.work + weight.work + 3,
    numerator.allocated + weight.allocated + 4⟩

theorem marginalRAM_values (weights : Array ℝ) (m : ℕ) (Z : ℝ) (i : Fin d) :
    (marginalRAM weights (List.finRange d) m Z i).value =
      (espMarginalProgram (fun x => weights[x.val]?.getD 0) m Z i).1 := by
  simp only [marginalRAM, deletedRAM_values, realLoad_values,
    Finset.insert_eq_of_mem (Finset.mem_singleton_self i), espMarginalProgram]

theorem marginalRAM_bounds (weights : Array ℝ) (order : List (Fin d)) (m : ℕ) (Z : ℝ) (i : Fin d) :
    (marginalRAM weights order m Z i).work ≤ 4 * m + 19 + order.length * (7 * m + 16) ∧
    (marginalRAM weights order m Z i).allocated ≤ 4 * m + 19 + order.length * (7 * m + 16) := by
  have hn := deletedRAM_bounds weights order (m - 1) i i
  have hk : m - 1 ≤ m := Nat.sub_le _ _
  have hkm := Nat.mul_le_mul_left order.length hk
  dsimp only [marginalRAM, realLoad]
  constructor <;> nlinarith [hn.1, hn.2]

def pairRAM (weights : Array ℝ) (order : List (Fin d)) (m : ℕ) (Z : ℝ) (i j : Fin d) :
    ResourceRun ℝ :=
  if i = j then
    let run := marginalRAM weights order m Z i
    ⟨run.value, run.work + 1, run.allocated + 1⟩
  else if m < 2 then ⟨0, 2, 2⟩ else
    let numerator := deletedRAM weights order (m - 2) i j
    let wi := realLoad weights i.val
    let wj := realLoad weights j.val
    ⟨wi.value * wj.value * numerator.value / Z,
      numerator.work + wi.work + wj.work + 6,
      numerator.allocated + wi.allocated + wj.allocated + 7⟩

theorem pairRAM_values (weights : Array ℝ) (m : ℕ) (Z : ℝ) (i j : Fin d) :
    (pairRAM weights (List.finRange d) m Z i j).value =
      (espPairProgram (fun x => weights[x.val]?.getD 0) m Z i j).1 := by
  simp only [pairRAM, espPairProgram, marginalRAM_values, deletedRAM_values, realLoad_values]
  split_ifs <;> rfl

theorem pairRAM_bounds (weights : Array ℝ) (order : List (Fin d)) (m : ℕ) (Z : ℝ) (i j : Fin d) :
    (pairRAM weights order m Z i j).work ≤ 4 * m + 23 + order.length * (7 * m + 16) ∧
    (pairRAM weights order m Z i j).allocated ≤ 4 * m + 23 + order.length * (7 * m + 16) := by
  have hm := marginalRAM_bounds weights order m Z i
  have hn := deletedRAM_bounds weights order (m - 2) i j
  have hk : m - 2 ≤ m := Nat.sub_le _ _
  have hkm := Nat.mul_le_mul_left order.length hk
  dsimp only [pairRAM, realLoad]
  split_ifs <;> dsimp only <;> constructor <;> nlinarith [hm.1, hm.2, hn.1, hn.2]

theorem pairRAM_linear (weights : Array ℝ) (m : ℕ) (Z : ℝ) (i j : Fin d)
    (hd : 1 ≤ d) (hm : 1 ≤ m) :
    (pairRAM weights (List.finRange d) m Z i j).work ≤ 50 * d * m ∧
    (pairRAM weights (List.finRange d) m Z i j).allocated ≤ 50 * d * m := by
  have h := pairRAM_bounds weights (List.finRange d) m Z i j
  simp only [List.length_finRange] at h
  have hdm : d ≤ d * m := by nlinarith
  have hmd : m ≤ d * m := by nlinarith
  constructor <;> nlinarith [h.1, h.2]

end MsetsPaper.Upper.RAMPrograms
