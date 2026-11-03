import MsetsPaper.Upper.StorageModel

/-! Operational access/allocation refinement of the ESP inner loops.
The allocation model conservatively retains all temporary scalar results and
recursion-frame slots until this finite ESP call returns. The resulting total
allocation bound can therefore be used by the iteration arena model without
requiring a constant-time list getter or in-place row overwrite.
-/

noncomputable section

namespace MsetsPaper.Upper

def resourceZeros : ℕ → ResourceRun (List ℝ)
  | 0 => ⟨[], 1, 1⟩
  | n + 1 =>
    let tail := resourceZeros n
    ⟨0 :: tail.value, tail.work + 2, tail.allocated + 2⟩

theorem resourceZeros_values (n : ℕ) : (resourceZeros n).value = List.replicate n 0 := by
  induction n <;> simp_all [resourceZeros, List.replicate_succ]

theorem resourceZeros_counts (n : ℕ) :
    (resourceZeros n).work = 2 * n + 1 ∧ (resourceZeros n).allocated = 2 * n + 1 := by
  induction n with
  | zero => simp [resourceZeros]
  | succ n ih => simp only [resourceZeros]; constructor <;> omega

def espInitialResource (m : ℕ) : ResourceRun (List ℝ) :=
  let zeros := resourceZeros m
  ⟨1 :: zeros.value, zeros.work + 1, zeros.allocated + 1⟩

theorem espInitialResource_values (m : ℕ) : (espInitialResource m).value = espInitial m := by
  simp [espInitialResource, resourceZeros_values, espInitial]

theorem espInitialResource_counts (m : ℕ) :
    (espInitialResource m).work = 2 * m + 2 ∧ (espInitialResource m).allocated = 2 * m + 2 := by
  have h := resourceZeros_counts m
  simp only [espInitialResource]
  constructor <;> omega

/-- Two scalar operations, two input constructor reads and one output write
per cell; allocation charges scalar intermediates, list cell and stack slots. -/
def espZipResource (w : ℝ) : List ℝ → List ℝ → ResourceRun (List ℝ)
  | x :: xs, y :: ys =>
    let tail := espZipResource w xs ys
    ⟨(x + w * y) :: tail.value, tail.work + 5, tail.allocated + 7⟩
  | _, _ => ⟨[], 2, 1⟩

theorem espZipResource_values (w : ℝ) (xs ys : List ℝ) :
    (espZipResource w xs ys).value = (espZip w xs ys).1 := by
  induction xs generalizing ys with
  | nil => simp [espZipResource, espZip]
  | cons x xs ih => cases ys <;> simp [espZipResource, espZip, ih]

theorem espZipResource_counts (w : ℝ) (xs ys : List ℝ) :
    (espZipResource w xs ys).work = 5 * min xs.length ys.length + 2 ∧
      (espZipResource w xs ys).allocated = 7 * min xs.length ys.length + 1 := by
  induction xs generalizing ys with
  | nil => simp [espZipResource]
  | cons x xs ih =>
    cases ys with
    | nil => simp [espZipResource]
    | cons y ys =>
      have h := ih ys
      simp only [espZipResource, List.length_cons, min_add_add_right]
      constructor <;> omega

def espStepResource (w : ℝ) : List ℝ → ResourceRun (List ℝ)
  | [] => ⟨[], 1, 1⟩
  | x :: xs =>
    let row := espZipResource w xs (x :: xs)
    ⟨x :: row.value, row.work + 2, row.allocated + 4⟩

theorem espStepResource_values (w : ℝ) (row : List ℝ) :
    (espStepResource w row).value = (espStep w row).1 := by
  cases row <;> simp [espStepResource, espStep, espZipResource_values]

theorem espStepResource_counts (w : ℝ) (row : List ℝ) (m : ℕ) (hlen : row.length = m + 1) :
    (espStepResource w row).work = 5 * m + 4 ∧
      (espStepResource w row).allocated = 7 * m + 5 := by
  cases row with
  | nil => simp at hlen
  | cons x xs =>
    have hx : xs.length = m := by simpa using hlen
    have h := espZipResource_counts w xs (x :: xs)
    simp only [List.length_cons, min_eq_left (Nat.le_succ _), hx] at h
    simp only [espStepResource]
    constructor <;> omega

def espDPResource {ι : Type*} (readWeight : ι → ResourceRun ℝ) (m : ℕ) :
    List ι → ResourceRun (List ℝ)
  | [] => espInitialResource m
  | i :: tail =>
    let previous := espDPResource readWeight m tail
    let weight := readWeight i
    let current := espStepResource weight.value previous.value
    ⟨current.value, previous.work + weight.work + current.work + 2,
      previous.allocated + weight.allocated + current.allocated + 4⟩

theorem espDPResource_values {ι : Type*} (readWeight : ι → ResourceRun ℝ)
    (m : ℕ) (order : List ι) :
    (espDPResource readWeight m order).value =
      (espDP (fun i => (readWeight i).value) m order).1 := by
  induction order with
  | nil => exact espInitialResource_values m
  | cons i tail ih => simp only [espDPResource, ih, espStepResource_values, espDP]

theorem espDPResource_length {ι : Type*} (readWeight : ι → ResourceRun ℝ)
    (m : ℕ) (order : List ι) : (espDPResource readWeight m order).value.length = m + 1 := by
  rw [espDPResource_values, espDP_length]

theorem espDPResource_bounds {ι : Type*} (readWeight : ι → ResourceRun ℝ)
    (m : ℕ) (order : List ι) (W A : ℕ)
    (hread : ∀ i ∈ order, (readWeight i).work ≤ W ∧ (readWeight i).allocated ≤ A) :
    (espDPResource readWeight m order).work ≤ 2 * m + 2 + order.length * (W + 5 * m + 6) ∧
    (espDPResource readWeight m order).allocated ≤ 2 * m + 2 + order.length * (A + 7 * m + 9) := by
  induction order with
  | nil => simpa [espDPResource] using (espInitialResource_counts m).imp le_of_eq le_of_eq
  | cons i tail ih =>
    have hi := hread i (by simp)
    have ht := ih (fun j hj => hread j (by simp [hj]))
    have hs := espStepResource_counts (readWeight i).value
      (espDPResource readWeight m tail).value m (espDPResource_length readWeight m tail)
    simp only [espDPResource, List.length_cons]
    constructor <;> nlinarith [hi.1, hi.2, ht.1, ht.2, hs.1, hs.2]

def espEvaluateResource {ι : Type*} (readWeight : ι → ResourceRun ℝ)
    (order : List ι) (k : ℕ) : ResourceRun ℝ :=
  let row := espDPResource readWeight k order
  let cell := resourceListRead 0 row.value k
  ⟨cell.value, row.work + cell.work, row.allocated + cell.allocated + 2⟩

theorem espEvaluateResource_values {ι : Type*} (readWeight : ι → ResourceRun ℝ)
    (order : List ι) (k : ℕ) :
    (espEvaluateResource readWeight order k).value =
      (espEvaluate (fun i => (readWeight i).value) order k).1 := by
  have hk : k < (espDP (fun i => (readWeight i).value) k order).1.length := by
    rw [espDP_length]
    omega
  simp only [espEvaluateResource, resourceListRead_values, espDPResource_values,
    List.getElem?_eq_getElem hk, Option.getD_some, espEvaluate]

theorem espEvaluateResource_bounds {ι : Type*} (readWeight : ι → ResourceRun ℝ)
    (order : List ι) (k W A : ℕ)
    (hread : ∀ i ∈ order, (readWeight i).work ≤ W ∧ (readWeight i).allocated ≤ A) :
    (espEvaluateResource readWeight order k).work ≤
      3 * k + 5 + order.length * (W + 5 * k + 6) ∧
    (espEvaluateResource readWeight order k).allocated ≤
      4 * k + 9 + order.length * (A + 7 * k + 9) := by
  have hdp := espDPResource_bounds readWeight k order W A hread
  have hr := resourceListRead_bounds 0 (espDPResource readWeight k order).value k
  rw [espDPResource_length] at hr
  simp only [espEvaluateResource]
  constructor <;> omega

/-- Suffix-table preprocessing with every row and record allocation charged.
The head is an alias of the stored first row, never a second DP computation. -/
def espSuffixResource {ι : Type*} (readWeight : ι → ResourceRun ℝ) (m : ℕ) :
    List ι → ResourceRun ESPTable
  | [] =>
    let row := espInitialResource m
    ⟨⟨row.value, [row.value], 0⟩, row.work + 2, row.allocated + 4⟩
  | i :: tail =>
    let previous := espSuffixResource readWeight m tail
    let weight := readWeight i
    let row := espStepResource weight.value previous.value.head
    ⟨⟨row.value, row.value :: previous.value.rows, previous.value.arithmetic + 2 * m⟩,
      previous.work + weight.work + row.work + 5,
      previous.allocated + weight.allocated + row.allocated + 8⟩

theorem espSuffixResource_values {ι : Type*} (readWeight : ι → ResourceRun ℝ)
    (m : ℕ) (order : List ι) :
    (espSuffixResource readWeight m order).value =
      espSuffixTable (fun i => (readWeight i).value) m order := by
  induction order with
  | nil => simp only [espSuffixResource, espInitialResource_values, espSuffixTable]
  | cons i tail ih =>
    simp only [espSuffixResource, ih, espStepResource_values, espSuffixTable]
    congr 2
    rw [espStep_cost, espSuffixTable_head, espDP_length, Nat.add_sub_cancel]

theorem espSuffixResource_head_length {ι : Type*} (readWeight : ι → ResourceRun ℝ)
    (m : ℕ) (order : List ι) :
    (espSuffixResource readWeight m order).value.head.length = m + 1 := by
  rw [espSuffixResource_values, espSuffixTable_head, espDP_length]

theorem espSuffixResource_bounds {ι : Type*} (readWeight : ι → ResourceRun ℝ)
    (m : ℕ) (order : List ι) (W A : ℕ)
    (hread : ∀ i ∈ order, (readWeight i).work ≤ W ∧ (readWeight i).allocated ≤ A) :
    (espSuffixResource readWeight m order).work ≤ 2 * m + 4 + order.length * (W + 5 * m + 9) ∧
    (espSuffixResource readWeight m order).allocated ≤ 2 * m + 6 + order.length * (A + 7 * m + 13) := by
  induction order with
  | nil =>
    have h := espInitialResource_counts m
    simp only [espSuffixResource, List.length_nil, Nat.zero_mul, Nat.add_zero]
    constructor <;> omega
  | cons i tail ih =>
    have hi := hread i (by simp)
    have ht := ih (fun j hj => hread j (by simp [hj]))
    have hs := espStepResource_counts (readWeight i).value
      (espSuffixResource readWeight m tail).value.head m (espSuffixResource_head_length readWeight m tail)
    simp only [espSuffixResource, List.length_cons]
    constructor <;> nlinarith [hi.1, hi.2, ht.1, ht.2, hs.1, hs.2]

variable {d : ℕ}

def resourceCachedWeight (weights : List ℝ) (i : Fin d) : ResourceRun ℝ :=
  resourceListRead 0 weights i.val

theorem resourceCachedWeight_values (weights : List ℝ) (hlen : weights.length = d) (i : Fin d) :
    (resourceCachedWeight weights i).value = cachedRealVector weights hlen i := by
  have hi : i.val < weights.length := by rw [hlen]; exact i.isLt
  simp only [resourceCachedWeight, resourceListRead_values,
    List.getElem?_eq_getElem hi, Option.getD_some, cachedRealVector]

theorem resourceCachedWeight_bounds (weights : List ℝ) (hlen : weights.length = d) (i : Fin d) :
    (resourceCachedWeight weights i).work ≤ d + 2 ∧
      (resourceCachedWeight weights i).allocated ≤ 2 * d + 3 := by
  simpa only [resourceCachedWeight, hlen] using resourceListRead_bounds 0 weights i.val

theorem espEvaluateResource_cached_bounds (weights : List ℝ) (hlen : weights.length = d)
    (order : List (Fin d)) (k : ℕ) (hlenOrder : order.length ≤ d) :
    (espEvaluateResource (resourceCachedWeight weights) order k).work ≤
      3 * k + 5 + d * (d + 5 * k + 8) ∧
    (espEvaluateResource (resourceCachedWeight weights) order k).allocated ≤
      4 * k + 9 + d * (2 * d + 7 * k + 12) := by
  have h := espEvaluateResource_bounds (resourceCachedWeight weights) order k (d + 2) (2 * d + 3)
    (fun i _ => resourceCachedWeight_bounds weights hlen i)
  have hw := Nat.mul_le_mul_right (d + 5 * k + 8) hlenOrder
  have ha := Nat.mul_le_mul_right (2 * d + 7 * k + 12) hlenOrder
  constructor <;> nlinarith [h.1, h.2]

theorem espSuffixResource_cached_bounds (weights : List ℝ) (hlen : weights.length = d) (m : ℕ) :
    (espSuffixResource (resourceCachedWeight weights) m (List.finRange d)).work ≤
      2 * m + 4 + d * (d + 5 * m + 11) ∧
    (espSuffixResource (resourceCachedWeight weights) m (List.finRange d)).allocated ≤
      2 * m + 6 + d * (2 * d + 7 * m + 16) := by
  have h := espSuffixResource_bounds (resourceCachedWeight weights) m (List.finRange d)
    (d + 2) (2 * d + 3) (fun i _ => resourceCachedWeight_bounds weights hlen i)
  simp only [List.length_finRange] at h
  constructor <;> nlinarith [h.1, h.2]

end MsetsPaper.Upper
