import MsetsPaper.Upper.StoredResourceOperations
import MsetsPaper.Upper.StoredESPResources
import MsetsPaper.Upper.ProjectionOracleProgram

noncomputable section
open scoped BigOperators

namespace MsetsPaper.Upper.ResourcePrograms

open SchurSolver (StoredVector storedVector resourceVectorRead resourceVectorRead_values
  resourceVectorRead_bounds)

variable {d m : ℕ}

def weightsCell (theta v : StoredVector d) (i : Fin d) : ResourceRun ℝ :=
  let a := resourceVectorRead theta i
  let b := resourceVectorRead v i
  ⟨Real.exp (a.value + b.value), a.work + b.work + 2, a.allocated + b.allocated + 2⟩

theorem weightsCell_values (theta v : StoredVector d) (i : Fin d) :
    (weightsCell theta v i).value = Real.exp (storedVector theta i + storedVector v i) := by
  simp only [weightsCell, resourceVectorRead_values]

theorem weightsCell_bounds (theta v : StoredVector d) (i : Fin d) :
    (weightsCell theta v i).work ≤ 2 * d + 6 ∧
      (weightsCell theta v i).allocated ≤ 4 * d + 8 := by
  have ha := resourceVectorRead_bounds theta i
  have hb := resourceVectorRead_bounds v i
  dsimp only [weightsCell]
  constructor <;> omega

def weightsResource (theta v : StoredVector d) : ResourceRun (StoredVector d) :=
  vectorProgram (weightsCell theta v)

theorem weightsResource_values (theta v : StoredVector d) :
    storedVector (weightsResource theta v).value =
      fun i => Real.exp (storedVector theta i + storedVector v i) := by
  simp only [weightsResource, vectorProgram_values, weightsCell_values]

theorem weightsResource_bounds (theta v : StoredVector d) (m : ℕ) :
    (weightsResource theta v).work ≤ 100 * (d + m + 1) ^ 2 ∧
      (weightsResource theta v).allocated ≤ 100 * (d + m + 1) ^ 2 := by
  have h := vectorProgram_bounds (weightsCell theta v) (2 * d + 6) (4 * d + 8)
    (weightsCell_bounds theta v)
  dsimp only [weightsResource]
  constructor <;> nlinarith [h.1, h.2, Nat.zero_le (d * m), Nat.zero_le (m ^ 2)]

theorem partitionResource_common_bounds (weights : StoredVector d) (m : ℕ) :
    (partitionResource weights m).work ≤ 100 * (d + m + 1) ^ 2 ∧
      (partitionResource weights m).allocated ≤ 100 * (d + m + 1) ^ 2 := by
  have h := partitionResource_bounds weights m
  constructor <;> nlinarith [h.1, h.2]

def absCell (v : StoredVector d) (i : Fin d) : ResourceRun ℝ :=
  let x := resourceVectorRead v i
  ⟨if x.value < 0 then -x.value else x.value, x.work + 2, x.allocated + 2⟩

theorem absCell_values (v : StoredVector d) (i : Fin d) :
    (absCell v i).value = |storedVector v i| := by
  simp only [absCell, resourceVectorRead_values]
  split_ifs with h
  · exact (abs_of_neg h).symm
  · exact (abs_of_nonneg (le_of_not_gt h)).symm

theorem absCell_bounds (v : StoredVector d) (i : Fin d) :
    (absCell v i).work ≤ d + 4 ∧ (absCell v i).allocated ≤ 2 * d + 5 := by
  have h := resourceVectorRead_bounds v i
  dsimp only [absCell]
  constructor <;> omega

def normResource (v : StoredVector d) : ResourceRun ℝ := sumProgram (absCell v)

theorem normResource_values (v : StoredVector d) :
    (normResource v).value = coordinateL1 (storedVector v) := by
  simp only [normResource, sumProgram_values, absCell_values, coordinateL1]

theorem normResource_bounds (v : StoredVector d) (m : ℕ) :
    (normResource v).work ≤ 100 * (d + m + 1) ^ 2 ∧
      (normResource v).allocated ≤ 100 * (d + m + 1) ^ 2 := by
  have h := sumProgram_bounds (absCell v) (d + 4) (2 * d + 5) (absCell_bounds v)
  dsimp only [normResource]
  constructor <;> nlinarith [h.1, h.2, Nat.zero_le (d * m), Nat.zero_le (m ^ 2)]

def signCell (v : StoredVector d) (i : Fin d) : ResourceRun ℝ :=
  let x := resourceVectorRead v i
  ⟨if 0 ≤ x.value then 1 else -1, x.work + 1, x.allocated + 1⟩

def signResource (v : StoredVector d) : ResourceRun (StoredVector d) := vectorProgram (signCell v)

theorem signResource_values (v : StoredVector d) :
    storedVector (signResource v).value = l1Separator (storedVector v) := by
  simp only [signResource, vectorProgram_values, signCell, resourceVectorRead_values, l1Separator]
  rfl

theorem signResource_bounds (v : StoredVector d) (m : ℕ) :
    (signResource v).work ≤ 100 * (d + m + 1) ^ 2 ∧
      (signResource v).allocated ≤ 100 * (d + m + 1) ^ 2 := by
  have hc (i : Fin d) : (signCell v i).work ≤ d + 3 ∧
      (signCell v i).allocated ≤ 2 * d + 4 := by
    have h := resourceVectorRead_bounds v i
    dsimp only [signCell]
    constructor <;> omega
  have h := vectorProgram_bounds (signCell v) (d + 3) (2 * d + 4) hc
  dsimp only [signResource]
  constructor <;> nlinarith [h.1, h.2, Nat.zero_le (d * m), Nat.zero_le (m ^ 2)]

def gradientCellResource (weights a b v : StoredVector d) (m : ℕ) (Z : ℝ)
    (i : Fin d) : ResourceRun ℝ :=
  let mu := marginalResource weights m Z i
  let av := resourceVectorRead a i
  let bv := resourceVectorRead b i
  let vv := resourceVectorRead v i
  let result := if 0 < vv.value then mu.value - av.value else
    if vv.value < 0 then mu.value - bv.value else mu.value - (av.value + bv.value) / 2
  ⟨result, mu.work + av.work + bv.work + vv.work + 5,
    mu.allocated + av.allocated + bv.allocated + vv.allocated + 5⟩

theorem gradientCellResource_values (weights a b v : StoredVector d) (m : ℕ) (Z : ℝ)
    (i : Fin d) :
    (gradientCellResource weights a b v m Z i).value =
      (projectionGradientCellProgram (storedVector weights) m Z
        (storedVector a) (storedVector b) (storedVector v) i).1 := by
  simp only [gradientCellResource, marginalResource_values, resourceVectorRead_values,
    projectionGradientCellProgram]
  split_ifs <;> rfl

def gradientCellBudget (d m : ℕ) : ℕ := 100 * (d + m + 1) ^ 2 + 6 * d + 20

theorem gradientCellResource_bounds (weights a b v : StoredVector d) (m : ℕ) (Z : ℝ)
    (i : Fin d) :
    (gradientCellResource weights a b v m Z i).work ≤ gradientCellBudget d m ∧
      (gradientCellResource weights a b v m Z i).allocated ≤ gradientCellBudget d m := by
  have hmu := marginalResource_bounds weights m Z i
  have ha := resourceVectorRead_bounds a i
  have hb := resourceVectorRead_bounds b i
  have hv := resourceVectorRead_bounds v i
  dsimp only [gradientCellResource, gradientCellBudget]
  constructor <;> omega

def gradientResource (theta a b v : StoredVector d) (m : ℕ) : ResourceRun (StoredVector d) :=
  let weights := weightsResource theta v
  let denominator := partitionResource weights.value m
  let cells := vectorProgram (gradientCellResource weights.value a b v m denominator.value)
  ⟨cells.value, weights.work + denominator.work + cells.work + 3,
    weights.allocated + denominator.allocated + cells.allocated + 5⟩

theorem gradientResource_values (theta a b v : StoredVector d) (hm : 1 ≤ m) :
    storedVector (gradientResource theta a b v m).value =
      projectionSubgradient (m := m) (storedVector theta) (storedVector a)
        (storedVector b) (storedVector v) := by
  simp only [gradientResource, vectorProgram_values, gradientCellResource_values,
    partitionResource_values, weightsResource_values]
  have hZ := espPartitionProgram_correct (storedVector theta + storedVector v) m
  simp only [Pi.add_apply] at hZ
  rw [hZ]
  funext i
  exact projectionGradientCellProgram_values _ _ _ _ hm i

def gradientBudget (d m : ℕ) : ℕ :=
  200 * (d + m + 1) ^ 2 + (gradientCellBudget d m + 4) * d + 20

theorem gradientResource_bounds (theta a b v : StoredVector d) (m : ℕ) :
    (gradientResource theta a b v m).work ≤ gradientBudget d m ∧
      (gradientResource theta a b v m).allocated ≤ gradientBudget d m := by
  let weights := (weightsResource theta v).value
  let Z := (partitionResource weights m).value
  have hw := weightsResource_bounds theta v m
  have hz := partitionResource_common_bounds weights m
  have hc := vectorProgram_bounds (gradientCellResource weights a b v m Z)
    (gradientCellBudget d m) (gradientCellBudget d m)
    (gradientCellResource_bounds weights a b v m Z)
  dsimp only [gradientResource, gradientBudget]
  dsimp only [weights, Z] at hz hc
  constructor <;> nlinarith [hw.1, hw.2, hz.1, hz.2, hc.1, hc.2]

def penaltyCellResource (a b v : StoredVector d) (i : Fin d) : ResourceRun ℝ :=
  let av := resourceVectorRead a i
  let bv := resourceVectorRead b i
  let vv := resourceVectorRead v i
  ⟨-av.value * max vv.value 0 + bv.value * max (-vv.value) 0,
    av.work + bv.work + vv.work + 7, av.allocated + bv.allocated + vv.allocated + 7⟩

theorem penaltyCellResource_bounds (a b v : StoredVector d) (i : Fin d) :
    (penaltyCellResource a b v i).work ≤ 3 * d + 13 ∧
      (penaltyCellResource a b v i).allocated ≤ 6 * d + 16 := by
  have ha := resourceVectorRead_bounds a i
  have hb := resourceVectorRead_bounds b i
  have hv := resourceVectorRead_bounds v i
  dsimp only [penaltyCellResource]
  constructor <;> omega

def penaltyResource (a b v : StoredVector d) : ResourceRun ℝ :=
  sumProgram (penaltyCellResource a b v)

theorem penaltyResource_values (a b v : StoredVector d) :
    (penaltyResource a b v).value = projectionPenalty (storedVector a) (storedVector b)
      (storedVector v) := by
  simp only [penaltyResource, sumProgram_values, penaltyCellResource,
    resourceVectorRead_values, projectionPenalty]

theorem penaltyResource_bounds (a b v : StoredVector d) (m : ℕ) :
    (penaltyResource a b v).work ≤ 100 * (d + m + 1) ^ 2 ∧
      (penaltyResource a b v).allocated ≤ 100 * (d + m + 1) ^ 2 := by
  have h := sumProgram_bounds (penaltyCellResource a b v) (3 * d + 13) (6 * d + 16)
    (penaltyCellResource_bounds a b v)
  dsimp only [penaltyResource]
  constructor <;> nlinarith [h.1, h.2, Nat.zero_le (d * m), Nat.zero_le (m ^ 2)]

def valueResource (theta a b v : StoredVector d) (m : ℕ) : ResourceRun ℝ :=
  let weights := weightsResource theta v
  let denominator := partitionResource weights.value m
  let penalty := penaltyResource a b v
  ⟨Real.log denominator.value + penalty.value,
    weights.work + denominator.work + penalty.work + 4,
    weights.allocated + denominator.allocated + penalty.allocated + 6⟩

theorem valueResource_values (theta a b v : StoredVector d) (m : ℕ) :
    (valueResource theta a b v m).value = projectionDual (m := m) (storedVector theta)
      (storedVector a) (storedVector b) (storedVector v) := by
  simp only [valueResource, partitionResource_values, weightsResource_values,
    penaltyResource_values, projectionDual, logPartition]
  have hZ := espPartitionProgram_correct (storedVector theta + storedVector v) m
  simp only [Pi.add_apply] at hZ
  rw [hZ]

theorem valueResource_bounds (theta a b v : StoredVector d) (m : ℕ) :
    (valueResource theta a b v m).work ≤ 300 * (d + m + 1) ^ 2 + 10 ∧
      (valueResource theta a b v m).allocated ≤ 300 * (d + m + 1) ^ 2 + 10 := by
  have hw := weightsResource_bounds theta v m
  have hz := partitionResource_common_bounds (weightsResource theta v).value m
  have hp := penaltyResource_bounds a b v m
  dsimp only [valueResource]
  constructor <;> omega

def cutResource (theta a b v : StoredVector d) (m : ℕ) (R : ℝ) : ResourceRun (StoredVector d) :=
  let norm := normResource v
  if norm.value ≤ R then
    let grad := gradientResource theta a b v m
    ⟨grad.value, norm.work + grad.work + 1, norm.allocated + grad.allocated + 2⟩
  else
    let sign := signResource v
    ⟨sign.value, norm.work + sign.work + 1, norm.allocated + sign.allocated + 2⟩

theorem cutResource_values (theta a b v : StoredVector d) (hm : 1 ≤ m) (R : ℝ) :
    storedVector (cutResource theta a b v m R).value =
      projectionEllipsoidOracle (m := m) (storedVector theta) (storedVector a)
        (storedVector b) R (storedVector v) := by
  simp only [cutResource, normResource_values, projectionEllipsoidOracle]
  split_ifs <;> simp only [gradientResource_values theta a b v hm, signResource_values]

def cutBudget (d m : ℕ) : ℕ := 100 * (d + m + 1) ^ 2 + gradientBudget d m + 2

theorem cutResource_bounds (theta a b v : StoredVector d) (m : ℕ) (R : ℝ) :
    (cutResource theta a b v m R).work ≤ cutBudget d m ∧
      (cutResource theta a b v m R).allocated ≤ cutBudget d m := by
  have hn := normResource_bounds v m
  have hg := gradientResource_bounds theta a b v m
  have hs := signResource_bounds v m
  dsimp only [cutResource, cutBudget]
  split_ifs <;> dsimp only <;> constructor <;> unfold gradientBudget at * <;> omega

def retainResource (theta a b candidate best : StoredVector d) (m : ℕ) (R : ℝ) :
    ResourceRun (StoredVector d) :=
  let norm := normResource candidate
  if norm.value ≤ R then
    let cv := valueResource theta a b candidate m
    let bv := valueResource theta a b best m
    ⟨if cv.value ≤ bv.value then candidate else best,
      norm.work + cv.work + bv.work + 2, norm.allocated + cv.allocated + bv.allocated + 3⟩
  else ⟨best, norm.work + 1, norm.allocated + 1⟩

theorem retainResource_values (theta a b candidate best : StoredVector d) (m : ℕ) (R : ℝ) :
    storedVector (retainResource theta a b candidate best m R).value =
      projectionRetainBest (m := m) (storedVector theta) (storedVector a) (storedVector b)
        R (storedVector candidate) (storedVector best) := by
  simp only [retainResource, normResource_values, valueResource_values, projectionRetainBest]
  split_ifs <;> simp_all

theorem retainResource_bounds (theta a b candidate best : StoredVector d) (m : ℕ) (R : ℝ) :
    (retainResource theta a b candidate best m R).work ≤ 700 * (d + m + 1) ^ 2 + 30 ∧
      (retainResource theta a b candidate best m R).allocated ≤ 700 * (d + m + 1) ^ 2 + 30 := by
  have hn := normResource_bounds candidate m
  have hc := valueResource_bounds theta a b candidate m
  have hb := valueResource_bounds theta a b best m
  dsimp only [retainResource]
  split_ifs <;> dsimp only <;> constructor <;> omega

end MsetsPaper.Upper.ResourcePrograms
