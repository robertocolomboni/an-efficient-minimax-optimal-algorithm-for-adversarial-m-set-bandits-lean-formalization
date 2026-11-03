import MsetsPaper.Upper.StoredESPResources
import MsetsPaper.Upper.StoredResourceOperations
import MsetsPaper.Upper.VectorUpdateProgram
import MsetsPaper.Upper.RoundRAMPreparation

/-! # Materialized moment preparation and observable feedback vectors

The program ranges over coordinates, never over the set of actions. The
partition denominator is computed once. The diagonal of the resulting
second-moment matrix supplies the marginal vector without additional ESP
computations. All list accesses and construction loops are charged.
-/

namespace MsetsPaper.Upper.RoundProgram

open SchurSolver ResourcePrograms ESPSampling
open MsetsLower MsetsLower.History Matrix

noncomputable section

variable {d m : ℕ}

def diagonalResource (A : StoredMatrix d) : ResourceRun (StoredVector d) :=
  vectorProgram (fun i => resourceMatrixRead A i i)

theorem diagonalResource_values (A : StoredMatrix d) :
    storedVector (diagonalResource A).value = fun i => storedMatrix A i i := by
  simp only [diagonalResource, vectorProgram_values, resourceMatrixRead_values]

theorem diagonalResource_bounds (A : StoredMatrix d) :
    (diagonalResource A).work ≤ (2 * d + 6) * d + 2 ∧
    (diagonalResource A).allocated ≤ (4 * d + 10) * d + 2 :=
  vectorProgram_bounds _ _ _ (fun i => resourceMatrixRead_bounds A i i)

def prepareMomentsResource (theta : StoredVector d) (m : ℕ) :
    ResourceRun (StoredMatrix d × StoredVector d) :=
  let moments := momentsStoredRAM theta m
  let marginals := diagonalResource moments.value
  ⟨(moments.value, marginals.value),
    moments.work + marginals.work + 2,
    moments.allocated + marginals.allocated + 2⟩

theorem prepareMomentsResource_matrix (theta : StoredVector d) (hm : 1 ≤ m) :
    storedMatrix (prepareMomentsResource theta m).value.1 =
      secondMoment (weightedLaw (m := m) (storedVector theta)) := by
  exact momentsStoredRAM_values theta hm

theorem prepareMomentsResource_marginal (theta : StoredVector d) (hm : 1 ≤ m) :
    storedVector (prepareMomentsResource theta m).value.2 =
      weightedMarginal (m := m) (storedVector theta) := by
  change storedVector (diagonalResource _).value = _
  rw [diagonalResource_values]
  change (fun i => storedMatrix (prepareMomentsResource theta m).value.1 i i) = _
  rw [prepareMomentsResource_matrix theta hm]
  funext i
  exact secondMoment_diagonal_eq_marginal (storedVector theta) i

/-- A single conservative polynomial bounds both the counted work and all
temporary allocations. It is independent of the horizon and learning rate. -/
theorem prepareMomentsResource_bounds (theta : StoredVector d) (m : ℕ) :
    (prepareMomentsResource theta m).work ≤ 200 * (d + m + 1)^4 ∧
    (prepareMomentsResource theta m).allocated ≤ 200 * (d + m + 1)^4 := by
  have hM := momentsStoredRAM_bounds theta m
  have hmu := diagonalResource_bounds (momentsStoredRAM theta m).value
  have hp : 150 * (d + m + 1)^4 +
      ((4 * d + 10) * d + 2) + 2 ≤ 200 * (d + m + 1)^4 := by
    ring_nf
    omega
  dsimp only [prepareMomentsResource]
  constructor <;> nlinarith [hM.1, hM.2, hmu.1, hmu.2]

/-- The same moment preparation used by the full round has the paper's
O(d^3 m) running time, including input/output copies and diagonal extraction. -/
theorem prepareMomentsResource_cubic (theta : StoredVector d)
    (hd : 1 ≤ d) (hm : 1 ≤ m) :
    (prepareMomentsResource theta m).work ≤ 550 * d^3*m := by
  have hM := momentsStoredRAM_cubic theta hd hm
  have hmu := (diagonalResource_bounds (momentsStoredRAM theta m).value).1
  have hd2 : d ≤ d*d := by nlinarith
  have hd3 : d*d ≤ d^3 := by nlinarith [Nat.mul_le_mul_left (d*d) hd]
  have hb : d*d ≤ d^3*m := hd3.trans (by simpa using Nat.mul_le_mul_left (d^3) hm)
  have hone : 1 ≤ d^3*m := hd.trans (hd2.trans hb)
  dsimp only [prepareMomentsResource]
  nlinarith

/-- Explicit finite-list membership, charging each comparison and branch.
This is used to form the feedback vector from the sampled coordinate list. -/
def containsResource (i : Fin d) : List (Fin d) → ResourceRun Bool
  | [] => ⟨false, 1, 1⟩
  | j :: js =>
    if i = j then ⟨true, 2, 1⟩ else
      let tail := containsResource i js
      ⟨tail.value, tail.work + 2, tail.allocated + 2⟩

theorem containsResource_values (i : Fin d) (xs : List (Fin d)) :
    (containsResource i xs).value = decide (i ∈ xs) := by
  induction xs with
  | nil => simp [containsResource]
  | cons j js ih => by_cases h : i = j <;> simp [containsResource, h, ih]

theorem containsResource_bounds (i : Fin d) (xs : List (Fin d)) :
    (containsResource i xs).work ≤ 2 * xs.length + 1 ∧
    (containsResource i xs).allocated ≤ 2 * xs.length + 1 := by
  induction xs with
  | nil => simp [containsResource]
  | cons j js ih =>
    by_cases h : i = j <;> simp only [containsResource, h, if_true, if_false,
      List.length_cons] <;> constructor <;> omega

def feedbackCellResource (xs : List (Fin d)) (Y : ℝ) (i : Fin d) : ResourceRun ℝ :=
  let present := containsResource i xs
  ⟨if present.value then Y else 0, present.work + 1, present.allocated + 1⟩

def feedbackResource (xs : List (Fin d)) (Y : ℝ) : ResourceRun (StoredVector d) :=
  vectorProgram (feedbackCellResource xs Y)

theorem feedbackResource_values (xs : List (Fin d)) (Y : ℝ) :
    storedVector (feedbackResource xs Y).value = fun i => if i ∈ xs then Y else 0 := by
  simp [feedbackResource, vectorProgram_values, feedbackCellResource,
    containsResource_values]

theorem feedbackResource_action (xs : List (Fin d)) (a : Action d m) (Y : ℝ)
    (ha : xs.toFinset = a.1) :
    storedVector (feedbackResource xs Y).value =
      Y • (fun i => selectedIndicator i a) := by
  rw [feedbackResource_values]
  ext i
  have hi : i ∈ xs ↔ i ∈ a.1 := by rw [← ha]; simp
  simp [selectedIndicator, hi]

theorem feedbackResource_bounds (xs : List (Fin d)) (Y : ℝ) :
    (feedbackResource xs Y).work ≤ (2 * xs.length + 4) * d + 2 ∧
    (feedbackResource xs Y).allocated ≤ (2 * xs.length + 6) * d + 2 := by
  apply vectorProgram_bounds _ (2 * xs.length + 2) (2 * xs.length + 2)
  intro i
  have h := containsResource_bounds i xs
  dsimp only [feedbackCellResource]
  constructor <;> omega

end

end MsetsPaper.Upper.RoundProgram
