import MsetsPaper.Upper.ESPMoments
import Mathlib.Data.List.ProdSigma

/-!
# Concrete deletion-DP algorithms for partition and second moments

Weights are the arithmetic-program inputs. Their conversion from the paper's
parameters is `w i = exp(theta i)`. All counters below count real arithmetic,
not the bit complexity of representing arbitrary real inputs.
-/

noncomputable section
open scoped BigOperators

namespace MsetsPaper.Upper

variable {d m : ℕ}

def espDeletedOrder (d : ℕ) (J : Finset (Fin d)) : List (Fin d) :=
  (List.finRange d).filter (fun i => i ∉ J)

theorem espDeletedOrder_nodup (d : ℕ) (J : Finset (Fin d)) :
    (espDeletedOrder d J).Nodup := (List.nodup_finRange d).filter _

theorem espDeletedOrder_toFinset (d : ℕ) (J : Finset (Fin d)) :
    (espDeletedOrder d J).toFinset = Finset.univ \ J := by
  ext i
  simp [espDeletedOrder]

theorem espDeletedOrder_length (d : ℕ) (J : Finset (Fin d)) :
    (espDeletedOrder d J).length ≤ d := by
  simpa [espDeletedOrder] using
    List.length_filter_le (fun i : Fin d => decide (i ∉ J)) (List.finRange d)

def espPartitionProgram (w : Fin d → ℝ) (m : ℕ) : ℝ × ℕ :=
  espEvaluate w (List.finRange d) m

theorem espPartitionProgram_correct (theta : Fin d → ℝ) (m : ℕ) :
    (espPartitionProgram (fun i => Real.exp (theta i)) m).1 = partition (m := m) theta := by
  rw [espPartitionProgram, espEvaluate_correct _ _ (List.nodup_finRange d),
    List.toFinset_finRange, partition_eq_esp]

theorem espPartitionProgram_cost (w : Fin d → ℝ) (m : ℕ) :
    (espPartitionProgram w m).2 = 2 * m * d := by
  simp [espPartitionProgram, espEvaluate_cost]

theorem log_partition_computed (theta : Fin d → ℝ) (m : ℕ) :
    Real.log (espPartitionProgram (fun i => Real.exp (theta i)) m).1 =
      Real.log (partition (m := m) theta) := by rw [espPartitionProgram_correct]

/-- Given the already computed normalizer, evaluate one deleted coefficient,
then execute one multiplication and one division. -/
def espMarginalProgram (w : Fin d → ℝ) (m : ℕ) (Z : ℝ) (i : Fin d) : ℝ × ℕ :=
  let numerator := espEvaluate w (espDeletedOrder d {i}) (m - 1)
  (w i * numerator.1 / Z, numerator.2 + 2)

theorem espMarginalProgram_correct (theta : Fin d → ℝ) (hm : 1 ≤ m) (i : Fin d) :
    (espMarginalProgram (fun j => Real.exp (theta j)) m (partition (m := m) theta) i).1 =
      weightedMarginal (m := m) theta i := by
  simp only [espMarginalProgram, espEvaluate_correct _ _ (espDeletedOrder_nodup _ _),
    espDeletedOrder_toFinset, Finset.sdiff_singleton_eq_erase]
  exact (weightedMarginal_eq_esp theta hm i).symm

theorem espMarginalProgram_cost_le (w : Fin d → ℝ) (m : ℕ) (Z : ℝ) (i : Fin d) :
    (espMarginalProgram w m Z i).2 ≤ 2 * m * d + 2 := by
  simp only [espMarginalProgram, espEvaluate_cost]
  exact Nat.add_le_add_right
    (Nat.mul_le_mul (Nat.mul_le_mul_left 2 (Nat.sub_le _ _))
      (espDeletedOrder_length d {i})) 2

/-- Actual pairwise-moment code. Rank one returns zero off the diagonal. -/
def espPairProgram (w : Fin d → ℝ) (m : ℕ) (Z : ℝ) (i j : Fin d) : ℝ × ℕ :=
  if i = j then espMarginalProgram w m Z i
  else if m < 2 then (0, 0)
  else
    let numerator := espEvaluate w (espDeletedOrder d {i, j}) (m - 2)
    (w i * w j * numerator.1 / Z, numerator.2 + 3)

theorem espPairProgram_correct (theta : Fin d → ℝ) (hm : 1 ≤ m) (i j : Fin d) :
    (espPairProgram (fun k => Real.exp (theta k)) m (partition (m := m) theta) i j).1 =
      secondMoment (weightedLaw (m := m) theta) i j := by
  unfold espPairProgram
  split_ifs with hij hr
  · subst j
    rw [espMarginalProgram_correct theta hm, secondMoment_diagonal_eq_marginal]
  · have hm1 : m = 1 := by omega
    subst m
    exact (secondMoment_rank_one_offdiag theta i j hij).symm
  · simp only [espEvaluate_correct _ _ (espDeletedOrder_nodup _ _), espDeletedOrder_toFinset]
    exact (secondMoment_offdiag_eq_esp theta (by omega) i j hij).symm

theorem espPairProgram_cost_le (w : Fin d → ℝ) (m : ℕ) (Z : ℝ) (i j : Fin d) :
    (espPairProgram w m Z i j).2 ≤ 2 * m * d + 3 := by
  unfold espPairProgram
  split_ifs
  · exact (espMarginalProgram_cost_le w m Z i).trans (by omega)
  · simp
  · simp only [espEvaluate_cost]
    exact Nat.add_le_add_right
      (Nat.mul_le_mul (Nat.mul_le_mul_left 2 (Nat.sub_le _ _))
        (espDeletedOrder_length d {i, j})) 3

/-- Evaluate and store an explicitly supplied list of matrix cells. -/
def espRunCells (w : Fin d → ℝ) (m : ℕ) (Z : ℝ) :
    List (Fin d × Fin d) → List ℝ × ℕ
  | [] => ([], 0)
  | (i, j) :: tail =>
    let cell := espPairProgram w m Z i j
    let rest := espRunCells w m Z tail
    (cell.1 :: rest.1, cell.2 + rest.2)

theorem espRunCells_correct (theta : Fin d → ℝ) (hm : 1 ≤ m)
    (cells : List (Fin d × Fin d)) :
    (espRunCells (fun i => Real.exp (theta i)) m (partition (m := m) theta) cells).1 =
      cells.map (fun ij => secondMoment (weightedLaw (m := m) theta) ij.1 ij.2) := by
  induction cells with
  | nil => rfl
  | cons ij cells ih =>
    obtain ⟨i, j⟩ := ij
    simp only [espRunCells, espPairProgram_correct theta hm, ih, List.map_cons]

theorem espRunCells_cost_le (w : Fin d → ℝ) (m : ℕ) (Z : ℝ)
    (cells : List (Fin d × Fin d)) :
    (espRunCells w m Z cells).2 ≤ (2 * m * d + 3) * cells.length := by
  induction cells with
  | nil => simp [espRunCells]
  | cons ij cells ih =>
    obtain ⟨i, j⟩ := ij
    have hc := espPairProgram_cost_le w m Z i j
    simp only [espRunCells, List.length_cons]
    nlinarith

def espMatrixCells (d : ℕ) : List (Fin d × Fin d) :=
  (List.finRange d).product (List.finRange d)

@[simp] theorem espMatrixCells_length (d : ℕ) : (espMatrixCells d).length = d * d := by
  change ((List.finRange d) ×ˢ (List.finRange d)).length = _
  rw [List.length_product]
  simp

/-- The complete matrix program computes its denominator once and stores d²
entries. The input list has size d, never the binomial-sized action space. -/
def espSecondMomentProgram (w : Fin d → ℝ) (m : ℕ) : List ℝ × ℕ :=
  let denominator := espPartitionProgram w m
  let cells := espRunCells w m denominator.1 (espMatrixCells d)
  (cells.1, denominator.2 + cells.2)

theorem espSecondMomentProgram_correct (theta : Fin d → ℝ) (hm : 1 ≤ m) :
    (espSecondMomentProgram (fun i => Real.exp (theta i)) m).1 =
      (espMatrixCells d).map
        (fun ij => secondMoment (weightedLaw (m := m) theta) ij.1 ij.2) := by
  simp only [espSecondMomentProgram, espPartitionProgram_correct,
    espRunCells_correct theta hm]

/-- Polynomial arithmetic cost, derived from every executed inner loop. -/
theorem espSecondMomentProgram_cost_le (w : Fin d → ℝ) (m : ℕ) :
    (espSecondMomentProgram w m).2 ≤ 2 * m * d + (2 * m * d + 3) * (d * d) := by
  simp only [espSecondMomentProgram, espPartitionProgram_cost]
  exact Nat.add_le_add_left
    (by simpa only [espMatrixCells_length] using
      espRunCells_cost_le w m (espPartitionProgram w m).1 (espMatrixCells d)) _

theorem espSecondMomentProgram_output_length (theta : Fin d → ℝ) (hm : 1 ≤ m) :
    (espSecondMomentProgram (fun i => Real.exp (theta i)) m).1.length = d * d := by
  rw [espSecondMomentProgram_correct theta hm, List.length_map, espMatrixCells_length]

end MsetsPaper.Upper
