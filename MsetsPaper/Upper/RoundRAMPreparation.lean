import MsetsPaper.Upper.ESPRAMMomentsFromTheta
import MsetsPaper.Upper.StoredResourceOperations

/-! The actual round's moment preparation uses the denominator-once RAM
batch. Input copying, row-major output copying, and reshaping are charged. -/

namespace MsetsPaper.Upper.RoundProgram
open SchurSolver ResourcePrograms RAMPrograms ESPSampling
noncomputable section
variable {d m : ℕ}

private theorem product_index {α β : Type*} (xs : List α) (ys : List β)
    (i j : ℕ) (hi : i < xs.length) (hj : j < ys.length) :
    (xs.product ys)[i * ys.length + j]? = some (xs[i], ys[j]) := by
  change (xs ×ˢ ys)[i * ys.length + j]? = _
  induction xs generalizing i with
  | nil => simp at hi
  | cons x xs ih =>
    cases i with
    | zero =>
      simp only [Nat.zero_mul, Nat.zero_add, List.getElem_cons_zero, List.product_cons]
      rw [List.getElem?_append_left (by simpa using hj), List.getElem?_map,
        List.getElem?_eq_getElem hj]
      rfl
    | succ i =>
      simp only [List.length_cons, Nat.succ_lt_succ_iff] at hi
      rw [List.product_cons, List.getElem?_append_right (by
        simp only [List.length_map, Nat.add_mul, Nat.one_mul]; omega)]
      simp only [List.length_map, List.getElem_cons_succ]
      have hn : (i + 1) * ys.length + j - ys.length = i * ys.length + j := by
        rw [Nat.add_mul, Nat.one_mul]
        omega
      rw [hn]
      exact ih i hi

theorem espMatrixCells_index (i j : Fin d) :
    (espMatrixCells d)[i.val * d + j.val]? = some (i,j) := by
  simpa [espMatrixCells] using product_index (List.finRange d) (List.finRange d)
    i.val j.val (by simpa using i.isLt) (by simpa using j.isLt)

theorem momentTableFromThetaRAM_all_bounds (theta : Array ℝ) (d m : ℕ) :
    (momentTableFromThetaRAM theta d m).work ≤ 100 * (d + m + 1)^4 ∧
    (momentTableFromThetaRAM theta d m).allocated ≤ 100 * (d + m + 1)^4 := by
  let weights := (weightsRAM theta d).value
  let order := (samplerOrderResource d).value
  let jobs := (pairJobsRows order order).value
  let Z := (espEvaluateRAM weights order m).value
  have hw := weightsRAM_bounds theta d
  have ho := samplerOrderResource_bounds d
  have hj := pairJobsRows_bounds order order
  have hz := espEvaluateRAM_bounds weights order m
  have hr := momentBatchRAM_bounds weights order m Z jobs
  have hlen : order.length = d := by simp [order, samplerOrderResource_values]
  have hjlen : jobs.length = d*d := by
    dsimp only [jobs]
    rw [pairJobsRows_values]
    change (order ×ˢ order).length = _
    rw [List.length_product, hlen]
  simp only [hlen, hjlen] at hj hz hr
  have hp : 11*d+8 + (5*d+1) + (1+d*(9*d+6)) +
      (4*m+9+d*(7*m+10)) + (1+d*d*(4*m+23+d*(7*m+16)+10)) + 13 ≤
      100*(d+m+1)^4 := by
    ring_nf
    omega
  dsimp only [weights, order, jobs, Z] at hj hz hr
  dsimp only [momentTableFromThetaRAM, momentTableRAM]
  constructor <;> nlinarith [hw.1, hw.2, ho.1, ho.2, hj.1, hj.2, hz.1, hz.2, hr.1, hr.2.1]

def momentsStoredRAM (theta : StoredVector d) (m : ℕ) : ResourceRun (StoredMatrix d) :=
  let input := realListToArray theta.val
  let table := momentTableFromThetaRAM input.value d m
  let flat := realListToArray table.values
  let matrix := matrixProgram (fun i j : Fin d => realLoad flat.value (i.val*d+j.val))
  ⟨matrix.value, input.work + table.work + flat.work + matrix.work + 3,
    input.allocated + table.allocated + flat.allocated + matrix.allocated + 3⟩

theorem copiedTheta_read (theta : StoredVector d) :
    (fun i : Fin d => (realListToArray theta.val).value[i.val]?.getD 0) =
      storedVector theta := by
  ext i
  have hi : i.val < theta.val.length := by rw [theta.property]; exact i.isLt
  simp [realListToArray, copyListToArray_values, storedVector, cachedRealVector,
    List.getElem?_eq_getElem hi]

theorem momentsStoredRAM_values (theta : StoredVector d) (hm : 1 ≤ m) :
    storedMatrix (momentsStoredRAM theta m).value =
      secondMoment (weightedLaw (m := m) (storedVector theta)) := by
  dsimp only [momentsStoredRAM]
  rw [matrixProgram_values]
  ext i j
  simp only [realLoad_values, realListToArray, copyListToArray_values, List.getElem?_toArray]
  rw [momentTableFromThetaRAM_values _ d m hm, List.getElem?_map,
    espMatrixCells_index]
  simp only [Option.map_some, Option.getD_some]
  have hc := copiedTheta_read theta
  simp only [realListToArray, copyListToArray_values] at hc
  exact congrArg (fun f : Fin d → ℝ => secondMoment (weightedLaw (m := m) f) i j) hc

theorem momentsStoredRAM_bounds (theta : StoredVector d) (m : ℕ) :
    (momentsStoredRAM theta m).work ≤ 150*(d+m+1)^4 ∧
    (momentsStoredRAM theta m).allocated ≤ 150*(d+m+1)^4 := by
  have hi := copyListToArray_counts (0 : ℝ) theta.val
  rw [theta.property] at hi
  have ht := momentTableFromThetaRAM_all_bounds (realListToArray theta.val).value d m
  have hf := copyListToArray_counts (0 : ℝ)
    (momentTableFromThetaRAM (realListToArray theta.val).value d m).values
  rw [momentTableFromThetaRAM_length] at hf
  have hM := matrixProgram_bounds (fun i j : Fin d => realLoad
    (realListToArray (momentTableFromThetaRAM (realListToArray theta.val).value d m).values).value
    (i.val*d+j.val)) 1 1 (fun _ _ => ⟨le_rfl,le_rfl⟩)
  have hp : (7*d+5) + 100*(d+m+1)^4 + (7*(d*d)+5) +
      ((5*d+5)*d+2) + 3 ≤ 150*(d+m+1)^4 := by ring_nf; omega
  dsimp only [momentsStoredRAM]
  constructor <;> nlinarith [hi.1,hi.2,ht.1,ht.2,hf.1,hf.2,hM.1,hM.2]

theorem momentsStoredRAM_cubic (theta : StoredVector d) (hd : 1 ≤ d) (hm : 1 ≤ m) :
    (momentsStoredRAM theta m).work ≤ 500*d^3*m := by
  have hi := (copyListToArray_counts (0 : ℝ) theta.val).1
  rw [theta.property] at hi
  have ht := momentTableFromThetaRAM_work (realListToArray theta.val).value d m hd hm
  have hf := (copyListToArray_counts (0 : ℝ)
    (momentTableFromThetaRAM (realListToArray theta.val).value d m).values).1
  rw [momentTableFromThetaRAM_length] at hf
  have hM := (matrixProgram_bounds (fun i j : Fin d => realLoad
    (realListToArray (momentTableFromThetaRAM (realListToArray theta.val).value d m).values).value
    (i.val*d+j.val)) 1 1 (fun _ _ => ⟨le_rfl,le_rfl⟩)).1
  have hd2 : d ≤ d*d := by nlinarith
  have hd3 : d*d ≤ d^3 := by nlinarith [Nat.mul_le_mul_left (d*d) hd]
  have hb : d*d ≤ d^3*m := hd3.trans (by simpa using Nat.mul_le_mul_left (d^3) hm)
  have hone : 1 ≤ d^3*m := hd.trans (hd2.trans hb)
  dsimp only [momentsStoredRAM]
  nlinarith

end
end MsetsPaper.Upper.RoundProgram

