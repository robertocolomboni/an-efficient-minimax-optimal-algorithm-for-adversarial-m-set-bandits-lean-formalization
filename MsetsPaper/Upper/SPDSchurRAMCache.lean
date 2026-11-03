import MsetsPaper.Upper.RAMBufferCopy

/-! Sequential copying of a stored matrix into owned RAM rows. This removes
repeated list traversal from the quadratic Schur update; copying is charged. -/

namespace MsetsPaper.Upper.RAMPrograms
noncomputable section

def packRowsRAM (rows : List (List ℝ)) : ResourceRun (Array (Array ℝ)) :=
  let inner := resourceMap realListToArray rows
  let outer := rowListToArray inner.value
  ⟨outer.value, inner.work + outer.work + 2, inner.allocated + outer.allocated + 2⟩

def matrixReadRAM (A : Array (Array ℝ)) (i j : ℕ) : ResourceRun ℝ :=
  let row := rowLoad A i
  let cell := realLoad row.value j
  ⟨cell.value, row.work + cell.work, row.allocated + cell.allocated⟩

theorem packRowsRAM_values (rows : List (List ℝ)) :
    (packRowsRAM rows).value = (rows.map List.toArray).toArray := by
  simp only [packRowsRAM, rowListToArray, realListToArray,
    copyListToArray_values, resourceMap_values]

theorem packRowsRAM_read (rows : List (List ℝ)) (i j : ℕ) :
    (matrixReadRAM (packRowsRAM rows).value i j).value =
      (rows[i]?.getD [])[j]?.getD 0 := by
  simp only [matrixReadRAM, rowLoad_values, realLoad_values, packRowsRAM_values,
    List.getElem?_toArray, List.getElem?_map]
  cases h : rows[i]? <;> simp [h]

theorem matrixReadRAM_counts (A : Array (Array ℝ)) (i j : ℕ) :
    (matrixReadRAM A i j).work = 2 ∧ (matrixReadRAM A i j).allocated = 2 := ⟨rfl, rfl⟩

theorem packRowsRAM_bounds (rows : List (List ℝ)) (n : ℕ)
    (hlen : rows.length = n) (hrows : ∀ row ∈ rows, row.length = n) :
    (packRowsRAM rows).work ≤ 7 * n ^ 2 + 14 * n + 8 ∧
      (packRowsRAM rows).allocated ≤ 7 * n ^ 2 + 14 * n + 8 := by
  have hi := resourceMap_bounds realListToArray rows (7 * n + 5) (5 * n + 5) (by
    intro row hr
    have h := copyListToArray_counts (0 : ℝ) row
    rw [hrows row hr] at h
    exact ⟨h.1.le, h.2.le⟩)
  have ho := copyListToArray_counts (#[] : Array ℝ) (resourceMap realListToArray rows).value
  have hinner : (resourceMap realListToArray rows).value.length = n := by
    rw [resourceMap_values, List.length_map, hlen]
  rw [hinner] at ho
  rw [hlen] at hi
  dsimp only [packRowsRAM, rowListToArray]
  constructor <;> nlinarith [hi.1, hi.2, ho.1, ho.2]

end
end MsetsPaper.Upper.RAMPrograms
