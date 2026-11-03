import MsetsPaper.Upper.StorageModel
import Mathlib.Analysis.SpecialFunctions.Log.Basic

/-! # Exact square root using only the manuscript's real-arithmetic primitives

The positive branch uses one comparison, one logarithm, one division, and
one exponential. The nonpositive branch returns zero after the comparison.
Thus sqrt is not added as an extra unit-cost oracle. Scalars and the branch
test occupy at most four fresh words in the same abstract word model.
-/

namespace MsetsPaper.Upper.ResourcePrograms
noncomputable section

def sqrtResource (x : ℝ) : ResourceRun ℝ :=
  if x ≤ 0 then ⟨0, 1, 1⟩ else ⟨Real.exp (Real.log x / 2), 4, 4⟩

theorem sqrtResource_values (x : ℝ) : (sqrtResource x).value = Real.sqrt x := by
  unfold sqrtResource
  split_ifs with hx
  · exact (Real.sqrt_eq_zero_of_nonpos hx).symm
  · have hxpos : 0 < x := lt_of_not_ge hx
    rw [← Real.log_sqrt hxpos.le, Real.exp_log (Real.sqrt_pos.mpr hxpos)]

theorem sqrtResource_bounds (x : ℝ) :
    (sqrtResource x).work ≤ 4 ∧ (sqrtResource x).allocated ≤ 4 := by
  unfold sqrtResource
  split_ifs <;> norm_num

theorem sqrtResource_positive_counts {x : ℝ} (hx : 0 < x) :
    (sqrtResource x).work = 4 ∧ (sqrtResource x).allocated = 4 := by
  simp [sqrtResource, not_le.mpr hx]

theorem sqrtResource_nonpositive_counts {x : ℝ} (hx : x ≤ 0) :
    (sqrtResource x).work = 1 ∧ (sqrtResource x).allocated = 1 := by
  simp [sqrtResource, hx]

end
end MsetsPaper.Upper.ResourcePrograms
