import MsetsLower.Prelude
import Mathlib.Data.Nat.Choose.Basic

/-!
# Sparse parameter reduction

The final theorem sets `s=min(m,d-m)`.  This file records the exact arithmetic
and binomial symmetry used to reduce to `s ≤ d/2` and then transport the result
back to the original action size.
-/

namespace MsetsLower.Lower

noncomputable section

/-- The fixed branch threshold `r_star = 2^32` from
`eq:lower-density-threshold`. -/
def densityThreshold : Nat := 2 ^ 32

theorem densityThreshold_eq : densityThreshold = 2 ^ 32 := rfl

/-- The smaller of an action and its complement. -/
def sparseSize (d m : Nat) : Nat := min m (d - m)

theorem sparseSize_bounds
    {d m : Nat} (hm_one : 1 ≤ m) (hm_lt : m ≤ d - 1) :
    1 ≤ sparseSize d m ∧ sparseSize d m ≤ d / 2 := by
  have hmd : m ≤ d := by omega
  have hcomp_one : 1 ≤ d - m := by omega
  constructor
  · exact le_min hm_one hcomp_one
  · dsimp [sparseSize]
    by_cases hmhalf : m ≤ d / 2
    · exact (min_le_left m (d - m)).trans hmhalf
    · have hcomphalf : d - m ≤ d / 2 := by omega
      exact (min_le_right m (d - m)).trans hcomphalf

theorem sparseSize_le_dimension
    {d m : Nat} (hmd : m ≤ d) : sparseSize d m ≤ d := by
  exact (min_le_left m (d - m)).trans hmd

/-- Literal binomial symmetry used in the last line of the proof of
`thm:lower-bound-explicit`. -/
theorem choose_sparseSize_eq
    {d m : Nat} (hmd : m ≤ d) :
    Nat.choose d (sparseSize d m) = Nat.choose d m := by
  dsimp [sparseSize]
  by_cases h : m ≤ d - m
  · rw [min_eq_left h]
  · rw [min_eq_right (le_of_not_ge h)]
    exact Nat.choose_symm hmd

/-- The manuscript assumptions `1≤m≤d-1` supply all hypotheses of the
complement reduction. -/
theorem sparseSize_parameters
    {d m : Nat} (hm_one : 1 ≤ m) (hm_lt : m ≤ d - 1) :
    let s := sparseSize d m
    1 ≤ s ∧ s ≤ d / 2 ∧ s ≤ d ∧ 0 < d - s := by
  dsimp
  have hb := sparseSize_bounds hm_one hm_lt
  have hmd : m ≤ d := by omega
  have hsd := sparseSize_le_dimension hmd
  omega

end

end MsetsLower.Lower
