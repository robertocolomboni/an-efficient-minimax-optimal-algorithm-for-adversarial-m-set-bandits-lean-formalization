import MsetsPaper.Upper.StorageModel
import MsetsPaper.Upper.MainParameters
import MsetsPaper.Upper.RealArithmeticPrimitives
import Mathlib.Data.Nat.Choose.Basic

/-! # Computing the action count and the learning rate without enumerating actions

The binomial coefficient is computed by m successive scalar products and
divisions. The exact-real model assigns one word to a scalar; this is not a
finite-precision or bit-complexity claim. The conservative allocation count
retains every recursive frame, and is still independent of T and delta.
-/

namespace MsetsPaper.Upper.RoundProgram

noncomputable section

def chooseResource (d : ℕ) : ℕ → ResourceRun ℝ
  | 0 => ⟨1, 1, 1⟩
  | k + 1 =>
    let previous := chooseResource d k
    ⟨previous.value * ((d - k : ℕ) : ℝ) / ((k + 1 : ℕ) : ℝ),
      previous.work + 7, previous.allocated + 9⟩

theorem chooseResource_values (d m : ℕ) :
    (chooseResource d m).value = (Nat.choose d m : ℝ) := by
  induction m with
  | zero => simp [chooseResource]
  | succ k ih =>
    simp only [chooseResource, ih]
    apply (div_eq_iff (show ((k + 1 : ℕ) : ℝ) ≠ 0 by positivity)).mpr
    exact_mod_cast (Nat.choose_succ_right_eq d k).symm

theorem chooseResource_counts (d m : ℕ) :
    (chooseResource d m).work = 7 * m + 1 ∧
    (chooseResource d m).allocated = 9 * m + 1 := by
  induction m with
  | zero => simp [chooseResource]
  | succ k ih => dsimp only [chooseResource]; constructor <;> omega

/-- One observable parameter setup. The minimum includes its comparison.
The fixed charge also includes scalar casts, temporaries, and result headers. -/
def learningRateResource (d m T : ℕ) (delta : ℝ) : ResourceRun (ℝ × ℝ) :=
  let count := chooseResource d m
  let cap := 1 / (256 * (d : ℝ))
  let logTerm := Real.log (12 * count.value / delta)
  let root := ResourcePrograms.sqrtResource (logTerm / (320 * (d : ℝ) * (T : ℝ)))
  let eta := min cap root.value
  ⟨(count.value, eta), count.work + root.work + 15, count.allocated + root.allocated + 19⟩

theorem learningRateResource_values (d m T : ℕ) (delta : ℝ) :
    (learningRateResource d m T delta).value =
      ((Nat.choose d m : ℝ), mainLearningRate d T (Nat.choose d m) delta) := by
  simp only [learningRateResource, chooseResource_values, ResourcePrograms.sqrtResource_values,
    mainLearningRate]

theorem learningRateResource_bounds (d m T : ℕ) (delta : ℝ) :
    (learningRateResource d m T delta).work ≤ 7 * m + 20 ∧
    (learningRateResource d m T delta).allocated ≤ 9 * m + 24 := by
  have h := chooseResource_counts d m
  have hs := ResourcePrograms.sqrtResource_bounds
    (Real.log (12 * (chooseResource d m).value / delta) / (320 * (d : ℝ) * (T : ℝ)))
  dsimp only [learningRateResource]
  constructor <;> omega

end

end MsetsPaper.Upper.RoundProgram
