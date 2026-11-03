import MsetsPaper.Upper.RoundRAMPreparation
import MsetsPaper.Upper.SamplerRAMComplete

/-! # The round's actual RAM sampler, including input copying

For positive rank the stored list is copied into an owned parameter array
and the complete RAM sampler is executed. Rank zero returns the empty list
directly, preserving the total API without a positivity premise.
-/

namespace MsetsPaper.Upper.RoundProgram

open SchurSolver RAMPrograms ESPSampling MsetsLower MeasureTheory
open scoped unitInterval

noncomputable section

variable {d m : ℕ}

def sampleStoredRAM (theta : StoredVector d) (m : ℕ) (u : Fin d → unitInterval) :
    ResourceRun (List (Fin d)) :=
  if m = 0 then ⟨[], 1, 1⟩ else
    let input := realListToArray theta.val
    let sampled := samplerFromThetaRAM input.value d m u
    ⟨sampled.1.value, input.work + sampled.1.work + 2,
      input.allocated + sampled.1.allocated + 2⟩

theorem sampleStoredRAM_card_nodup (theta : StoredVector d) (hmd : m ≤ d)
    (u : Fin d → unitInterval) :
    (sampleStoredRAM theta m u).value.length = m ∧
      (sampleStoredRAM theta m u).value.Nodup := by
  by_cases hm : m = 0
  · simp [sampleStoredRAM, hm]
  · simpa only [sampleStoredRAM, if_neg hm] using
      samplerFromThetaRAM_card_nodup (realListToArray theta.val).value d m hmd u

theorem sampleStoredRAM_output (theta : StoredVector d) (m : ℕ)
    (u : Fin d → unitInterval) :
    (sampleStoredRAM theta m u).value.toFinset = (sampleMSet (storedVector theta) m u).output := by
  by_cases hm : m = 0
  · subst m
    simp only [sampleStoredRAM, if_pos rfl, List.toFinset_nil]
    exact (Finset.card_eq_zero.mp (sampleMSet_card (storedVector theta) (Nat.zero_le d) u)).symm
  · simp only [sampleStoredRAM, if_neg hm]
    rw [samplerFromThetaRAM_output]
    have hr : (fun i : Fin d ↦ (realLoad (realListToArray theta.val).value i.val).value) =
        storedVector theta := by
      simpa only [realLoad_values] using copiedTheta_read theta
    rw [hr]

theorem sampleStoredRAM_probability (theta : StoredVector d) (hmd : m ≤ d)
    (a : Action d m) :
    uniformCube (Fin d) {u | (sampleStoredRAM theta m u).value.toFinset = a.val} =
      ENNReal.ofReal (weightedLaw (storedVector theta) a) := by
  simp only [sampleStoredRAM_output]
  exact sampleMSet_probability (storedVector theta) hmd a

/-- Includes the actual list-to-array copy and all RAM preprocessing. -/
theorem sampleStoredRAM_bounds (theta : StoredVector d) (hmd : m ≤ d)
    (u : Fin d → unitInterval) :
    (sampleStoredRAM theta m u).work ≤ 158 * d * m + 7 * d + 7 ∧
    (sampleStoredRAM theta m u).allocated ≤ 158 * d * m + 5 * d + 7 := by
  by_cases hm : m = 0
  · simp only [sampleStoredRAM, if_pos hm]
    constructor <;> omega
  · have hd : 1 ≤ d := by omega
    have hmpos : 1 ≤ m := by omega
    have hs := samplerFromThetaRAM_linear (realListToArray theta.val).value d m hd hmpos u
    have hc := copyListToArray_counts (0 : ℝ) theta.val
    rw [theta.property] at hc
    simp only [sampleStoredRAM, if_neg hm]
    dsimp only [realListToArray] at *
    constructor <;> omega

end
end MsetsPaper.Upper.RoundProgram
