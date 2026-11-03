import MsetsPaper.Upper.SamplerRAM

/-! # Lazy independent uniform draws in the RAM sampler

One coordinate of the independent uniform cube is read only when its item is
examined in a nonterminal quota branch. The ordered input is nodup, hence no
random coordinate is requested twice. Each draw costs one operation/word; the
separate counter records the actual number of requested uniforms. No whole
random tape is materialized in this program.
-/

namespace MsetsPaper.Upper.RAMPrograms
open ESPSampling MeasureTheory ProbabilityTheory
open scoped unitInterval ENNReal
noncomputable section

def uniformDrawRAM {d : ℕ} (u : Fin d → unitInterval) (i : Fin d) : ResourceRun ℝ :=
  ⟨(u i : ℝ), 1, 1⟩

def randomSamplerRAM {d : ℕ} (weights : Array ℝ) (u : Fin d → unitInterval)
    (rows : Array (Array ℝ)) :
    List (Fin d) → ℕ → ℕ → ℕ → ResourceRun (List (Fin d)) × ℕ
  | [], _, _, _ => (⟨[], 1, 1⟩, 0)
  | i :: tail, remaining, quota, cursor =>
    if quota = 0 then (⟨[], 2, 2⟩, 0) else
    if quota = remaining then
      let copied := copyIndexList (i :: tail)
      (⟨copied.value, copied.work + 3, copied.allocated + 3⟩, 0)
    else
      let uniform := uniformDrawRAM u i
      let threshold := thresholdRAM weights rows cursor quota i
      if uniform.value ≤ threshold.value then
        let next := randomSamplerRAM weights u rows tail (remaining - 1) (quota - 1) (cursor + 1)
        (⟨i :: next.1.value, uniform.work + threshold.work + next.1.work + 9,
          uniform.allocated + threshold.allocated + next.1.allocated + 9⟩, next.2 + 1)
      else
        let next := randomSamplerRAM weights u rows tail (remaining - 1) quota (cursor + 1)
        (⟨next.1.value, uniform.work + threshold.work + next.1.work + 9,
          uniform.allocated + threshold.allocated + next.1.allocated + 9⟩, next.2 + 1)

theorem randomSamplerRAM_resource {d : ℕ} (weights : Array ℝ) (u : Fin d → unitInterval)
    (rows : Array (Array ℝ)) (order : List (Fin d)) (remaining quota cursor : ℕ) :
    (randomSamplerRAM weights u rows order remaining quota cursor).1 =
      samplerRAM weights (uniformArray u) rows order remaining quota cursor := by
  induction order generalizing remaining quota cursor with
  | nil => rfl
  | cons i tail ih =>
    have hv : (realLoad (uniformArray u) i.val).value = (u i : ℝ) := realLoad_ofFn _ i
    have hw : (realLoad (uniformArray u) i.val).work = 1 := rfl
    have ha : (realLoad (uniformArray u) i.val).allocated = 1 := rfl
    simp only [randomSamplerRAM, samplerRAM, uniformDrawRAM, hv, hw, ha]
    split_ifs <;> simp_all only [ih, ↓reduceIte]

theorem randomSamplerRAM_draws {d : ℕ} (weights : Array ℝ) (u : Fin d → unitInterval)
    (rows : Array (Array ℝ)) (order : List (Fin d)) (remaining quota cursor : ℕ) :
    (randomSamplerRAM weights u rows order remaining quota cursor).2 ≤ order.length := by
  induction order generalizing remaining quota cursor with
  | nil => simp [randomSamplerRAM]
  | cons i tail ih =>
    have hy := ih (remaining - 1) (quota - 1) (cursor + 1)
    have hn := ih (remaining - 1) quota (cursor + 1)
    simp only [randomSamplerRAM, List.length_cons]
    split_ifs <;> dsimp only <;> omega

theorem randomSamplerRAM_postprocessing_linear {d : ℕ}
    (weights : Array ℝ) (u : Fin d → unitInterval) (rows : Array (Array ℝ)) (m : ℕ) :
    (randomSamplerRAM weights u rows (List.finRange d) d m 0).1.work ≤ 25 * d + 3 ∧
      (randomSamplerRAM weights u rows (List.finRange d) d m 0).1.allocated ≤ 25 * d + 3 ∧
      (randomSamplerRAM weights u rows (List.finRange d) d m 0).2 ≤ d := by
  rw [randomSamplerRAM_resource]
  exact ⟨(samplerRAM_postprocessing_linear weights (uniformArray u) rows m).1,
    (samplerRAM_postprocessing_linear weights (uniformArray u) rows m).2,
    by simpa using randomSamplerRAM_draws weights u rows (List.finRange d) d m 0⟩

theorem randomSamplerRAM_weighted_probability {d m : ℕ} (theta : Fin d → ℝ)
    (weights : Array ℝ) (rows : Array (Array ℝ)) (hmd : m ≤ d)
    (hw : ∀ i : Fin d, (realLoad weights i.val).value = Real.exp (theta i))
    (hrows : decodeRows rows = (espSuffixTable (fun i => Real.exp (theta i)) m (List.finRange d)).rows)
    (a : Action d m) :
    uniformCube (Fin d) {u | (randomSamplerRAM weights u rows
      (List.finRange d) d m 0).1.value.toFinset = a.val} =
        ENNReal.ofReal (weightedLaw theta a) := by
  simp_rw [randomSamplerRAM_resource]
  exact samplerRAM_weighted_probability theta weights rows hmd hw hrows a

end
end MsetsPaper.Upper.RAMPrograms
