import MsetsPaper.Upper.RAMMemory
import MsetsPaper.Upper.SamplerResources

/-! # Linear postprocessing for exact sampling from a cached RAM suffix table

The suffix table and scalar weights are already materialized arrays. A cursor
advances through its rows, and a remaining-length counter avoids repeated list
length computations. The output is an actual list, with no Finset insertion
or deduplication inside the program. The full-quota branch copies the remaining
input list explicitly and charges that work. Array decoding below is used only
in specifications and proofs, never in the sampling computation.
-/

namespace MsetsPaper.Upper.RAMPrograms
open ESPSampling
noncomputable section

def decodeRows (rows : Array (Array ℝ)) : List (List ℝ) :=
  rows.toList.map Array.toList

theorem decodeRows_read (rows : Array (Array ℝ)) (i : ℕ) :
    (decodeRows rows)[i]?.getD [] = (rows[i]?.getD #[]).toList := by
  simp only [decodeRows, List.getElem?_map, Array.getElem?_toList]
  cases rows[i]? <;> rfl

def copyIndexList {d : ℕ} : List (Fin d) → ResourceRun (List (Fin d))
  | [] => ⟨[], 1, 1⟩
  | i :: tail =>
    let next := copyIndexList tail
    ⟨i :: next.value, next.work + 4, next.allocated + 4⟩

theorem copyIndexList_values {d : ℕ} (xs : List (Fin d)) :
    (copyIndexList xs).value = xs := by induction xs <;> simp_all [copyIndexList]

theorem copyIndexList_counts {d : ℕ} (xs : List (Fin d)) :
    (copyIndexList xs).work = 4 * xs.length + 1 ∧
      (copyIndexList xs).allocated = 4 * xs.length + 1 := by
  induction xs with
  | nil => simp [copyIndexList]
  | cons i xs ih => simp only [copyIndexList, List.length_cons]; constructor <;> omega

def thresholdRAM {d : ℕ} (weights : Array ℝ) (rows : Array (Array ℝ))
    (cursor quota : ℕ) (i : Fin d) : ResourceRun ℝ :=
  let currentRow := rowLoad rows cursor
  let nextRow := rowLoad rows (cursor + 1)
  let numerator := realLoad nextRow.value (quota - 1)
  let denominator := realLoad currentRow.value quota
  let weight := realLoad weights i.val
  ⟨weight.value * numerator.value / denominator.value,
    currentRow.work + nextRow.work + numerator.work + denominator.work + weight.work + 4,
    currentRow.allocated + nextRow.allocated + numerator.allocated + denominator.allocated +
      weight.allocated + 4⟩

theorem thresholdRAM_values {d : ℕ} (weights : Array ℝ) (rows : Array (Array ℝ))
    (cursor quota : ℕ) (i : Fin d) :
    (thresholdRAM weights rows cursor quota i).value =
      tableThreshold (fun j : Fin d => (realLoad weights j.val).value)
        ((decodeRows rows).drop cursor) quota i := by
  simp only [thresholdRAM, tableThreshold, readCell, realLoad_values, rowLoad_values,
    List.getElem?_drop, Nat.add_zero, decodeRows_read, Array.getElem?_toList]

theorem thresholdRAM_counts {d : ℕ} (weights : Array ℝ) (rows : Array (Array ℝ))
    (cursor quota : ℕ) (i : Fin d) :
    (thresholdRAM weights rows cursor quota i).work = 9 ∧
      (thresholdRAM weights rows cursor quota i).allocated = 9 := ⟨rfl, rfl⟩

def samplerRAM {d : ℕ} (weights uniforms : Array ℝ) (rows : Array (Array ℝ)) :
    List (Fin d) → ℕ → ℕ → ℕ → ResourceRun (List (Fin d))
  | [], _, _, _ => ⟨[], 1, 1⟩
  | i :: tail, remaining, quota, cursor =>
    if quota = 0 then ⟨[], 2, 2⟩ else
    if quota = remaining then
      let copied := copyIndexList (i :: tail)
      ⟨copied.value, copied.work + 3, copied.allocated + 3⟩
    else
      let uniform := realLoad uniforms i.val
      let threshold := thresholdRAM weights rows cursor quota i
      if uniform.value ≤ threshold.value then
        let next := samplerRAM weights uniforms rows tail (remaining - 1) (quota - 1) (cursor + 1)
        ⟨i :: next.value, uniform.work + threshold.work + next.work + 9,
          uniform.allocated + threshold.allocated + next.allocated + 9⟩
      else
        let next := samplerRAM weights uniforms rows tail (remaining - 1) quota (cursor + 1)
        ⟨next.value, uniform.work + threshold.work + next.work + 9,
          uniform.allocated + threshold.allocated + next.allocated + 9⟩

theorem samplerRAM_values {d : ℕ} (weights uniforms : Array ℝ) (rows : Array (Array ℝ))
    (order : List (Fin d)) (remaining quota cursor : ℕ) (hlen : remaining = order.length) :
    (samplerRAM weights uniforms rows order remaining quota cursor).value =
      (samplerListResource (fun i : Fin d => realLoad weights i.val)
        (fun i : Fin d => realLoad uniforms i.val) order quota ((decodeRows rows).drop cursor)).value := by
  induction order generalizing remaining quota cursor with
  | nil => rfl
  | cons i tail ih =>
    have hdrop : ((decodeRows rows).drop cursor).tail = (decodeRows rows).drop (cursor + 1) := by
      rw [← List.drop_one, List.drop_drop]
    simp only [samplerRAM, samplerListResource, resourceLength_values, hlen,
      copyIndexList_values, thresholdRAM_values, thresholdResource_values, hdrop]
    split_ifs
    · rfl
    · rfl
    · exact congrArg (List.cons i) (ih ((i :: tail).length - 1) (quota - 1) (cursor + 1) (by simp))
    · exact ih ((i :: tail).length - 1) quota (cursor + 1) (by simp)

theorem samplerRAM_bounds {d : ℕ} (weights uniforms : Array ℝ) (rows : Array (Array ℝ))
    (order : List (Fin d)) (remaining quota cursor : ℕ) :
    (samplerRAM weights uniforms rows order remaining quota cursor).work ≤ 25 * order.length + 3 ∧
      (samplerRAM weights uniforms rows order remaining quota cursor).allocated ≤ 25 * order.length + 3 := by
  induction order generalizing remaining quota cursor with
  | nil => simp [samplerRAM]
  | cons i tail ih =>
    have hc := copyIndexList_counts (i :: tail)
    have ht := thresholdRAM_counts weights rows cursor quota i
    have hyes := ih (remaining - 1) (quota - 1) (cursor + 1)
    have hno := ih (remaining - 1) quota (cursor + 1)
    simp only [samplerRAM, List.length_cons]
    split_ifs <;> dsimp only [realLoad] <;> constructor <;>
      simp only [List.length_cons] at hc <;> omega

theorem samplerRAM_sublist {d : ℕ} (weights uniforms : Array ℝ) (rows : Array (Array ℝ))
    (order : List (Fin d)) (remaining quota cursor : ℕ) (hlen : remaining = order.length) :
    (samplerRAM weights uniforms rows order remaining quota cursor).value.Sublist order := by
  rw [samplerRAM_values weights uniforms rows order remaining quota cursor hlen]
  exact samplerListResource_sublist _ _ _ _ _

theorem samplerRAM_nodup {d : ℕ} (weights uniforms : Array ℝ) (rows : Array (Array ℝ))
    (order : List (Fin d)) (remaining quota cursor : ℕ) (hlen : remaining = order.length)
    (hn : order.Nodup) :
    (samplerRAM weights uniforms rows order remaining quota cursor).value.Nodup :=
  (samplerRAM_sublist weights uniforms rows order remaining quota cursor hlen).nodup hn

/-- Correctness under representation invariants supplied by the actual DP
preprocessor. They describe input contents, not any requested sampling result. -/
theorem samplerRAM_correct {d : ℕ} (weights uniforms : Array ℝ) (rows : Array (Array ℝ))
    (w u : Fin d → ℝ) (order : List (Fin d)) (m quota : ℕ) (hn : order.Nodup)
    (hr : quota ≤ m)
    (hw : ∀ i : Fin d, (realLoad weights i.val).value = w i)
    (hu : ∀ i : Fin d, (realLoad uniforms i.val).value = u i)
    (hrows : decodeRows rows = (espSuffixTable w m order).rows) :
    (samplerRAM weights uniforms rows order order.length quota 0).value.toFinset =
      sequentialList w u order quota := by
  rw [samplerRAM_values weights uniforms rows order order.length quota 0 rfl,
    samplerListResource_values, List.drop_zero, hrows]
  simp_rw [hw, hu]
  exact tableSampler_correct w u m order hn quota hr

theorem realLoad_ofFn {d : ℕ} (f : Fin d → ℝ) (i : Fin d) :
    (realLoad (Array.ofFn f) i.val).value = f i := by
  simp [realLoad, i.isLt]

open scoped unitInterval ENNReal
open MeasureTheory ProbabilityTheory

/-- An independent uniform tape is input to the postprocessing phase.
Producing/materializing that tape is a separate linear primitive cost. -/
def uniformArray {d : ℕ} (u : Fin d → unitInterval) : Array ℝ :=
  Array.ofFn (fun i => (u i : ℝ))

theorem samplerRAM_weighted_output {d : ℕ} (theta : Fin d → ℝ)
    (weights : Array ℝ) (rows : Array (Array ℝ)) (m : ℕ)
    (hw : ∀ i : Fin d, (realLoad weights i.val).value = Real.exp (theta i))
    (hrows : decodeRows rows = (espSuffixTable (fun i => Real.exp (theta i)) m (List.finRange d)).rows)
    (u : Fin d → unitInterval) :
    (samplerRAM weights (uniformArray u) rows (List.finRange d) d m 0).value.toFinset =
      (sampleMSet theta m u).output := by
  have hh := samplerRAM_correct weights (uniformArray u) rows
    (fun i => Real.exp (theta i)) (fun i => (u i : ℝ)) (List.finRange d) m m
    (List.nodup_finRange d) le_rfl hw (fun i => realLoad_ofFn _ i) hrows
  simp only [List.length_finRange] at hh
  rw [hh]
  exact (tableSampler_correct _ _ m _ (List.nodup_finRange d) m le_rfl).symm

theorem samplerRAM_weighted_probability {d m : ℕ} (theta : Fin d → ℝ)
    (weights : Array ℝ) (rows : Array (Array ℝ)) (hmd : m ≤ d)
    (hw : ∀ i : Fin d, (realLoad weights i.val).value = Real.exp (theta i))
    (hrows : decodeRows rows = (espSuffixTable (fun i => Real.exp (theta i)) m (List.finRange d)).rows)
    (a : Action d m) :
    uniformCube (Fin d) {u | (samplerRAM weights (uniformArray u) rows
      (List.finRange d) d m 0).value.toFinset = a.val} =
        ENNReal.ofReal (weightedLaw theta a) := by
  simp_rw [samplerRAM_weighted_output theta weights rows m hw hrows]
  exact sampleMSet_probability theta hmd a

theorem samplerRAM_weighted_card {d m : ℕ} (theta : Fin d → ℝ)
    (weights : Array ℝ) (rows : Array (Array ℝ)) (hmd : m ≤ d)
    (hw : ∀ i : Fin d, (realLoad weights i.val).value = Real.exp (theta i))
    (hrows : decodeRows rows = (espSuffixTable (fun i => Real.exp (theta i)) m (List.finRange d)).rows)
    (u : Fin d → unitInterval) :
    (samplerRAM weights (uniformArray u) rows (List.finRange d) d m 0).value.length = m := by
  have hn := samplerRAM_nodup weights (uniformArray u) rows (List.finRange d) d m 0
    (by simp) (List.nodup_finRange d)
  rw [← List.toFinset_card_of_nodup hn, samplerRAM_weighted_output theta weights rows m hw hrows]
  exact sampleMSet_card theta hmd u

/-- The postprocessing bound is linear in d and independent of m, once the
suffix coefficients and input tape are cached. Both reads per coefficient
lookup are actual array loads, not unit-cost list accesses. -/
theorem samplerRAM_postprocessing_linear {d : ℕ} (weights uniforms : Array ℝ)
    (rows : Array (Array ℝ)) (m : ℕ) :
    (samplerRAM weights uniforms rows (List.finRange d) d m 0).work ≤ 25 * d + 3 ∧
      (samplerRAM weights uniforms rows (List.finRange d) d m 0).allocated ≤ 25 * d + 3 := by
  simpa only [List.length_finRange] using
    samplerRAM_bounds weights uniforms rows (List.finRange d) d m 0

end
end MsetsPaper.Upper.RAMPrograms
