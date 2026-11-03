import MsetsPaper.Upper.ESPSamplingLaw

/-!
# The table-backed sampler and its operational arithmetic counter

The sampler reads precomputed coefficient rows and never enumerates subsets.
Each nonterminal branch executes one multiplication, one division and one
uniform comparison. The counters below count arithmetic and uniform draws;
they are not a bit-complexity or data-structure runtime assertion.
-/

noncomputable section
open scoped BigOperators unitInterval ENNReal
open MeasureTheory ProbabilityTheory

namespace MsetsPaper.Upper.ESPSampling

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

def readCell (row : List ℝ) (k : ℕ) : ℝ := row[k]?.getD 0

theorem readCell_dp (w : ι → ℝ) (m : ℕ) (order : List ι)
    (hn : order.Nodup) (k : ℕ) (hk : k ≤ m) :
    readCell (espDP w m order).1 k = esp w order.toFinset k := by
  have hb : k < (espDP w m order).1.length := by rw [espDP_length]; omega
  simp only [readCell, List.getElem?_eq_getElem hb, Option.getD_some]
  exact espDP_correct w m order hn k hk

theorem espSuffixTable_first (w : ι → ℝ) (m : ℕ) (order : List ι) :
    (espSuffixTable w m order).rows[0]?.getD [] = (espDP w m order).1 := by
  cases order <;> simp [espSuffixTable, espDP, espSuffixTable_head]

theorem espSuffixTable_second (w : ι → ℝ) (m : ℕ) (i : ι) (tail : List ι) :
    (espSuffixTable w m (i :: tail)).rows[1]?.getD [] = (espDP w m tail).1 := by
  simp only [espSuffixTable, List.getElem?_cons_succ]
  exact espSuffixTable_first w m tail

def tableThreshold (w : ι → ℝ) (rows : List (List ℝ)) (r : ℕ) (i : ι) : ℝ :=
  w i * readCell (rows[1]?.getD []) (r - 1) / readCell (rows[0]?.getD []) r

theorem tableThreshold_correct (w : ι → ℝ) (m : ℕ) (i : ι) (tail : List ι)
    (hn : (i :: tail).Nodup) (r : ℕ) (hr : r ≤ m) :
    tableThreshold w (espSuffixTable w m (i :: tail)).rows r i =
      sequentialThreshold w (i :: tail).toFinset r i := by
  obtain ⟨hi, ht⟩ := List.nodup_cons.mp hn
  simp only [tableThreshold, espSuffixTable_second, espSuffixTable_first,
    readCell_dp w m tail ht (r - 1) (by omega), readCell_dp w m (i :: tail) hn r hr]
  simp only [sequentialThreshold, List.toFinset_cons,
    Finset.erase_insert (show i ∉ tail.toFinset by simpa using hi)]

structure SamplerResult (ι : Type*) where
  output : Finset ι
  arithmetic : ℕ
  draws : ℕ

/-- The actual branch recursion, instrumented at its two real operations and
one draw. Terminating quotas consume no further random numbers. -/
def tableSampler (w u : ι → ℝ) : List ι → ℕ → List (List ℝ) → SamplerResult ι
  | [], _, _ => ⟨∅, 0, 0⟩
  | i :: tail, r, rows =>
    if r = 0 then ⟨∅, 0, 0⟩
    else if r = (i :: tail).length then ⟨(i :: tail).toFinset, 0, 0⟩
    else if u i ≤ tableThreshold w rows r i then
      let next := tableSampler w u tail (r - 1) rows.tail
      ⟨insert i next.output, next.arithmetic + 2, next.draws + 1⟩
    else
      let next := tableSampler w u tail r rows.tail
      ⟨next.output, next.arithmetic + 2, next.draws + 1⟩

theorem tableSampler_correct (w u : ι → ℝ) (m : ℕ) (order : List ι)
    (hn : order.Nodup) (r : ℕ) (hr : r ≤ m) :
    (tableSampler w u order r (espSuffixTable w m order).rows).output =
      sequentialList w u order r := by
  induction order generalizing r with
  | nil => rfl
  | cons i tail ih =>
    have ht := (List.nodup_cons.mp hn).2
    simp only [tableSampler, sequentialList, tableThreshold_correct w m i tail hn r hr]
    split_ifs with hzero hfull htake
    · rfl
    · rfl
    · simpa only [espSuffixTable, List.tail_cons] using
        congrArg (insert i) (ih ht (r - 1) (by omega))
    · simpa only [espSuffixTable, List.tail_cons] using ih ht r hr

theorem tableSampler_cost (w u : ι → ℝ) (order : List ι) (r : ℕ)
    (rows : List (List ℝ)) :
    (tableSampler w u order r rows).arithmetic ≤ 2 * order.length ∧
      (tableSampler w u order r rows).draws ≤ order.length := by
  induction order generalizing r rows with
  | nil => simp [tableSampler]
  | cons i tail ih =>
    simp only [tableSampler]
    split_ifs with hzero hfull htake
    · simp
    · simp
    · have h := ih (r - 1) rows.tail
      simp only [List.length_cons]
      constructor <;> omega
    · have h := ih r rows.tail
      simp only [List.length_cons]
      constructor <;> omega

variable {d m : ℕ}

/-- Actual fixed-order sampler with the precomputed suffix table. -/
def sampleMSet (theta : Fin d → ℝ) (m : ℕ) (u : Fin d → unitInterval) :
    SamplerResult (Fin d) :=
  let w := fun i => Real.exp (theta i)
  let cache := espSuffixTable w m (List.finRange d)
  let run := tableSampler w (fun i => (u i : ℝ)) (List.finRange d) m cache.rows
  ⟨run.output, cache.arithmetic + run.arithmetic, run.draws⟩

theorem sampleMSet_card (theta : Fin d → ℝ) (hmd : m ≤ d) (u : Fin d → unitInterval) :
    (sampleMSet theta m u).output.card = m := by
  unfold sampleMSet
  rw [tableSampler_correct _ _ m _ (List.nodup_finRange d) m le_rfl]
  exact sequentialList_card _ _ _ (List.nodup_finRange d) m (by simpa using hmd)

/-- The efficient DP sampler has exactly the paper's actual p_theta law. -/
theorem sampleMSet_probability (theta : Fin d → ℝ) (hmd : m ≤ d) (a : Action d m) :
    uniformCube (Fin d) {u | (sampleMSet theta m u).output = a.val} =
      ENNReal.ofReal (weightedLaw theta a) := by
  have heq (u : Fin d → unitInterval) : (sampleMSet theta m u).output =
      cubeSampler (fun i => Real.exp (theta i)) (List.finRange d) m u := by
    exact tableSampler_correct _ _ m _ (List.nodup_finRange d) m le_rfl
  simp only [heq]
  rw [cubeSampler_probability _ (fun i => Real.exp_pos (theta i)) _
    (List.nodup_finRange d) m (by simpa using hmd)]
  congr 1
  rw [List.toFinset_finRange, restrictedMass,
    if_pos (by simp [Finset.mem_powersetCard, a.property])]
  exact (weightedLaw_eq_esp theta a).symm

theorem sampleMSet_cost (theta : Fin d → ℝ) (m : ℕ) (u : Fin d → unitInterval) :
    (sampleMSet theta m u).arithmetic ≤ 2 * m * d + 2 * d ∧
      (sampleMSet theta m u).draws ≤ d := by
  have h := tableSampler_cost
    (fun i => Real.exp (theta i)) (fun i => (u i : ℝ)) (List.finRange d) m
    (espSuffixTable (fun i => Real.exp (theta i)) m (List.finRange d)).rows
  simpa only [sampleMSet, espSuffixTable_cost, List.length_finRange,
    Nat.add_le_add_iff_left] using h

end MsetsPaper.Upper.ESPSampling
