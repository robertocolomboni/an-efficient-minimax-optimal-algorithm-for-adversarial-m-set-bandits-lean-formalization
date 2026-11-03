import MsetsPaper.Lower.SparseCappedTableBridge
import MsetsPaper.Lower.SparseCappedMoments

/-! # The two exact pathwise counting identities for surviving favorable bits -/

namespace MsetsPaper.Lower.SparseCapped

open MsetsLower MsetsLower.History MeasureTheory ProbabilityTheory Set
open scoped BigOperators ENNReal ProbabilityTheory

noncomputable section

def favorable {d : ℕ} (S : Finset (Fin d)) (U : Bits d) : Finset (Fin d) :=
  S.filter (fun i => U i = true)

/-- The test excludes the tested bit, exactly as in the manuscript. -/
def survivalTest {d : ℕ} (m : ℕ) (S : Finset (Fin d)) (U : Bits d) (i : Fin d) : Prop :=
  i ∈ S ∧ ((favorable S U).erase i).card < m

instance survivalTest_decidable {d : ℕ} (m : ℕ) (S : Finset (Fin d))
    (U : Bits d) (i : Fin d) : Decidable (survivalTest m S U i) :=
  inferInstanceAs (Decidable (i ∈ S ∧ ((favorable S U).erase i).card < m))

theorem favorable_subset {d : ℕ} (S : Finset (Fin d)) (U : Bits d) :
    favorable S U ⊆ S := Finset.filter_subset _ _

theorem survivalTest_of_false {d m : ℕ} (S : Finset (Fin d)) (U : Bits d) (i : Fin d)
    (hu : U i = false) :
    survivalTest m S U i ↔ i ∈ S ∧ (favorable S U).card < m := by
  have hi : i ∉ favorable S U := by simp [favorable, hu]
  simp [survivalTest, Finset.erase_eq_of_notMem hi]

theorem survivalTest_of_true {d m : ℕ} (S : Finset (Fin d)) (U : Bits d) (i : Fin d)
    (hu : U i = true) :
    survivalTest m S U i ↔ i ∈ S ∧ (favorable S U).card ≤ m := by
  by_cases hi : i ∈ S
  · have hif : i ∈ favorable S U := by simp [favorable, hi, hu]
    have hp : 0 < (favorable S U).card := Finset.card_pos.mpr ⟨i, hif⟩
    simp only [survivalTest, hi, true_and, Finset.card_erase_of_mem hif]
    omega
  · simp [survivalTest, hi]

/-- Fixing the other bits yields the SAME event in both tested-bit worlds. -/
theorem survivalTest_update {d m : ℕ} (S : Finset (Fin d)) (U : Bits d)
    (i : Fin d) (b : Bool) :
    survivalTest m S (Function.update U i b) i ↔ survivalTest m S U i := by
  have heq : (favorable S (Function.update U i b)).erase i = (favorable S U).erase i := by
    ext j
    by_cases hji : j = i <;> simp [favorable, hji, Function.update]
  simp only [survivalTest, heq]

theorem false_witnesses_eq {d m : ℕ} (S : Finset (Fin d)) (U : Bits d) :
    Finset.univ.filter (fun i => U i = false ∧ survivalTest m S U i) =
      if (favorable S U).card < m then S \ favorable S U else ∅ := by
  classical
  ext i
  by_cases hN : (favorable S U).card < m
  · simp only [hN, if_true, Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_sdiff]
    cases hu : U i
    · simp [survivalTest_of_false S U i hu, favorable, hu]
      exact fun _ => hN
    · simp [favorable, hu]
  · simp only [hN, if_false, Finset.mem_filter, Finset.mem_univ, true_and,
      Finset.notMem_empty, iff_false, not_and]
    intro hu
    simp [survivalTest_of_false S U i hu, hN]

theorem true_witnesses_eq {d m : ℕ} (S : Finset (Fin d)) (U : Bits d) :
    Finset.univ.filter (fun i => U i = true ∧ survivalTest m S U i) =
      if (favorable S U).card ≤ m then favorable S U else ∅ := by
  classical
  ext i
  by_cases hN : (favorable S U).card ≤ m
  · simp only [hN, if_true, Finset.mem_filter, Finset.mem_univ, true_and]
    cases hu : U i
    · simp [favorable, hu]
    · simp [survivalTest_of_true S U i hu, favorable, hu]
      exact fun _ => hN
  · simp only [hN, if_false, Finset.mem_filter, Finset.mem_univ, true_and,
      Finset.notMem_empty, iff_false, not_and]
    intro hu
    simp [survivalTest_of_true S U i hu, hN]

theorem sum_false_survivalTests {d m : ℕ} (S : Finset (Fin d)) (U : Bits d) :
    (∑ i : Fin d, if U i = false ∧ survivalTest m S U i then (1 : ℝ) else 0) =
      if (favorable S U).card < m then (S.card : ℝ) - (favorable S U).card else 0 := by
  classical
  have hc := congrArg (fun s : Finset (Fin d) => (s.card : ℝ)) (false_witnesses_eq (m := m) S U)
  simpa only [Finset.card_filter, Nat.cast_sum, Nat.cast_ite, Nat.cast_one, Nat.cast_zero,
    apply_ite, Finset.card_sdiff_of_subset (favorable_subset S U),
    Nat.cast_sub (Finset.card_le_card (favorable_subset S U)), Finset.card_empty] using hc

theorem sum_true_survivalTests {d m : ℕ} (S : Finset (Fin d)) (U : Bits d) :
    (∑ i : Fin d, if U i = true ∧ survivalTest m S U i then (1 : ℝ) else 0) =
      if (favorable S U).card ≤ m then ((favorable S U).card : ℝ) else 0 := by
  classical
  have hc := congrArg (fun s : Finset (Fin d) => (s.card : ℝ)) (true_witnesses_eq (m := m) S U)
  simpa only [Finset.card_filter, Nat.cast_sum, Nat.cast_ite, Nat.cast_one, Nat.cast_zero,
    apply_ite, Finset.card_empty] using hc

theorem sum_false_survivalTests_ge {d m : ℕ} (S : Finset (Fin d)) (U : Bits d)
    (hS : (7 / 8 : ℝ) * d ≤ S.card) :
    (if (favorable S U).card < m then (7 / 8 : ℝ) * d - m else 0) ≤
      ∑ i : Fin d, if U i = false ∧ survivalTest m S U i then (1 : ℝ) else 0 := by
  rw [sum_false_survivalTests]
  split_ifs with hN
  · have hNR : ((favorable S U).card : ℝ) ≤ m := by exact_mod_cast hN.le
    linarith
  · rfl

theorem sum_true_survivalTests_le {d m : ℕ} (S : Finset (Fin d)) (U : Bits d) :
    (∑ i : Fin d, if U i = true ∧ survivalTest m S U i then (1 : ℝ) else 0) ≤ m := by
  rw [sum_true_survivalTests]
  split_ifs with hN
  · exact_mod_cast hN
  · positivity

def historySurvivalTest {d m : ℕ} (c : ℕ) (t : ℕ) (U : Bits d)
    (i : Fin d) : Set (History d m t) :=
  {h | survivalTest m (historyActiveItems c t h) U i}

theorem historyActiveItems_eq_mask {d m : ℕ} (c t : ℕ) (h : History d m t) :
    historyActiveItems c t h = Finset.univ.filter (fun i => activeMask c t h i = true) := by
  ext i
  simp only [historyActiveItems, Finset.mem_filter, Finset.mem_univ, true_and]
  change historyNatCount i t h < c ↔
    (if selectedCount i t h < (c : ℝ) then true else false) = true
  rw [← cast_historyNatCount]
  norm_cast
  simp

theorem measurable_historyActiveItems {d m : ℕ} (c t : ℕ) :
    Measurable (historyActiveItems (d := d) (m := m) c t) := by
  have heq : historyActiveItems (d := d) (m := m) c t =
      fun h => Finset.univ.filter (fun i => activeMask c t h i = true) :=
    funext (historyActiveItems_eq_mask c t)
  rw [heq]
  exact (measurable_of_finite (fun M : Bits d =>
    Finset.univ.filter (fun i => M i = true))).comp (measurable_activeMask c t)

theorem measurableSet_historySurvivalTest {d m : ℕ} (c t : ℕ)
    (U : Bits d) (i : Fin d) : MeasurableSet (historySurvivalTest (m := m) c t U i) := by
  exact (measurable_historyActiveItems c t)
    (Set.to_countable {S : Finset (Fin d) | survivalTest m S U i}).measurableSet

theorem historySurvivalTest_update {d m : ℕ} (c t : ℕ) (U : Bits d)
    (i : Fin d) (b : Bool) :
    historySurvivalTest (m := m) c t (Function.update U i b) i =
      historySurvivalTest (m := m) c t U i := by
  ext h
  exact survivalTest_update _ U i b

theorem favorable_history_eq {d m T : ℕ} (c t : ℕ) (xi : Table d T)
    (h : History d m t) :
    favorable (historyActiveItems c t h) xi.1 = favorableActiveItems c xi t h := by
  ext i
  simp only [favorable, historyActiveItems, favorableActiveItems, Finset.mem_filter,
    Finset.mem_univ, true_and]
  rw [← cast_historyNatCount]
  norm_cast
  tauto

end

end MsetsPaper.Lower.SparseCapped
