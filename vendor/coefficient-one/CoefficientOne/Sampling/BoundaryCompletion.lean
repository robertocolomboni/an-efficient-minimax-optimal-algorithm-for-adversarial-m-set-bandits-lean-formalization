import CoefficientOne.Sampling.OutputMetric
import Mathlib.MeasureTheory.OuterMeasure.BorelCantelli

/-!
# The Borel completion by eventual values

This is the countable-fiber construction in the proof of Corollary 2(i).
It is defined everywhere, including sequences which do not stabilize.
-/

open Set Filter MeasureTheory
open scoped Topology

namespace CoefficientOne.Sampling

noncomputable section

variable {Y X : Type*}

def StableValue (f : ℕ → Y) (y : Y) : Prop := ∃ N, ∀ j, N ≤ j → f j = y

theorem stableValue_unique {f : ℕ → Y} {y z : Y}
    (hy : StableValue f y) (hz : StableValue f z) : y = z := by
  obtain ⟨N, hN⟩ := hy
  obtain ⟨M, hM⟩ := hz
  exact (hN (max N M) (le_max_left ..)).symm.trans (hM (max N M) (le_max_right ..))

def finiteCompletion (fallback : Y) (f : ℕ → Y) : Y := by
  classical
  exact if h : ∃ y, StableValue f y then Classical.choose h else fallback

theorem finiteCompletion_of_stable {f : ℕ → Y} (fallback : Y) {y : Y}
    (hy : StableValue f y) : finiteCompletion fallback f = y := by
  classical
  have he : ∃ z, StableValue f z := ⟨y, hy⟩
  simp only [finiteCompletion, dif_pos he]
  exact stableValue_unique (Classical.choose_spec he) hy

theorem finiteCompletion_eq_iff (fallback y : Y) (f : ℕ → Y) :
    finiteCompletion fallback f = y ↔
      StableValue f y ∨ (y = fallback ∧ ¬ ∃ z, StableValue f z) := by
  classical
  by_cases he : ∃ z, StableValue f z
  · obtain ⟨z, hz⟩ := he
    rw [finiteCompletion_of_stable fallback hz]
    constructor
    · rintro rfl
      exact Or.inl hz
    · rintro (hy | ⟨_, hn⟩)
      · exact stableValue_unique hz hy
      · exact (hn ⟨z, hz⟩).elim
  · simp only [finiteCompletion, dif_neg he]
    constructor
    · intro h
      exact Or.inr ⟨h.symm, he⟩
    · rintro (hy | ⟨hy, _⟩)
      · exact (he ⟨y, hy⟩).elim
      · exact hy.symm

theorem finiteCompletion_property (P : Y → Prop) (fallback : Y) (hfallback : P fallback)
    (f : ℕ → Y) (hf : ∀ j, P (f j)) : P (finiteCompletion fallback f) := by
  classical
  by_cases he : ∃ y, StableValue f y
  · obtain ⟨y, hy⟩ := he
    rw [finiteCompletion_of_stable fallback hy]
    obtain ⟨N, hN⟩ := hy
    exact hN N le_rfl ▸ hf N
  · simpa only [finiteCompletion, dif_neg he] using hfallback

theorem exists_stableValue_iff (f : ℕ → Y) :
    (∃ y, StableValue f y) ↔ ∃ N, ∀ j, N ≤ j → f j = f N := by
  constructor
  · rintro ⟨y, N, hN⟩
    exact ⟨N, fun j hj => (hN j hj).trans (hN N le_rfl).symm⟩
  · rintro ⟨N, hN⟩
    exact ⟨f N, N, hN⟩

variable [MeasurableSpace X] [MeasurableSpace Y] [MeasurableSingletonClass Y]

theorem measurableSet_stableValue (A : ℕ → X → Y) (hA : ∀ j, Measurable (A j)) (y : Y) :
    MeasurableSet {x | StableValue (fun j => A j x) y} := by
  have he : {x | StableValue (fun j => A j x) y} =
      ⋃ N : ℕ, ⋂ j : ℕ, {x | N ≤ j → A j x = y} := by
    ext x
    simp [StableValue]
  rw [he]
  apply MeasurableSet.iUnion
  intro N
  apply MeasurableSet.iInter
  intro j
  by_cases hNj : N ≤ j
  · convert (hA j) (measurableSet_singleton y) using 1 <;> ext x <;> simp [hNj]
  · simp [hNj]

theorem measurableSet_hasStableValue [Countable Y] (A : ℕ → X → Y)
    (hA : ∀ j, Measurable (A j)) :
    MeasurableSet {x | ∃ y, StableValue (fun j => A j x) y} := by
  have he : {x | ∃ y, StableValue (fun j => A j x) y} =
      ⋃ y : Y, {x | StableValue (fun j => A j x) y} := by ext; simp
  rw [he]
  exact MeasurableSet.iUnion (measurableSet_stableValue A hA)

theorem measurable_finiteCompletion [Countable Y] (fallback : Y) (A : ℕ → X → Y)
    (hA : ∀ j, Measurable (A j)) :
    Measurable (fun x => finiteCompletion fallback (fun j => A j x)) := by
  classical
  apply measurable_to_countable'
  intro y
  have he : {x | finiteCompletion fallback (fun j => A j x) = y} =
      {x | StableValue (fun j => A j x) y} ∪
      {x | y = fallback ∧ ¬ ∃ z, StableValue (fun j => A j x) z} := by
    ext x
    exact finiteCompletion_eq_iff fallback y (fun j => A j x)
  change MeasurableSet {x | finiteCompletion fallback (fun j => A j x) = y}
  rw [he]
  apply (measurableSet_stableValue A hA y).union
  by_cases hy : y = fallback
  · convert (measurableSet_hasStableValue A hA).compl using 1 <;> ext x <;> simp [hy]
  · simp [hy]

theorem stableValue_of_eventually_adjacent_eq (f : ℕ → Y)
    (hf : ∀ᶠ j in atTop, f (j + 1) = f j) : ∃ y, StableValue f y := by
  obtain ⟨N, hN⟩ := eventually_atTop.1 hf
  refine ⟨f N, N, ?_⟩
  intro j hj
  induction j, hj using Nat.le_induction with
  | base => rfl
  | succ j hj ih => exact (hN j hj).trans ih

theorem outputDistance_ge_two_of_card_eq {ι : Type*} [Fintype ι] [DecidableEq ι]
    {S T : Finset ι} (hc : S.card = T.card) (hne : S ≠ T) :
    2 ≤ outputDistance S T := by
  classical
  have hnST : ¬ S ⊆ T := fun h => hne (Finset.eq_of_subset_of_card_le h hc.ge)
  have hnTS : ¬ T ⊆ S := fun h => hne (Finset.eq_of_subset_of_card_le h hc.le).symm
  obtain ⟨a, haS, haT⟩ := Finset.not_subset.mp hnST
  obtain ⟨b, hbT, hbS⟩ := Finset.not_subset.mp hnTS
  have hab : a ≠ b := fun he => haT (he ▸ hbT)
  have hs : {a, b} ⊆ symmDiff S T := by
    intro i hi
    rcases Finset.mem_insert.mp hi with rfl | hi
    · exact Finset.mem_symmDiff.mpr (Or.inl ⟨haS, haT⟩)
    · have hi' : i = b := Finset.mem_singleton.mp hi
      subst i
      exact Finset.mem_symmDiff.mpr (Or.inr ⟨hbT, hbS⟩)
  have hcard := Finset.card_le_card hs
  simp only [Finset.card_pair hab] at hcard
  unfold outputDistance
  exact_mod_cast hcard

theorem ae_stableValue_of_summable_disagreement (μ : Measure X) (A : ℕ → X → Y)
    (hs : (∑' j, μ {x | A (j + 1) x ≠ A j x}) ≠ ⊤) :
    ∀ᵐ x ∂μ, ∃ y, StableValue (fun j => A j x) y := by
  have h := ae_eventually_notMem hs
  filter_upwards [h] with x hx
  apply stableValue_of_eventually_adjacent_eq
  exact hx.mono fun j hj => by simpa only [Set.mem_setOf_eq, not_not] using hj

theorem measure_disagreement_le_half_expected {ι : Type*} [Fintype ι] [DecidableEq ι]
    (μ : Measure X) [IsFiniteMeasure μ] {F G : X → Finset ι}
    (hF : Measurable F) (hG : Measurable G) (hc : ∀ x, (F x).card = (G x).card) :
    μ {x | F x ≠ G x} ≤ ENNReal.ofReal (expectedOutputDistance μ F G / 2) := by
  have hi := (integrable_outputDistance μ hF hG).div_const 2
  have hn : 0 ≤ᵐ[μ] fun x => outputDistance (F x) (G x) / 2 :=
    Eventually.of_forall fun x => div_nonneg (outputDistance_nonneg _ _) (by norm_num)
  have hm := hi.measure_le_integral hn (s := {x | F x ≠ G x}) (fun x hx => by
    have hh := outputDistance_ge_two_of_card_eq (hc x) hx
    linarith)
  simpa only [integral_div, expectedOutputDistance] using hm

theorem ae_stableValue_of_summable_expected {ι : Type*} [Fintype ι] [DecidableEq ι]
    (μ : Measure X) [IsFiniteMeasure μ] (A : ℕ → X → Finset ι)
    (hA : ∀ j, Measurable (A j))
    (hc : ∀ j x, (A (j + 1) x).card = (A j x).card)
    (hs : Summable (fun j => expectedOutputDistance μ (A (j + 1)) (A j))) :
    ∀ᵐ x ∂μ, ∃ S, StableValue (fun j => A j x) S := by
  apply ae_stableValue_of_summable_disagreement
  apply ne_top_of_le_ne_top (hs.div_const 2).tsum_ofReal_ne_top
  exact ENNReal.tsum_le_tsum (fun j =>
    measure_disagreement_le_half_expected μ (hA (j + 1)) (hA j) (hc j))

theorem eventually_eq_finiteCompletion (fallback : Y) {f : ℕ → Y}
    (hf : ∃ y, StableValue f y) : ∀ᶠ j in atTop, f j = finiteCompletion fallback f := by
  obtain ⟨y, hy⟩ := hf
  rw [finiteCompletion_of_stable fallback hy]
  exact eventually_atTop.2 hy

/-- Bounded convergence for every observable on the finite output space. -/
theorem integral_finiteCompletion_tendsto [Fintype Y] (μ : Measure X) [IsFiniteMeasure μ]
    (fallback : Y) (A : ℕ → X → Y) (hA : ∀ j, Measurable (A j))
    (hs : ∀ᵐ x ∂μ, ∃ y, StableValue (fun j => A j x) y) (φ : Y → ℝ) :
    Tendsto (fun j => ∫ x, φ (A j x) ∂μ) atTop
      (𝓝 (∫ x, φ (finiteCompletion fallback (fun j => A j x)) ∂μ)) := by
  classical
  apply tendsto_integral_of_dominated_convergence (fun _ => ∑ y : Y, ‖φ y‖)
  · intro j
    have hφ : Measurable φ := measurable_of_finite φ
    exact (show Measurable (fun x => φ (A j x)) from fun s hs => hA j (hφ hs)).aestronglyMeasurable
  · exact integrable_const _
  · intro j
    exact Eventually.of_forall fun x => Finset.single_le_sum
      (fun y _ => norm_nonneg (φ y)) (Finset.mem_univ (A j x))
  · filter_upwards [hs] with x hx
    have he := (eventually_eq_finiteCompletion fallback hx).mono
      (fun j hj => congrArg φ hj)
    rw [Filter.tendsto_congr' he]
    exact tendsto_const_nhds

/-- The two stabilization events are intersected only for this fixed pair. -/
theorem expectedOutputDistance_completion_tendsto {ι : Type*} [Fintype ι] [DecidableEq ι]
    (μ : Measure X) [IsFiniteMeasure μ] (fallback : Finset ι)
    (A B : ℕ → X → Finset ι) (hA : ∀ j, Measurable (A j)) (hB : ∀ j, Measurable (B j))
    (hsA : ∀ᵐ x ∂μ, ∃ S, StableValue (fun j => A j x) S)
    (hsB : ∀ᵐ x ∂μ, ∃ S, StableValue (fun j => B j x) S) :
    Tendsto (fun j => expectedOutputDistance μ (A j) (B j)) atTop
      (𝓝 (expectedOutputDistance μ
        (fun x => finiteCompletion fallback (fun j => A j x))
        (fun x => finiteCompletion fallback (fun j => B j x)))) := by
  unfold expectedOutputDistance
  apply tendsto_integral_of_dominated_convergence (fun _ => (Fintype.card ι : ℝ))
  · intro j
    exact (measurable_outputDistance (hA j) (hB j)).aestronglyMeasurable
  · exact integrable_const _
  · intro j
    exact Eventually.of_forall fun x => by
      rw [Real.norm_eq_abs, abs_of_nonneg (outputDistance_nonneg _ _)]
      exact outputDistance_le_card _ _
  · filter_upwards [hsA, hsB] with x hxA hxB
    have heA := eventually_eq_finiteCompletion fallback hxA
    have heB := eventually_eq_finiteCompletion fallback hxB
    have he := (heA.and heB).mono (fun j hj => congrArg₂ outputDistance hj.1 hj.2)
    rw [Filter.tendsto_congr' he]
    exact tendsto_const_nhds

theorem expectedOutputDistance_completion_le {ι : Type*} [Fintype ι] [DecidableEq ι]
    (μ : Measure X) [IsFiniteMeasure μ] (fallback : Finset ι)
    (A B : ℕ → X → Finset ι) (hA : ∀ j, Measurable (A j)) (hB : ∀ j, Measurable (B j))
    (hsA : ∀ᵐ x ∂μ, ∃ S, StableValue (fun j => A j x) S)
    (hsB : ∀ᵐ x ∂μ, ∃ S, StableValue (fun j => B j x) S)
    {c : ℕ → ℝ} {L : ℝ} (hc : Tendsto c atTop (𝓝 L))
    (hb : ∀ j, expectedOutputDistance μ (A j) (B j) ≤ c j) :
    expectedOutputDistance μ
        (fun x => finiteCompletion fallback (fun j => A j x))
        (fun x => finiteCompletion fallback (fun j => B j x)) ≤ L := by
  exact le_of_tendsto_of_tendsto
    (expectedOutputDistance_completion_tendsto μ fallback A B hA hB hsA hsB)
    hc (Eventually.of_forall hb)

end
end CoefficientOne.Sampling
