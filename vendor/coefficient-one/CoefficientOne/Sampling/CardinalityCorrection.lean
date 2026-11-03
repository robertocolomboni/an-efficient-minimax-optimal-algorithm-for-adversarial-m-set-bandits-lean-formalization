import CoefficientOne.Sampling.DummyCardinality
import Mathlib.MeasureTheory.Function.Floor

/-! # Borel correction on the null exceptional seeds -/

open MeasureTheory Filter EffectiveResistance

namespace CoefficientOne.Sampling
noncomputable section

def cardinalityCorrect (n : ℕ) (s : ℝ) (S : Finset (Fin n)) : Finset (Fin n) :=
  if S.card = ⌊s⌋₊ ∨ S.card = ⌈s⌉₊ then S else initialSegment n ⌊s⌋₊

theorem cardinalityCorrect_card {n : ℕ} {s : ℝ} (hs : 0 ≤ s) (hsn : s ≤ n)
    (S : Finset (Fin n)) :
    (cardinalityCorrect n s S).card = ⌊s⌋₊ ∨ (cardinalityCorrect n s S).card = ⌈s⌉₊ := by
  unfold cardinalityCorrect
  split_ifs with h
  · exact h
  · exact Or.inl (initialSegment_card
      ((Nat.cast_le (α := ℝ)).mp ((Nat.floor_le hs).trans hsn)))

variable {X : Type*} [MeasurableSpace X]

theorem measurable_cardinalityCorrect {n : ℕ} {s : X → ℝ} {F : X → Finset (Fin n)}
    (hs : Measurable s) (hF : Measurable F) :
    Measurable (fun x => cardinalityCorrect n (s x) (F x)) := by
  have hcard : Measurable (fun x => (F x).card) :=
    (measurable_of_finite Finset.card).comp hF
  have he : MeasurableSet {x | (F x).card = ⌊s x⌋₊ ∨ (F x).card = ⌈s x⌉₊} :=
    (measurableSet_eq_fun hcard hs.nat_floor).union (measurableSet_eq_fun hcard hs.nat_ceil)
  exact Measurable.ite he hF ((measurable_of_countable (initialSegment n)).comp hs.nat_floor)

theorem cardinalityCorrect_ae_eq {n : ℕ} (μ : Measure X) (s : X → ℝ) (F : X → Finset (Fin n))
    (hcard : ∀ᵐ x ∂μ, (F x).card = ⌊s x⌋₊ ∨ (F x).card = ⌈s x⌉₊) :
    (fun x => cardinalityCorrect n (s x) (F x)) =ᵐ[μ] F := by
  exact hcard.mono fun x hx => by simp only [cardinalityCorrect, if_pos hx]

theorem cardinalityCorrect_integral {n : ℕ} (μ : Measure X) (s : X → ℝ)
    (F : X → Finset (Fin n))
    (hcard : ∀ᵐ x ∂μ, (F x).card = ⌊s x⌋₊ ∨ (F x).card = ⌈s x⌉₊)
    (φ : Finset (Fin n) → ℝ) :
    (∫ x, φ (cardinalityCorrect n (s x) (F x)) ∂μ) = ∫ x, φ (F x) ∂μ :=
  integral_congr_ae ((cardinalityCorrect_ae_eq μ s F hcard).mono fun _ h => congrArg φ h)

theorem cardinalityCorrect_expectedDistance {n : ℕ} (μ : Measure X) [IsFiniteMeasure μ]
    (s t : X → ℝ) (F G : X → Finset (Fin n))
    (hF : ∀ᵐ x ∂μ, (F x).card = ⌊s x⌋₊ ∨ (F x).card = ⌈s x⌉₊)
    (hG : ∀ᵐ x ∂μ, (G x).card = ⌊t x⌋₊ ∨ (G x).card = ⌈t x⌉₊) :
    expectedOutputDistance μ (fun x => cardinalityCorrect n (s x) (F x))
      (fun x => cardinalityCorrect n (t x) (G x)) = expectedOutputDistance μ F G := by
  apply integral_congr_ae
  filter_upwards [cardinalityCorrect_ae_eq μ s F hF, cardinalityCorrect_ae_eq μ t G hG] with x hx hy
  rw [hx, hy]

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

theorem measurable_sampleIndicator {F : X → Finset ι} (hF : Measurable F) (i : ι) :
    Measurable (fun x => indicator i (F x)) :=
  (measurable_of_finite (indicator i)).comp hF

theorem integrable_sampleIndicator (μ : Measure X) [IsFiniteMeasure μ]
    {F : X → Finset ι} (hF : Measurable F) (i : ι) :
    Integrable (fun x => indicator i (F x)) μ := by
  apply Integrable.mono' (integrable_const (1 : ℝ)) (measurable_sampleIndicator hF i).aestronglyMeasurable
  exact Eventually.of_forall fun x => by simp [indicator]; split_ifs <;> norm_num

theorem integral_sampleIndicator_eq_probability (μ : Measure X)
    {F : X → Finset ι} (hF : Measurable F) (i : ι) :
    (∫ x, indicator i (F x) ∂μ) = (μ {x | i ∈ F x}).toReal := by
  classical
  have hs : MeasurableSet {x | i ∈ F x} := by
    exact hF (Set.toFinite {S : Finset ι | i ∈ S}).measurableSet
  have he : (fun x => indicator i (F x)) =
      ({x | i ∈ F x} : Set X).indicator (fun _ => (1 : ℝ)) := by
    funext x
    simp only [indicator, Set.indicator_apply, Set.mem_setOf_eq]
  rw [he, integral_indicator_const (1 : ℝ) hs]
  simp only [smul_eq_mul, mul_one, measureReal_def]

theorem probability_member_eq_of_integral (μ : Measure X) [IsFiniteMeasure μ]
    {F : X → Finset ι} (hF : Measurable F) (i : ι) {p : ℝ}
    (hmean : (∫ x, indicator i (F x) ∂μ) = p) :
    μ {x | i ∈ F x} = ENNReal.ofReal p := by
  rw [integral_sampleIndicator_eq_probability μ hF i] at hmean
  rw [← hmean, ENNReal.ofReal_toReal (measure_ne_top μ _)]

theorem sampleIndicator_zero_forces_exclusion (μ : Measure X) [IsFiniteMeasure μ]
    {F : X → Finset ι} (hF : Measurable F) (i : ι)
    (hmean : (∫ x, indicator i (F x) ∂μ) = 0) : ∀ᵐ x ∂μ, i ∉ F x := by
  have hn : 0 ≤ᵐ[μ] fun x => indicator i (F x) :=
    Eventually.of_forall fun x => by simp [indicator]; split_ifs <;> norm_num
  have hz := (integral_eq_zero_iff_of_nonneg_ae hn (integrable_sampleIndicator μ hF i)).mp hmean
  filter_upwards [hz] with x hx
  simpa [indicator] using hx

theorem sampleIndicator_one_forces_inclusion (μ : Measure X) [IsProbabilityMeasure μ]
    {F : X → Finset ι} (hF : Measurable F) (i : ι)
    (hmean : (∫ x, indicator i (F x) ∂μ) = 1) : ∀ᵐ x ∂μ, i ∈ F x := by
  have hn : 0 ≤ᵐ[μ] fun x => 1 - indicator i (F x) :=
    Eventually.of_forall fun x => by simp [indicator]; split_ifs <;> norm_num
  have hi := (integrable_const (1 : ℝ)).sub (integrable_sampleIndicator μ hF i)
  have hz : (∫ x, 1 - indicator i (F x) ∂μ) = 0 := by
    rw [integral_sub (integrable_const _) (integrable_sampleIndicator μ hF i), hmean]
    simp
  have he := (integral_eq_zero_iff_of_nonneg_ae hn hi).mp hz
  filter_upwards [he] with x hx
  by_contra hm
  simp [indicator, hm] at hx

theorem liftedSampler_cardinality_ae {k : ℕ} (μ : Measure X) [IsProbabilityMeasure μ]
    {s : ℝ} (hs : 0 ≤ s) (hsk : s ≤ k) (F : X → Finset (ι ⊕ Fin k))
    (hF : Measurable F) (hcard : ∀ x, (F x).card = k)
    (hmean : ∀ j, (∫ x, indicator (Sum.inr j) (F x) ∂μ) =
      dummyCoordinate ((k : ℝ) - s) j.val) :
    ∀ᵐ x ∂μ, (F x).toLeft.card = ⌊s⌋₊ ∨ (F x).toLeft.card = ⌈s⌉₊ := by
  have hzero : ∀ j : Fin k, ∀ᵐ x ∂μ,
      dummyCoordinate ((k : ℝ) - s) j.val = 0 → Sum.inr j ∉ F x := by
    intro j
    by_cases hj : dummyCoordinate ((k : ℝ) - s) j.val = 0
    · exact (sampleIndicator_zero_forces_exclusion μ hF (Sum.inr j) ((hmean j).trans hj)).mono
        fun x hx _ => hx
    · exact Eventually.of_forall fun _ h => (hj h).elim
  have hone : ∀ j : Fin k, ∀ᵐ x ∂μ,
      dummyCoordinate ((k : ℝ) - s) j.val = 1 → Sum.inr j ∈ F x := by
    intro j
    by_cases hj : dummyCoordinate ((k : ℝ) - s) j.val = 1
    · exact (sampleIndicator_one_forces_inclusion μ hF (Sum.inr j) ((hmean j).trans hj)).mono
        fun x hx _ => hx
    · exact Eventually.of_forall fun _ h => (hj h).elim
  filter_upwards [ae_all_iff.mpr hzero, ae_all_iff.mpr hone] with x hx hy
  exact realSelected_card_floor_or_ceil hs hsk (F x) (hcard x) hx hy

end
end CoefficientOne.Sampling
