import MsetsLower.Prelude
import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.Data.Finset.Card

/-!
# Averaging finitely many events

This module proves the measure-theoretic averaging step used in
`eq:lower-confidence-average-event`.  It is deliberately independent of the
confidence construction: a pointwise lower bound on the fraction of events
holding on a high-probability good set is integrated exactly.
-/

namespace MsetsLower.Probability

open MeasureTheory Set
open scoped BigOperators

noncomputable section

/-- Fraction of a finite family of events which occurs at an outcome. -/
def eventFraction
    {Omega ι : Type*} (s : Finset ι) (E : ι → Set Omega) (omega : Omega) : Real :=
  (∑ i ∈ s, (E i).indicator (fun _ => (1 : Real)) omega) / (s.card : Real)

/-- Fraction of a finite family of scores above a threshold. -/
def highScoreFraction
    {ι : Type*} (s : Finset ι) (score : ι → Real) (threshold : Real) : Real :=
  ((s.filter fun i => threshold ≤ score i).card : Real) / (s.card : Real)

theorem eventFraction_eq_highScoreFraction
    {Omega ι : Type*} (s : Finset ι) (score : ι → Omega → Real)
    (threshold : Real) (omega : Omega) :
    eventFraction s (fun i => {x | threshold ≤ score i x}) omega =
      highScoreFraction s (fun i => score i omega) threshold := by
  classical
  unfold eventFraction highScoreFraction
  congr 1
  rw [show ∑ i ∈ s,
      ({x | threshold ≤ score i x} : Set Omega).indicator
          (fun _ => (1 : Real)) omega =
        ∑ i ∈ s, if threshold ≤ score i omega then (1 : Real) else 0 by
      apply Finset.sum_congr rfl
      intro i hi
      by_cases hscore : threshold ≤ score i omega <;>
        simp [Set.indicator_of_mem, Set.indicator_of_notMem, hscore]]
  rw [Finset.sum_boole]

/-- The finite counting argument below
`eq:lower-confidence-average-score`: an average at least `M/4`, while every
score is at most `17M/16`, forces at least a `2/15` fraction of scores to be
at least `M/8`. -/
theorem highScoreFraction_ge_two_fifteenths
    {ι : Type*} (s : Finset ι) (hs : s.Nonempty)
    (score : ι → Real) {M : Real} (hM : 0 < M)
    (haverage : M / 4 ≤ (∑ i ∈ s, score i) / (s.card : Real))
    (hupper : ∀ i ∈ s, score i ≤ (17 : Real) * M / 16) :
    (2 : Real) / 15 ≤ highScoreFraction s score (M / 8) := by
  classical
  let high := s.filter fun i => M / 8 ≤ score i
  let low := s.filter fun i => ¬ M / 8 ≤ score i
  have hcardNat : high.card + low.card = s.card := by
    simpa [high, low] using
      (Finset.card_filter_add_card_filter_not (s := s)
        (fun i => M / 8 ≤ score i))
  have hcardReal : (high.card : Real) + (low.card : Real) = (s.card : Real) := by
    exact_mod_cast hcardNat
  have hNpos : (0 : Real) < s.card := by
    exact_mod_cast hs.card_pos
  have hhigh : (∑ i ∈ high, score i) ≤
      (high.card : Real) * ((17 : Real) * M / 16) := by
    calc
      (∑ i ∈ high, score i) ≤
          ∑ _i ∈ high, ((17 : Real) * M / 16) := by
        apply Finset.sum_le_sum
        intro i hi
        have hi' : i ∈ s.filter (fun j => M / 8 ≤ score j) := by
          simpa [high] using hi
        exact hupper i (Finset.mem_filter.mp hi').1
      _ = (high.card : Real) * ((17 : Real) * M / 16) := by simp
  have hlow : (∑ i ∈ low, score i) ≤
      (low.card : Real) * (M / 8) := by
    calc
      (∑ i ∈ low, score i) ≤ ∑ _i ∈ low, M / 8 := by
        apply Finset.sum_le_sum
        intro i hi
        have hi' : i ∈ s.filter (fun j => ¬M / 8 ≤ score j) := by
          simpa [low] using hi
        have hnot : ¬M / 8 ≤ score i := (Finset.mem_filter.mp hi').2
        exact le_of_lt (not_le.mp hnot)
      _ = (low.card : Real) * (M / 8) := by simp
  have hsplit : (∑ i ∈ s, score i) =
      (∑ i ∈ high, score i) + ∑ i ∈ low, score i := by
    simpa [high, low] using
      (Finset.sum_filter_add_sum_filter_not s
        (fun i => M / 8 ≤ score i) score).symm
  have hsumUpper : (∑ i ∈ s, score i) ≤
      (high.card : Real) * ((17 : Real) * M / 16) +
        (low.card : Real) * (M / 8) := by
    rw [hsplit]
    exact add_le_add hhigh hlow
  have hsumLower : M / 4 * (s.card : Real) ≤ ∑ i ∈ s, score i :=
    (le_div_iff₀ hNpos).mp haverage
  have hcount : (2 : Real) / 15 * (s.card : Real) ≤ high.card := by
    nlinarith
  unfold highScoreFraction
  change (2 : Real) / 15 ≤
    ((s.filter fun i => M / 8 ≤ score i).card : Real) / (s.card : Real)
  apply (le_div_iff₀ hNpos).2
  simpa [high] using hcount

theorem measurable_eventFraction
    {Omega ι : Type*} [MeasurableSpace Omega]
    (s : Finset ι) (E : ι → Set Omega)
    (hE : ∀ i ∈ s, MeasurableSet (E i)) :
    Measurable (eventFraction s E) := by
  apply Measurable.div_const
  exact Finset.measurable_fun_sum s fun i hi =>
    measurable_const.indicator (hE i hi)

theorem eventFraction_nonneg
    {Omega ι : Type*} (s : Finset ι) (E : ι → Set Omega) (omega : Omega) :
    0 ≤ eventFraction s E omega := by
  unfold eventFraction
  apply div_nonneg
  · apply Finset.sum_nonneg
    intro i hi
    by_cases hmem : omega ∈ E i
    · simp [Set.indicator_of_mem hmem]
    · simp [Set.indicator_of_notMem hmem]
  · positivity

theorem integrable_eventFraction
    {Omega ι : Type*} [MeasurableSpace Omega]
    (P : Measure Omega) [IsFiniteMeasure P]
    (s : Finset ι) (E : ι → Set Omega)
    (hE : ∀ i ∈ s, MeasurableSet (E i)) :
    Integrable (eventFraction s E) P := by
  unfold eventFraction
  apply Integrable.div_const
  exact integrable_finsetSum s fun i hi =>
    (integrable_const (1 : Real)).indicator (hE i hi)

/-- The expectation of the occurring-event fraction is the average of the
individual event probabilities. -/
theorem integral_eventFraction
    {Omega ι : Type*} [MeasurableSpace Omega]
    (P : Measure Omega) [IsFiniteMeasure P]
    (s : Finset ι) (E : ι → Set Omega)
    (hE : ∀ i ∈ s, MeasurableSet (E i)) :
    (∫ omega, eventFraction s E omega ∂P) =
      (∑ i ∈ s, P.real (E i)) / (s.card : Real) := by
  unfold eventFraction
  rw [integral_div]
  rw [integral_finsetSum s]
  · apply congrArg (fun x : Real => x / (s.card : Real))
    apply Finset.sum_congr rfl
    intro i hi
    exact integral_indicator_one (hE i hi)
  · intro i hi
    exact (integrable_const (1 : Real)).indicator (hE i hi)

/-- Exact probability form of the final integration in
`eq:lower-confidence-average-event`.

On a set of probability at least `15/16`, if at least a `2/15` fraction of
the events occurs pointwise, then their average probability is at least
`1/8`. -/
theorem average_event_probability_ge_one_eighth
    {Omega ι : Type*} [MeasurableSpace Omega]
    (P : Measure Omega) [IsProbabilityMeasure P]
    (s : Finset ι)
    (E : ι → Set Omega) (hE : ∀ i ∈ s, MeasurableSet (E i))
    (G : Set Omega) (hG : MeasurableSet G)
    (hGprob : (15 : Real) / 16 ≤ P.real G)
    (hfraction : ∀ omega ∈ G, (2 : Real) / 15 ≤ eventFraction s E omega) :
    (1 : Real) / 8 ≤ (∑ i ∈ s, P.real (E i)) / (s.card : Real) := by
  let beta : Omega → Real := G.indicator (fun _ => (2 : Real) / 15)
  have hbeta_integrable : Integrable beta P := by
    exact (integrable_const ((2 : Real) / 15)).indicator hG
  have halpha_integrable : Integrable (eventFraction s E) P :=
    integrable_eventFraction P s E hE
  have hpoint : ∀ omega, beta omega ≤ eventFraction s E omega := by
    intro omega
    by_cases homega : omega ∈ G
    · simpa [beta, Set.indicator_of_mem homega] using hfraction omega homega
    · have hnonneg := eventFraction_nonneg s E omega
      simpa [beta, Set.indicator_of_notMem homega] using hnonneg
  have hmono : (∫ omega, beta omega ∂P) ≤
      ∫ omega, eventFraction s E omega ∂P :=
    integral_mono hbeta_integrable halpha_integrable hpoint
  have hbeta_integral :
      (∫ omega, beta omega ∂P) = P.real G * ((2 : Real) / 15) := by
    dsimp [beta]
    simpa [smul_eq_mul] using
      (integral_indicator_const (μ := P) ((2 : Real) / 15) hG)
  have hgood_integral :
      P.real G * ((2 : Real) / 15) ≤
        ∫ omega, eventFraction s E omega ∂P := by
    rwa [hbeta_integral] at hmono
  rw [integral_eventFraction P s E hE] at hgood_integral
  have hprob_nonneg : 0 ≤ P.real G := measureReal_nonneg
  nlinarith

end

end MsetsLower.Probability

#print axioms MsetsLower.Probability.integral_eventFraction
#print axioms MsetsLower.Probability.average_event_probability_ge_one_eighth
