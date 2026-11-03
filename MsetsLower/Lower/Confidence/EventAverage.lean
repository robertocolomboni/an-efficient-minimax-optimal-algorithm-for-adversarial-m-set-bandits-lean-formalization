import MsetsLower.Lower.Confidence.AverageScore
import MsetsLower.Probability.FiniteEventAverage

/-!
# From pathwise confidence scores to average event probability

This file closes the averaging step in `eq:lower-confidence-average-event`,
conditional only on the preceding good-event probability estimate.  The
candidate scores and both events are literal measurable functions of the
observable history.
-/

namespace MsetsLower.Lower.Confidence

open MsetsLower MeasureTheory Set
open scoped BigOperators

noncomputable section

theorem measurable_noiseShapeSum
    {n k : Nat} (noise : Nat → Real) :
    ∀ t, Measurable (noiseShapeSum (n := n) (k := k) noise t) := by
  intro t
  induction t with
  | zero => exact measurable_const
  | succ t ih => exact (ih.comp measurable_fst).add measurable_const

theorem measurable_confidenceScore
    {n k : Nat} (hkn : k ≤ n) (noise : Nat → Real)
    (Delta B : Real) (i : Fin n) :
    ∀ t, Measurable (confidenceScore hkn noise Delta B i t) := by
  intro t
  induction t with
  | zero => exact measurable_const
  | succ t ih =>
      have haction : Measurable (fun h : History n k (t + 1) => h.2.1) :=
        measurable_fst.comp measurable_snd
      have hpenalty : Measurable
          (fun h : History n k (t + 1) => candidatePenalty hkn h.2.1) :=
        (measurable_of_finite (candidatePenalty hkn)).comp haction
      have hactive : Measurable
          (fun h : History n k (t + 1) => activeIndicator hkn B t h.1) :=
        (measurable_activeIndicator hkn B t).comp measurable_fst
      have hmissed : Measurable
          (fun h : History n k (t + 1) => missedIndicator i h.2.1) :=
        (measurable_of_finite (missedIndicator i)).comp haction
      exact ((ih.comp measurable_fst).add hpenalty).add
        (((measurable_const.mul hactive).mul hmissed))

/-- The measurable good set from `eq:lower-confidence-good-event`, viewed on
the terminal observable history. -/
def confidenceGoodEvent
    {n k T : Nat} (hkn : k ≤ n) (noise : Nat → Real) (B : Real) :
    Set (History n k T) :=
  {h | cumulativePenalty hkn T h < B ∧
    (T : Real) / 2 ≤ noiseShapeSum noise T h}

theorem measurableSet_confidenceGoodEvent
    {n k T : Nat} (hkn : k ≤ n) (noise : Nat → Real) (B : Real) :
    MeasurableSet (confidenceGoodEvent (T := T) hkn noise B) := by
  exact (measurableSet_lt (measurable_cumulativePenalty hkn T) measurable_const).inter
    (measurableSet_le measurable_const (measurable_noiseShapeSum noise T))

/-- Candidate event `E_i={R_i ≥ ΔT/8}` from the manuscript. -/
def confidenceScoreEvent
    {n k T : Nat} (hkn : k ≤ n) (noise : Nat → Real)
    (Delta B : Real) (i : Fin n) : Set (History n k T) :=
  {h | Delta * T / 8 ≤ confidenceScore hkn noise Delta B i T h}

theorem measurableSet_confidenceScoreEvent
    {n k T : Nat} (hkn : k ≤ n) (noise : Nat → Real)
    (Delta B : Real) (i : Fin n) :
    MeasurableSet (confidenceScoreEvent (T := T) hkn noise Delta B i) :=
  measurableSet_le measurable_const
    (measurable_confidenceScore hkn noise Delta B i T)

theorem noiseShapeSum_le_time
    {n k : Nat} (noise : Nat → Real)
    (hnoise : ∀ t, noise t ∈ Icc (-1 : Real) 1) :
    ∀ (t : Nat) (h : History n k t), noiseShapeSum noise t h ≤ t := by
  intro t
  induction t with
  | zero => intro h; simp
  | succ t ih =>
      intro h
      rw [noiseShapeSum_succ]
      have hshape := (Feedback.shape_mem_Icc (hnoise t)).2
      have hprev := ih h.1
      push_cast
      linarith

theorem confidenceScore_le_cumulative_add_shape
    {n k : Nat} (hkn : k ≤ n) (noise : Nat → Real)
    (hnoise : ∀ t, noise t ∈ Icc (-1 : Real) 1)
    (Delta : Real) (hDelta : 0 ≤ Delta) (B : Real) (i : Fin n) :
    ∀ (t : Nat) (h : History n k t),
      confidenceScore hkn noise Delta B i t h ≤
        cumulativePenalty hkn t h + Delta * noiseShapeSum noise t h := by
  intro t
  induction t with
  | zero => intro h; simp [confidenceScore, cumulativePenalty, noiseShapeSum]
  | succ t ih =>
      intro h
      rw [confidenceScore_succ, cumulativePenalty_succ, noiseShapeSum_succ]
      have hshape := Feedback.shape_mem_Icc (hnoise t)
      have hactive := activeIndicator_mem_Icc hkn B t h.1
      have hmissed := missedIndicator_mem_Icc i h.2.1
      have hbase : 0 ≤ Delta * Feedback.shape (noise t) :=
        mul_nonneg hDelta hshape.1
      have hbonus :
          Delta * Feedback.shape (noise t) * activeIndicator hkn B t h.1 *
              missedIndicator i h.2.1 ≤
            Delta * Feedback.shape (noise t) := by
        calc
          Delta * Feedback.shape (noise t) * activeIndicator hkn B t h.1 *
                missedIndicator i h.2.1 ≤
              Delta * Feedback.shape (noise t) * activeIndicator hkn B t h.1 := by
            simpa using mul_le_mul_of_nonneg_left hmissed.2
              (mul_nonneg hbase hactive.1)
          _ ≤ Delta * Feedback.shape (noise t) := by
            simpa using mul_le_mul_of_nonneg_left hactive.2 hbase
      linarith [ih h.1]

/-- On the good set, every candidate score has the manuscript's upper bound
`17 ΔT/16`. -/
theorem confidenceScore_le_seventeen_sixteenths
    {n k T : Nat} (hkn : k ≤ n) (noise : Nat → Real)
    (hnoise : ∀ t, noise t ∈ Icc (-1 : Real) 1)
    (Delta : Real) (hDelta : 0 ≤ Delta) (B : Real)
    (hB : B = Delta * T / 16) (i : Fin n) (h : History n k T)
    (hgood : h ∈ confidenceGoodEvent (T := T) hkn noise B) :
    confidenceScore hkn noise Delta B i T h ≤
      (17 : Real) * (Delta * T) / 16 := by
  have hscore := confidenceScore_le_cumulative_add_shape
    hkn noise hnoise Delta hDelta B i T h
  have hshape := noiseShapeSum_le_time noise hnoise T h
  have hshapeScaled :
      Delta * noiseShapeSum noise T h ≤ Delta * T :=
    mul_le_mul_of_nonneg_left hshape hDelta
  have hpenalty : cumulativePenalty hkn T h < B := hgood.1
  calc
    confidenceScore hkn noise Delta B i T h ≤
        cumulativePenalty hkn T h + Delta * noiseShapeSum noise T h := hscore
    _ ≤ cumulativePenalty hkn T h + Delta * T :=
      by linarith
    _ ≤ B + Delta * T := by linarith
    _ = (17 : Real) * (Delta * T) / 16 := by rw [hB]; ring

/-- Equation `eq:lower-confidence-average-event`, conditional on the
preceding estimate `P(G)≥15/16`.  All remaining hypotheses are precisely the
deterministic parameter conditions already used for
`eq:lower-confidence-average-score`. -/
theorem lower_confidence_average_event
    {n k T : Nat} (hk : 1 ≤ k) (hkn : k ≤ n)
    (hN : 2 ≤ (confidenceCandidates n k hkn).card)
    (noise : Nat → Real) (hnoise : ∀ t, noise t ∈ Icc (-1 : Real) 1)
    (Delta : Real) (hDelta : 0 < Delta)
    (hscale : Delta / (confidenceCandidates n k hkn).card ≤
      1 / (8 * (k : Real))) (B : Real) (hB : B = Delta * T / 16)
    (hT : 1 ≤ T)
    (P : Measure (History n k T)) [IsProbabilityMeasure P]
    (hGprob : (15 : Real) / 16 ≤
      P.real (confidenceGoodEvent hkn noise B)) :
    (1 : Real) / 8 ≤
      (∑ i ∈ confidenceCandidates n k hkn,
        P.real (confidenceScoreEvent hkn noise Delta B i)) /
          (confidenceCandidates n k hkn).card := by
  let candidates := confidenceCandidates n k hkn
  let events : Fin n → Set (History n k T) :=
    fun i => confidenceScoreEvent hkn noise Delta B i
  have hM : 0 < Delta * T := mul_pos hDelta (by exact_mod_cast hT)
  have hcandidates : candidates.Nonempty := by
    exact Finset.card_pos.mp (lt_of_lt_of_le (by omega : 0 < 2) hN)
  have hE : ∀ i ∈ candidates, MeasurableSet (events i) := by
    intro i hi
    exact measurableSet_confidenceScoreEvent hkn noise Delta B i
  apply Probability.average_event_probability_ge_one_eighth
    P candidates events hE (confidenceGoodEvent hkn noise B)
    (measurableSet_confidenceGoodEvent hkn noise B) hGprob
  intro h hhgood
  change (2 : Real) / 15 ≤ Probability.eventFraction candidates
    (fun i => {x | Delta * T / 8 ≤
      confidenceScore hkn noise Delta B i T x}) h
  rw [Probability.eventFraction_eq_highScoreFraction]
  apply Probability.highScoreFraction_ge_two_fifteenths
    candidates hcandidates (fun i => confidenceScore hkn noise Delta B i T h) hM
  · simpa [candidates, totalConfidenceScore] using
      (lower_confidence_average_score hk hkn hN noise hnoise Delta hDelta.le
        hscale B h hhgood.1 hhgood.2)
  · intro i hi
    exact confidenceScore_le_seventeen_sixteenths hkn noise hnoise Delta
      hDelta.le B hB i h hhgood

end

end MsetsLower.Lower.Confidence

#print axioms MsetsLower.Lower.Confidence.measurable_confidenceScore
#print axioms MsetsLower.Lower.Confidence.confidenceScore_le_seventeen_sixteenths
#print axioms MsetsLower.Lower.Confidence.lower_confidence_average_event
