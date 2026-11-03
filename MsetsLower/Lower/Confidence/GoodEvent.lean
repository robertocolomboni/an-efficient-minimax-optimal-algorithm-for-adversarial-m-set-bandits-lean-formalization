import MsetsLower.Lower.Confidence.EventAverage

/-!
# Probability of the confidence good event

This file formalizes the union-bound assembly in
`eq:lower-confidence-good-event`.  The Hoeffding estimate and the small-penalty
case enter as the two preceding probability bounds, exactly as in the paper.
-/

namespace MsetsLower.Lower.Confidence

open MsetsLower MeasureTheory Set

noncomputable section

/-- The noise half-space whose complement is controlled by Hoeffding. -/
def confidenceShapeGoodEvent
    {n k T : Nat} (noise : Nat → Real) : Set (History n k T) :=
  {h | (T : Real) / 2 ≤ noiseShapeSum noise T h}

theorem measurableSet_confidenceShapeGoodEvent
    {n k T : Nat} (noise : Nat → Real) :
    MeasurableSet (confidenceShapeGoodEvent (n := n) (k := k) (T := T) noise) :=
  measurableSet_le measurable_const (measurable_noiseShapeSum noise T)

/-- The small-penalty half-space in the good event. -/
def confidencePenaltyGoodEvent
    {n k T : Nat} (hkn : k ≤ n) (B : Real) : Set (History n k T) :=
  {h | cumulativePenalty hkn T h < B}

theorem measurableSet_confidencePenaltyGoodEvent
    {n k T : Nat} (hkn : k ≤ n) (B : Real) :
    MeasurableSet (confidencePenaltyGoodEvent (T := T) hkn B) :=
  measurableSet_lt (measurable_cumulativePenalty hkn T) measurable_const

theorem confidenceGoodEvent_eq_inter
    {n k T : Nat} (hkn : k ≤ n) (noise : Nat → Real) (B : Real) :
    confidenceGoodEvent (T := T) hkn noise B =
      confidencePenaltyGoodEvent (T := T) hkn B ∩
        confidenceShapeGoodEvent (n := n) (k := k) (T := T) noise := rfl

/-- Generic two-event lower union bound in real probability normalization. -/
theorem probability_inter_ge_one_sub_complements
    {Omega : Type*} [MeasurableSpace Omega]
    (P : Measure Omega) [IsProbabilityMeasure P]
    (A H : Set Omega) (hA : MeasurableSet A) (hH : MeasurableSet H) :
    1 - P.real Aᶜ - P.real Hᶜ ≤ P.real (A ∩ H) := by
  have hidentity := measureReal_union_add_inter (μ := P) (s := A) hH
  have hunion : P.real (A ∪ H) ≤ 1 := measureReal_le_one
  have hAc := probReal_compl_eq_one_sub (μ := P) hA
  have hHc := probReal_compl_eq_one_sub (μ := P) hH
  linarith

/-- Equation `eq:lower-confidence-good-event`: the small-penalty branch and
the Hoeffding failure estimate imply `P₀(G) ≥ 15/16`. -/
theorem lower_confidence_good_event
    {n k T : Nat} (hkn : k ≤ n) (noise : Nat → Real) (B delta : Real)
    (P : Measure (History n k T)) [IsProbabilityMeasure P]
    (hpenaltyFailure :
      P.real {h | B ≤ cumulativePenalty hkn T h} < delta)
    (hshapeFailure :
      P.real {h | noiseShapeSum noise T h < (T : Real) / 2} ≤
        (1 : Real) / 32)
    (hdelta : delta ≤ 1 / (2 : Real) ^ 36) :
    (15 : Real) / 16 ≤ P.real (confidenceGoodEvent hkn noise B) := by
  let A := confidencePenaltyGoodEvent (T := T) hkn B
  let H := confidenceShapeGoodEvent (n := n) (k := k) (T := T) noise
  have hA : MeasurableSet A := measurableSet_confidencePenaltyGoodEvent hkn B
  have hH : MeasurableSet H := measurableSet_confidenceShapeGoodEvent noise
  have hAc : Aᶜ = {h | B ≤ cumulativePenalty hkn T h} := by
    ext h
    simp [A, confidencePenaltyGoodEvent]
  have hHc : Hᶜ = {h | noiseShapeSum noise T h < (T : Real) / 2} := by
    ext h
    simp [H, confidenceShapeGoodEvent, not_le]
  have hinter := probability_inter_ge_one_sub_complements P A H hA hH
  rw [hAc, hHc] at hinter
  rw [confidenceGoodEvent_eq_inter hkn noise B]
  change (15 : Real) / 16 ≤ P.real (A ∩ H)
  nlinarith

end

end MsetsLower.Lower.Confidence

#print axioms MsetsLower.Lower.Confidence.probability_inter_ge_one_sub_complements
#print axioms MsetsLower.Lower.Confidence.lower_confidence_good_event
