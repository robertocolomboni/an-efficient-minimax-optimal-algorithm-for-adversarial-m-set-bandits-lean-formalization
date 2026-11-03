import MsetsLower.Lower.Confidence.GoodEvent
import MsetsLower.Lower.Confidence.ReferenceConcentration
import MsetsLower.Lower.ThresholdArithmetic

/-!
# The observable confidence good event under the reference process

This file instantiates the union bound of `GoodEvent` with the statistic
recovered from the actual action--scalar-feedback history.  In particular,
the Hoeffding premise is discharged from the reference-process law rather
than assumed.
-/

namespace MsetsLower.Lower.Confidence

open MsetsLower MeasureTheory Set

noncomputable section

/-- The observable recovered-noise half-space used in the reference-law
good event. -/
def observableConfidenceShapeGoodEvent
    {n k T : Nat} (hkn : k ≤ n) : Set (History n k T) :=
  {h | (T : Real) / 2 ≤ observableNoiseShapeSum hkn T h}

theorem measurableSet_observableConfidenceShapeGoodEvent
    {n k T : Nat} (hkn : k ≤ n) :
    MeasurableSet (observableConfidenceShapeGoodEvent (T := T) hkn) :=
  measurableSet_le measurable_const
    (measurable_observableNoiseShapeSum hkn T)

/-- The literal observable good event under `P₀`: the stopping penalty is
small and the recovered-noise shape sum is at least `T/2`. -/
def observableConfidenceGoodEvent
    {n k T : Nat} (hkn : k ≤ n) (B : Real) : Set (History n k T) :=
  confidencePenaltyGoodEvent hkn B ∩
    observableConfidenceShapeGoodEvent hkn

theorem measurableSet_observableConfidenceGoodEvent
    {n k T : Nat} (hkn : k ≤ n) (B : Real) :
    MeasurableSet (observableConfidenceGoodEvent (T := T) hkn B) :=
  (measurableSet_confidencePenaltyGoodEvent hkn B).inter
    (measurableSet_observableConfidenceShapeGoodEvent hkn)

/-- On histories carrying the reference encoding of a fixed noise sequence,
the observable good event is exactly the manuscript's fixed-noise event. -/
theorem mem_observableConfidenceGoodEvent_iff_referenceCompatible
    {n k T : Nat} (hk : 1 ≤ k) (hkn : k ≤ n)
    (noise : Nat → Real) (B : Real) (h : History n k T)
    (hcompat : ReferenceHistoryCompatible hkn noise T h) :
    h ∈ observableConfidenceGoodEvent (T := T) hkn B ↔
      h ∈ confidenceGoodEvent (T := T) hkn noise B := by
  change
    (cumulativePenalty hkn T h < B ∧
      (T : Real) / 2 ≤ observableNoiseShapeSum hkn T h) ↔
    (cumulativePenalty hkn T h < B ∧
      (T : Real) / 2 ≤ noiseShapeSum noise T h)
  rw [observableNoiseShapeSum_eq_noiseShapeSum_of_referenceCompatible
    hk hkn noise T h hcompat]

/-- The confidence horizon and the manuscript's small-`δ` regime make the
concrete Hoeffding remainder at most `1/32`. -/
theorem confidence_horizon_exp_lowerTail_le
    {n k T : Nat} {delta : Real}
    (hk : 1 ≤ k) (hkn : k ≤ n)
    (hdelta_pos : 0 < delta)
    (hdelta_small : delta ≤ 1 / (2 : Real) ^ 36)
    (hhorizon :
      4 * (n : Real) * (k : Real) ^ 2 *
          MsetsLower.Lower.confidenceLog delta ≤ (T : Real)) :
    Real.exp (-(T : Real) / 18) ≤ (1 : Real) / 32 := by
  have hpow_pos : 0 < (2 : Real) ^ 36 := by positivity
  have hinv_pos : 0 < (1 : Real) / delta := div_pos zero_lt_one hdelta_pos
  have hpow_le_inv : (2 : Real) ^ 36 ≤ 1 / delta := by
    apply (le_div_iff₀ hdelta_pos).2
    calc
      (2 : Real) ^ 36 * delta ≤
          (2 : Real) ^ 36 * (1 / (2 : Real) ^ 36) :=
        mul_le_mul_of_nonneg_left hdelta_small hpow_pos.le
      _ = 1 := by field_simp
  have hlog_lower :
      (36 : Real) * Real.log 2 ≤
        MsetsLower.Lower.confidenceLog delta := by
    have hlogmono :
        Real.log ((2 : Real) ^ 36) ≤ Real.log (1 / delta) :=
      Real.strictMonoOn_log.monotoneOn hpow_pos hinv_pos hpow_le_inv
    rw [Real.log_pow] at hlogmono
    simpa [MsetsLower.Lower.confidenceLog] using hlogmono
  have hn : 1 ≤ n := hk.trans hkn
  have hk_real : (1 : Real) ≤ k := by exact_mod_cast hk
  have hn_real : (1 : Real) ≤ n := by exact_mod_cast hn
  have hlog_two_nonneg : 0 ≤ Real.log 2 := Real.log_nonneg (by norm_num)
  have hconfidence_nonneg :
      0 ≤ MsetsLower.Lower.confidenceLog delta :=
    hlog_lower.trans' (mul_nonneg (by norm_num) hlog_two_nonneg)
  have hscale :
      (144 : Real) * Real.log 2 ≤
        4 * (n : Real) * (k : Real) ^ 2 *
          MsetsLower.Lower.confidenceLog delta := by
    calc
      (144 : Real) * Real.log 2 =
          4 * 1 * 1 ^ 2 * ((36 : Real) * Real.log 2) := by ring
      _ ≤ 4 * (n : Real) * (k : Real) ^ 2 *
          MsetsLower.Lower.confidenceLog delta := by
        gcongr
  have hT_lower : (144 : Real) * Real.log 2 ≤ (T : Real) :=
    hscale.trans hhorizon
  have hlog32 : Real.log 32 = (5 : Real) * Real.log 2 := by
    rw [show (32 : Real) = 2 ^ 5 by norm_num, Real.log_pow]
    norm_num
  have hone_div_32 : (1 : Real) / 32 = Real.exp (-Real.log 32) := by
    rw [Real.exp_neg, Real.exp_log (by norm_num : (0 : Real) < 32)]
    norm_num
  rw [hone_div_32]
  apply Real.exp_le_exp.mpr
  rw [hlog32]
  nlinarith

/-- Observable form of `eq:lower-confidence-good-event`.  Its only
probabilistic premise is the manuscript's literal small-penalty branch;
the recovered-noise failure estimate is proved from `P₀`. -/
theorem lower_confidence_reference_good_event
    {n k T : Nat} (hk : 1 ≤ k) (hkn : k ≤ n)
    (P : Policy n k) (B delta : Real)
    (hdelta_pos : 0 < delta)
    (hdelta_small : delta ≤ 1 / (2 : Real) ^ 36)
    (hhorizon :
      4 * (n : Real) * (k : Real) ^ 2 *
          MsetsLower.Lower.confidenceLog delta ≤ (T : Real))
    (hpenaltyFailure :
      ((confidenceReferenceProcess P hkn).law T).real
          {h | B ≤ cumulativePenalty hkn T h} < delta) :
    (15 : Real) / 16 ≤
      ((confidenceReferenceProcess P hkn).law T).real
        (observableConfidenceGoodEvent hkn B) := by
  let P0 : Measure (History n k T) :=
    (confidenceReferenceProcess P hkn).law T
  letI : IsProbabilityMeasure P0 :=
    (confidenceReferenceProcess P hkn).law_isProbabilityMeasure T
  let A := confidencePenaltyGoodEvent (T := T) hkn B
  let H := observableConfidenceShapeGoodEvent (T := T) hkn
  have hA : MeasurableSet A := measurableSet_confidencePenaltyGoodEvent hkn B
  have hH : MeasurableSet H :=
    measurableSet_observableConfidenceShapeGoodEvent hkn
  have hAc : Aᶜ = {h | B ≤ cumulativePenalty hkn T h} := by
    ext h
    simp [A, confidencePenaltyGoodEvent]
  have hHc :
      Hᶜ = {h | observableNoiseShapeSum hkn T h < (T : Real) / 2} := by
    ext h
    simp [H, observableConfidenceShapeGoodEvent, not_le]
  have hshapeFailure :
      P0.real {h | observableNoiseShapeSum hkn T h < (T : Real) / 2} ≤
        (1 : Real) / 32 :=
    (confidenceReference_observableNoiseShapeSum_lowerTail P hkn T).trans
      (confidence_horizon_exp_lowerTail_le hk hkn hdelta_pos
        hdelta_small hhorizon)
  have hinter := @probability_inter_ge_one_sub_complements
    (History n k T) (by infer_instance) P0 (by infer_instance) A H hA hH
  rw [hAc, hHc] at hinter
  change (15 : Real) / 16 ≤ P0.real (A ∩ H)
  change P0.real {h | B ≤ cumulativePenalty hkn T h} < delta at hpenaltyFailure
  nlinarith

end

end MsetsLower.Lower.Confidence

#print axioms MsetsLower.Lower.Confidence.mem_observableConfidenceGoodEvent_iff_referenceCompatible
#print axioms MsetsLower.Lower.Confidence.confidence_horizon_exp_lowerTail_le
#print axioms MsetsLower.Lower.Confidence.lower_confidence_reference_good_event
