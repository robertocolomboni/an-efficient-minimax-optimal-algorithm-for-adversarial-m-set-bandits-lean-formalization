import MsetsLower.Lower.Confidence.ObservableScore
import Mathlib.Probability.Kernel.Composition.Lemmas

/-!
# Concrete reference-law concentration for the confidence construction

The recovered noise in every reference round is the push-forward inverse of
the exact source-uniform feedback construction.  We use that conditional law
and Mathlib's subgaussian composition lemma to prove the manuscript's literal
Hoeffding estimate, with no tail-bound hypothesis.
-/

namespace MsetsLower.Lower.Confidence

open MsetsLower Feedback
open MeasureTheory ProbabilityTheory Set
open scoped BigOperators ENNReal NNReal ProbabilityTheory

noncomputable section

def recoveredConfidenceNoisePair {n k : Nat} (hkn : k ≤ n) :
    MSetAction n k × Real → Real :=
  fun AY => recoveredConfidenceNoise hkn AY.1 AY.2

theorem measurable_recoveredConfidenceNoisePair {n k : Nat} (hkn : k ≤ n) :
    Measurable (recoveredConfidenceNoisePair hkn) :=
  measurable_recoveredConfidenceNoise hkn

theorem feedbackDensityMeasure_zero_map_double :
    (feedbackDensityMeasure 0).map (fun y : Real => 2 * y) =
      sourceUniformMeasure := by
  rw [← feedbackPushforwardMeasure_eq_densityMeasure
    (u := (0 : Real)) (by norm_num)]
  unfold feedbackPushforwardMeasure
  rw [Measure.map_map (by fun_prop) (continuous_feedbackMap 0).measurable]
  have hfun : (fun y : Real => 2 * y) ∘ feedbackMap 0 = id := by
    funext z
    simp only [Function.comp_apply, id_eq]
    unfold feedbackMap
    ring
  rw [hfun, Measure.map_id]

/-- Conditional on every observable prefix, the recovered reference noise
has exactly the original `Unif[-1,1]` source law. -/
theorem confidenceReferenceRoundKernel_map_recoveredNoise
    {n k : Nat} (P : Policy n k) (hkn : k ≤ n) (t : Nat)
    (h : History n k t) :
    (confidenceReferenceRoundKernel P hkn t h).map
        (recoveredConfidenceNoisePair hkn) = sourceUniformMeasure := by
  letI : IsMarkovKernel
      (confidenceReferenceFeedbackKernel :
        Kernel (History n k t × MSetAction n k) Real) :=
    confidenceReferenceFeedbackKernel_isMarkov
  rw [confidenceReferenceRoundKernel,
    Kernel.map_apply _ (confidenceFeedbackEquiv hkn).measurable]
  rw [Measure.map_map (measurable_recoveredConfidenceNoisePair hkn)
    (confidenceFeedbackEquiv hkn).measurable]
  have hcomp : recoveredConfidenceNoisePair hkn ∘ confidenceFeedbackEquiv hkn =
      (fun AY : MSetAction n k × Real => 2 * AY.2) := by
    funext AY
    rcases AY with ⟨A, y⟩
    exact recoveredConfidenceNoise_confidenceScalarFeedback hkn A y
  rw [hcomp]
  change Measure.map ((fun y : Real => 2 * y) ∘ Prod.snd)
    ((confidenceReferenceLatentRoundKernel P t) h) = sourceUniformMeasure
  rw [← Measure.map_map (by fun_prop : Measurable (fun y : Real => 2 * y))
    measurable_snd]
  rw [← Measure.snd]
  unfold confidenceReferenceLatentRoundKernel
  rw [Kernel.compProd_apply_eq_compProd_sectR]
  rw [Measure.snd_compProd]
  change
    ((Kernel.const (MSetAction n k) (feedbackDensityMeasure 0)) ∘ₘ
      P.kernel t h).map (fun y : Real => 2 * y) = sourceUniformMeasure
  rw [Measure.const_comp]
  simp only [measure_univ, one_smul]
  exact feedbackDensityMeasure_zero_map_double

theorem confidenceReferenceRoundKernel_map_recoveredNoise_kernel
    {n k : Nat} (P : Policy n k) (hkn : k ≤ n) (t : Nat) :
    (confidenceReferenceRoundKernel P hkn t).map
        (recoveredConfidenceNoisePair hkn) =
      Kernel.const (History n k t) sourceUniformMeasure := by
  ext h s hs
  rw [Kernel.map_apply _ (measurable_recoveredConfidenceNoisePair hkn) h,
    confidenceReferenceRoundKernel_map_recoveredNoise, Kernel.const_apply]

def centeredRecoveredConfidenceShape {n k : Nat} (hkn : k ≤ n) :
    MSetAction n k × Real → Real :=
  fun AY => (2 / 3 : Real) -
    shape (recoveredConfidenceNoisePair hkn AY)

theorem measurable_centeredRecoveredConfidenceShape
    {n k : Nat} (hkn : k ≤ n) :
    Measurable (centeredRecoveredConfidenceShape hkn) := by
  unfold centeredRecoveredConfidenceShape
  exact measurable_const.sub <|
    measurable_shape.comp (measurable_recoveredConfidenceNoisePair hkn)

/-- The fresh centered shape is conditionally `1/4`-subgaussian at every
reference round, even for an arbitrary adaptive randomized policy. -/
theorem confidenceReferenceRound_hasSubgaussianMGF
    {n k : Nat} (P : Policy n k) (hkn : k ≤ n) (t : Nat) :
    Kernel.HasSubgaussianMGF (centeredRecoveredConfidenceShape hkn) (1 / 4)
      (confidenceReferenceRoundKernel P hkn t)
      ((confidenceReferenceProcess P hkn).law t) := by
  have hmap : Kernel.HasSubgaussianMGF
      (fun z => (2 / 3 : Real) - shape z) (1 / 4)
      ((confidenceReferenceRoundKernel P hkn t).map
        (recoveredConfidenceNoisePair hkn))
      ((confidenceReferenceProcess P hkn).law t) := by
    rw [confidenceReferenceRoundKernel_map_recoveredNoise_kernel]
    constructor
    · intro s
      simpa using
        (hasSubgaussianMGF_centeredLowerShape_sourceUniformMeasure.integrable_exp_mul s)
    · filter_upwards with h
      intro s
      simpa using
        (hasSubgaussianMGF_centeredLowerShape_sourceUniformMeasure.mgf_le s)
  have hout := Kernel.HasSubgaussianMGF.of_map
    (measurable_recoveredConfidenceNoisePair hkn) hmap
  change Kernel.HasSubgaussianMGF
    (fun x => (2 / 3 : Real) - shape (recoveredConfidenceNoisePair hkn x))
      (1 / 4) (confidenceReferenceRoundKernel P hkn t)
      ((confidenceReferenceProcess P hkn).law t)
  exact hout

/-- Recursive centered lower-tail sum
`sum_t (2/3 - g(recovered Z_t))`. -/
def observableCenteredLowerShapeSum {n k : Nat} (hkn : k ≤ n) :
    (t : Nat) → History n k t → Real
  | 0, _ => 0
  | t + 1, h =>
      observableCenteredLowerShapeSum hkn t h.1 +
        centeredRecoveredConfidenceShape hkn h.2

@[simp] theorem observableCenteredLowerShapeSum_zero
    {n k : Nat} (hkn : k ≤ n) (h : History n k 0) :
    observableCenteredLowerShapeSum hkn 0 h = 0 := rfl

@[simp] theorem observableCenteredLowerShapeSum_succ
    {n k t : Nat} (hkn : k ≤ n) (h : History n k (t + 1)) :
    observableCenteredLowerShapeSum hkn (t + 1) h =
      observableCenteredLowerShapeSum hkn t h.1 +
        centeredRecoveredConfidenceShape hkn h.2 := rfl

theorem observableCenteredLowerShapeSum_eq
    {n k : Nat} (hkn : k ≤ n) :
    ∀ (t : Nat) (h : History n k t),
      observableCenteredLowerShapeSum hkn t h =
        (2 / 3 : Real) * t - observableNoiseShapeSum hkn t h := by
  intro t
  induction t with
  | zero => intro h; simp
  | succ t ih =>
      intro h
      rw [observableCenteredLowerShapeSum_succ,
        observableNoiseShapeSum_succ, ih h.1]
      unfold centeredRecoveredConfidenceShape recoveredConfidenceNoisePair
      push_cast
      ring

theorem measurable_observableCenteredLowerShapeSum
    {n k : Nat} (hkn : k ≤ n) :
    ∀ t, Measurable (observableCenteredLowerShapeSum hkn t) := by
  intro t
  induction t with
  | zero => exact measurable_const
  | succ t ih =>
      exact (ih.comp measurable_fst).add <|
        (measurable_centeredRecoveredConfidenceShape hkn).comp measurable_snd

private theorem confidenceReference_centeredSum_hasSubgaussianMGF_succ
    {n k t : Nat} (P : Policy n k) (hkn : k ≤ n)
    (ih : HasSubgaussianMGF (observableCenteredLowerShapeSum hkn t)
      ((t : NNReal) / 4) ((confidenceReferenceProcess P hkn).law t)) :
    HasSubgaussianMGF (observableCenteredLowerShapeSum hkn (t + 1))
      (((t + 1 : Nat) : NNReal) / 4)
      ((confidenceReferenceProcess P hkn).law (t + 1)) := by
  change HasSubgaussianMGF
    (fun p : History n k t × (MSetAction n k × Real) =>
      observableCenteredLowerShapeSum hkn t p.1 +
        centeredRecoveredConfidenceShape hkn p.2)
    (((t + 1 : Nat) : NNReal) / 4)
    ((confidenceReferenceProcess P hkn).law t ⊗ₘ
      confidenceReferenceRoundKernel P hkn t)
  let μ := (confidenceReferenceProcess P hkn).law t
  let κ : Kernel Unit (History n k t) := Kernel.const Unit μ
  let η := confidenceReferenceRoundKernel P hkn t
  letI : IsProbabilityMeasure μ :=
    (confidenceReferenceProcess P hkn).law_isProbabilityMeasure t
  letI hκmarkov : IsMarkovKernel κ := by dsimp [κ]; infer_instance
  letI hηmarkov : IsMarkovKernel η :=
    confidenceReferenceRoundKernel_isMarkov P hkn t
  letI : IsZeroOrMarkovKernel κ := ⟨Or.inr hκmarkov⟩
  letI : IsFiniteKernel κ :=
    ⟨⟨1, ENNReal.one_lt_top, fun a => by rw [measure_univ]⟩⟩
  letI hκsf : IsSFiniteKernel κ := by infer_instance
  letI : IsZeroOrMarkovKernel η := ⟨Or.inr hηmarkov⟩
  letI : IsFiniteKernel η :=
    ⟨⟨1, ENNReal.one_lt_top, fun a => by rw [measure_univ]⟩⟩
  letI hηsf : IsSFiniteKernel η := by infer_instance
  have hX : Kernel.HasSubgaussianMGF
      (observableCenteredLowerShapeSum hkn t) ((t : NNReal) / 4)
      κ (Measure.dirac ()) := by
    simpa [κ, μ] using (HasSubgaussianMGF_iff_kernel.mp ih)
  have hY : Kernel.HasSubgaussianMGF
      (centeredRecoveredConfidenceShape hkn) (1 / 4) η (κ ∘ₘ Measure.dirac ()) := by
    have hround := confidenceReferenceRound_hasSubgaussianMGF P hkn t
    simpa [κ, μ, η] using hround
  have hsum := hX.add_comp hY
  let ξ : Kernel Unit (History n k t × (MSetAction n k × Real)) :=
    κ ⊗ₖ Kernel.prodMkLeft Unit η
  have hξ : ξ () = μ ⊗ₘ η := by
    unfold ξ
    have hprodSf : IsSFiniteKernel (Kernel.prodMkLeft Unit η) := by infer_instance
    have happly := @Kernel.compProd_apply_eq_compProd_sectR
      _ _ _ _ _ _ κ (Kernel.prodMkLeft Unit η) hκsf hprodSf ()
    rw [happly]
    rfl
  have hξcomp : ξ ∘ₘ Measure.dirac () = μ ⊗ₘ η := by
    rw [Measure.dirac_bind (Kernel.measurable ξ)]
    exact hξ
  have hparam : (t : NNReal) / 4 + 1 / 4 = (((t + 1 : Nat) : NNReal) / 4) := by
    push_cast
    ring
  rw [hparam] at hsum
  constructor
  · intro s
    have hs := hsum.integrable_exp_mul s
    rw [hξcomp] at hs
    exact hs
  · intro s
    have hsall : ∀ q : Real,
        mgf (fun p : History n k t × (MSetAction n k × Real) =>
            observableCenteredLowerShapeSum hkn t p.1 +
              centeredRecoveredConfidenceShape hkn p.2)
          (ξ ()) q ≤
        Real.exp (((((t + 1 : Nat) : NNReal) / 4 : NNReal) : Real) * q ^ 2 / 2) := by
      simpa [ξ] using hsum.mgf_le
    have hs := hsall s
    rw [hξ] at hs
    exact hs

/-- The full recovered centered sum is `T/4`-subgaussian under the genuine
observable reference process. -/
theorem confidenceReference_centeredSum_hasSubgaussianMGF
    {n k : Nat} (P : Policy n k) (hkn : k ≤ n) :
    ∀ T : Nat,
    HasSubgaussianMGF (observableCenteredLowerShapeSum hkn T)
      ((T : NNReal) / 4) ((confidenceReferenceProcess P hkn).law T) := by
  intro T
  induction T with
  | zero =>
      simpa only [observableCenteredLowerShapeSum, Nat.cast_zero, zero_div] using
        (HasSubgaussianMGF.fun_zero
          (μ := (confidenceReferenceProcess P hkn).law 0))
  | succ T ih =>
      exact confidenceReference_centeredSum_hasSubgaussianMGF_succ P hkn ih

/-- The manuscript's concrete Hoeffding estimate under `P₀`, now stated for
the literal recovered-noise statistic of the observable history. -/
theorem confidenceReference_observableNoiseShapeSum_lowerTail
    {n k : Nat} (P : Policy n k) (hkn : k ≤ n) (T : Nat) :
    ((confidenceReferenceProcess P hkn).law T).real
        {h | observableNoiseShapeSum hkn T h < (T : Real) / 2} ≤
      Real.exp (-(T : Real) / 18) := by
  cases T with
  | zero => simp
  | succ T =>
      let μ := (confidenceReferenceProcess P hkn).law (T + 1)
      let X := observableCenteredLowerShapeSum hkn (T + 1)
      letI : IsProbabilityMeasure μ :=
        (confidenceReferenceProcess P hkn).law_isProbabilityMeasure (T + 1)
      have hsg := confidenceReference_centeredSum_hasSubgaussianMGF
        P hkn (T + 1)
      have htail := hsg.measure_ge_le
        (ε := ((T + 1 : Nat) : Real) / 6) (by positivity)
      have hsubset :
          {h : History n k (T + 1) |
              observableNoiseShapeSum hkn (T + 1) h <
                ((T + 1 : Nat) : Real) / 2} ⊆
            {h | ((T + 1 : Nat) : Real) / 6 ≤ X h} := by
        intro h hh
        have heq := observableCenteredLowerShapeSum_eq hkn (T + 1) h
        change observableNoiseShapeSum hkn (T + 1) h <
          ((T + 1 : Nat) : Real) / 2 at hh
        change ((T + 1 : Nat) : Real) / 6 ≤ X h
        rw [show X h = observableCenteredLowerShapeSum hkn (T + 1) h from rfl,
          heq]
        norm_num at hh ⊢
        linarith
      calc
        μ.real {h | observableNoiseShapeSum hkn (T + 1) h <
            ((T + 1 : Nat) : Real) / 2} ≤
          μ.real {h | ((T + 1 : Nat) : Real) / 6 ≤ X h} :=
            measureReal_mono hsubset (by finiteness)
        _ ≤ Real.exp
            (-(((T + 1 : Nat) : Real) / 6) ^ 2 /
              (2 * ((((T + 1 : Nat) : NNReal) / 4 : NNReal) : Real))) := by
          simpa [μ, X] using htail
        _ = Real.exp (-((T + 1 : Nat) : Real) / 18) := by
          congr 1
          have hpos : (0 : Real) < (T + 1 : Nat) := by positivity
          simp only [NNReal.coe_div, NNReal.coe_natCast]
          norm_num
          field_simp
          ring

end

end MsetsLower.Lower.Confidence

#print axioms MsetsLower.Lower.Confidence.confidenceReferenceRoundKernel_map_recoveredNoise
#print axioms MsetsLower.Lower.Confidence.confidenceReferenceRound_hasSubgaussianMGF
#print axioms MsetsLower.Lower.Confidence.confidenceReference_centeredSum_hasSubgaussianMGF
#print axioms MsetsLower.Lower.Confidence.confidenceReference_observableNoiseShapeSum_lowerTail
