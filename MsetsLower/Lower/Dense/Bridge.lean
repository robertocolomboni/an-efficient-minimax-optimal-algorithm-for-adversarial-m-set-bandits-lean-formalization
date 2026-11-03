import MsetsLower.Lower.Dense.Moment
import MsetsLower.Lower.Dense.Assouad
import Mathlib.Probability.Kernel.Composition.Lemmas

/-!
# Observable/joint-law bridge for the dense construction

This file identifies the observable marginal of the genuine paired-item
experiment with the adaptive Bernoulli-feedback law, then instantiates the
finite Assouad estimators and transfers their conclusion back to the joint
law used by the moment argument.
-/

namespace MsetsLower.Lower.Dense

open MsetsLower
open MeasureTheory ProbabilityTheory InformationTheory
open scoped BigOperators ENNReal NNReal ProbabilityTheory

noncomputable section

/-! ## The exact selected-item Bernoulli law -/

/-- Boolean statistic revealed by a paired item after fixing the action. -/
def pairedSelectedBool {n k : Nat} (hD : 2 * k ≤ n)
    (A : MSetAction n k) (J : PairItem k) : Bool :=
  decide (pairCoordinate hD J ∈ pairedSection hD A)

theorem measurable_pairedSelectedBool {n k : Nat} (hD : 2 * k ≤ n)
    (A : MSetAction n k) : Measurable (pairedSelectedBool hD A) :=
  measurable_of_finite _

theorem bernoulliLaw_apply_singleton_true {a : Real} :
    bernoulliLaw a {true} = ENNReal.ofReal a := by
  rw [bernoulliLaw, withDensity_apply _ (MeasurableSet.singleton true),
    lintegral_fintype]
  simp [bernoulliDensity, bernoulliMass]

theorem pairedPMF_selected_true {n k : Nat} (hk : 1 ≤ k)
    (hD : 2 * k ≤ n) (θ : Fin k → PairSign) (ε : Real)
    (hε0 : 0 ≤ ε) (hε1 : ε ≤ 1) (A : MSetAction n k) :
    (pairedPMF hk θ ε hε0 hε1).toMeasure
        {J | pairedSelectedBool hD A J = true} =
      ENNReal.ofReal (pairedBernoulliParameter hD θ ε A) := by
  let p := pairedPMF hk θ ε hε0 hε1
  rw [PMF.toMeasure_apply_fintype]
  change (∑ J ∈ (Finset.univ : Finset (PairItem k)),
      {J | pairedSelectedBool hD A J = true}.indicator p J) =
    ENNReal.ofReal
      (∑ J ∈ (Finset.univ : Finset (PairItem k)),
        pairedProbability θ ε J * pairedSelected hD A J)
  rw [ENNReal.ofReal_sum_of_nonneg (fun J _ =>
      mul_nonneg (pairedProbability_nonneg hk θ hε0 hε1 J)
        (pairedSelected_mem_Icc hD A J).1)]
  apply Finset.sum_congr rfl
  intro J _
  by_cases hJ : pairCoordinate hD J ∈ pairedSection hD A
  · simp only [pairCoordinate_mem_pairedSection_iff] at hJ
    simp [p, pairedSelectedBool, pairedSelected, hJ]
  · simp only [pairCoordinate_mem_pairedSection_iff] at hJ
    simp [p, pairedSelectedBool, pairedSelected, hJ]

/-- Under the literal paired PMF, the selected-item statistic is exactly the
Bernoulli law used by the observable adaptive process. -/
theorem pairedPMF_map_selectedBool {n k : Nat} (hk : 1 ≤ k)
    (hD : 2 * k ≤ n) (θ : Fin k → PairSign) (ε : Real)
    (hε0 : 0 ≤ ε) (hε1 : ε ≤ 1) (A : MSetAction n k) :
    (pairedPMF hk θ ε hε0 hε1).toMeasure.map
        (pairedSelectedBool hD A) =
      bernoulliLaw (pairedBernoulliParameter hD θ ε A) := by
  let μ := (pairedPMF hk θ ε hε0 hε1).toMeasure.map
    (pairedSelectedBool hD A)
  let ν := bernoulliLaw (pairedBernoulliParameter hD θ ε A)
  have hparam := pairedBernoulliParameter_mem_Icc hk hD θ hε0 hε1 A
  have hμprob : IsProbabilityMeasure μ := by
    dsimp [μ]
    infer_instance
  have hνprob : IsProbabilityMeasure ν :=
    ⟨bernoulliLaw_apply_univ hparam.1 hparam.2⟩
  have htrue : μ {true} = ν {true} := by
    dsimp [μ, ν]
    rw [Measure.map_apply (measurable_pairedSelectedBool hD A)
      (MeasurableSet.singleton true)]
    change (pairedPMF hk θ ε hε0 hε1).toMeasure
      {J | pairedSelectedBool hD A J = true} = _
    rw [
      pairedPMF_selected_true hk hD θ ε hε0 hε1 A,
      bernoulliLaw_apply_singleton_true]
  apply Measure.ext_of_singleton
  intro b
  cases b
  · have hcompl : ({false} : Set Bool) = ({true} : Set Bool)ᶜ := by
      ext x
      cases x <;> simp
    rw [hcompl, measure_compl (MeasurableSet.singleton true)
        (measure_ne_top μ {true}),
      measure_compl (MeasurableSet.singleton true)
        (measure_ne_top ν {true}), htrue]
    rw [show μ Set.univ = 1 from hμprob.measure_univ,
      show ν Set.univ = 1 from hνprob.measure_univ]
  · exact htrue

/-! ## One-round and full-history pushforwards -/

def pairedJointBoolObservation {n k : Nat} (hD : 2 * k ≤ n) :
    MSetAction n k × PairItem k → MSetAction n k × Bool
  | (A, J) => (A, pairedSelectedBool hD A J)

def pairedJointScalarObservation {n k : Nat} (hD : 2 * k ≤ n) :
    MSetAction n k × PairItem k → MSetAction n k × Real
  | (A, J) => (A, actionLoss A (pairedLoss hD J))

theorem measurable_pairedJointBoolObservation {n k : Nat}
    (hD : 2 * k ≤ n) : Measurable (pairedJointBoolObservation hD) :=
  measurable_of_finite _

theorem measurable_pairedJointScalarObservation {n k : Nat}
    (hD : 2 * k ≤ n) : Measurable (pairedJointScalarObservation hD) :=
  measurable_of_finite _

theorem pairedJointRoundKernel_map_bool {n k : Nat}
    (P : Policy n k) (hk : 1 ≤ k) (hD : 2 * k ≤ n)
    (θ : Fin k → PairSign) (ε : Real) (hε0 : 0 ≤ ε)
    (hε1 : ε ≤ 1) (t : Nat) (h : PairedJointHistory n k t) :
    (pairedJointRoundKernel P hk hD θ ε hε0 hε1 t h).map
        (pairedJointBoolObservation hD) =
      pairedLatentRoundKernel P hk hD θ ε t
        (pairedJointObservedHistory hD t h) := by
  letI : IsMarkovKernel (pairedHistoryActionBoolKernel hk hD θ ε t) :=
    pairedHistoryActionBoolKernel_isMarkov hk hD θ ε hε0 hε1 t
  ext s hs
  rw [Measure.map_apply (measurable_pairedJointBoolObservation hD) hs]
  unfold pairedJointRoundKernel pairedLatentRoundKernel
  rw [Kernel.compProd_apply
      (hs.preimage (measurable_pairedJointBoolObservation hD)),
    Kernel.compProd_apply hs]
  unfold pairedJointActionKernel
  rw [Kernel.comap_apply]
  apply lintegral_congr
  intro A
  unfold pairedJointItemKernel pairedHistoryActionBoolKernel
  rw [Kernel.const_apply, Kernel.comap_apply]
  have hm := congrArg
    (fun μ : Measure Bool => μ (Prod.mk A ⁻¹' s))
    (pairedPMF_map_selectedBool hk hD θ ε hε0 hε1 A)
  rw [Measure.map_apply (measurable_pairedSelectedBool hD A)
    (measurable_prodMk_left hs)] at hm
  exact hm

theorem pairedJointScalarObservation_eq_encode_bool {n k : Nat}
    (hk : 1 ≤ k) (hD : 2 * k ≤ n) :
    pairedJointScalarObservation hD =
      encodePairedActionFeedback hD ∘ pairedJointBoolObservation hD := by
  funext z
  rcases z with ⟨A, J⟩
  apply Prod.ext
  · rfl
  · exact (pairedScalarFeedback_selected_eq_actionLoss hk hD A J).symm

theorem pairedJointRoundKernel_map_scalar {n k : Nat}
    (P : Policy n k) (hk : 1 ≤ k) (hD : 2 * k ≤ n)
    (θ : Fin k → PairSign) (ε : Real) (hε0 : 0 ≤ ε)
    (hε1 : ε ≤ 1) (t : Nat) (h : PairedJointHistory n k t) :
    (pairedJointRoundKernel P hk hD θ ε hε0 hε1 t h).map
        (pairedJointScalarObservation hD) =
      pairedAdaptiveRoundKernel P hk hD θ ε t
        (pairedJointObservedHistory hD t h) := by
  rw [pairedJointScalarObservation_eq_encode_bool hk hD]
  rw [← Measure.map_map
    (measurable_encodePairedActionFeedback hD)
    (measurable_pairedJointBoolObservation hD)]
  rw [pairedJointRoundKernel_map_bool]
  unfold pairedAdaptiveRoundKernel
  exact (Kernel.map_apply _ (measurable_encodePairedActionFeedback hD) _).symm

/-- General change-of-variables lemma for a composition-product when both
the base law and every conditional kernel are pushed forward. -/
theorem map_compProd_of_map_apply
    {α α' β β' : Type*}
    [MeasurableSpace α] [MeasurableSpace α']
    [MeasurableSpace β] [MeasurableSpace β']
    (μ : Measure α) (ν : Measure α')
    (κ : Kernel α β) (η : Kernel α' β')
    [SFinite μ] [SFinite ν]
    [IsSFiniteKernel κ] [IsSFiniteKernel η]
    (f : α → α') (g : β → β')
    (hf : Measurable f) (hg : Measurable g)
    (hbase : μ.map f = ν)
    (hkernel : ∀ a, (κ a).map g = η (f a)) :
    (μ ⊗ₘ κ).map (Prod.map f g) = ν ⊗ₘ η := by
  ext s hs
  rw [Measure.map_apply (hf.prodMap hg) hs,
    Measure.compProd_apply (hs.preimage (hf.prodMap hg)),
    Measure.compProd_apply hs]
  have hinner (a : α) :
      κ a (Prod.mk a ⁻¹' (Prod.map f g ⁻¹' s)) =
        η (f a) (Prod.mk (f a) ⁻¹' s) := by
    have hm := congrArg
      (fun ρ : Measure β' => ρ (Prod.mk (f a) ⁻¹' s))
      (hkernel a)
    rw [Measure.map_apply hg (measurable_prodMk_left hs)] at hm
    exact hm
  simp_rw [hinner]
  rw [← hbase,
    lintegral_map (Kernel.measurable_kernel_prodMk_left hs) hf]

/-- The observable marginal of the genuine latent-item construction is
exactly the adaptive scalar-feedback history law used in the KL argument. -/
theorem pairedJointObservedHistory_map_law {n k : Nat}
    (P : Policy n k) (hk : 1 ≤ k) (hD : 2 * k ≤ n)
    (θ : Fin k → PairSign) (ε : Real) (hε0 : 0 ≤ ε)
    (hε1 : ε ≤ 1) : ∀ t : Nat,
    (pairedJointLaw P hk hD θ ε hε0 hε1 t).map
        (pairedJointObservedHistory hD t) =
      (pairedAdaptiveProcess P hk hD θ ε hε0 hε1).law t := by
  intro t
  induction t with
  | zero =>
      simp [pairedJointLaw, HistoryKernelProcess.law,
        pairedJointObservedHistory]
  | succ t ih =>
      let μ : Measure (PairedJointHistory n k t) :=
        pairedJointLaw P hk hD θ ε hε0 hε1 t
      let ν : Measure (History n k t) :=
        (pairedAdaptiveProcess P hk hD θ ε hε0 hε1).law t
      let κ : Kernel (PairedJointHistory n k t)
          (MSetAction n k × PairItem k) :=
        pairedJointRoundKernel P hk hD θ ε hε0 hε1 t
      let η : Kernel (History n k t) (MSetAction n k × Real) :=
        pairedAdaptiveRoundKernel P hk hD θ ε t
      letI : IsProbabilityMeasure μ :=
        pairedJointLaw_isProbabilityMeasure P hk hD θ ε hε0 hε1 t
      letI : IsProbabilityMeasure ν := by
        dsimp [ν]
        infer_instance
      let hsfμ : SFinite μ := by infer_instance
      letI : SFinite μ := hsfμ
      let hsfν : SFinite ν := by infer_instance
      letI : SFinite ν := hsfν
      letI : IsMarkovKernel κ := by
        dsimp [κ]
        infer_instance
      letI : IsMarkovKernel η :=
        pairedAdaptiveRoundKernel_isMarkov P hk hD θ ε hε0 hε1 t
      let hskκ : IsSFiniteKernel κ := by infer_instance
      letI : IsSFiniteKernel κ := hskκ
      let hskη : IsSFiniteKernel η := by infer_instance
      letI : IsSFiniteKernel η := hskη
      have hfun : pairedJointObservedHistory hD (t + 1) =
          Prod.map (pairedJointObservedHistory hD t)
            (pairedJointScalarObservation hD) := by
        funext x
        rcases x with ⟨h, A, J⟩
        rfl
      change (μ ⊗ₘ κ).map (pairedJointObservedHistory hD (t + 1)) =
        ν ⊗ₘ η
      rw [hfun]
      exact @map_compProd_of_map_apply
        (PairedJointHistory n k t)
        (History n k t)
        (MSetAction n k × PairItem k)
        (MSetAction n k × Real)
        (inferInstanceAs (MeasurableSpace (PairedJointHistory n k t)))
        (inferInstanceAs (MeasurableSpace (History n k t)))
        (inferInstanceAs (MeasurableSpace (MSetAction n k × PairItem k)))
        (inferInstanceAs (MeasurableSpace (MSetAction n k × Real)))
        μ ν κ η hsfμ hsfν hskκ hskη
        (pairedJointObservedHistory hD t)
        (pairedJointScalarObservation hD)
        (measurable_pairedJointObservedHistory hD t)
        (measurable_pairedJointScalarObservation hD)
        (by simpa [μ, ν] using ih)
        (fun h => by
          simpa [κ, η] using
            pairedJointRoundKernel_map_scalar
              P hk hD θ ε hε0 hε1 t h)

/-! ## Extracting the action trajectory from an observable history -/

/-- The action played at round `r` in a length-`t` observable history.
The definition ignores feedback and therefore applies without restricting the
ambient real-valued feedback type to the two values used by the construction. -/
def historyAction {n k : Nat} :
    (t : Nat) → History n k t → Fin t → MSetAction n k
  | 0, _h, r => Fin.elim0 r
  | t + 1, h, r =>
      Fin.lastCases h.2.1 (fun i => historyAction t h.1 i) r

@[simp] theorem historyAction_succ_last {n k t : Nat}
    (h : History n k t) (A : MSetAction n k) (y : Real) :
    historyAction (t + 1) (h, (A, y)) (Fin.last t) = A := by
  simp [historyAction]

@[simp] theorem historyAction_succ_castSucc {n k t : Nat}
    (h : History n k t) (A : MSetAction n k) (y : Real) (r : Fin t) :
    historyAction (t + 1) (h, (A, y)) r.castSucc =
      historyAction t h r := by
  simp [historyAction]

/-- Each extracted action is a measurable function of the complete observable
history.  This is the precise history-measurability needed by Assouad. -/
theorem measurable_historyAction {n k : Nat} :
    ∀ (t : Nat) (r : Fin t),
      Measurable (fun h : History n k t => historyAction t h r) := by
  intro t
  induction t with
  | zero =>
      intro r
      exact Fin.elim0 r
  | succ t ih =>
      intro r
      refine Fin.lastCases ?_ (fun i => ?_) r
      · simp only [historyAction, Fin.lastCases_last]
        fun_prop
      · simp only [historyAction, Fin.lastCases_castSucc]
        fun_prop

/-- On a projected joint history, summing the extracted actions reproduces
exactly the cumulative discrepancy used by the moment block. -/
theorem sum_historyAction_observed_eq_pairedTotalDisagreement
    {n k : Nat} (hD : 2 * k ≤ n) (θ : Fin k → PairSign) :
    ∀ (t : Nat) (h : PairedJointHistory n k t),
      (∑ r : Fin t,
        pairedDisagreement hD θ
          (historyAction t (pairedJointObservedHistory hD t h) r)) =
        pairedTotalDisagreement hD θ t h := by
  intro t
  induction t with
  | zero =>
      intro h
      simp [pairedTotalDisagreement]
  | succ t ih =>
      rintro ⟨h, A, J⟩
      rw [Fin.sum_univ_castSucc]
      simp only [pairedJointObservedHistory, historyAction_succ_castSucc,
        historyAction_succ_last, pairedTotalDisagreement]
      rw [ih h]

/-! ## Deterministic round/fallback estimators -/

/-- The manuscript estimator with the sampled round and fallback sign fixed.
Keeping these choices deterministic is what permits a direct application of
`lower_dense_assouad`; the two finite averages are restored below. -/
def pairedRoundEstimator {n k T : Nat} (hD : 2 * k ≤ n)
    (r : Fin T) (fallback : PairSign) :
    History n k T → Fin k → PairSign :=
  fun h g =>
    pairedCoordinateEstimate hD (historyAction T h r) fallback g

theorem measurableSet_pairedRoundEstimator {n k T : Nat}
    (hD : 2 * k ≤ n) (r : Fin T) (fallback : PairSign) :
    ∀ g s,
      MeasurableSet
        {h : History n k T | pairedRoundEstimator hD r fallback h g = s} := by
  intro g s
  change MeasurableSet
    ((fun h : History n k T => historyAction T h r) ⁻¹'
      {A : MSetAction n k |
        pairedCoordinateEstimate hD A fallback g = s})
  exact (measurable_historyAction T r)
    (show MeasurableSet
      {A : MSetAction n k | pairedCoordinateEstimate hD A fallback g = s}
      from MeasurableSet.of_discrete)

/-- A coordinate error probability for a fixed round and fallback is the
integral of its literal `0/1` error indicator. -/
theorem coordinateErrorProbability_pairedRoundEstimator_eq_integral
    {n k T : Nat}
    (Q : (Fin k → PairSign) → Measure (History n k T))
    [∀ θ, IsFiniteMeasure (Q θ)]
    (hD : 2 * k ≤ n) (r : Fin T) (fallback : PairSign)
    (θ : Fin k → PairSign) (g : Fin k) :
    coordinateErrorProbability Q (pairedRoundEstimator hD r fallback) θ g =
      ∫ h,
        (if pairedCoordinateEstimate hD (historyAction T h r) fallback g ≠
            θ g then (1 : Real) else 0) ∂Q θ := by
  let E : Set (History n k T) :=
    coordinateErrorEvent (pairedRoundEstimator hD r fallback) θ g
  have hE : MeasurableSet E :=
    measurableSet_coordinateErrorEvent
      (pairedRoundEstimator hD r fallback)
      (measurableSet_pairedRoundEstimator hD r fallback) θ g
  have hfun :
      (fun h : History n k T =>
        if pairedCoordinateEstimate hD (historyAction T h r) fallback g ≠
            θ g then (1 : Real) else 0) =
        E.indicator (fun _ => (1 : Real)) := by
    funext h
    by_cases hh :
        pairedCoordinateEstimate hD (historyAction T h r) fallback g ≠ θ g
    · simp [E, coordinateErrorEvent, pairedRoundEstimator,
        Set.indicator, hh]
    · simp [E, coordinateErrorEvent, pairedRoundEstimator,
        Set.indicator, hh]
  calc
    coordinateErrorProbability Q (pairedRoundEstimator hD r fallback) θ g =
        (Q θ).real E := by
      rfl
    _ = ∫ h, E.indicator (fun _ => (1 : Real)) h ∂Q θ :=
      (integral_indicator_one hE).symm
    _ = ∫ h,
        (if pairedCoordinateEstimate hD (historyAction T h r) fallback g ≠
            θ g then (1 : Real) else 0) ∂Q θ := by
      rw [hfun]

/-- Expected Hamming loss for one fixed deterministic estimator, expressed as
an integral of the sum of coordinate-error indicators. -/
theorem expectedHammingLoss_pairedRoundEstimator_eq_integral
    {n k T : Nat}
    (Q : (Fin k → PairSign) → Measure (History n k T))
    [∀ θ, IsFiniteMeasure (Q θ)]
    (hD : 2 * k ≤ n) (r : Fin T) (fallback : PairSign)
    (θ : Fin k → PairSign) :
    expectedHammingLoss Q (pairedRoundEstimator hD r fallback) θ =
      ∫ h, ∑ g : Fin k,
        (if pairedCoordinateEstimate hD (historyAction T h r) fallback g ≠
            θ g then (1 : Real) else 0) ∂Q θ := by
  rw [expectedHammingLoss]
  simp_rw [coordinateErrorProbability_pairedRoundEstimator_eq_integral
    Q hD r fallback θ]
  rw [← integral_finsetSum]
  intro g _
  let E : Set (History n k T) :=
    coordinateErrorEvent (pairedRoundEstimator hD r fallback) θ g
  have hE : MeasurableSet E :=
    measurableSet_coordinateErrorEvent
      (pairedRoundEstimator hD r fallback)
      (measurableSet_pairedRoundEstimator hD r fallback) θ g
  have hfun :
      (fun h : History n k T =>
        if pairedCoordinateEstimate hD (historyAction T h r) fallback g ≠
            θ g then (1 : Real) else 0) =
        E.indicator (fun _ => (1 : Real)) := by
    funext h
    by_cases hh :
        pairedCoordinateEstimate hD (historyAction T h r) fallback g ≠ θ g
    · simp [E, coordinateErrorEvent, pairedRoundEstimator,
        Set.indicator, hh]
    · simp [E, coordinateErrorEvent, pairedRoundEstimator,
        Set.indicator, hh]
  rw [hfun]
  exact (integrable_const (1 : Real)).indicator hE

theorem integrable_pairedRound_error_sum
    {n k T : Nat} (Q : Measure (History n k T)) [IsFiniteMeasure Q]
    (hD : 2 * k ≤ n) (r : Fin T) (fallback : PairSign)
    (θ : Fin k → PairSign) :
    Integrable
      (fun h => ∑ g : Fin k,
        (if pairedCoordinateEstimate hD (historyAction T h r) fallback g ≠
            θ g then (1 : Real) else 0)) Q := by
  apply integrable_finsetSum Finset.univ
  intro g _
  let E : Set (History n k T) :=
    coordinateErrorEvent (pairedRoundEstimator hD r fallback) θ g
  have hE : MeasurableSet E :=
    measurableSet_coordinateErrorEvent
      (pairedRoundEstimator hD r fallback)
      (measurableSet_pairedRoundEstimator hD r fallback) θ g
  have hfun :
      (fun h : History n k T =>
        if pairedCoordinateEstimate hD (historyAction T h r) fallback g ≠
            θ g then (1 : Real) else 0) =
        E.indicator (fun _ => (1 : Real)) := by
    funext h
    by_cases hh :
        pairedCoordinateEstimate hD (historyAction T h r) fallback g ≠ θ g
    · simp [E, coordinateErrorEvent, pairedRoundEstimator,
        Set.indicator, hh]
    · simp [E, coordinateErrorEvent, pairedRoundEstimator,
        Set.indicator, hh]
  rw [hfun]
  exact (integrable_const (1 : Real)).indicator hE

/-- Averaging the two deterministic fallback estimators gives exactly the
manuscript's fair coordinate-error integral for the fixed round. -/
theorem average_fallback_expectedHammingLoss_eq_integral_fair
    {n k T : Nat}
    (Q : (Fin k → PairSign) → Measure (History n k T))
    [∀ θ, IsFiniteMeasure (Q θ)]
    (hD : 2 * k ≤ n) (r : Fin T) (θ : Fin k → PairSign) :
    (expectedHammingLoss Q
          (pairedRoundEstimator hD r PairSign.neg) θ +
        expectedHammingLoss Q
          (pairedRoundEstimator hD r PairSign.pos) θ) / 2 =
      ∫ h, ∑ g : Fin k,
        fairCoordinateError hD θ (historyAction T h r) g ∂Q θ := by
  rw [expectedHammingLoss_pairedRoundEstimator_eq_integral
      Q hD r PairSign.neg θ,
    expectedHammingLoss_pairedRoundEstimator_eq_integral
      Q hD r PairSign.pos θ]
  rw [← integral_add
    (integrable_pairedRound_error_sum (Q θ) hD r PairSign.neg θ)
    (integrable_pairedRound_error_sum (Q θ) hD r PairSign.pos θ),
    ← integral_div]
  apply integral_congr_ae
  apply ae_of_all
  intro h
  simp only [fairCoordinateError]
  simp only [div_eq_mul_inv]
  rw [← Finset.sum_add_distrib, Finset.sum_mul]

theorem sum_fairCoordinateError_eq_average_error_sums
    {n k : Nat} (hD : 2 * k ≤ n) (θ : Fin k → PairSign)
    (A : MSetAction n k) :
    (∑ g : Fin k, fairCoordinateError hD θ A g) =
      ((∑ g : Fin k,
          if pairedCoordinateEstimate hD A PairSign.neg g ≠ θ g
          then (1 : Real) else 0) +
        ∑ g : Fin k,
          if pairedCoordinateEstimate hD A PairSign.pos g ≠ θ g
          then (1 : Real) else 0) / 2 := by
  simp only [fairCoordinateError, div_eq_mul_inv]
  rw [← Finset.sum_add_distrib, Finset.sum_mul]

theorem integrable_sum_fairCoordinateError
    {n k T : Nat} (Q : Measure (History n k T)) [IsFiniteMeasure Q]
    (hD : 2 * k ≤ n) (r : Fin T) (θ : Fin k → PairSign) :
    Integrable
      (fun h => ∑ g : Fin k,
        fairCoordinateError hD θ (historyAction T h r) g) Q := by
  have hn := integrable_pairedRound_error_sum
    Q hD r PairSign.neg θ
  have hp := integrable_pairedRound_error_sum
    Q hD r PairSign.pos θ
  have havg := (hn.add hp).div_const 2
  apply havg.congr
  apply ae_of_all
  intro h
  exact (sum_fairCoordinateError_eq_average_error_sums
    hD θ (historyAction T h r)).symm

/-- Average, first over the two fallback signs and then over the `T` rounds,
of the deterministic Assouad risks. -/
def averagedRoundEstimatorRisk {n k T : Nat}
    (Q : (Fin k → PairSign) → Measure (History n k T))
    (hD : 2 * k ≤ n) (θ : Fin k → PairSign) : Real :=
  (T : Real)⁻¹ * ∑ r : Fin T,
    (expectedHammingLoss Q
          (pairedRoundEstimator hD r PairSign.neg) θ +
      expectedHammingLoss Q
          (pairedRoundEstimator hD r PairSign.pos) θ) / 2

/-- The preceding finite average is exactly the expectation of the
random-round/Rademacher estimator appearing in the manuscript. -/
theorem averagedRoundEstimatorRisk_eq_integral_randomRound
    {n k T : Nat}
    (Q : (Fin k → PairSign) → Measure (History n k T))
    [∀ θ, IsFiniteMeasure (Q θ)]
    (hD : 2 * k ≤ n) (θ : Fin k → PairSign) :
    averagedRoundEstimatorRisk Q hD θ =
      ∫ h, randomRoundExpectedHamming hD θ
        (historyAction T h) ∂Q θ := by
  unfold averagedRoundEstimatorRisk
  simp_rw [average_fallback_expectedHammingLoss_eq_integral_fair
    Q hD]
  rw [← integral_finsetSum Finset.univ
      (fun r _ => integrable_sum_fairCoordinateError (Q θ) hD r θ),
    ← integral_const_mul]
  apply integral_congr_ae
  apply ae_of_all
  intro h
  unfold randomRoundExpectedHamming randomRoundCoordinateError
  change (T : Real)⁻¹ * ∑ r : Fin T, ∑ g : Fin k,
      fairCoordinateError hD θ (historyAction T h r) g =
    ∑ g : Fin k, (T : Real)⁻¹ * ∑ r : Fin T,
      fairCoordinateError hD θ (historyAction T h r) g
  rw [← Finset.mul_sum, Finset.sum_comm]

theorem sum_pair_average_eq_average_sums
    {α : Type*} [Fintype α] (f g : α → Real) :
    (∑ x : α, (f x + g x) / 2) =
      ((∑ x : α, f x) + ∑ x : α, g x) / 2 := by
  simp only [div_eq_mul_inv]
  rw [← Finset.sum_add_distrib, Finset.sum_mul]

/-- If Assouad gives the same lower bound for every fixed round and each of
the two fixed fallback signs, the two finite averages retain that bound. -/
theorem average_averagedRoundEstimatorRisk_ge_of_fixed
    {n k T : Nat} (hT : 1 ≤ T)
    (Q : (Fin k → PairSign) → Measure (History n k T))
    (hD : 2 * k ≤ n)
    (hfixed : ∀ (r : Fin T) (fallback : PairSign),
      (Fintype.card (Fin k → PairSign) : Real)⁻¹ *
          ∑ θ : Fin k → PairSign,
            expectedHammingLoss Q
              (pairedRoundEstimator hD r fallback) θ ≥
        3 * (k : Real) / 8) :
    (Fintype.card (Fin k → PairSign) : Real)⁻¹ *
        ∑ θ : Fin k → PairSign,
          averagedRoundEstimatorRisk Q hD θ ≥
      3 * (k : Real) / 8 := by
  let c : Real :=
    (Fintype.card (Fin k → PairSign) : Real)⁻¹
  let L : Real := 3 * (k : Real) / 8
  let risk (r : Fin T) (fallback : PairSign)
      (θ : Fin k → PairSign) : Real :=
    expectedHammingLoss Q (pairedRoundEstimator hD r fallback) θ
  have hround (r : Fin T) :
      c * ∑ θ : Fin k → PairSign,
          (risk r PairSign.neg θ + risk r PairSign.pos θ) / 2 ≥ L := by
    have hn : c * ∑ θ : Fin k → PairSign,
        risk r PairSign.neg θ ≥ L := by
      simpa [c, L, risk] using hfixed r PairSign.neg
    have hp : c * ∑ θ : Fin k → PairSign,
        risk r PairSign.pos θ ≥ L := by
      simpa [c, L, risk] using hfixed r PairSign.pos
    rw [sum_pair_average_eq_average_sums]
    calc
      c * (((∑ θ : Fin k → PairSign, risk r PairSign.neg θ) +
          ∑ θ : Fin k → PairSign, risk r PairSign.pos θ) / 2) =
          (c * (∑ θ : Fin k → PairSign, risk r PairSign.neg θ) +
            c * (∑ θ : Fin k → PairSign, risk r PairSign.pos θ)) / 2 := by
        ring
      _ ≥ L := by linarith
  have hsum := Finset.sum_le_sum
    (fun r (_ : r ∈ (Finset.univ : Finset (Fin T))) => hround r)
  have hsum' :
      (T : Real) * L ≤
        ∑ r : Fin T, c * ∑ θ : Fin k → PairSign,
          (risk r PairSign.neg θ + risk r PairSign.pos θ) / 2 := by
    simpa using hsum
  have hTpos : (0 : Real) < T := by exact_mod_cast hT
  have hscaled := mul_le_mul_of_nonneg_left hsum'
    (inv_nonneg.mpr hTpos.le)
  change c * ∑ θ : Fin k → PairSign,
      (T : Real)⁻¹ * ∑ r : Fin T,
        (risk r PairSign.neg θ + risk r PairSign.pos θ) / 2 ≥ L
  calc
    L = (T : Real)⁻¹ * ((T : Real) * L) := by
      field_simp [ne_of_gt hTpos]
    _ ≤ (T : Real)⁻¹ *
        (∑ r : Fin T, c * ∑ θ : Fin k → PairSign,
          (risk r PairSign.neg θ + risk r PairSign.pos θ) / 2) := hscaled
    _ = c * ∑ θ : Fin k → PairSign,
        (T : Real)⁻¹ * ∑ r : Fin T,
          (risk r PairSign.neg θ + risk r PairSign.pos θ) / 2 := by
      calc
        (T : Real)⁻¹ *
            (∑ r : Fin T, c * ∑ θ : Fin k → PairSign,
              (risk r PairSign.neg θ + risk r PairSign.pos θ) / 2) =
            (T : Real)⁻¹ * (c * ∑ r : Fin T,
              ∑ θ : Fin k → PairSign,
                (risk r PairSign.neg θ + risk r PairSign.pos θ) / 2) := by
          congr 1
          rw [Finset.mul_sum]
        _ = c * ((T : Real)⁻¹ * ∑ θ : Fin k → PairSign,
              ∑ r : Fin T,
                (risk r PairSign.neg θ + risk r PairSign.pos θ) / 2) := by
          rw [Finset.sum_comm]
          ring
        _ = c * ∑ θ : Fin k → PairSign,
            (T : Real)⁻¹ * ∑ r : Fin T,
              (risk r PairSign.neg θ + risk r PairSign.pos θ) / 2 := by
          congr 1
          rw [Finset.mul_sum]

/-! ## Assouad instantiated by the adaptive observable laws -/

/-- Averaged Hamming lower bound for the actual adaptive observable process.
The only information input is `paired_sequential_kl`, whose one-step Bernoulli
calculation and adaptive chain rule were proved upstream. -/
theorem lower_dense_average_randomRoundExpectedHamming
    {n k T : Nat} (P : Policy n k) (hk : 1 ≤ k)
    (hD : 2 * k ≤ n) (hT : 1 ≤ T)
    (hk_half : k ≤ n / 2) (horizon : n ^ 2 ≤ T) :
    (Fintype.card (Fin k → PairSign) : Real)⁻¹ *
        ∑ θ : Fin k → PairSign,
          ∫ h, randomRoundExpectedHamming hD θ (historyAction T h)
            ∂(pairedAdaptiveProcess P hk hD θ (denseEpsilon k T)
              (denseEpsilon_nonneg k T)
              (denseEpsilon_le_one_paper_regime hk hk_half horizon)).law T ≥
      3 * (k : Real) / 8 := by
  let ε : Real := denseEpsilon k T
  let hε0 : 0 ≤ ε := denseEpsilon_nonneg k T
  let hε16 : ε ≤ (1 : Real) / 16 :=
    denseEpsilon_le_sixteenth hk hk_half horizon
  let hε1 : ε ≤ 1 := hε16.trans (by norm_num)
  let Q : (Fin k → PairSign) → Measure (History n k T) :=
    fun θ => (pairedAdaptiveProcess P hk hD θ ε hε0 hε1).law T
  letI : ∀ θ, IsProbabilityMeasure (Q θ) := fun θ => by
    dsimp [Q]
    infer_instance
  have hKL (θ : Fin k → PairSign) :
      (∑ g : Fin k, klDiv (Q θ) (Q (flipHypothesis θ g))) ≤
        ENNReal.ofReal
          (16 * denseEpsilon k T ^ 2 * (T : Real) /
            (2 * (k : Real))) := by
    simpa [Q, ε, hε0, hε1] using
      paired_sequential_kl P hk hD θ
        (denseEpsilon_nonneg k T)
        (denseEpsilon_le_sixteenth hk hk_half horizon) T
  have hfixed (r : Fin T) (fallback : PairSign) :
      (Fintype.card (Fin k → PairSign) : Real)⁻¹ *
          ∑ θ : Fin k → PairSign,
            expectedHammingLoss Q
              (pairedRoundEstimator hD r fallback) θ ≥
        3 * (k : Real) / 8 :=
    lower_dense_assouad hk hT Q
      (pairedRoundEstimator hD r fallback)
      (measurableSet_pairedRoundEstimator hD r fallback) hKL
  have havg := average_averagedRoundEstimatorRisk_ge_of_fixed
    hT Q hD hfixed
  change (Fintype.card (Fin k → PairSign) : Real)⁻¹ *
      ∑ θ : Fin k → PairSign,
        ∫ h, randomRoundExpectedHamming hD θ (historyAction T h)
          ∂Q θ ≥ 3 * (k : Real) / 8
  calc
    (Fintype.card (Fin k → PairSign) : Real)⁻¹ *
        ∑ θ : Fin k → PairSign,
          ∫ h, randomRoundExpectedHamming hD θ (historyAction T h)
            ∂Q θ =
      (Fintype.card (Fin k → PairSign) : Real)⁻¹ *
        ∑ θ : Fin k → PairSign,
          averagedRoundEstimatorRisk Q hD θ := by
      congr 1
      apply Finset.sum_congr rfl
      intro θ _
      exact (averagedRoundEstimatorRisk_eq_integral_randomRound
        Q hD θ).symm
    _ ≥ 3 * (k : Real) / 8 := havg

/-! ## Transferring the estimation gap to the genuine joint law -/

theorem measurable_historyDisagreementSum
    {n k T : Nat} (hD : 2 * k ≤ n) (θ : Fin k → PairSign) :
    Measurable
      (fun h : History n k T => ∑ r : Fin T,
        pairedDisagreement hD θ (historyAction T h r)) := by
  apply Finset.measurable_sum
  intro r _
  exact (measurable_of_finite
    (fun A : MSetAction n k => pairedDisagreement hD θ A)).comp
      (measurable_historyAction T r)

/-- The expected action discrepancy computed on the observable adaptive law
is exactly the expected `pairedTotalDisagreement` on the latent joint law. -/
theorem integral_observable_disagreement_eq_joint_total
    {n k T : Nat} (P : Policy n k) (hk : 1 ≤ k)
    (hD : 2 * k ≤ n) (θ : Fin k → PairSign) (ε : Real)
    (hε0 : 0 ≤ ε) (hε1 : ε ≤ 1) :
    (∫ h, ∑ r : Fin T,
        pairedDisagreement hD θ (historyAction T h r)
      ∂(pairedAdaptiveProcess P hk hD θ ε hε0 hε1).law T) =
      ∫ h, pairedTotalDisagreement hD θ T h
        ∂pairedJointLaw P hk hD θ ε hε0 hε1 T := by
  let f : History n k T → Real := fun h => ∑ r : Fin T,
    pairedDisagreement hD θ (historyAction T h r)
  have hf : Measurable f := measurable_historyDisagreementSum hD θ
  have hmap := pairedJointObservedHistory_map_law
    P hk hD θ ε hε0 hε1 T
  change (∫ h, f h
      ∂(pairedAdaptiveProcess P hk hD θ ε hε0 hε1).law T) = _
  calc
    (∫ h, f h
        ∂(pairedAdaptiveProcess P hk hD θ ε hε0 hε1).law T) =
        ∫ h, f h ∂(pairedJointLaw P hk hD θ ε hε0 hε1 T).map
          (pairedJointObservedHistory hD T) := by
      rw [hmap]
    _ = ∫ h, f (pairedJointObservedHistory hD T h)
          ∂pairedJointLaw P hk hD θ ε hε0 hε1 T := by
      exact integral_map
        (measurable_pairedJointObservedHistory hD T).aemeasurable
        hf.aestronglyMeasurable
    _ = ∫ h, pairedTotalDisagreement hD θ T h
          ∂pairedJointLaw P hk hD θ ε hε0 hε1 T := by
      apply integral_congr_ae
      apply ae_of_all
      intro h
      exact sum_historyAction_observed_eq_pairedTotalDisagreement hD θ T h

/-- Assouad plus the estimation--regret identity produces one hypercube
hypothesis whose genuine adaptive joint law has the manuscript's
`3kT/4` expected discrepancy.  This discharges the upstream hypothesis of the
moment block without inserting the conclusion as an assumption. -/
theorem exists_pairedJoint_expected_disagreement_ge
    {n k T : Nat} (P : Policy n k) (hk : 1 ≤ k)
    (hD : 2 * k ≤ n) (hT : 1 ≤ T)
    (hk_half : k ≤ n / 2) (horizon : n ^ 2 ≤ T) :
    ∃ θ : Fin k → PairSign,
      3 * (k : Real) * (T : Real) / 4 ≤
        ∫ h, pairedTotalDisagreement hD θ T h
          ∂pairedJointLaw P hk hD θ (denseEpsilon k T)
            (denseEpsilon_nonneg k T)
            (denseEpsilon_le_one_paper_regime hk hk_half horizon) T := by
  let hε1 := denseEpsilon_le_one_paper_regime hk hk_half horizon
  let Q : (Fin k → PairSign) → Measure (History n k T) := fun θ =>
    (pairedAdaptiveProcess P hk hD θ (denseEpsilon k T)
      (denseEpsilon_nonneg k T) hε1).law T
  let ham : (Fin k → PairSign) → Real := fun θ =>
    ∫ h, randomRoundExpectedHamming hD θ (historyAction T h) ∂Q θ
  let gap : (Fin k → PairSign) → Real := fun θ =>
    ∫ h, pairedTotalDisagreement hD θ T h
      ∂pairedJointLaw P hk hD θ (denseEpsilon k T)
        (denseEpsilon_nonneg k T) hε1 T
  have haverage :
      (Fintype.card (Fin k → PairSign) : Real)⁻¹ *
          ∑ θ : Fin k → PairSign, ham θ ≥
        3 * (k : Real) / 8 := by
    simpa [ham, Q, hε1] using
      lower_dense_average_randomRoundExpectedHamming
        P hk hD hT hk_half horizon
  have hlink (θ : Fin k → PairSign) :
      ham θ = 1 / (2 * (T : Real)) * gap θ := by
    calc
      ham θ = 1 / (2 * (T : Real)) *
          ∫ h, ∑ r : Fin T,
            pairedDisagreement hD θ (historyAction T h r) ∂Q θ := by
        exact lower_dense_estimation_regret_link_integral
          (Q θ) hT hD θ (historyAction T)
      _ = 1 / (2 * (T : Real)) * gap θ := by
        congr 1
        exact integral_observable_disagreement_eq_joint_total
          P hk hD θ (denseEpsilon k T)
            (denseEpsilon_nonneg k T) hε1
  exact exists_large_gap_of_average_hamming hk hT ham gap hlink haverage

/-! ## Probabilistic dense capstone before deterministic fixing -/

/-- The entire paper-regime moment block for the hypothesis supplied by the
observable-law Assouad argument. -/
theorem exists_lower_dense_moment_block_paper_regime
    {n k T : Nat} (P : Policy n k) (hk : 1 ≤ k)
    (hD : 2 * k ≤ n) (hT : 1 ≤ T)
    (hk_half : k ≤ n / 2) (horizon : n ^ 2 ≤ T) :
    ∃ θ : Fin k → PairSign,
      (((k : Real) * Real.sqrt T / 32 ≤
          ∫ h, pairedGap hD θ T h
            ∂pairedJointLaw P hk hD θ (denseEpsilon k T)
              (denseEpsilon_nonneg k T)
              (denseEpsilon_le_one_paper_regime hk hk_half horizon) T) ∧
        ((∫ h, (pairedGap hD θ T h) ^ 2
            ∂pairedJointLaw P hk hD θ (denseEpsilon k T)
              (denseEpsilon_nonneg k T)
              (denseEpsilon_le_one_paper_regime hk hk_half horizon) T) ≤
          3 * (k : Real) ^ 2 * (T : Real)) ∧
        ((1 : Real) / 12288 ≤
          (pairedJointLaw P hk hD θ (denseEpsilon k T)
            (denseEpsilon_nonneg k T)
            (denseEpsilon_le_one_paper_regime hk hk_half horizon) T).real
            {h | (k : Real) * Real.sqrt T / 64 ≤
              pairedExternalRegret hD T h})) := by
  obtain ⟨θ, hdis⟩ := exists_pairedJoint_expected_disagreement_ge
    P hk hD hT hk_half horizon
  exact ⟨θ, lower_dense_moment_block_paper_regime
    P hk hD hT hk_half horizon θ hdis⟩

/-- Probabilistic form of `prop:lower-bounded-action` before fixing a
deterministic loss table: for one paired hypothesis, the genuine adaptive
experiment has regret at least `k√T/64` with probability strictly greater
than `2⁻¹⁴`. -/
theorem lower_dense_probabilistic_action_capstone
    {n k T : Nat} (P : Policy n k) (hk : 1 ≤ k)
    (hD : 2 * k ≤ n) (hT : 1 ≤ T)
    (hk_half : k ≤ n / 2) (horizon : n ^ 2 ≤ T) :
    ∃ θ : Fin k → PairSign,
      (2 : Real) ^ (-14 : Int) <
        (pairedJointLaw P hk hD θ (denseEpsilon k T)
          (denseEpsilon_nonneg k T)
          (denseEpsilon_le_one_paper_regime hk hk_half horizon) T).real
          {h | (k : Real) * Real.sqrt T / 64 ≤
            pairedExternalRegret hD T h} := by
  obtain ⟨θ, _hmean, _hsecond, hprob⟩ :=
    exists_lower_dense_moment_block_paper_regime
      P hk hD hT hk_half horizon
  exact ⟨θ, one_div_12288_gt_two_zpow_neg_fourteen.trans_le hprob⟩

end

end MsetsLower.Lower.Dense

#print axioms MsetsLower.Lower.Dense.pairedPMF_map_selectedBool
#print axioms MsetsLower.Lower.Dense.pairedJointObservedHistory_map_law
#print axioms MsetsLower.Lower.Dense.integral_observable_disagreement_eq_joint_total
#print axioms MsetsLower.Lower.Dense.exists_pairedJoint_expected_disagreement_ge
#print axioms MsetsLower.Lower.Dense.lower_dense_probabilistic_action_capstone
