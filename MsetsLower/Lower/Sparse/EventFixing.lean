import MsetsLower.Lower.Sparse.Gamma
import MsetsLower.Lower.Sparse.FinalArithmetic

/-!
# Fixing the sparse `Gamma` event to one deterministic table

The likelihood argument produces a lower bound for an observable event under
the centered hidden-table joint law.  This file transports that same event
through the actual-history equivalence and the finite noise-table mixture,
then proves sectionwise that it implies the desired regret event.  Averaging
finally fixes one genuine auxiliary table.
-/

set_option linter.style.header false

namespace MsetsLower.Lower.Sparse

open MsetsLower Feedback MeasureTheory ProbabilityTheory Set
open MsetsLower.Lower
open scoped BigOperators ENNReal ProbabilityTheory

noncomputable section

/-! ## The same event on the three exact joint-law realizations -/

def sparseCenteredGammaEvent
    {n n' k r B T : Nat} (hk : 1 <= k)
    (eta : Real) (heta0 : 0 <= eta) (heta : eta <= (1 : Real) / 16)
    (q c0 : Nat) (hn' : n' <= n) (hprod : n' = k * r) (hr : 0 < r)
    (sigma : Equiv.Perm (Fin n')) (threshold : Real) :
    Set (SparseHiddenTable B n × History n k T) :=
  {z | threshold <=
    sparseGamma hk eta heta0 heta q c0 hn' hprod hr sigma T z}

theorem measurableSet_sparseCenteredGammaEvent
    {n n' k r B T : Nat} (hk : 1 <= k)
    (eta : Real) (heta0 : 0 <= eta) (heta : eta <= (1 : Real) / 16)
    (q c0 : Nat) (hn' : n' <= n) (hprod : n' = k * r) (hr : 0 < r)
    (sigma : Equiv.Perm (Fin n')) (threshold : Real) :
    MeasurableSet (sparseCenteredGammaEvent (B := B) (T := T)
      hk eta heta0 heta q c0 hn' hprod hr sigma threshold) :=
  measurableSet_le measurable_const
    (measurable_sparseGamma (B := B) hk eta heta0 heta q c0 hn'
      hprod hr sigma T)

def sparseActualGammaEvent
    {n n' k r B T : Nat} (hk : 1 <= k)
    (eta : Real) (heta0 : 0 <= eta) (heta : eta <= (1 : Real) / 16)
    (q c0 : Nat) (hn' : n' <= n) (hprod : n' = k * r) (hr : 0 < r)
    (sigma : Equiv.Perm (Fin n')) (threshold : Real) :
    Set (SparseHiddenTable B n × History n k T) :=
  {z | threshold <=
    sparseGamma hk eta heta0 heta q c0 hn' hprod hr sigma T
      (z.1, (sparseActualHistoryEquiv n k T).symm z.2)}

theorem measurableSet_sparseActualGammaEvent
    {n n' k r B T : Nat} (hk : 1 <= k)
    (eta : Real) (heta0 : 0 <= eta) (heta : eta <= (1 : Real) / 16)
    (q c0 : Nat) (hn' : n' <= n) (hprod : n' = k * r) (hr : 0 < r)
    (sigma : Equiv.Perm (Fin n')) (threshold : Real) :
    MeasurableSet (sparseActualGammaEvent (B := B) (T := T)
      hk eta heta0 heta q c0 hn' hprod hr sigma threshold) := by
  apply measurableSet_le measurable_const
  exact (measurable_sparseGamma (B := B) hk eta heta0 heta q c0 hn'
    hprod hr sigma T).comp
      (measurable_fst.prodMk
        ((sparseActualHistoryEquiv n k T).symm.measurable.comp measurable_snd))

def sparseAuxGammaEvent
    {n n' k r B T : Nat} (hk : 1 <= k)
    (eta : Real) (heta0 : 0 <= eta) (heta : eta <= (1 : Real) / 16)
    (q c0 : Nat) (hn' : n' <= n) (hprod : n' = k * r) (hr : 0 < r)
    (sigma : Equiv.Perm (Fin n')) (threshold : Real) :
    Set (SparseAuxTable B n T × History n k T) :=
  sparseForgetNoise ⁻¹'
    sparseActualGammaEvent hk eta heta0 heta q c0 hn'
      hprod hr sigma threshold

theorem measurableSet_sparseAuxGammaEvent
    {n n' k r B T : Nat} (hk : 1 <= k)
    (eta : Real) (heta0 : 0 <= eta) (heta : eta <= (1 : Real) / 16)
    (q c0 : Nat) (hn' : n' <= n) (hprod : n' = k * r) (hr : 0 < r)
    (sigma : Equiv.Perm (Fin n')) (threshold : Real) :
    MeasurableSet (sparseAuxGammaEvent (B := B) (T := T)
      hk eta heta0 heta q c0 hn' hprod hr sigma threshold) :=
  (measurableSet_sparseActualGammaEvent (B := B) (T := T)
    hk eta heta0 heta q c0 hn' hprod hr sigma threshold).preimage
      measurable_sparseForgetNoise

/-- Both exact pushforwards preserve the complete `Gamma` event, including
its hidden-table dependence. -/
theorem sparseAuxGammaEvent_measure_eq_centered
    {n n' k r B T : Nat} (P : Policy n k) (hk : 1 <= k)
    (eta : Real) (heta0 : 0 <= eta) (heta : eta <= (1 : Real) / 16)
    (q c0 : Nat) (hn' : n' <= n) (hprod : n' = k * r) (hr : 0 < r)
    (sigma : Equiv.Perm (Fin n')) (threshold : Real) :
    sparseAuxParametricJointMeasure P hk eta heta0 heta n' q c0 T B
        (sparseAuxGammaEvent hk eta heta0 heta q c0 hn'
          hprod hr sigma threshold) =
      sparseJointLaw (sparseHiddenTableMeasure B n) (sparseCenteredPolicy P)
          (sparseHiddenTableParameterFamily hk eta heta0 heta n' q c0 B) T
        (sparseCenteredGammaEvent hk eta heta0 heta q c0 hn'
          hprod hr sigma threshold) := by
  let centeredMap : SparseHiddenTable B n × History n k T ->
      SparseHiddenTable B n × History n k T :=
    fun z => (z.1, sparseActualHistoryEquiv n k T z.2)
  have hcenterMap : Measurable centeredMap :=
    measurable_fst.prodMk
      ((sparseActualHistoryEquiv n k T).measurable.comp measurable_snd)
  have hactual := congrArg
    (fun mu : Measure (SparseHiddenTable B n × History n k T) =>
      mu (sparseActualGammaEvent hk eta heta0 heta q c0 hn'
        hprod hr sigma threshold))
    (sparseJointLaw_map_actualHistory
      (sparseHiddenTableMeasure B n) P
      (sparseHiddenTableParameterFamily hk eta heta0 heta n' q c0 B) T)
  rw [Measure.map_apply hcenterMap
    (measurableSet_sparseActualGammaEvent (B := B) (T := T)
      hk eta heta0 heta q c0 hn' hprod hr sigma threshold)] at hactual
  have hpreimage : centeredMap ⁻¹'
      sparseActualGammaEvent hk eta heta0 heta q c0 hn'
        hprod hr sigma threshold =
      sparseCenteredGammaEvent hk eta heta0 heta q c0 hn'
        hprod hr sigma threshold := by
    ext z
    simp [centeredMap, sparseActualGammaEvent, sparseCenteredGammaEvent]
  rw [hpreimage] at hactual
  have haux := congrArg
    (fun mu : Measure (SparseHiddenTable B n × History n k T) =>
      mu (sparseActualGammaEvent hk eta heta0 heta q c0 hn'
        hprod hr sigma threshold))
    (sparseAuxParametricJointMeasure_map_forgetNoise
      P hk eta heta0 heta n' q c0)
  rw [Measure.map_apply measurable_sparseForgetNoise
    (measurableSet_sparseActualGammaEvent (B := B) (T := T)
      hk eta heta0 heta q c0 hn' hprod hr sigma threshold)] at haux
  change sparseAuxParametricJointMeasure P hk eta heta0 heta n' q c0 T B
      (sparseAuxGammaEvent hk eta heta0 heta q c0 hn'
        hprod hr sigma threshold) = _ at haux
  exact haux.trans hactual.symm

/-! ## Sectionwise event-to-regret implication -/

/-- On every fixed auxiliary-table section, the `Gamma` event implies the
parametric regret event almost surely.  The only exceptional histories are
the protocol-incompatible ones, which have zero run-law mass. -/
theorem sparseAuxGammaEvent_measure_le_regretEvent
    {n n' k r B T : Nat} (P : Policy n k) (hk : 1 <= k)
    (hkn' : k <= n')
    (eta : Real) (heta0 : 0 <= eta) (heta : eta <= (1 : Real) / 16)
    (q c0 : Nat) (hn' : n' <= n) (hprod : n' = k * r) (hr : 0 < r)
    (sigma : Equiv.Perm (Fin n')) :
    (sparseAuxParametricJointMeasure P hk eta heta0 heta n' q c0 T B).real
        (sparseAuxGammaEvent hk eta heta0 heta q c0 hn' hprod hr sigma
          (sparseA / 8 * (k : Real) * (T : Real))) <=
      (sparseAuxParametricJointMeasure P hk eta heta0 heta n' q c0 T B).real
        (parametricRegretEvent
          (sparseTableLossProcess hk eta heta0 heta n' q c0 T B) T
          (sparseA * eta * (T : Real) / 8)) := by
  let L : ParametricLossProcess (SparseAuxTable B n T) n k :=
    sparseTableLossProcess hk eta heta0 heta n' q c0 T B
  let mu : Measure (SparseAuxTable B n T) := sparseAuxTableMeasure B n T
  let E : Set (SparseAuxTable B n T × History n k T) :=
    sparseAuxGammaEvent (B := B) (T := T) hk eta heta0 heta q c0 hn'
      hprod hr sigma (sparseA / 8 * (k : Real) * (T : Real))
  have hkn : k <= n := hkn'.trans hn'
  letI : IsProbabilityMeasure
      (sparseAuxParametricJointMeasure P hk eta heta0 heta n' q c0 T B) := by
    unfold sparseAuxParametricJointMeasure
    infer_instance
  have hmeasure :
      sparseAuxParametricJointMeasure P hk eta heta0 heta n' q c0 T B E <=
        sparseAuxParametricJointMeasure P hk eta heta0 heta n' q c0 T B
          (parametricRegretEvent L T (sparseA * eta * (T : Real) / 8)) := by
    unfold sparseAuxParametricJointMeasure
    rw [Measure.bind_apply
      (measurableSet_sparseAuxGammaEvent (B := B) (T := T)
        hk eta heta0 heta q c0 hn' hprod hr sigma
          (sparseA / 8 * (k : Real) * (T : Real)))
      (Kernel.aemeasurable _),
      Measure.bind_apply
        (measurableSet_parametricRegretEvent L T
          (sparseA * eta * (T : Real) / 8)) (Kernel.aemeasurable _)]
    apply lintegral_mono
    intro table
    change (parametricRunWithParameterKernel P L T table) E <=
      parametricRunWithParameterKernel P L T table
        (parametricRegretEvent L T (sparseA * eta * (T : Real) / 8))
    rw [parametricRunWithParameterKernel_regretEvent_apply hkn,
      parametricRunWithParameterKernel_apply,
      Measure.map_apply measurable_prodMk_left
        (measurableSet_sparseAuxGammaEvent (B := B) (T := T)
          hk eta heta0 heta q c0 hn' hprod hr sigma
            (sparseA / 8 * (k : Real) * (T : Real)))]
    apply measure_mono_ae
    filter_upwards [ae_runLaw_sparseProtocolHistoryCompatible P (L.at table) T]
      with h hcompat
    intro hE
    have hcompat' : SparseProtocolHistoryCompatible
        (sparseLossProcess hk eta heta0 heta n' q c0 T
          (sparseHiddenTableU table.1)
          (sparseHiddenTableU_abs_le_one table.1)
          (sparseTableZ table) (sparseTableZ_mem_Icc table)) T h := by
      rw [sparseTableLossProcess_at] at hcompat
      exact hcompat
    have hGamma : sparseA / 8 * (k : Real) * (T : Real) <=
        sparseGamma hk eta heta0 heta q c0 hn' hprod hr sigma T
          (table.1, (sparseActualHistoryEquiv n k T).symm h) := by
      exact hE
    have hgap := sparseGamma_event_implies_maxScoreGap
      hk eta heta0 heta q c0 hn' hprod hr sigma table.1
      (sparseTableZ table) (sparseTableZ_mem_Icc table) h hcompat'
      (sparseA / 8 * (k : Real) * (T : Real)) hGamma
    have hregret := lower_sparse_regret_identity (q := q) (c0 := c0)
      hk hkn' hn' eta heta0 heta
      (sparseHiddenTableU table.1) (sparseHiddenTableU_abs_le_one table.1)
      (sparseTableZ table) (sparseTableZ_mem_Icc table) h
    have hfinal := sparse_score_event_implies_regret_eta
      (k := (k : Real)) (T0 := (T : Real)) (eta := eta)
      (gamma := sparseMaxSignalScore q c0 hn'
        (sparseHiddenTableU table.1) (sparseTableZ table) T h -
          sparseLearnerScore n' q c0
            (sparseHiddenTableU table.1) (sparseTableZ table) T h)
      (regret := pathRegret
        (sparseLossProcess hk eta heta0 heta n' q c0 T
          (sparseHiddenTableU table.1)
          (sparseHiddenTableU_abs_le_one table.1)
          (sparseTableZ table) (sparseTableZ_mem_Icc table)) T h)
      (by exact_mod_cast (show 0 < k by omega)) heta0 hgap hregret
    change sparseA * eta * (T : Real) / 8 <=
      pathRegret (L.at table) T h
    rw [sparseTableLossProcess_at]
    exact hfinal
  exact ENNReal.toReal_mono (measure_ne_top _ _) hmeasure

/-! ## Deterministic fixing and semantic lower tail -/

/-- A centered full-table lower bound for the `Gamma` event fixes to one
genuine `(U,Z)` table and yields the same-probability regret tail. -/
theorem lower_sparse_fixed_tail_of_centeredGamma_event
    {n n' k r B T : Nat} (P : Policy n k) (hk : 1 <= k)
    (hkn' : k <= n')
    (eta : Real) (heta0 : 0 <= eta) (heta : eta <= (1 : Real) / 16)
    (q c0 : Nat) (hn' : n' <= n) (hprod : n' = k * r) (hr : 0 < r)
    (sigma : Equiv.Perm (Fin n')) (probability : Real)
    (hGammaProbability : probability <=
      (sparseJointLaw (sparseHiddenTableMeasure B n) (sparseCenteredPolicy P)
        (sparseHiddenTableParameterFamily hk eta heta0 heta n' q c0 B) T).real
          (sparseCenteredGammaEvent hk eta heta0 heta q c0 hn'
            hprod hr sigma (sparseA / 8 * (k : Real) * (T : Real)))) :
    HasRegretLowerTail (hkn'.trans hn') P T
      (sparseA * eta * (T : Real) / 8) probability := by
  let L : ParametricLossProcess (SparseAuxTable B n T) n k :=
    sparseTableLossProcess hk eta heta0 heta n' q c0 T B
  let mu : Measure (SparseAuxTable B n T) := sparseAuxTableMeasure B n T
  have htransfer := sparseAuxGammaEvent_measure_eq_centered
    (B := B) (T := T)
    P hk eta heta0 heta q c0 hn' hprod hr sigma
      (sparseA / 8 * (k : Real) * (T : Real))
  have hGammaAux : probability <=
      (sparseAuxParametricJointMeasure P hk eta heta0 heta n' q c0 T B).real
        (sparseAuxGammaEvent hk eta heta0 heta q c0 hn' hprod hr sigma
          (sparseA / 8 * (k : Real) * (T : Real))) := by
    simpa [measureReal_def, htransfer] using hGammaProbability
  have haverage : probability <=
      ((parametricRunWithParameterKernel P L T) ∘ₘ mu).real
        (parametricRegretEvent L T (sparseA * eta * (T : Real) / 8)) := by
    change probability <=
      (sparseAuxParametricJointMeasure P hk eta heta0 heta n' q c0 T B).real
        (parametricRegretEvent L T (sparseA * eta * (T : Real) / 8))
    exact hGammaAux.trans <|
      sparseAuxGammaEvent_measure_le_regretEvent
        P hk hkn' eta heta0 heta q c0 hn' hprod hr sigma
  obtain ⟨table, htable⟩ := exists_fixed_parametric_regret
    (hkn'.trans hn') mu P L T (sparseA * eta * (T : Real) / 8)
      probability haverage
  refine ⟨L.at table, ?_⟩
  unfold regretTailProbability
  apply (ENNReal.ofReal_le_iff_le_toReal (measure_ne_top _ _)).2
  simpa [measureReal_def] using htable

#print axioms sparseAuxGammaEvent_measure_eq_centered
#print axioms sparseAuxGammaEvent_measure_le_regretEvent
#print axioms lower_sparse_fixed_tail_of_centeredGamma_event

end

end MsetsLower.Lower.Sparse
