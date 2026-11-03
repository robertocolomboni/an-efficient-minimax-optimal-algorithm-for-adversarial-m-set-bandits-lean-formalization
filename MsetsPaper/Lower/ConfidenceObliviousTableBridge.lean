import MsetsPaper.Lower.ConfidenceObliviousProcess
import MsetsPaper.Lower.DenseCommonNoiseTableBridge

/-! # Operational equality: pre-sampled noise tables and fresh feedback laws -/

namespace MsetsPaper.Lower.ConfidenceOblivious

open MsetsLower MsetsLower.Feedback MsetsLower.Lower MsetsLower.Lower.Confidence
open MeasureTheory ProbabilityTheory Set
open scoped ENNReal ProbabilityTheory

noncomputable section

def referenceMixture {d m : ℕ} (P : Policy d m) (hm : 1 ≤ m) (hmd : m ≤ d) (T : ℕ) :
    Measure (History d m T) :=
  parametricRunKernel P (referenceTableLossProcess hm hmd T) T ∘ₘ DenseCommonNoise.noiseTableMeasure T

def plantedMixture {d m : ℕ} (P : Policy d m) (hm : 1 ≤ m) (hmd : m ≤ d)
    (Delta : ℝ) (hDelta : 0 ≤ Delta) (hsmall : (m : ℝ) * Delta ≤ 1 / 2 ^ 13)
    (i : Fin d) (T : ℕ) : Measure (History d m T) :=
  parametricRunKernel P (plantedTableLossProcess hm hmd Delta hDelta hsmall i T) T ∘ₘ
    DenseCommonNoise.noiseTableMeasure T

theorem tableNoise_snoc_prefix {T t : ℕ} (Z : Table T) (z : Noise) (ht : t < T) :
    tableNoise (DenseCommonNoise.noiseSnoc Z z) t = tableNoise Z t := by
  simp only [tableNoise, dif_pos ht, dif_pos (show t < T + 1 by omega)]
  exact congrArg Subtype.val (DenseCommonNoise.noiseSnoc_castSucc Z z ⟨t, ht⟩)

theorem tableNoise_snoc_last {T : ℕ} (Z : Table T) (z : Noise) :
    tableNoise (DenseCommonNoise.noiseSnoc Z z) T = z.val := by
  simp only [tableNoise, dif_pos (show T < T + 1 by omega)]
  exact congrArg Subtype.val (DenseCommonNoise.noiseSnoc_last Z z)

def sourceObservation {d m : ℕ} (hmd : m ≤ d) (eta : ℝ) (U : Fin d → ℝ)
    (az : MSetAction d m × Noise) : MSetAction d m × ℝ :=
  (az.1, confidenceScalarFeedback hmd az.1
    (feedbackMap (DenseCommonNoise.feedbackParameter eta U az.1) az.2.val))

theorem measurable_sourceObservation {d m : ℕ} (hmd : m ≤ d) (eta : ℝ) (U : Fin d → ℝ) :
    Measurable (sourceObservation hmd eta U) := by
  apply measurable_fst.prodMk
  apply measurable_from_prod_countable_right
  intro a
  unfold confidenceScalarFeedback feedbackMap shape
  fun_prop

theorem sourceObservation_law {d m : ℕ} (P : Policy d m) (hm : 1 ≤ m) (hmd : m ≤ d)
    {eta : ℝ} (heta : 0 ≤ eta) (hs : eta ≤ 1 / 16)
    (U : Fin d → ℝ) (hU : ∀ i, |U i| ≤ 1) (t : ℕ) (h : History d m t) :
    ((P.kernel t h).prod DenseCommonNoise.noiseMeasure).map (sourceObservation hmd eta U) =
      freshRoundKernel P hmd eta U t h := by
  letI := DenseCommonNoise.latentFeedbackKernel_isMarkov hm heta hs U hU t
  letI : IsMarkovKernel (DenseCommonNoise.latentRoundKernel P eta U t) := by
    unfold DenseCommonNoise.latentRoundKernel; infer_instance
  ext s hset
  rw [Measure.map_apply (measurable_sourceObservation hmd eta U) hset,
    Measure.prod_apply ((measurable_sourceObservation hmd eta U) hset),
    freshRoundKernel,
    Kernel.map_apply' _ (confidenceFeedbackEquiv hmd).measurable h hset,
    DenseCommonNoise.latentRoundKernel,
    Kernel.compProd_apply ((confidenceFeedbackEquiv hmd).measurable hset)]
  apply lintegral_congr
  intro a
  have hu := (DenseCommonNoise.abs_feedbackParameter_le hm heta U hU a).trans hs
  have hg : Measurable (confidenceScalarFeedback hmd a) := measurable_const.add (measurable_id.div_const 4)
  have hf : Measurable (fun z : Noise => confidenceScalarFeedback hmd a
      (feedbackMap (DenseCommonNoise.feedbackParameter eta U a) z.val)) :=
    hg.comp ((continuous_feedbackMap _).measurable.comp measurable_subtype_coe)
  have hmap : DenseCommonNoise.noiseMeasure.map
      (fun z : Noise => confidenceScalarFeedback hmd a
        (feedbackMap (DenseCommonNoise.feedbackParameter eta U a) z.val)) =
      (feedbackDensityMeasure (DenseCommonNoise.feedbackParameter eta U a)).map
        (confidenceScalarFeedback hmd a) := by
    rw [← feedbackPushforwardMeasure_eq_densityMeasure hu, feedbackPushforwardMeasure,
      Measure.map_map hg (continuous_feedbackMap _).measurable,
      ← DenseCommonNoise.map_noiseMeasure,
      Measure.map_map (hg.comp (continuous_feedbackMap _).measurable) measurable_subtype_coe]
    rfl
  have heq := congrArg (fun μ : Measure ℝ => μ (Prod.mk a ⁻¹' s)) hmap
  rw [Measure.map_apply hf (measurable_prodMk_left hset),
    Measure.map_apply hg (measurable_prodMk_left hset)] at heq
  exact heq

/-- Generic finite-product induction. Its hypotheses are local operational
identities (prefix agreement and one fresh observation), not an assumed
history-law equivalence or lower-bound conclusion. -/
theorem tableMixture_eq_fresh_of_local {d m : ℕ} (P : Policy d m)
    (L : (T : ℕ) → ParametricLossProcess (Table T) d m) (K : HistoryKernelProcess d m)
    (hprefix : ∀ T (Z : Table T) (z : Noise),
      runLaw P ((L (T + 1)).at (DenseCommonNoise.noiseSnoc Z z)) T = runLaw P ((L T).at Z) T)
    (hstep : ∀ T (Z : Table T) (h : History d m T) (s : Set (MSetAction d m × ℝ)),
      MeasurableSet s →
      (∫⁻ z, observationKernel P ((L (T + 1)).at (DenseCommonNoise.noiseSnoc Z z)) T h s
        ∂DenseCommonNoise.noiseMeasure) = K.kernel T h s) :
    ∀ T, parametricRunKernel P (L T) T ∘ₘ DenseCommonNoise.noiseTableMeasure T = K.law T := by
  have hswap (T : ℕ) (Z : Table T) (μ : Measure (History d m T)) [SFinite μ]
      (s : Set (History d m (T + 1))) (hset : MeasurableSet s) :
      (∫⁻ z, ∫⁻ h, observationKernel P ((L (T + 1)).at (DenseCommonNoise.noiseSnoc Z z))
        T h (Prod.mk h ⁻¹' s) ∂μ ∂DenseCommonNoise.noiseMeasure) =
      ∫⁻ h, ∫⁻ z, observationKernel P ((L (T + 1)).at (DenseCommonNoise.noiseSnoc Z z))
        T h (Prod.mk h ⁻¹' s) ∂DenseCommonNoise.noiseMeasure ∂μ := by
    let f : Noise × History d m T → ℝ≥0∞ := fun x =>
      observationKernel P ((L (T + 1)).at (DenseCommonNoise.noiseSnoc Z x.1)) T x.2 (Prod.mk x.2 ⁻¹' s)
    have hfeq : f = fun x => parametricRoundKernel P (L (T + 1)) T
        (DenseCommonNoise.noiseSnoc Z x.1, x.2) s := by
      funext x
      rw [parametricRoundKernel_apply, roundKernel_apply P _ T x.2 hset]
      exact observationKernel_apply P _ T x.2 (measurable_prodMk_left hset)
    have hinput : Measurable (fun x : Noise × History d m T =>
        (DenseCommonNoise.noiseSnoc Z x.1, x.2)) :=
      ((DenseCommonNoise.measurable_noiseSnoc T).comp
        (measurable_const.prodMk measurable_fst)).prodMk measurable_snd
    have hf : Measurable f := by
      rw [hfeq]
      exact (Kernel.measurable_coe (parametricRoundKernel P (L (T + 1)) T) hset).comp hinput
    calc
      _ = ∫⁻ x, f x ∂DenseCommonNoise.noiseMeasure.prod μ := (lintegral_prod _ hf.aemeasurable).symm
      _ = _ := lintegral_prod_symm' f hf
  have happly (T : ℕ) (Z : Table T) (s : Set (History d m T)) :
      parametricRunKernel P (L T) T Z s = runLaw P ((L T).at Z) T s :=
    congrArg (fun μ : Measure (History d m T) => μ s)
      (parametricRunKernel_apply P (L T) Z T)
  intro T
  induction T with
  | zero =>
      ext s hset
      rw [Measure.bind_apply hset (Kernel.aemeasurable _)]
      simp_rw [happly 0]
      simp [runLaw, HistoryKernelProcess.law]
  | succ T ih =>
      ext s hset
      rw [Measure.bind_apply hset (Kernel.aemeasurable _),
        DenseCommonNoise.lintegral_noiseTable_snoc (Kernel.measurable_coe _ hset)]
      simp_rw [happly (T + 1)]
      have hsucc (Z : Table T) (z : Noise) :
          runLaw P ((L (T + 1)).at (DenseCommonNoise.noiseSnoc Z z)) (T + 1) s =
            ∫⁻ h, observationKernel P ((L (T + 1)).at (DenseCommonNoise.noiseSnoc Z z)) T h
              (Prod.mk h ⁻¹' s) ∂runLaw P ((L T).at Z) T := by
        rw [runLaw_succ_eq_compProd, hprefix]
        exact Measure.compProd_apply hset
      simp_rw [hsucc, hswap T _ _ s hset]
      have hobs (Z : Table T) (h : History d m T) :=
        hstep T Z h (Prod.mk h ⁻¹' s) (measurable_prodMk_left hset)
      simp_rw [hobs]
      have hq : Measurable (fun h : History d m T => K.kernel T h (Prod.mk h ⁻¹' s)) :=
        Kernel.measurable_kernel_prodMk_left (κ := K.kernel T) hset
      simp_rw [← parametricRunKernel_apply P (L T)]
      rw [← Measure.lintegral_bind (Kernel.aemeasurable _) hq.aemeasurable, ih,
        HistoryKernelProcess.law_succ]
      exact (Measure.compProd_apply hset).symm

theorem average_observationKernel_eq_fresh {d m T : ℕ}
    (P : Policy d m) (hm : 1 ≤ m) (hmd : m ≤ d)
    (L : ParametricLossProcess (Table (T + 1)) d m)
    {eta : ℝ} (heta : 0 ≤ eta) (hs : eta ≤ 1 / 16)
    (U : Fin d → ℝ) (hU : ∀ i, |U i| ≤ 1) (Z : Table T) (h : History d m T)
    (hfeedback : ∀ (z : Noise) (a : MSetAction d m),
      actionLoss a ((L.at (DenseCommonNoise.noiseSnoc Z z)).itemLoss T h) =
        (sourceObservation hmd eta U (a, z)).2)
    (s : Set (MSetAction d m × ℝ)) (hset : MeasurableSet s) :
    (∫⁻ z, observationKernel P (L.at (DenseCommonNoise.noiseSnoc Z z)) T h s
      ∂DenseCommonNoise.noiseMeasure) = freshRoundKernel P hmd eta U T h s := by
  let g := sourceObservation hmd eta U
  have hg := measurable_sourceObservation hmd eta U
  have hmap (z : Noise) : observationKernel P (L.at (DenseCommonNoise.noiseSnoc Z z)) T h s =
      (P.kernel T h) {a | g (a, z) ∈ s} := by
    rw [observationKernel_apply _ _ _ _ hset]
    congr 1
    ext a
    change (a, actionLoss a ((L.at (DenseCommonNoise.noiseSnoc Z z)).itemLoss T h)) ∈ s ↔ _
    rw [hfeedback]
    rfl
  simp_rw [hmap]
  calc
    _ = ((P.kernel T h).prod DenseCommonNoise.noiseMeasure) (g ⁻¹' s) :=
      (Measure.prod_apply_symm (hg hset)).symm
    _ = (((P.kernel T h).prod DenseCommonNoise.noiseMeasure).map g) s :=
      (Measure.map_apply hg hset).symm
    _ = _ := congrArg (fun μ : Measure (MSetAction d m × ℝ) => μ s)
      (sourceObservation_law P hm hmd heta hs U hU T h)

theorem referenceMixture_eq_process {d m : ℕ} (P : Policy d m) (hm : 1 ≤ m) (hmd : m ≤ d)
    (Delta : ℝ) (hDelta : 0 ≤ Delta) (hsmall : (m : ℝ) * Delta ≤ 1 / 2 ^ 13) (T : ℕ) :
    referenceMixture P hm hmd T = (referenceProcess P hm hmd Delta hDelta hsmall).law T := by
  apply tableMixture_eq_fresh_of_local P (referenceTableLossProcess hm hmd)
    (referenceProcess P hm hmd Delta hDelta hsmall)
  · intro t Z z
    apply DenseCommonNoise.runLaw_eq_of_prefix
    intro r hr h
    change referenceItemLoss hmd (tableNoise (DenseCommonNoise.noiseSnoc Z z) r) =
      referenceItemLoss hmd (tableNoise Z r)
    rw [tableNoise_snoc_prefix Z z hr]
  · intro t Z h s hset
    apply average_observationKernel_eq_fresh P hm hmd _
      (feedback_scale_admissible hDelta hsmall).1 (feedback_scale_admissible hDelta hsmall).2
      (fun _ => 0) (by intro j; norm_num) Z h _ s hset
    intro z a
    change actionLoss a (referenceItemLoss hmd (tableNoise (DenseCommonNoise.noiseSnoc Z z) t)) = _
    rw [tableNoise_snoc_last]
    exact reference_feedback_identity hm hmd (4 * m * Delta) z.val a

theorem plantedMixture_eq_process {d m : ℕ} (P : Policy d m) (hm : 1 ≤ m) (hmd : m ≤ d)
    (Delta : ℝ) (hDelta : 0 ≤ Delta) (hsmall : (m : ℝ) * Delta ≤ 1 / 2 ^ 13) (i : Fin d) (T : ℕ) :
    plantedMixture P hm hmd Delta hDelta hsmall i T =
      (plantedProcess P hm hmd Delta hDelta hsmall i).law T := by
  apply tableMixture_eq_fresh_of_local P (plantedTableLossProcess hm hmd Delta hDelta hsmall i)
    (plantedProcess P hm hmd Delta hDelta hsmall i)
  · intro t Z z
    apply DenseCommonNoise.runLaw_eq_of_prefix
    intro r hr h
    change plantedItemLoss hmd (tableNoise (DenseCommonNoise.noiseSnoc Z z) r) Delta 1 i =
      plantedItemLoss hmd (tableNoise Z r) Delta 1 i
    rw [tableNoise_snoc_prefix Z z hr]
  · intro t Z h s hset
    apply average_observationKernel_eq_fresh P hm hmd _
      (feedback_scale_admissible hDelta hsmall).1 (feedback_scale_admissible hDelta hsmall).2
      (oneHot i) (abs_oneHot_le i) Z h _ s hset
    intro z a
    change actionLoss a (plantedItemLoss hmd
      (tableNoise (DenseCommonNoise.noiseSnoc Z z) t) Delta 1 i) = _
    rw [tableNoise_snoc_last]
    exact planted_feedback_identity hm hmd Delta z.val i a

end

end MsetsPaper.Lower.ConfidenceOblivious
