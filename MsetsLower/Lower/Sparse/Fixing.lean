import MsetsLower.Information.SequentialKL
import MsetsLower.Lower.Sparse.Table

/-!
# Exact finite-table realization of the sparse experiment

The likelihood argument uses centered feedback `F_u(Z)`, while the protocol
records the action loss `1/2 + F_u(Z)`.  Here a finite iid source table is
integrated out one coordinate at a time.  The resulting law is exactly the
actual-feedback adaptive process, so the final probabilistic construction can
be fixed to one deterministic non-anticipating loss table.
-/

set_option linter.style.header false

namespace MsetsLower.Lower.Sparse

open MsetsLower Feedback MeasureTheory ProbabilityTheory Set
open scoped ENNReal ProbabilityTheory

noncomputable section

/-! ## One fresh source coordinate -/

theorem sourceUniformMeasure_map_feedbackMap_sparseClamp
    {u : Real} (hu : |u| ≤ (1 : Real) / 16) :
    sourceUniformMeasure.map
        (fun z => feedbackMap u (sparseClampUnit z)) =
      feedbackDensityMeasure u := by
  calc
    sourceUniformMeasure.map
        (fun z => feedbackMap u (sparseClampUnit z)) =
        (sourceUniformMeasure.map sparseClampUnit).map (feedbackMap u) := by
      simpa [Function.comp_def] using
        (Measure.map_map (continuous_feedbackMap u).measurable
          measurable_sparseClampUnit).symm
    _ = sourceUniformMeasure.map (feedbackMap u) := by
      rw [sourceUniformMeasure_map_sparseClampUnit]
    _ = feedbackDensityMeasure u :=
      feedbackPushforwardMeasure_eq_densityMeasure hu

private theorem map_compProd_snd_of_map_apply
    {alpha beta gamma : Type*}
    [MeasurableSpace alpha] [MeasurableSpace beta] [MeasurableSpace gamma]
    (mu : Measure alpha) (kappa : Kernel alpha beta)
    (eta : Kernel alpha gamma)
    [SFinite mu] [IsSFiniteKernel kappa] [IsSFiniteKernel eta]
    (g : alpha → beta → gamma)
    (hg : Measurable (fun input : alpha × beta => g input.1 input.2))
    (hmap : ∀ a, (kappa a).map (g a) = eta a) :
    (mu ⊗ₘ kappa).map (fun input => (input.1, g input.1 input.2)) =
      mu ⊗ₘ eta := by
  ext s hs
  have hpair : Measurable
      (fun input : alpha × beta => (input.1, g input.1 input.2)) :=
    measurable_fst.prodMk hg
  rw [Measure.map_apply hpair hs,
    Measure.compProd_apply (hs.preimage hpair),
    Measure.compProd_apply hs]
  apply lintegral_congr
  intro a
  have happly := congrArg
    (fun rho : Measure gamma => rho (Prod.mk a ⁻¹' s)) (hmap a)
  have hga : Measurable (g a) := by
    simpa [Function.uncurry, Function.comp_def] using
      hg.comp (measurable_const.prodMk measurable_id)
  rw [Measure.map_apply hga (measurable_prodMk_left hs)] at happly
  simpa only [Set.preimage, Set.mem_setOf_eq] using happly

private theorem sparse_centered_source_mixture
    {n k : Nat} (P : Policy n k) (V : SparseAdaptiveParameters n k)
    (t : Nat) (h : History n k t) :
    ((P.kernel t h) ⊗ₘ
        Kernel.const (MSetAction n k) sourceUniformMeasure).map
        (fun input =>
          (input.1,
            feedbackMap (V.value t h input.1)
              (sparseClampUnit input.2))) =
      sparseAdaptiveRoundKernel P V t h := by
  let u : History n k t × MSetAction n k → Real :=
    fun ha => V.value t ha.1 ha.2
  let eta : Kernel (MSetAction n k) Real :=
    (sparseParamFeedbackKernel u).comap
      (fun A => (h, A)) measurable_prodMk_left
  letI : IsProbabilityMeasure sourceUniformMeasure := inferInstance
  letI : IsMarkovKernel
      (Kernel.const (MSetAction n k) sourceUniformMeasure) := by
    infer_instance
  letI : IsMarkovKernel (sparseParamFeedbackKernel u) :=
    sparseParamFeedbackKernel_isMarkov u (V.measurable_value t)
      (fun ha => V.abs_le t ha.1 ha.2)
  letI : IsMarkovKernel eta := by
    dsimp [eta]
    infer_instance
  have hg : Measurable (fun input : MSetAction n k × Real =>
      feedbackMap (V.value t h input.1) (sparseClampUnit input.2)) := by
    have hu : Measurable (fun input : MSetAction n k × Real =>
        V.value t h input.1) :=
      (V.measurable_value t).comp
        (measurable_const.prodMk measurable_fst)
    have hz : Measurable (fun input : MSetAction n k × Real =>
        sparseClampUnit input.2) :=
      measurable_sparseClampUnit.comp measurable_snd
    unfold feedbackMap shape
    exact (hz.div_const 2).add
      (hu.mul (measurable_const.sub (hz.pow_const 2)))
  have hmap : ∀ A : MSetAction n k,
      sourceUniformMeasure.map
          (fun z => feedbackMap (V.value t h A) (sparseClampUnit z)) =
        eta A := by
    intro A
    dsimp [eta]
    rw [sparseParamFeedbackKernel_apply u (V.measurable_value t)
      (h, A) (V.abs_le t h A)]
    exact sourceUniformMeasure_map_feedbackMap_sparseClamp
      (V.abs_le t h A)
  have hsource := map_compProd_snd_of_map_apply
    (P.kernel t h)
    (Kernel.const (MSetAction n k) sourceUniformMeasure) eta
    (fun A z => feedbackMap (V.value t h A) (sparseClampUnit z))
    hg hmap
  rw [hsource]
  ext s hs
  rw [Measure.compProd_apply hs]
  rw [sparseAdaptiveRoundKernel, Kernel.compProd_apply hs]
  rfl

def sparseSourceObservation
    {n k : Nat} (eta : Real) (n' q c0 : Nat)
    (U : Nat → Fin n → Real) (t : Nat) (h : History n k t) :
    MSetAction n k × Real → MSetAction n k × Real :=
  fun input =>
    (input.1, (1 : Real) / 2 +
      feedbackMap
        (sparseFeedbackParameter eta n' q c0 U t h input.1)
        (sparseClampUnit input.2))

theorem measurable_sparseSourceObservation
    {n k : Nat} (eta : Real) (n' q c0 : Nat)
    (U : Nat → Fin n → Real) (t : Nat) (h : History n k t) :
    Measurable (sparseSourceObservation eta n' q c0 U t h) := by
  refine measurable_fst.prodMk ?_
  have hu : Measurable (fun input : MSetAction n k × Real =>
      sparseFeedbackParameter eta n' q c0 U t h input.1) :=
    (measurable_of_finite
      (fun A : MSetAction n k =>
        sparseFeedbackParameter eta n' q c0 U t h A)).comp measurable_fst
  have hz : Measurable (fun input : MSetAction n k × Real =>
      sparseClampUnit input.2) :=
    measurable_sparseClampUnit.comp measurable_snd
  unfold feedbackMap shape
  exact measurable_const.add <|
    (hz.div_const 2).add
      (hu.mul (measurable_const.sub (hz.pow_const 2)))

/-- Sampling a fresh clipped source coordinate and recording the actual
action loss realizes exactly the affine transport of the centered density
experiment. -/
theorem sparse_source_actual_mixture
    {n k : Nat} (P : Policy n k) (hk : 1 ≤ k)
    (eta : Real) (heta0 : 0 ≤ eta) (heta : eta ≤ (1 : Real) / 16)
    (n' q c0 : Nat) (U : Nat → Fin n → Real)
    (hU : ∀ b i, |U b i| ≤ 1) (t : Nat) (h : History n k t) :
    ((P.kernel t h) ⊗ₘ
        Kernel.const (MSetAction n k) sourceUniformMeasure).map
        (sparseSourceObservation eta n' q c0 U t h) =
      sparseActualAdaptiveRoundKernel P
        (sparseAdaptiveParametersOfTable hk eta heta0 heta n' q c0 U hU)
        t h := by
  let V := sparseAdaptiveParametersOfTable hk eta heta0 heta n' q c0 U hU
  let h0 : History n k t := (sparseActualHistoryEquiv n k t).symm h
  have hp : (sparseCenteredPolicy P).kernel t h0 = P.kernel t h := by
    rw [sparseCenteredPolicy_kernel]
    simp [h0]
  have hu (A : MSetAction n k) :
      V.value t h0 A = V.value t h A := by
    change sparseFeedbackParameter eta n' q c0 U t h0 A =
      sparseFeedbackParameter eta n' q c0 U t h A
    simpa [h0] using
      (sparseFeedbackParameter_actualHistory eta U h0 A).symm
  have hcenter := sparse_centered_source_mixture
    (sparseCenteredPolicy P) V t h0
  rw [hp] at hcenter
  have hcenter' :
      ((P.kernel t h) ⊗ₘ
          Kernel.const (MSetAction n k) sourceUniformMeasure).map
          (fun input =>
            (input.1,
              feedbackMap (V.value t h input.1)
                (sparseClampUnit input.2))) =
        sparseAdaptiveRoundKernel (sparseCenteredPolicy P) V t h0 := by
    rw [show (fun input : MSetAction n k × Real =>
        (input.1,
          feedbackMap (V.value t h input.1) (sparseClampUnit input.2))) =
        (fun input =>
          (input.1,
            feedbackMap (V.value t h0 input.1)
              (sparseClampUnit input.2))) by
      funext input
      apply Prod.ext
      · rfl
      · rw [hu]]
    exact hcenter
  let g : MSetAction n k × Real → MSetAction n k × Real :=
    fun input =>
      (input.1,
        feedbackMap (V.value t h input.1) (sparseClampUnit input.2))
  have hg : Measurable g := by
    refine measurable_fst.prodMk ?_
    have hu' : Measurable (fun input : MSetAction n k × Real =>
        V.value t h input.1) :=
      (measurable_of_finite
        (fun A : MSetAction n k => V.value t h A)).comp measurable_fst
    have hz : Measurable (fun input : MSetAction n k × Real =>
        sparseClampUnit input.2) :=
      measurable_sparseClampUnit.comp measurable_snd
    unfold feedbackMap shape
    exact (hz.div_const 2).add
      (hu'.mul (measurable_const.sub (hz.pow_const 2)))
  have hmapmap :
      (((P.kernel t h) ⊗ₘ
          Kernel.const (MSetAction n k) sourceUniformMeasure).map g).map
          (sparseObservationShiftEquiv n k) =
        ((P.kernel t h) ⊗ₘ
          Kernel.const (MSetAction n k) sourceUniformMeasure).map
          (sparseSourceObservation eta n' q c0 U t h) := by
    have hmm := Measure.map_map
      (μ := (P.kernel t h) ⊗ₘ
        Kernel.const (MSetAction n k) sourceUniformMeasure)
      (sparseObservationShiftEquiv n k).measurable hg
    rw [hmm]
    congr 1
  calc
    ((P.kernel t h) ⊗ₘ
        Kernel.const (MSetAction n k) sourceUniformMeasure).map
        (sparseSourceObservation eta n' q c0 U t h) =
        (((P.kernel t h) ⊗ₘ
          Kernel.const (MSetAction n k) sourceUniformMeasure).map g).map
          (sparseObservationShiftEquiv n k) := hmapmap.symm
    _ = (sparseAdaptiveRoundKernel (sparseCenteredPolicy P) V t h0).map
          (sparseObservationShiftEquiv n k) := by rw [hcenter']
    _ = sparseActualAdaptiveRoundKernel P V t h := by
      have hactual :=
        sparseActualAdaptiveRoundKernel_at_actualHistory P V t h0
      simpa [h0] using hactual.symm

/-! ## Recursive integration of the finite noise table -/

private theorem roundKernel_eq_of_itemLoss_eq
    {n k t : Nat} (P : Policy n k) (L K : LossProcess n k)
    (hitem : ∀ h : History n k t, L.itemLoss t h = K.itemLoss t h) :
    roundKernel P L t = roundKernel P K t := by
  ext h s hs
  rw [roundKernel_apply P L t h hs, roundKernel_apply P K t h hs]
  congr 1
  ext A
  rw [hitem h]

private theorem runLaw_eq_of_itemLoss_eq_before
    {n k : Nat} (P : Policy n k) (L K : LossProcess n k) :
    ∀ T : Nat,
      (∀ t, t < T → ∀ h : History n k t,
        L.itemLoss t h = K.itemLoss t h) →
      runLaw P L T = runLaw P K T := by
  intro T
  induction T with
  | zero => intro _; rfl
  | succ T ih =>
      intro hitem
      rw [runLaw_succ, runLaw_succ,
        ih (fun t ht h => hitem t (by omega) h),
        roundKernel_eq_of_itemLoss_eq P L K (hitem T (by omega))]

def sparseNoiseSnocLossProcess
    {n k T : Nat} (hk : 1 ≤ k) (eta : Real) (heta0 : 0 ≤ eta)
    (heta : eta ≤ (1 : Real) / 16) (n' q c0 : Nat)
    (U : Nat → Fin n → Real) (hU : ∀ b i, |U b i| ≤ 1) :
    ParametricLossProcess (SparseNoiseTable T × Real) n k :=
  sparseNoiseTableLossProcess hk eta heta0 heta n' q c0 (T + 1) U hU

theorem sparseNoiseTable_runLaw_snoc_prefix
    {n k T : Nat} (P : Policy n k) (hk : 1 ≤ k)
    (eta : Real) (heta0 : 0 ≤ eta) (heta : eta ≤ (1 : Real) / 16)
    (n' q c0 : Nat) (U : Nat → Fin n → Real)
    (hU : ∀ b i, |U b i| ≤ 1)
    (table : SparseNoiseTable T) (z : Real) :
    runLaw P
        ((sparseNoiseSnocLossProcess (T := T) hk eta heta0 heta
          n' q c0 U hU).at (table, z)) T =
      runLaw P
        ((sparseNoiseTableLossProcess hk eta heta0 heta
          n' q c0 T U hU).at table) T := by
  apply runLaw_eq_of_itemLoss_eq_before
  intro t ht h
  funext i
  have ht' : t < T + 1 := by omega
  simp only [sparseNoiseSnocLossProcess,
    sparseNoiseTableLossProcess, ParametricLossProcess.at,
    sparseItemLoss, ht, ht', if_true]
  rw [sparseNoiseTableAt_snoc_prefix table z ht]

private theorem lintegral_map_eq_prod_map_apply
    {alpha beta gamma : Type*}
    [MeasurableSpace alpha] [MeasurableSpace beta] [MeasurableSpace gamma]
    (mu : Measure alpha) (nu : Measure beta) [SFinite mu] [SFinite nu]
    (g : beta × alpha → gamma) (hg : Measurable g)
    (s : Set gamma) (hs : MeasurableSet s) :
    (∫⁻ x, (nu.map (fun y => g (y, x))) s ∂mu) =
      ((nu.prod mu).map g) s := by
  rw [Measure.map_apply hg hs,
    Measure.prod_apply_symm (hs.preimage hg)]
  apply lintegral_congr
  intro x
  calc
    (nu.map (fun y => g (y, x))) s =
        nu ((fun y => g (y, x)) ⁻¹' s) :=
      Measure.map_apply
        (hg.comp (measurable_id.prodMk measurable_const)) hs
    _ = nu ((fun x_1 => (x_1, x)) ⁻¹' g ⁻¹' s) := rfl

set_option maxHeartbeats 1000000 in
-- Dependent-history elaboration through the parametric observation kernel is expensive.
theorem lintegral_sparseNoiseTable_observationKernel
    {n k T : Nat} (P : Policy n k) (hk : 1 ≤ k)
    (eta : Real) (heta0 : 0 ≤ eta) (heta : eta ≤ (1 : Real) / 16)
    (n' q c0 : Nat) (U : Nat → Fin n → Real)
    (hU : ∀ b i, |U b i| ≤ 1)
    (table : SparseNoiseTable T) (h : History n k T)
    (s : Set (MSetAction n k × Real)) (hs : MeasurableSet s) :
    (∫⁻ z, observationKernel P
        ((sparseNoiseSnocLossProcess (T := T) hk eta heta0 heta
          n' q c0 U hU).at (table, z)) T h s
        ∂sourceUniformMeasure) =
      sparseActualAdaptiveRoundKernel P
        (sparseAdaptiveParametersOfTable hk eta heta0 heta n' q c0 U hU)
        T h s := by
  let g := sparseSourceObservation eta n' q c0 U T h
  have hg : Measurable g :=
    measurable_sparseSourceObservation eta n' q c0 U T h
  calc
    _ = ∫⁻ z, ((P.kernel T h).map (fun A => g (A, z))) s
          ∂sourceUniformMeasure := by
      apply lintegral_congr
      intro z
      rw [observationKernel_apply P
        ((sparseNoiseSnocLossProcess (T := T) hk eta heta0 heta
          n' q c0 U hU).at (table, z)) T h hs]
      calc
        _ = (P.kernel T h) ((fun A => g (A, z)) ⁻¹' s) := by
          congr 1
          ext A
          change
            (A, actionLoss A
              (sparseItemLoss eta n' q c0 (T + 1) U
                (sparseNoiseTableAt (T := T + 1) (table, z)) T h)) ∈ s ↔
              g (A, z) ∈ s
          have hloss := lower_sparse_action_loss hk eta n' q c0 (T + 1)
            U (sparseNoiseTableAt (T := T + 1) (table, z)) (by omega) h A
          rw [sparseNoiseTableAt_snoc_last] at hloss
          have hpair :
              (A, actionLoss A
                (sparseItemLoss eta n' q c0 (T + 1) U
                  (sparseNoiseTableAt (T := T + 1) (table, z)) T h)) =
                g (A, z) := by
            apply Prod.ext
            · rfl
            · exact hloss
          rw [hpair]
        _ = ((P.kernel T h).map (fun A => g (A, z))) s :=
          (Measure.map_apply
            (hg.comp (measurable_id.prodMk measurable_const)) hs).symm
    _ = (((P.kernel T h).prod sourceUniformMeasure).map g) s :=
      lintegral_map_eq_prod_map_apply sourceUniformMeasure
        (P.kernel T h) g hg s hs
    _ = ((((P.kernel T h) ⊗ₘ
          Kernel.const (MSetAction n k) sourceUniformMeasure).map g)) s := by
      rw [Measure.compProd_const]
    _ = sparseActualAdaptiveRoundKernel P
        (sparseAdaptiveParametersOfTable hk eta heta0 heta n' q c0 U hU)
        T h s := by
      exact congrArg (fun mu : Measure (MSetAction n k × Real) => mu s)
        (sparse_source_actual_mixture P hk eta heta0 heta n' q c0 U hU T h)

private theorem lintegral_swap_parametric_observation
    {Xi : Type*} [MeasurableSpace Xi]
    {n k t : Nat} (P : Policy n k)
    (L : ParametricLossProcess (Xi × Real) n k) (xi : Xi)
    (mu : Measure (History n k t)) [SFinite mu]
    (s : Set (History n k (t + 1))) (hs : MeasurableSet s) :
    (∫⁻ z, ∫⁻ h, observationKernel P (L.at (xi, z)) t h
          (Prod.mk h ⁻¹' s) ∂mu ∂sourceUniformMeasure) =
      ∫⁻ h, ∫⁻ z, observationKernel P (L.at (xi, z)) t h
          (Prod.mk h ⁻¹' s) ∂sourceUniformMeasure ∂mu := by
  let f : Real × History n k t → ENNReal :=
    fun input => observationKernel P (L.at (xi, input.1)) t input.2
      (Prod.mk input.2 ⁻¹' s)
  have hround : f = fun input =>
      parametricRoundKernel P L t ((xi, input.1), input.2) s := by
    funext input
    change observationKernel P (L.at (xi, input.1)) t input.2
        (Prod.mk input.2 ⁻¹' s) =
      parametricRoundKernel P L t ((xi, input.1), input.2) s
    rw [parametricRoundKernel_apply]
    rw [roundKernel_apply P (L.at (xi, input.1)) t input.2 hs,
      observationKernel_apply P (L.at (xi, input.1)) t input.2
        (measurable_prodMk_left hs)]
    congr 1
  have hinput : Measurable (fun input : Real × History n k t =>
      ((xi, input.1), input.2)) :=
    (measurable_const.prodMk measurable_fst).prodMk measurable_snd
  have hf : Measurable f := by
    rw [hround]
    exact (Kernel.measurable_coe (parametricRoundKernel P L t) hs).comp hinput
  calc
    _ = ∫⁻ input, f input ∂(sourceUniformMeasure.prod mu) := by
      rw [MeasureTheory.lintegral_prod _ hf.aemeasurable]
    _ = _ := MeasureTheory.lintegral_prod_symm' f hf

theorem sparseNoiseTable_runLaw_snoc_succ_apply
    {n k T : Nat} (P : Policy n k) (hk : 1 ≤ k)
    (eta : Real) (heta0 : 0 ≤ eta) (heta : eta ≤ (1 : Real) / 16)
    (n' q c0 : Nat) (U : Nat → Fin n → Real)
    (hU : ∀ b i, |U b i| ≤ 1)
    (table : SparseNoiseTable T) (z : Real)
    (s : Set (History n k (T + 1))) (hs : MeasurableSet s) :
    runLaw P
        ((sparseNoiseSnocLossProcess (T := T) hk eta heta0 heta
          n' q c0 U hU).at (table, z)) (T + 1) s =
      ∫⁻ h, observationKernel P
          ((sparseNoiseSnocLossProcess (T := T) hk eta heta0 heta
            n' q c0 U hU).at (table, z)) T h (Prod.mk h ⁻¹' s)
        ∂runLaw P
          ((sparseNoiseTableLossProcess hk eta heta0 heta
            n' q c0 T U hU).at table) T := by
  rw [runLaw_succ_eq_compProd]
  change (runLaw P
      ((sparseNoiseSnocLossProcess (T := T) hk eta heta0 heta
        n' q c0 U hU).at (table, z)) T ⊗ₘ
      observationKernel P
        ((sparseNoiseSnocLossProcess (T := T) hk eta heta0 heta
          n' q c0 U hU).at (table, z)) T) s = _
  rw [sparseNoiseTable_runLaw_snoc_prefix
    P hk eta heta0 heta n' q c0 U hU table z]
  rw [Measure.compProd_apply hs]

def sparseNoiseTableMixture
    {n k : Nat} (P : Policy n k) (hk : 1 ≤ k)
    (eta : Real) (heta0 : 0 ≤ eta) (heta : eta ≤ (1 : Real) / 16)
    (n' q c0 : Nat) (U : Nat → Fin n → Real)
    (hU : ∀ b i, |U b i| ≤ 1) (T : Nat) :
    Measure (History n k T) :=
  parametricRunKernel P
      (sparseNoiseTableLossProcess hk eta heta0 heta n' q c0 T U hU) T ∘ₘ
    sparseNoiseTableMeasure T

/-- Exact conditional mixture identity: at every finite horizon, integrating
the source-noise table gives the actual observable adaptive law. -/
theorem sparseNoiseTableMixture_eq_actualProcess
    {n k : Nat} (P : Policy n k) (hk : 1 ≤ k)
    (eta : Real) (heta0 : 0 ≤ eta) (heta : eta ≤ (1 : Real) / 16)
    (n' q c0 : Nat) (U : Nat → Fin n → Real)
    (hU : ∀ b i, |U b i| ≤ 1) :
    ∀ T : Nat,
      sparseNoiseTableMixture P hk eta heta0 heta n' q c0 U hU T =
        (sparseActualAdaptiveProcess P
          (sparseAdaptiveParametersOfTable hk eta heta0 heta
            n' q c0 U hU)).law T := by
  intro T
  induction T with
  | zero =>
      unfold sparseNoiseTableMixture
      rw [sparseNoiseTableMeasure,
        Measure.dirac_bind (Kernel.measurable _)]
      rw [parametricRunKernel_apply]
  | succ T ih =>
      let V := sparseAdaptiveParametersOfTable hk eta heta0 heta
        n' q c0 U hU
      letI : IsMarkovKernel (sparseActualAdaptiveRoundKernel P V T) :=
        sparseActualAdaptiveRoundKernel.instIsMarkovKernel P V T
      ext s hs
      unfold sparseNoiseTableMixture
      rw [Measure.bind_apply hs (Kernel.aemeasurable _)]
      rw [sparseNoiseTableMeasure]
      change (∫⁻ a : SparseNoiseTable T × Real,
          (parametricRunKernel P
            (sparseNoiseSnocLossProcess (T := T) hk eta heta0 heta
              n' q c0 U hU) (T + 1)) a s
            ∂((sparseNoiseTableMeasure T).prod sourceUniformMeasure)) = _
      rw [MeasureTheory.lintegral_prod _
        (Kernel.measurable_coe
          (parametricRunKernel P
            (sparseNoiseSnocLossProcess (T := T) hk eta heta0 heta
              n' q c0 U hU) (T + 1)) hs).aemeasurable]
      have heval (table : SparseNoiseTable T) (z : Real) :
          parametricRunKernel P
            (sparseNoiseSnocLossProcess (T := T) hk eta heta0 heta
              n' q c0 U hU) (T + 1) (table, z) s =
          runLaw P
            ((sparseNoiseSnocLossProcess (T := T) hk eta heta0 heta
              n' q c0 U hU).at (table, z)) (T + 1) s :=
        congrArg (fun μ : Measure (History n k (T + 1)) => μ s)
          (parametricRunKernel_apply P
            (sparseNoiseSnocLossProcess (T := T) hk eta heta0 heta n' q c0 U hU)
            (table, z) (T + 1))
      simp_rw [heval]
      have hsucc (table : SparseNoiseTable T) (z : Real) :=
        sparseNoiseTable_runLaw_snoc_succ_apply P hk eta heta0 heta
          n' q c0 U hU table z s hs
      simp_rw [hsucc]
      have hswap (table : SparseNoiseTable T) :=
        lintegral_swap_parametric_observation (t := T) P
          (sparseNoiseSnocLossProcess (T := T) hk eta heta0 heta
            n' q c0 U hU) table
          (runLaw P
            ((sparseNoiseTableLossProcess hk eta heta0 heta
              n' q c0 T U hU).at table) T) s hs
      simp_rw [hswap]
      have hobs (table : SparseNoiseTable T) (h : History n k T) :=
        lintegral_sparseNoiseTable_observationKernel P hk eta heta0 heta
          n' q c0 U hU table h
          (Prod.mk h ⁻¹' s) (measurable_prodMk_left hs)
      simp_rw [hobs]
      have hq : Measurable (fun h : History n k T =>
          sparseActualAdaptiveRoundKernel P V T h (Prod.mk h ⁻¹' s)) :=
        Kernel.measurable_kernel_prodMk_left
          (κ := sparseActualAdaptiveRoundKernel P V T) hs
      simp_rw [← parametricRunKernel_apply P
        (sparseNoiseTableLossProcess hk eta heta0 heta
          n' q c0 T U hU)]
      rw [← Measure.lintegral_bind (Kernel.aemeasurable _) hq.aemeasurable]
      change (∫⁻ h, sparseActualAdaptiveRoundKernel P V T h
          (Prod.mk h ⁻¹' s)
          ∂sparseNoiseTableMixture P hk eta heta0 heta
            n' q c0 U hU T) = _
      rw [ih]
      rw [HistoryKernelProcess.law_succ]
      change (∫⁻ h, sparseActualAdaptiveRoundKernel P V T h
          (Prod.mk h ⁻¹' s)
          ∂(sparseActualAdaptiveProcess P V).law T) =
        (((sparseActualAdaptiveProcess P V).law T) ⊗ₘ
          sparseActualAdaptiveRoundKernel P V T) s
      rw [Measure.compProd_apply hs]

/-! ## Hidden-table joint law and the complete auxiliary mixture -/

theorem sparseHiddenTableParameterFamily_at
    {n k : Nat} (hk : 1 ≤ k) (eta : Real) (heta0 : 0 ≤ eta)
    (heta : eta ≤ (1 : Real) / 16) (n' q c0 B : Nat)
    (table : SparseHiddenTable B n) :
    (sparseHiddenTableParameterFamily hk eta heta0 heta
        n' q c0 B).at table =
      sparseAdaptiveParametersOfTable hk eta heta0 heta n' q c0
        (sparseHiddenTableU table)
        (sparseHiddenTableU_abs_le_one table) := by
  rfl

/-- Conditional actual-history law as a Markov kernel of the hidden table. -/
def sparseActualFamilyLawKernel
    {Omega : Type*} [MeasurableSpace Omega] {n k : Nat}
    (P : Policy n k) (F : SparseAdaptiveParameterFamily Omega n k)
    (T : Nat) : Kernel Omega (History n k T) :=
  (sparseFamilyLawKernel (sparseCenteredPolicy P) F T).map
    (sparseActualHistoryEquiv n k T)

instance sparseActualFamilyLawKernel.instIsMarkovKernel
    {Omega : Type*} [MeasurableSpace Omega] {n k : Nat}
    (P : Policy n k) (F : SparseAdaptiveParameterFamily Omega n k)
    (T : Nat) : IsMarkovKernel (sparseActualFamilyLawKernel P F T) := by
  unfold sparseActualFamilyLawKernel
  letI : IsMarkovKernel
      (sparseFamilyLawKernel (sparseCenteredPolicy P) F T) :=
    sparseFamilyLawKernel.instIsMarkovKernel (sparseCenteredPolicy P) F T
  exact Kernel.IsMarkovKernel.map _
    (sparseActualHistoryEquiv n k T).measurable

theorem sparseActualFamilyLawKernel_apply
    {Omega : Type*} [MeasurableSpace Omega] {n k : Nat}
    (P : Policy n k) (F : SparseAdaptiveParameterFamily Omega n k)
    (T : Nat) (omega : Omega) :
    sparseActualFamilyLawKernel P F T omega =
      (sparseActualAdaptiveProcess P (F.at omega)).law T := by
  unfold sparseActualFamilyLawKernel
  rw [Kernel.map_apply _ (sparseActualHistoryEquiv n k T).measurable]
  rw [sparseFamilyLawKernel_apply]
  exact sparseActualHistory_map_adaptiveLaw P (F.at omega) T

def sparseActualJointLaw
    {Omega : Type*} [MeasurableSpace Omega] {n k : Nat}
    (mu : Measure Omega) (P : Policy n k)
    (F : SparseAdaptiveParameterFamily Omega n k) (T : Nat) :
    Measure (Omega × History n k T) :=
  mu ⊗ₘ sparseActualFamilyLawKernel P F T

/-- The centered joint law used by the likelihood proof, pushed through the
affine history equivalence, is literally the actual-feedback joint law. -/
theorem sparseJointLaw_map_actualHistory
    {Omega : Type*} [MeasurableSpace Omega] {n k : Nat}
    (mu : Measure Omega) [SFinite mu] (P : Policy n k)
    (F : SparseAdaptiveParameterFamily Omega n k) (T : Nat) :
    (sparseJointLaw mu (sparseCenteredPolicy P) F T).map
        (fun input =>
          (input.1, sparseActualHistoryEquiv n k T input.2)) =
      sparseActualJointLaw mu P F T := by
  let kappa := sparseFamilyLawKernel (sparseCenteredPolicy P) F T
  let etaK := sparseActualFamilyLawKernel P F T
  letI : IsSFiniteKernel kappa := by
    dsimp [kappa]
    infer_instance
  letI : IsSFiniteKernel etaK := by
    dsimp [etaK]
    infer_instance
  have h := @MsetsLower.Lower.Dense.map_compProd_of_map_apply
    Omega Omega (History n k T) (History n k T)
    inferInstance inferInstance inferInstance inferInstance
    mu mu kappa etaK (by infer_instance) (by infer_instance)
    (by infer_instance) (by infer_instance)
    id (sparseActualHistoryEquiv n k T) measurable_id
    (sparseActualHistoryEquiv n k T).measurable Measure.map_id
    (fun omega => by
      unfold etaK sparseActualFamilyLawKernel
      rw [Kernel.map_apply _ (sparseActualHistoryEquiv n k T).measurable]
      rfl)
  change (mu ⊗ₘ
      sparseFamilyLawKernel (sparseCenteredPolicy P) F T).map
        (Prod.map id (sparseActualHistoryEquiv n k T)) =
    mu ⊗ₘ sparseActualFamilyLawKernel P F T
  exact h

def sparseAuxParametricJointMeasure
    {n k : Nat} (P : Policy n k) (hk : 1 ≤ k)
    (eta : Real) (heta0 : 0 ≤ eta) (heta : eta ≤ (1 : Real) / 16)
    (n' q c0 T B : Nat) :
    Measure (SparseAuxTable B n T × History n k T) :=
  (parametricRunWithParameterKernel P
      (sparseTableLossProcess hk eta heta0 heta n' q c0 T B) T) ∘ₘ
    sparseAuxTableMeasure B n T

def sparseForgetNoise
    {B n k T : Nat} :
    SparseAuxTable B n T × History n k T →
      SparseHiddenTable B n × History n k T :=
  fun input => (input.1.1, input.2)

theorem measurable_sparseForgetNoise {B n k T : Nat} :
    Measurable (sparseForgetNoise (B := B) (n := n) (k := k) (T := T)) :=
  measurable_fst.fst.prodMk measurable_snd

private theorem sparseTable_runLaw_eq_noiseTable_runLaw
    {n k T B : Nat} (P : Policy n k) (hk : 1 ≤ k)
    (eta : Real) (heta0 : 0 ≤ eta) (heta : eta ≤ (1 : Real) / 16)
    (n' q c0 : Nat) (hidden : SparseHiddenTable B n)
    (noise : SparseNoiseTable T) :
    runLaw P
        ((sparseTableLossProcess hk eta heta0 heta n' q c0 T B).at
          (hidden, noise)) T =
      runLaw P
        ((sparseNoiseTableLossProcess hk eta heta0 heta n' q c0 T
          (sparseHiddenTableU hidden)
          (sparseHiddenTableU_abs_le_one hidden)).at noise) T := by
  apply runLaw_eq_of_itemLoss_eq_before
  intro t ht h
  rfl

set_option maxHeartbeats 1000000 in
-- The equality exposes two nested continuous table integrals and a dependent history kernel.
theorem sparseAuxParametricJointMeasure_map_forgetNoise
    {n k T B : Nat} (P : Policy n k) (hk : 1 ≤ k)
    (eta : Real) (heta0 : 0 ≤ eta) (heta : eta ≤ (1 : Real) / 16)
    (n' q c0 : Nat) :
    (sparseAuxParametricJointMeasure P hk eta heta0 heta
      n' q c0 T B).map sparseForgetNoise =
      sparseActualJointLaw (sparseHiddenTableMeasure B n) P
        (sparseHiddenTableParameterFamily hk eta heta0 heta
          n' q c0 B) T := by
  ext s hs
  rw [Measure.map_apply measurable_sparseForgetNoise hs]
  unfold sparseAuxParametricJointMeasure sparseAuxTableMeasure
  rw [Measure.bind_apply
    (hs.preimage measurable_sparseForgetNoise) (Kernel.aemeasurable _)]
  rw [MeasureTheory.lintegral_prod _
    ((Kernel.measurable_coe
      (parametricRunWithParameterKernel P
        (sparseTableLossProcess hk eta heta0 heta n' q c0 T B) T)
      (hs.preimage measurable_sparseForgetNoise)).aemeasurable)]
  unfold sparseActualJointLaw
  rw [Measure.compProd_apply hs]
  apply lintegral_congr
  intro hidden
  have hsection : MeasurableSet
      (Prod.mk hidden ⁻¹' s : Set (History n k T)) :=
    measurable_prodMk_left hs
  have hbind :
      (∫⁻ noise,
        parametricRunWithParameterKernel P
          (sparseTableLossProcess hk eta heta0 heta n' q c0 T B) T
          (hidden, noise)
          (sparseForgetNoise ⁻¹' s) ∂sparseNoiseTableMeasure T) =
        sparseNoiseTableMixture P hk eta heta0 heta n' q c0
          (sparseHiddenTableU hidden)
          (sparseHiddenTableU_abs_le_one hidden) T
          (Prod.mk hidden ⁻¹' s) := by
    unfold sparseNoiseTableMixture
    rw [Measure.bind_apply hsection (Kernel.aemeasurable _)]
    apply lintegral_congr
    intro noise
    rw [parametricRunWithParameterKernel_apply]
    rw [Measure.map_apply measurable_prodMk_left
      (hs.preimage measurable_sparseForgetNoise)]
    rw [sparseTable_runLaw_eq_noiseTable_runLaw P hk eta heta0 heta
      n' q c0 hidden noise]
    rw [← parametricRunKernel_apply P
      (sparseNoiseTableLossProcess hk eta heta0 heta n' q c0 T
        (sparseHiddenTableU hidden)
        (sparseHiddenTableU_abs_le_one hidden))]
    rfl
  rw [hbind]
  rw [sparseNoiseTableMixture_eq_actualProcess]
  rw [sparseActualFamilyLawKernel_apply,
    sparseHiddenTableParameterFamily_at]

#print axioms sourceUniformMeasure_map_feedbackMap_sparseClamp
#print axioms sparse_source_actual_mixture
#print axioms sparseNoiseTableMixture_eq_actualProcess
#print axioms sparseJointLaw_map_actualHistory
#print axioms sparseAuxParametricJointMeasure_map_forgetNoise

end

end MsetsLower.Lower.Sparse
