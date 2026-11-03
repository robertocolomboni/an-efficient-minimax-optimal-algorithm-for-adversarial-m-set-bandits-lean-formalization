import MsetsLower.Lower.Confidence.Table
import MsetsLower.Lower.Confidence.ReferenceSelection
import MsetsLower.Lower.Statement
import MsetsLower.Lower.Dense.Bridge

/-!
# Fixing finite confidence tables

This file identifies the uniform finite-table mixture with the stochastic
reference and planted processes and then fixes a single admissible table.
-/

namespace MsetsLower.Lower.Confidence

open MsetsLower Feedback MeasureTheory ProbabilityTheory Set
open scoped ENNReal ProbabilityTheory

noncomputable section

private theorem roundKernel_eq_of_itemLoss_eq
    {n k t : Nat} (P : Policy n k) (L K : LossProcess n k)
    (hitem : ∀ h : History n k t, L.itemLoss t h = K.itemLoss t h) :
    roundKernel P L t = roundKernel P K t := by
  ext h s hs
  rw [roundKernel_apply P L t h hs, roundKernel_apply P K t h hs]
  congr 1
  ext A
  rw [hitem h]

theorem runLaw_eq_of_itemLoss_eq_before
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

theorem confidenceReferenceTable_runLaw_snoc_prefix
    {n k T : Nat} (hk : 1 ≤ k) (hkn : k ≤ n)
    (P : Policy n k) (table : ConfidenceNoiseTable T) (z : Real) :
    runLaw P
        ((confidenceReferenceTableLossProcess hk hkn (T + 1)).at (table, z)) T =
      runLaw P ((confidenceReferenceTableLossProcess hk hkn T).at table) T := by
  apply runLaw_eq_of_itemLoss_eq_before
  intro t ht h
  change referenceItemLoss hkn
      (confidenceTableNoise (T := T + 1) (table, z) t) =
    referenceItemLoss hkn (confidenceTableNoise table t)
  rw [confidenceTableNoise_snoc_prefix table z ht]

theorem confidencePlantedTable_runLaw_snoc_prefix
    {n k T : Nat} (hk : 1 ≤ k) (hkn : k ≤ n)
    (P : Policy n k) (table : ConfidenceNoiseTable T) (z : Real)
    (Delta : Real) (hDelta : 0 ≤ Delta)
    (hsmall : (k : Real) * Delta ≤ 1 / (2 : Real) ^ 13)
    (B : Real) (i : Fin n) :
    runLaw P
        ((confidencePlantedTableLossProcess hk hkn (T + 1) Delta hDelta
          hsmall B i).at (table, z)) T =
      runLaw P
        ((confidencePlantedTableLossProcess hk hkn T Delta hDelta
          hsmall B i).at table) T := by
  apply runLaw_eq_of_itemLoss_eq_before
  intro t ht h
  change plantedItemLoss hkn
      (confidenceTableNoise (T := T + 1) (table, z) t) Delta
        (activeIndicator hkn B t h) i =
    plantedItemLoss hkn (confidenceTableNoise table t) Delta
      (activeIndicator hkn B t h) i
  rw [confidenceTableNoise_snoc_prefix table z ht]

/-! ## One fresh source coordinate gives the stochastic feedback kernel -/

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

theorem sourceUniformMeasure_map_feedbackMap_clamp
    {u : Real} (hu : |u| ≤ 1 / 16) :
    sourceUniformMeasure.map
        (fun z => feedbackMap u (clampConfidenceNoise z)) =
      feedbackDensityMeasure u := by
  calc
    sourceUniformMeasure.map
        (fun z => feedbackMap u (clampConfidenceNoise z)) =
        (sourceUniformMeasure.map clampConfidenceNoise).map
          (feedbackMap u) := by
      simpa [Function.comp_def] using
        (Measure.map_map (continuous_feedbackMap u).measurable
          measurable_clampConfidenceNoise).symm
    _ = sourceUniformMeasure.map (feedbackMap u) := by
      rw [sourceUniformMeasure_map_clampConfidenceNoise]
    _ = feedbackDensityMeasure u :=
      feedbackPushforwardMeasure_eq_densityMeasure hu

/-- The normalized reference feedback generated from a clipped source. -/
def confidenceReferenceSourceFeedback
    (_A : MSetAction n k) (z : Real) : Real :=
  feedbackMap 0 (clampConfidenceNoise z)

theorem measurable_uncurry_confidenceReferenceSourceFeedback
    {n k : Nat} :
    Measurable (Function.uncurry
      (confidenceReferenceSourceFeedback (n := n) (k := k))) := by
  exact (continuous_feedbackMap 0).measurable.comp
    (measurable_clampConfidenceNoise.comp measurable_snd)

/-- The normalized planted feedback generated from a clipped source. -/
def confidencePlantedSourceFeedback
    {n k : Nat} (hkn : k ≤ n) (Delta B : Real) (i : Fin n) (t : Nat)
    (h : History n k t) (A : MSetAction n k) (z : Real) : Real :=
  by
    classical
    exact if (h, A) ∈ confidenceActiveSelectedSet hkn B i t then
      feedbackMap (-4 * Delta) (clampConfidenceNoise z)
    else feedbackMap 0 (clampConfidenceNoise z)

theorem measurable_uncurry_confidencePlantedSourceFeedback
    {n k : Nat} (hkn : k ≤ n) (Delta B : Real) (i : Fin n) (t : Nat)
    (h : History n k t) :
    Measurable (Function.uncurry
      (confidencePlantedSourceFeedback hkn Delta B i t h)) := by
  classical
  unfold confidencePlantedSourceFeedback
  apply Measurable.ite
  · exact (measurableSet_confidenceActiveSelectedSet hkn B i t).preimage
      (measurable_const.prodMk measurable_fst)
  · exact (continuous_feedbackMap (-4 * Delta)).measurable.comp
      (measurable_clampConfidenceNoise.comp measurable_snd)
  · exact (continuous_feedbackMap 0).measurable.comp
      (measurable_clampConfidenceNoise.comp measurable_snd)

private theorem confidenceReference_source_latent_mixture
    {n k : Nat} (P : Policy n k) (t : Nat) (h : History n k t) :
    ((P.kernel t h) ⊗ₘ
        Kernel.const (MSetAction n k) sourceUniformMeasure).map
        (fun input =>
          (input.1, confidenceReferenceSourceFeedback input.1 input.2)) =
      confidenceReferenceLatentRoundKernel P t h := by
  let eta : Kernel (MSetAction n k) Real :=
    Kernel.const (MSetAction n k) (feedbackDensityMeasure 0)
  letI : IsProbabilityMeasure sourceUniformMeasure := inferInstance
  letI : IsProbabilityMeasure (feedbackDensityMeasure 0) :=
    ⟨feedbackDensityMeasure_apply_univ (by norm_num)⟩
  letI : IsMarkovKernel
      (Kernel.const (MSetAction n k) sourceUniformMeasure) := by infer_instance
  letI : IsMarkovKernel eta := by dsimp [eta]; infer_instance
  letI : IsMarkovKernel
      (confidenceReferenceFeedbackKernel :
        Kernel (History n k t × MSetAction n k) Real) :=
    confidenceReferenceFeedbackKernel_isMarkov
  have hmap : ∀ A : MSetAction n k,
      sourceUniformMeasure.map
          (confidenceReferenceSourceFeedback A) = eta A := by
    intro A
    dsimp [confidenceReferenceSourceFeedback, eta]
    exact sourceUniformMeasure_map_feedbackMap_clamp (by norm_num)
  have hsource := map_compProd_snd_of_map_apply
    (P.kernel t h)
    (Kernel.const (MSetAction n k) sourceUniformMeasure) eta
    confidenceReferenceSourceFeedback
    measurable_uncurry_confidenceReferenceSourceFeedback hmap
  rw [hsource]
  ext s hs
  rw [Measure.compProd_apply hs]
  rw [confidenceReferenceLatentRoundKernel, Kernel.compProd_apply hs]
  rfl

private theorem confidencePlanted_source_latent_mixture
    {n k : Nat} (P : Policy n k) (hkn : k ≤ n)
    (Delta : Real) (hfeedback : |4 * Delta| ≤ 1 / 16)
    (B : Real) (i : Fin n) (t : Nat) (h : History n k t) :
    ((P.kernel t h) ⊗ₘ
        Kernel.const (MSetAction n k) sourceUniformMeasure).map
        (fun input =>
          (input.1,
            confidencePlantedSourceFeedback hkn Delta B i t h
              input.1 input.2)) =
      confidencePlantedLatentRoundKernel P hkn Delta B i t h := by
  classical
  let eta : Kernel (MSetAction n k) Real :=
    (confidencePlantedFeedbackKernel hkn Delta B i t).comap
      (fun A => (h, A)) measurable_prodMk_left
  letI : IsProbabilityMeasure sourceUniformMeasure := inferInstance
  letI : IsMarkovKernel
      (confidencePlantedFeedbackKernel hkn Delta B i t) :=
    confidencePlantedFeedbackKernel_isMarkov hkn hfeedback B i t
  letI : IsMarkovKernel
      (Kernel.const (MSetAction n k) sourceUniformMeasure) := by infer_instance
  letI : IsMarkovKernel eta := by dsimp [eta]; infer_instance
  have hneg : |-4 * Delta| ≤ 1 / 16 := by
    simpa [abs_mul] using hfeedback
  have hmap : ∀ A : MSetAction n k,
      sourceUniformMeasure.map
          (confidencePlantedSourceFeedback hkn Delta B i t h A) = eta A := by
    intro A
    change sourceUniformMeasure.map
        (confidencePlantedSourceFeedback hkn Delta B i t h A) =
      confidencePlantedFeedbackKernel hkn Delta B i t (h, A)
    by_cases hmem : (h, A) ∈ confidenceActiveSelectedSet hkn B i t
    · change sourceUniformMeasure.map
          (fun z => if (h, A) ∈ confidenceActiveSelectedSet hkn B i t then
            feedbackMap (-4 * Delta) (clampConfidenceNoise z)
          else feedbackMap 0 (clampConfidenceNoise z)) = _
      simp only [if_pos hmem]
      rw [confidencePlantedFeedbackKernel_apply_of_mem hkn Delta B i t
        (h, A) hmem]
      exact sourceUniformMeasure_map_feedbackMap_clamp hneg
    · change sourceUniformMeasure.map
          (fun z => if (h, A) ∈ confidenceActiveSelectedSet hkn B i t then
            feedbackMap (-4 * Delta) (clampConfidenceNoise z)
          else feedbackMap 0 (clampConfidenceNoise z)) = _
      simp only [if_neg hmem]
      rw [confidencePlantedFeedbackKernel_apply_of_notMem hkn Delta B i t
        (h, A) hmem]
      exact sourceUniformMeasure_map_feedbackMap_clamp (by norm_num)
  have hsource := map_compProd_snd_of_map_apply
    (P.kernel t h)
    (Kernel.const (MSetAction n k) sourceUniformMeasure) eta
    (confidencePlantedSourceFeedback hkn Delta B i t h)
    (measurable_uncurry_confidencePlantedSourceFeedback
      hkn Delta B i t h) hmap
  rw [hsource]
  ext s hs
  rw [Measure.compProd_apply hs]
  rw [confidencePlantedLatentRoundKernel, Kernel.compProd_apply hs]
  rfl

/-! ## Source-coordinate realization of the observable round kernels -/

theorem confidenceReference_source_observation_mixture
    {n k : Nat} (hk : 1 ≤ k) (hkn : k ≤ n)
    (P : Policy n k) (t : Nat) (h : History n k t) :
    ((P.kernel t h) ⊗ₘ
        Kernel.const (MSetAction n k) sourceUniformMeasure).map
        (fun input =>
          (input.1,
            actionLoss input.1
              (referenceItemLoss hkn (clampConfidenceNoise input.2)))) =
      confidenceReferenceRoundKernel P hkn t h := by
  have hfun :
      (fun input : MSetAction n k × Real =>
          (input.1,
            actionLoss input.1
              (referenceItemLoss hkn (clampConfidenceNoise input.2)))) =
        (fun input => confidenceFeedbackEquiv hkn
          (input.1, confidenceReferenceSourceFeedback input.1 input.2)) := by
    funext input
    apply Prod.ext
    · rfl
    · exact (confidenceScalarFeedback_zero_eq_reference_actionLoss
        hk hkn input.1 (clampConfidenceNoise input.2)).symm
  rw [hfun]
  calc
    _ = (((P.kernel t h) ⊗ₘ
          Kernel.const (MSetAction n k) sourceUniformMeasure).map
            (fun input =>
              (input.1,
                confidenceReferenceSourceFeedback input.1 input.2))).map
          (confidenceFeedbackEquiv hkn) := by
        have hmm := Measure.map_map
          (μ := (P.kernel t h) ⊗ₘ
            Kernel.const (MSetAction n k) sourceUniformMeasure)
          (confidenceFeedbackEquiv hkn).measurable
          (measurable_fst.prodMk
            measurable_uncurry_confidenceReferenceSourceFeedback)
        convert hmm.symm using 1 <;> rfl
    _ = _ := by
      rw [confidenceReference_source_latent_mixture]
      ext s hs
      rw [confidenceReferenceRoundKernel,
        Kernel.map_apply' _ (confidenceFeedbackEquiv hkn).measurable h hs]
      rw [Measure.map_apply (confidenceFeedbackEquiv hkn).measurable hs]

theorem confidencePlanted_source_observation_mixture
    {n k : Nat} (hk : 1 ≤ k) (hkn : k ≤ n)
    (P : Policy n k) {Delta : Real}
    (hfeedback : |4 * Delta| ≤ 1 / 16) (B : Real) (i : Fin n)
    (t : Nat) (h : History n k t) :
    ((P.kernel t h) ⊗ₘ
        Kernel.const (MSetAction n k) sourceUniformMeasure).map
        (fun input =>
          (input.1,
            actionLoss input.1
              (plantedItemLoss hkn (clampConfidenceNoise input.2) Delta
                (activeIndicator hkn B t h) i))) =
      confidencePlantedRoundKernel P hkn Delta B i t h := by
  classical
  have hfun :
      (fun input : MSetAction n k × Real =>
          (input.1,
            actionLoss input.1
              (plantedItemLoss hkn (clampConfidenceNoise input.2) Delta
                (activeIndicator hkn B t h) i))) =
        (fun input => confidenceFeedbackEquiv hkn
          (input.1, confidencePlantedSourceFeedback hkn Delta B i t h
            input.1 input.2)) := by
    funext input
    apply Prod.ext
    · rfl
    · change actionLoss input.1
          (plantedItemLoss hkn (clampConfidenceNoise input.2) Delta
            (activeIndicator hkn B t h) i) =
        confidenceScalarFeedback hkn input.1
          (confidencePlantedSourceFeedback hkn Delta B i t h
            input.1 input.2)
      by_cases hmem :
          (h, input.1) ∈ confidenceActiveSelectedSet hkn B i t
      · rw [show confidencePlantedSourceFeedback hkn Delta B i t h
            input.1 input.2 =
            feedbackMap (-4 * Delta) (clampConfidenceNoise input.2) by
          simp [confidencePlantedSourceFeedback, hmem]]
        exact (confidenceScalarFeedback_planted_of_mem
          hk hkn Delta B i t h input.1
            (clampConfidenceNoise input.2) hmem).symm
      · rw [show confidencePlantedSourceFeedback hkn Delta B i t h
            input.1 input.2 =
            feedbackMap 0 (clampConfidenceNoise input.2) by
          simp [confidencePlantedSourceFeedback, hmem]]
        exact (confidenceScalarFeedback_planted_of_notMem
          hk hkn Delta B i t h input.1
            (clampConfidenceNoise input.2) hmem).symm
  rw [hfun]
  calc
    _ = (((P.kernel t h) ⊗ₘ
          Kernel.const (MSetAction n k) sourceUniformMeasure).map
            (fun input =>
              (input.1,
                confidencePlantedSourceFeedback hkn Delta B i t h
                  input.1 input.2))).map
          (confidenceFeedbackEquiv hkn) := by
        have hmm := Measure.map_map
          (μ := (P.kernel t h) ⊗ₘ
            Kernel.const (MSetAction n k) sourceUniformMeasure)
          (confidenceFeedbackEquiv hkn).measurable
          (measurable_fst.prodMk
            (measurable_uncurry_confidencePlantedSourceFeedback
              hkn Delta B i t h))
        convert hmm.symm using 1 <;> rfl
    _ = _ := by
      rw [confidencePlanted_source_latent_mixture
        P hkn Delta hfeedback B i t h]
      ext s hs
      rw [confidencePlantedRoundKernel,
        Kernel.map_apply' _ (confidenceFeedbackEquiv hkn).measurable h hs]
      rw [Measure.map_apply (confidenceFeedbackEquiv hkn).measurable hs]

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

theorem measurable_confidenceReferenceSourceObservation
    {n k : Nat} (hk : 1 ≤ k) (hkn : k ≤ n) :
    Measurable (fun input : MSetAction n k × Real =>
      (input.1,
        actionLoss input.1
          (referenceItemLoss hkn (clampConfidenceNoise input.2)))) := by
  have hfun :
      (fun input : MSetAction n k × Real =>
        (input.1,
          actionLoss input.1
            (referenceItemLoss hkn (clampConfidenceNoise input.2)))) =
      (fun input => confidenceFeedbackEquiv hkn
        (input.1, confidenceReferenceSourceFeedback input.1 input.2)) := by
    funext input
    apply Prod.ext
    · rfl
    · exact (confidenceScalarFeedback_zero_eq_reference_actionLoss
        hk hkn input.1 (clampConfidenceNoise input.2)).symm
  rw [hfun]
  exact (confidenceFeedbackEquiv hkn).measurable.comp
    (measurable_fst.prodMk
      measurable_uncurry_confidenceReferenceSourceFeedback)

theorem measurable_confidencePlantedSourceObservation
    {n k : Nat} (hk : 1 ≤ k) (hkn : k ≤ n)
    (Delta B : Real) (i : Fin n) (t : Nat) (h : History n k t) :
    Measurable (fun input : MSetAction n k × Real =>
      (input.1,
        actionLoss input.1
          (plantedItemLoss hkn (clampConfidenceNoise input.2) Delta
            (activeIndicator hkn B t h) i))) := by
  classical
  refine measurable_fst.prodMk ?_
  rw [show (fun input : MSetAction n k × Real =>
      actionLoss input.1
        (plantedItemLoss hkn (clampConfidenceNoise input.2) Delta
          (activeIndicator hkn B t h) i)) =
      (fun input =>
        (1 : Real) / 4 + clampConfidenceNoise input.2 / 8 +
          (candidateCount hkn input.1 : Real) / (8 * k) -
          Delta * shape (clampConfidenceNoise input.2) *
            activeIndicator hkn B t h *
              (if i ∈ input.1.1 then 1 else 0)) by
    funext input
    exact actionLoss_plantedItemLoss hk hkn
      (clampConfidenceNoise input.2) Delta
        (activeIndicator hkn B t h) i input.1]
  have hz : Measurable (fun input : MSetAction n k × Real =>
      clampConfidenceNoise input.2) :=
    measurable_clampConfidenceNoise.comp measurable_snd
  have hc : Measurable (fun input : MSetAction n k × Real =>
      (candidateCount hkn input.1 : Real)) :=
    (measurable_of_finite (fun A : MSetAction n k =>
      (candidateCount hkn A : Real))).comp measurable_fst
  have hi : Measurable (fun input : MSetAction n k × Real =>
      (if i ∈ input.1.1 then (1 : Real) else 0)) :=
    (measurable_of_finite (fun A : MSetAction n k =>
      if i ∈ A.1 then (1 : Real) else 0)).comp measurable_fst
  exact (((measurable_const.add (hz.div_const 8)).add
    (hc.div_const (8 * (k : Real)))).sub
      ((((measurable_const.mul (measurable_shape.comp hz)).mul
        measurable_const).mul hi)))

/-- The successor table process with its parameter type exposed as a product.
This avoids relying on transparency of the recursive table type in measure
and kernel calculations. -/
def confidenceReferenceSnocLossProcess
    {n k T : Nat} (hk : 1 ≤ k) (hkn : k ≤ n) :
    ParametricLossProcess (ConfidenceNoiseTable T × Real) n k :=
  confidenceReferenceTableLossProcess hk hkn (T + 1)

def confidencePlantedSnocLossProcess
    {n k T : Nat} (hk : 1 ≤ k) (hkn : k ≤ n)
    (Delta : Real) (hDelta : 0 ≤ Delta)
    (hsmall : (k : Real) * Delta ≤ 1 / (2 : Real) ^ 13)
    (B : Real) (i : Fin n) :
    ParametricLossProcess (ConfidenceNoiseTable T × Real) n k :=
  confidencePlantedTableLossProcess hk hkn (T + 1) Delta hDelta hsmall B i

theorem lintegral_confidenceReferenceTable_observationKernel
    {n k T : Nat} (hk : 1 ≤ k) (hkn : k ≤ n)
    (P : Policy n k) (table : ConfidenceNoiseTable T)
    (h : History n k T) (s : Set (MSetAction n k × Real))
    (hs : MeasurableSet s) :
    (∫⁻ z, observationKernel P
        ((confidenceReferenceSnocLossProcess (T := T) hk hkn).at
          (table, z)) T h s ∂sourceUniformMeasure) =
      confidenceReferenceRoundKernel P hkn T h s := by
  let g : MSetAction n k × Real → MSetAction n k × Real :=
    fun input =>
      (input.1,
        actionLoss input.1
          (referenceItemLoss hkn (clampConfidenceNoise input.2)))
  have hg : Measurable g :=
    measurable_confidenceReferenceSourceObservation hk hkn
  calc
    _ = ∫⁻ z, ((P.kernel T h).map (fun A => g (A, z))) s
          ∂sourceUniformMeasure := by
      apply lintegral_congr
      intro z
      have hitem : ∀ A : MSetAction n k,
          actionLoss A
              (((confidenceReferenceSnocLossProcess (T := T) hk hkn).at
                (table, z)).itemLoss T h) = (g (A, z)).2 := by
        intro A
        change actionLoss A
            (referenceItemLoss hkn
              (confidenceTableNoise (T := T + 1) (table, z) T)) =
          actionLoss A
            (referenceItemLoss hkn (clampConfidenceNoise z))
        rw [confidenceTableNoise_snoc_last]
      rw [observationKernel_apply P
        ((confidenceReferenceSnocLossProcess (T := T) hk hkn).at
          (table, z)) T h hs]
      calc
        _ = (P.kernel T h) ((fun A => g (A, z)) ⁻¹' s) := by
          congr 1
          ext A
          change
            (A, actionLoss A
              (((confidenceReferenceSnocLossProcess (T := T) hk hkn).at
                (table, z)).itemLoss T h)) ∈ s ↔ g (A, z) ∈ s
          have hpair :
              (A, actionLoss A
                (((confidenceReferenceSnocLossProcess (T := T) hk hkn).at
                  (table, z)).itemLoss T h)) = g (A, z) := by
            apply Prod.ext
            · rfl
            · exact hitem A
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
    _ = confidenceReferenceRoundKernel P hkn T h s := by
      exact congrArg (fun mu : Measure (MSetAction n k × Real) => mu s)
        (confidenceReference_source_observation_mixture
          hk hkn P T h)

theorem lintegral_confidencePlantedTable_observationKernel
    {n k T : Nat} (hk : 1 ≤ k) (hkn : k ≤ n)
    (P : Policy n k) (table : ConfidenceNoiseTable T)
    (Delta : Real) (hDelta : 0 ≤ Delta)
    (hsmall : (k : Real) * Delta ≤ 1 / (2 : Real) ^ 13)
    (hfeedback : |4 * Delta| ≤ 1 / 16)
    (B : Real) (i : Fin n) (h : History n k T)
    (s : Set (MSetAction n k × Real)) (hs : MeasurableSet s) :
    (∫⁻ z, observationKernel P
        ((confidencePlantedSnocLossProcess (T := T) hk hkn Delta hDelta
          hsmall B i).at (table, z)) T h s ∂sourceUniformMeasure) =
      confidencePlantedRoundKernel P hkn Delta B i T h s := by
  let g : MSetAction n k × Real → MSetAction n k × Real :=
    fun input =>
      (input.1,
        actionLoss input.1
          (plantedItemLoss hkn (clampConfidenceNoise input.2) Delta
            (activeIndicator hkn B T h) i))
  have hg : Measurable g :=
    measurable_confidencePlantedSourceObservation
      hk hkn Delta B i T h
  calc
    _ = ∫⁻ z, ((P.kernel T h).map (fun A => g (A, z))) s
          ∂sourceUniformMeasure := by
      apply lintegral_congr
      intro z
      have hitem : ∀ A : MSetAction n k,
          actionLoss A
              (((confidencePlantedSnocLossProcess (T := T) hk hkn Delta hDelta
                hsmall B i).at (table, z)).itemLoss T h) = (g (A, z)).2 := by
        intro A
        change actionLoss A
            (plantedItemLoss hkn
              (confidenceTableNoise (T := T + 1) (table, z) T) Delta
                (activeIndicator hkn B T h) i) =
          actionLoss A
            (plantedItemLoss hkn (clampConfidenceNoise z) Delta
              (activeIndicator hkn B T h) i)
        rw [confidenceTableNoise_snoc_last]
      rw [observationKernel_apply P
        ((confidencePlantedSnocLossProcess (T := T) hk hkn Delta hDelta
          hsmall B i).at (table, z)) T h hs]
      calc
        _ = (P.kernel T h) ((fun A => g (A, z)) ⁻¹' s) := by
          congr 1
          ext A
          change
            (A, actionLoss A
              (((confidencePlantedSnocLossProcess (T := T) hk hkn Delta hDelta
                hsmall B i).at (table, z)).itemLoss T h)) ∈ s ↔
              g (A, z) ∈ s
          have hpair :
              (A, actionLoss A
                (((confidencePlantedSnocLossProcess (T := T) hk hkn Delta hDelta
                  hsmall B i).at (table, z)).itemLoss T h)) = g (A, z) := by
            apply Prod.ext
            · rfl
            · exact hitem A
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
    _ = confidencePlantedRoundKernel P hkn Delta B i T h s := by
      exact congrArg (fun mu : Measure (MSetAction n k × Real) => mu s)
        (confidencePlanted_source_observation_mixture
          hk hkn P hfeedback B i T h)

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

theorem confidenceReferenceTable_runLaw_snoc_succ_apply
    {n k T : Nat} (hk : 1 ≤ k) (hkn : k ≤ n)
    (P : Policy n k) (table : ConfidenceNoiseTable T) (z : Real)
    (s : Set (History n k (T + 1))) (hs : MeasurableSet s) :
    runLaw P
        ((confidenceReferenceSnocLossProcess (T := T) hk hkn).at
          (table, z)) (T + 1) s =
      ∫⁻ h, observationKernel P
          ((confidenceReferenceSnocLossProcess (T := T) hk hkn).at
            (table, z)) T h (Prod.mk h ⁻¹' s)
        ∂runLaw P ((confidenceReferenceTableLossProcess hk hkn T).at table) T := by
  rw [runLaw_succ_eq_compProd]
  change (runLaw P
      ((confidenceReferenceTableLossProcess hk hkn (T + 1)).at
        (table, z)) T ⊗ₘ
      observationKernel P
        ((confidenceReferenceTableLossProcess hk hkn (T + 1)).at
          (table, z)) T) s = _
  rw [confidenceReferenceTable_runLaw_snoc_prefix hk hkn P table z]
  rw [Measure.compProd_apply hs]
  simp only [confidenceReferenceSnocLossProcess]

theorem confidencePlantedTable_runLaw_snoc_succ_apply
    {n k T : Nat} (hk : 1 ≤ k) (hkn : k ≤ n)
    (P : Policy n k) (table : ConfidenceNoiseTable T) (z : Real)
    (Delta : Real) (hDelta : 0 ≤ Delta)
    (hsmall : (k : Real) * Delta ≤ 1 / (2 : Real) ^ 13)
    (B : Real) (i : Fin n)
    (s : Set (History n k (T + 1))) (hs : MeasurableSet s) :
    runLaw P
        ((confidencePlantedSnocLossProcess (T := T) hk hkn Delta hDelta
          hsmall B i).at (table, z)) (T + 1) s =
      ∫⁻ h, observationKernel P
          ((confidencePlantedSnocLossProcess (T := T) hk hkn Delta hDelta
            hsmall B i).at (table, z)) T h (Prod.mk h ⁻¹' s)
        ∂runLaw P
          ((confidencePlantedTableLossProcess hk hkn T Delta hDelta
            hsmall B i).at table) T := by
  rw [runLaw_succ_eq_compProd]
  change (runLaw P
      ((confidencePlantedTableLossProcess hk hkn (T + 1) Delta hDelta
        hsmall B i).at (table, z)) T ⊗ₘ
      observationKernel P
        ((confidencePlantedTableLossProcess hk hkn (T + 1) Delta hDelta
          hsmall B i).at (table, z)) T) s = _
  rw [confidencePlantedTable_runLaw_snoc_prefix
    hk hkn P table z Delta hDelta hsmall B i]
  rw [Measure.compProd_apply hs]
  simp only [confidencePlantedSnocLossProcess]

/-! ## Exact finite-table mixtures -/

def confidenceReferenceTableMixture
    {n k : Nat} (hk : 1 ≤ k) (hkn : k ≤ n)
    (P : Policy n k) (T : Nat) : Measure (History n k T) :=
  parametricRunKernel P (confidenceReferenceTableLossProcess hk hkn T) T ∘ₘ
    confidenceNoiseTableMeasure T

def confidencePlantedTableMixture
    {n k : Nat} (hk : 1 ≤ k) (hkn : k ≤ n)
    (P : Policy n k) (T : Nat)
    (Delta : Real) (hDelta : 0 ≤ Delta)
    (hsmall : (k : Real) * Delta ≤ 1 / (2 : Real) ^ 13)
    (B : Real) (i : Fin n) : Measure (History n k T) :=
  parametricRunKernel P
      (confidencePlantedTableLossProcess hk hkn T Delta hDelta hsmall B i) T ∘ₘ
    confidenceNoiseTableMeasure T

theorem confidenceReferenceTableMixture_eq_process
    {n k : Nat} (hk : 1 ≤ k) (hkn : k ≤ n) (P : Policy n k) :
    ∀ T : Nat, confidenceReferenceTableMixture hk hkn P T =
      (confidenceReferenceProcess P hkn).law T := by
  intro T
  induction T with
  | zero =>
      unfold confidenceReferenceTableMixture
      rw [confidenceNoiseTableMeasure,
        Measure.dirac_bind (Kernel.measurable _)]
      rw [parametricRunKernel_apply]
  | succ T ih =>
      letI : IsMarkovKernel (confidenceReferenceRoundKernel P hkn T) :=
        confidenceReferenceRoundKernel_isMarkov P hkn T
      ext s hs
      unfold confidenceReferenceTableMixture
      rw [Measure.bind_apply hs (Kernel.aemeasurable _)]
      rw [confidenceNoiseTableMeasure]
      change (∫⁻ a : ConfidenceNoiseTable T × Real,
          (parametricRunKernel P
            (confidenceReferenceSnocLossProcess (T := T) hk hkn) (T + 1)) a s
            ∂((confidenceNoiseTableMeasure T).prod sourceUniformMeasure)) = _
      rw [MeasureTheory.lintegral_prod _
        (Kernel.measurable_coe
          (parametricRunKernel P
            (confidenceReferenceSnocLossProcess (T := T) hk hkn) (T + 1))
          hs).aemeasurable]
      have happ (table : ConfidenceNoiseTable T) (z : Real) :
          parametricRunKernel P (confidenceReferenceSnocLossProcess (T := T) hk hkn)
            (T + 1) (table, z) s =
          runLaw P ((confidenceReferenceSnocLossProcess (T := T) hk hkn).at
            (table, z)) (T + 1) s :=
        congrArg (fun mu : Measure (History n k (T + 1)) => mu s)
          (parametricRunKernel_apply P _ (table, z) (T + 1))
      simp_rw [happ]
      have hsucc (table : ConfidenceNoiseTable T) (z : Real) :=
        confidenceReferenceTable_runLaw_snoc_succ_apply
          hk hkn P table z s hs
      simp_rw [hsucc]
      have hswap (table : ConfidenceNoiseTable T) :=
        lintegral_swap_parametric_observation (t := T) P
          (confidenceReferenceSnocLossProcess (T := T) hk hkn) table
          (runLaw P
            ((confidenceReferenceTableLossProcess hk hkn T).at table) T)
          s hs
      simp_rw [hswap]
      have hobs (table : ConfidenceNoiseTable T) (h : History n k T) :=
        lintegral_confidenceReferenceTable_observationKernel
          hk hkn P table h (Prod.mk h ⁻¹' s) (measurable_prodMk_left hs)
      simp_rw [hobs]
      have hq : Measurable (fun h : History n k T =>
          confidenceReferenceRoundKernel P hkn T h (Prod.mk h ⁻¹' s)) :=
        Kernel.measurable_kernel_prodMk_left
          (κ := confidenceReferenceRoundKernel P hkn T) hs
      simp_rw [← parametricRunKernel_apply P
        (confidenceReferenceTableLossProcess hk hkn T)]
      rw [← Measure.lintegral_bind (Kernel.aemeasurable _) hq.aemeasurable]
      change (∫⁻ h, confidenceReferenceRoundKernel P hkn T h
          (Prod.mk h ⁻¹' s) ∂confidenceReferenceTableMixture hk hkn P T) = _
      rw [ih]
      rw [HistoryKernelProcess.law_succ]
      change (∫⁻ h, confidenceReferenceRoundKernel P hkn T h
          (Prod.mk h ⁻¹' s) ∂(confidenceReferenceProcess P hkn).law T) =
        (((confidenceReferenceProcess P hkn).law T) ⊗ₘ
          confidenceReferenceRoundKernel P hkn T) s
      rw [Measure.compProd_apply hs]

theorem confidencePlantedTableMixture_eq_process
    {n k : Nat} (hk : 1 ≤ k) (hkn : k ≤ n) (P : Policy n k)
    (Delta : Real) (hDelta : 0 ≤ Delta)
    (hsmall : (k : Real) * Delta ≤ 1 / (2 : Real) ^ 13)
    (hfeedback : |4 * Delta| ≤ 1 / 16)
    (B : Real) (i : Fin n) :
    ∀ T : Nat,
      confidencePlantedTableMixture hk hkn P T Delta hDelta hsmall B i =
        (confidencePlantedProcess P hkn Delta hfeedback B i).law T := by
  intro T
  induction T with
  | zero =>
      unfold confidencePlantedTableMixture
      rw [confidenceNoiseTableMeasure,
        Measure.dirac_bind (Kernel.measurable _)]
      rw [parametricRunKernel_apply]
  | succ T ih =>
      letI : IsMarkovKernel
          (confidencePlantedRoundKernel P hkn Delta B i T) :=
        confidencePlantedRoundKernel_isMarkov P hkn hfeedback B i T
      ext s hs
      unfold confidencePlantedTableMixture
      rw [Measure.bind_apply hs (Kernel.aemeasurable _)]
      rw [confidenceNoiseTableMeasure]
      change (∫⁻ a : ConfidenceNoiseTable T × Real,
          (parametricRunKernel P
            (confidencePlantedSnocLossProcess (T := T) hk hkn Delta hDelta
              hsmall B i) (T + 1)) a s
            ∂((confidenceNoiseTableMeasure T).prod sourceUniformMeasure)) = _
      rw [MeasureTheory.lintegral_prod _
        (Kernel.measurable_coe
          (parametricRunKernel P
            (confidencePlantedSnocLossProcess (T := T) hk hkn Delta hDelta
              hsmall B i) (T + 1)) hs).aemeasurable]
      have happ (table : ConfidenceNoiseTable T) (z : Real) :
          parametricRunKernel P
            (confidencePlantedSnocLossProcess (T := T) hk hkn Delta hDelta hsmall B i)
            (T + 1) (table, z) s =
          runLaw P ((confidencePlantedSnocLossProcess (T := T) hk hkn Delta hDelta
            hsmall B i).at (table, z)) (T + 1) s :=
        congrArg (fun mu : Measure (History n k (T + 1)) => mu s)
          (parametricRunKernel_apply P _ (table, z) (T + 1))
      simp_rw [happ]
      have hsucc (table : ConfidenceNoiseTable T) (z : Real) :=
        confidencePlantedTable_runLaw_snoc_succ_apply
          hk hkn P table z Delta hDelta hsmall B i s hs
      simp_rw [hsucc]
      have hswap (table : ConfidenceNoiseTable T) :=
        lintegral_swap_parametric_observation (t := T) P
          (confidencePlantedSnocLossProcess (T := T) hk hkn Delta hDelta
            hsmall B i) table
          (runLaw P
            ((confidencePlantedTableLossProcess hk hkn T Delta hDelta
              hsmall B i).at table) T) s hs
      simp_rw [hswap]
      have hobs (table : ConfidenceNoiseTable T) (h : History n k T) :=
        lintegral_confidencePlantedTable_observationKernel
          hk hkn P table Delta hDelta hsmall hfeedback B i h
            (Prod.mk h ⁻¹' s) (measurable_prodMk_left hs)
      simp_rw [hobs]
      have hq : Measurable (fun h : History n k T =>
          confidencePlantedRoundKernel P hkn Delta B i T h
            (Prod.mk h ⁻¹' s)) :=
        Kernel.measurable_kernel_prodMk_left
          (κ := confidencePlantedRoundKernel P hkn Delta B i T) hs
      simp_rw [← parametricRunKernel_apply P
        (confidencePlantedTableLossProcess hk hkn T Delta hDelta
          hsmall B i)]
      rw [← Measure.lintegral_bind (Kernel.aemeasurable _) hq.aemeasurable]
      change (∫⁻ h, confidencePlantedRoundKernel P hkn Delta B i T h
          (Prod.mk h ⁻¹' s)
          ∂confidencePlantedTableMixture hk hkn P T Delta hDelta hsmall B i) = _
      rw [ih]
      rw [HistoryKernelProcess.law_succ]
      change (∫⁻ h, confidencePlantedRoundKernel P hkn Delta B i T h
          (Prod.mk h ⁻¹' s)
          ∂(confidencePlantedProcess P hkn Delta hfeedback B i).law T) =
        (((confidencePlantedProcess P hkn Delta hfeedback B i).law T) ⊗ₘ
          confidencePlantedRoundKernel P hkn Delta B i T) s
      rw [Measure.compProd_apply hs]

/-! ## A fixing interface for history events -/

/-- Convert a lower bound for a common observable history event into a fixed
parameter regret tail.  The implication to regret is allowed to hold almost
surely in every deterministic section; this is the form needed when an
observable statistic is identified with its source-table version on the
support of the protocol law. -/
theorem exists_fixed_parametric_regret_of_ae_history_event
    {Xi : Type*} [MeasurableSpace Xi] {n k t : Nat} (hkn : k ≤ n)
    (mu : Measure Xi) [IsProbabilityMeasure mu]
    (P : Policy n k) (L : ParametricLossProcess Xi n k)
    (threshold probability : Real) (E : Set (History n k t))
    (hE : MeasurableSet E)
    (haverage : probability ≤
      ((parametricRunKernel P L t) ∘ₘ mu).real E)
    (hsub : ∀ xi : Xi, ∀ᵐ h ∂runLaw P (L.at xi) t,
      h ∈ E → threshold ≤ pathRegret (L.at xi) t h) :
    ∃ xi : Xi, probability ≤
      (runLaw P (L.at xi) t).real
        {h | threshold ≤ pathRegret (L.at xi) t h} := by
  let K := parametricRunWithParameterKernel P L t
  letI : IsMarkovKernel K :=
    parametricRunWithParameterKernel.instIsMarkovKernel P L t
  have hmeasure :
      ((parametricRunKernel P L t) ∘ₘ mu) E ≤
        (K ∘ₘ mu) (parametricRegretEvent L t threshold) := by
    rw [Measure.bind_apply hE (Kernel.aemeasurable _),
      Measure.bind_apply (measurableSet_parametricRegretEvent L t threshold)
        (Kernel.aemeasurable _)]
    apply lintegral_mono
    intro xi
    change parametricRunKernel P L t xi E ≤
      K xi (parametricRegretEvent L t threshold)
    rw [parametricRunKernel_apply]
    change runLaw P (L.at xi) t E ≤
      parametricRunWithParameterKernel P L t xi
        (parametricRegretEvent L t threshold)
    rw [parametricRunWithParameterKernel_regretEvent_apply hkn]
    exact measure_mono_ae (hsub xi)
  have hreal :
      ((parametricRunKernel P L t) ∘ₘ mu).real E ≤
        (K ∘ₘ mu).real (parametricRegretEvent L t threshold) := by
    exact ENNReal.toReal_mono (measure_ne_top _ _) hmeasure
  exact exists_fixed_parametric_regret hkn mu P L t threshold probability
    (haverage.trans (by simpa [K] using hreal))

/-! ## Support of deterministic protocol sections -/

/-- Histories whose recorded scalar feedback is exactly the feedback generated
by a fixed deterministic loss process. -/
def ProtocolHistoryCompatible {n k : Nat} (L : LossProcess n k) :
    (t : Nat) → History n k t → Prop
  | 0, _ => True
  | t + 1, h =>
      ProtocolHistoryCompatible L t h.1 ∧
        h.2.2 = actionLoss h.2.1 (L.itemLoss t h.1)

theorem measurableSet_protocolHistoryCompatible
    {n k : Nat} (L : LossProcess n k) : ∀ t : Nat,
    MeasurableSet {h : History n k t | ProtocolHistoryCompatible L t h} := by
  intro t
  induction t with
  | zero => simp [ProtocolHistoryCompatible]
  | succ t ih =>
      have hinput : Measurable (fun h : History n k (t + 1) =>
          (h.1, h.2.1)) :=
        measurable_fst.prodMk (measurable_fst.comp measurable_snd)
      have hloss : Measurable (fun h : History n k (t + 1) =>
          actionLoss h.2.1 (L.itemLoss t h.1)) :=
        (measurable_actionLoss_joint (L.measurable_itemLoss t)).comp hinput
      change MeasurableSet {h : History n k (t + 1) |
        ProtocolHistoryCompatible L t h.1 ∧
          h.2.2 = actionLoss h.2.1 (L.itemLoss t h.1)}
      exact (ih.preimage measurable_fst).inter
        (measurableSet_eq_fun (measurable_snd.comp measurable_snd) hloss)

theorem ae_roundKernel_protocolHistoryCompatible
    {n k t : Nat} (P : Policy n k) (L : LossProcess n k)
    (h : History n k t) (hcompat : ProtocolHistoryCompatible L t h) :
    ∀ᵐ h' ∂roundKernel P L t h,
      ProtocolHistoryCompatible L (t + 1) h' := by
  unfold roundKernel
  rw [Kernel.map_apply _ (measurable_extendRun L t) h]
  change ∀ᵐ h' ∂(actionHistoryKernel P t h).map (extendRun L t),
    h' ∈ {h' : History n k (t + 1) |
      ProtocolHistoryCompatible L (t + 1) h'}
  apply (ae_map_iff (measurable_extendRun L t).aemeasurable
    (measurableSet_protocolHistoryCompatible L (t + 1))).2
  rw [actionHistoryKernel_apply]
  apply (ae_map_iff measurable_prodMk_left.aemeasurable
    ((measurableSet_protocolHistoryCompatible L (t + 1)).preimage
      (measurable_extendRun L t))).2
  apply ae_of_all
  intro A
  exact ⟨hcompat, rfl⟩

theorem ae_runLaw_protocolHistoryCompatible
    {n k : Nat} (P : Policy n k) (L : LossProcess n k) : ∀ t : Nat,
    ∀ᵐ h ∂runLaw P L t, ProtocolHistoryCompatible L t h := by
  intro t
  induction t with
  | zero => simp [runLaw, ProtocolHistoryCompatible]
  | succ t ih =>
      rw [runLaw_succ]
      apply Measure.ae_comp_of_ae_ae
        (measurableSet_protocolHistoryCompatible L (t + 1))
      filter_upwards [ih] with h hcompat
      exact ae_roundKernel_protocolHistoryCompatible P L h hcompat

theorem protocolHistoryCompatible_to_planted
    {n k : Nat} (hk : 1 ≤ k) (hkn : k ≤ n)
    (noise : Nat → Real) (hnoise : ∀ t, noise t ∈ Icc (-1 : Real) 1)
    (Delta : Real) (hDelta : 0 ≤ Delta)
    (hsmall : (k : Real) * Delta ≤ 1 / (2 : Real) ^ 13)
    (B : Real) (i : Fin n) : ∀ (t : Nat) (h : History n k t),
    ProtocolHistoryCompatible
        (plantedLossProcess hk hkn noise hnoise Delta hDelta hsmall B i) t h →
      PlantedHistoryCompatible hkn noise Delta B i t h := by
  intro t
  induction t with
  | zero => intro h _; trivial
  | succ t ih =>
      intro h hcompat
      refine ⟨ih h.1 hcompat.1, ?_⟩
      exact hcompat.2

/-! ## Reference penalty and planted score imply regret -/

theorem reference_played_sub_coreComparator
    {n k : Nat} (hk : 1 ≤ k) (hkn : k ≤ n)
    (i : Fin n) (hi : i ∈ confidenceCandidates n k hkn)
    (z : Real) (A : MSetAction n k) :
    actionLoss A (referenceItemLoss hkn z) -
        actionLoss (coreComparator hk hkn i hi) (referenceItemLoss hkn z) =
      candidatePenalty hkn A := by
  rw [actionLoss_referenceItemLoss hk hkn,
    actionLoss_referenceItemLoss hk hkn,
    candidateCount_coreComparator]
  unfold candidatePenalty
  ring

theorem reference_comparatorRegret_eq_cumulativePenalty
    {n k : Nat} (hk : 1 ≤ k) (hkn : k ≤ n)
    (noise : Nat → Real) (hnoise : ∀ t, noise t ∈ Icc (-1 : Real) 1)
    (i : Fin n) (hi : i ∈ confidenceCandidates n k hkn) :
    ∀ (t : Nat) (h : History n k t),
      realizedCumulativeLoss (referenceLossProcess hk hkn noise hnoise) t h -
        comparatorCumulativeLoss (referenceLossProcess hk hkn noise hnoise)
          t h (coreComparator hk hkn i hi) =
      cumulativePenalty hkn t h := by
  intro t
  induction t with
  | zero => intro h; simp [realizedCumulativeLoss,
      comparatorCumulativeLoss, cumulativePenalty]
  | succ t ih =>
      rintro ⟨hprev, ⟨A, y⟩⟩
      change
        (realizedCumulativeLoss
            (referenceLossProcess hk hkn noise hnoise) t hprev +
          actionLoss A (referenceItemLoss hkn (noise t))) -
        (comparatorCumulativeLoss
            (referenceLossProcess hk hkn noise hnoise) t hprev
              (coreComparator hk hkn i hi) +
          actionLoss (coreComparator hk hkn i hi)
            (referenceItemLoss hkn (noise t))) = _
      rw [cumulativePenalty_succ]
      calc
        _ =
            (realizedCumulativeLoss
                (referenceLossProcess hk hkn noise hnoise) t hprev -
              comparatorCumulativeLoss
                (referenceLossProcess hk hkn noise hnoise) t hprev
                  (coreComparator hk hkn i hi)) +
              (actionLoss A (referenceItemLoss hkn (noise t)) -
                actionLoss (coreComparator hk hkn i hi)
                  (referenceItemLoss hkn (noise t))) := by ring
        _ = cumulativePenalty hkn t hprev + candidatePenalty hkn A := by
          rw [ih hprev,
            reference_played_sub_coreComparator hk hkn i hi]

theorem cumulativePenalty_le_reference_pathRegret
    {n k : Nat} (hk : 1 ≤ k) (hkn : k ≤ n)
    (noise : Nat → Real) (hnoise : ∀ t, noise t ∈ Icc (-1 : Real) 1)
    (i : Fin n) (hi : i ∈ confidenceCandidates n k hkn)
    (t : Nat) (h : History n k t) :
    cumulativePenalty hkn t h ≤
      pathRegret (referenceLossProcess hk hkn noise hnoise) t h := by
  rw [← reference_comparatorRegret_eq_cumulativePenalty
    hk hkn noise hnoise i hi t h]
  exact comparatorRegret_le_pathRegret _ t h (coreComparator hk hkn i hi)

/-! ## Fixing the two stochastic confidence branches -/

theorem exists_fixed_reference_penalty_regret
    {n k T : Nat} (hk : 1 ≤ k) (hkn : k ≤ n)
    (P : Policy n k) (B probability : Real)
    (i : Fin n) (hi : i ∈ confidenceCandidates n k hkn)
    (hprobability : probability ≤
      ((confidenceReferenceProcess P hkn).law T).real
        {h | B ≤ cumulativePenalty hkn T h}) :
    ∃ table : ConfidenceNoiseTable T,
      probability ≤
        (runLaw P ((confidenceReferenceTableLossProcess hk hkn T).at table) T).real
          {h | B ≤ pathRegret
            ((confidenceReferenceTableLossProcess hk hkn T).at table) T h} := by
  let E : Set (History n k T) := {h | B ≤ cumulativePenalty hkn T h}
  have hE : MeasurableSet E :=
    measurableSet_le measurable_const (measurable_cumulativePenalty hkn T)
  have haverage : probability ≤
      ((parametricRunKernel P
          (confidenceReferenceTableLossProcess hk hkn T) T) ∘ₘ
        confidenceNoiseTableMeasure T).real E := by
    change probability ≤
      (confidenceReferenceTableMixture hk hkn P T).real E
    rw [confidenceReferenceTableMixture_eq_process hk hkn P T]
    exact hprobability
  apply exists_fixed_parametric_regret_of_ae_history_event hkn
    (confidenceNoiseTableMeasure T) P
      (confidenceReferenceTableLossProcess hk hkn T)
      B probability E hE haverage
  intro table
  apply ae_of_all
  intro h hpenalty
  have hregret := cumulativePenalty_le_reference_pathRegret
    hk hkn (confidenceTableNoise table)
      (confidenceTableNoise_mem_Icc table) i hi T h
  rw [confidenceReferenceTableLossProcess_at hk hkn table]
  exact hpenalty.trans hregret

theorem exists_fixed_planted_score_regret
    {n k T : Nat} (hk : 1 ≤ k) (hkn : k ≤ n)
    (P : Policy n k) (Delta : Real) (hDelta : 0 ≤ Delta)
    (hsmall : (k : Real) * Delta ≤ 1 / (2 : Real) ^ 13)
    (hfeedback : |4 * Delta| ≤ 1 / 16)
    (B : Real) (i : Fin n) (hi : i ∈ confidenceCandidates n k hkn)
    (probability : Real)
    (hprobability : probability ≤
      ((confidencePlantedProcess P hkn Delta hfeedback B i).law T).real
        (observableConfidenceScoreEvent hkn Delta B i)) :
    ∃ table : ConfidenceNoiseTable T,
      probability ≤
        (runLaw P
          ((confidencePlantedTableLossProcess hk hkn T Delta hDelta
            hsmall B i).at table) T).real
          {h | Delta * T / 8 ≤
            pathRegret
              ((confidencePlantedTableLossProcess hk hkn T Delta hDelta
                hsmall B i).at table) T h} := by
  let E : Set (History n k T) :=
    observableConfidenceScoreEvent hkn Delta B i
  have hE : MeasurableSet E :=
    measurableSet_observableConfidenceScoreEvent hkn Delta B i
  have haverage : probability ≤
      ((parametricRunKernel P
          (confidencePlantedTableLossProcess hk hkn T Delta hDelta
            hsmall B i) T) ∘ₘ confidenceNoiseTableMeasure T).real E := by
    change probability ≤
      (confidencePlantedTableMixture hk hkn P T Delta hDelta hsmall B i).real E
    rw [confidencePlantedTableMixture_eq_process
      hk hkn P Delta hDelta hsmall hfeedback B i T]
    exact hprobability
  apply exists_fixed_parametric_regret_of_ae_history_event hkn
    (confidenceNoiseTableMeasure T) P
      (confidencePlantedTableLossProcess hk hkn T Delta hDelta hsmall B i)
      (Delta * T / 8) probability E hE haverage
  intro table
  have hsupport := ae_runLaw_protocolHistoryCompatible P
    ((confidencePlantedTableLossProcess hk hkn T Delta hDelta
      hsmall B i).at table) T
  filter_upwards [hsupport] with h hcompat
  intro hevent
  have hL := confidencePlantedTableLossProcess_at
    hk hkn table Delta hDelta hsmall B i
  have hcompat' : ProtocolHistoryCompatible
      (plantedLossProcess hk hkn (confidenceTableNoise table)
        (confidenceTableNoise_mem_Icc table) Delta hDelta hsmall B i) T h := by
    simpa only [hL] using hcompat
  have hplanted := protocolHistoryCompatible_to_planted
    hk hkn (confidenceTableNoise table)
      (confidenceTableNoise_mem_Icc table) Delta hDelta hsmall B i T h hcompat'
  have hscoreEvent :=
    (mem_observableConfidenceScoreEvent_iff_plantedCompatible
      hk hkn (confidenceTableNoise table) Delta B i h hplanted).mp hevent
  have hscore := lower_confidence_score hk hkn
    (confidenceTableNoise table) (confidenceTableNoise_mem_Icc table)
      Delta hDelta hsmall B i hi T h
  rw [hL]
  change Delta * (T : Real) / 8 ≤
    confidenceScore hkn (confidenceTableNoise table) Delta B i T h at hscoreEvent
  exact hscoreEvent.trans hscore

theorem lower_confidence_reference_penalty_tail
    {n k T : Nat} (hk : 1 ≤ k) (hkn : k ≤ n)
    (P : Policy n k) (B probability : Real)
    (hcandidates : (confidenceCandidates n k hkn).Nonempty)
    (hprobability : probability ≤
      ((confidenceReferenceProcess P hkn).law T).real
        {h | B ≤ cumulativePenalty hkn T h}) :
    MsetsLower.Lower.HasRegretLowerTail hkn P T B probability := by
  obtain ⟨i, hi⟩ := hcandidates
  obtain ⟨table, htable⟩ := exists_fixed_reference_penalty_regret
    hk hkn P B probability i hi hprobability
  refine ⟨(confidenceReferenceTableLossProcess hk hkn T).at table, ?_⟩
  unfold MsetsLower.Lower.regretTailProbability
  apply (ENNReal.ofReal_le_iff_le_toReal (measure_ne_top _ _)).2
  simpa [measureReal_def] using htable

theorem lower_confidence_planted_score_tail
    {n k T : Nat} (hk : 1 ≤ k) (hkn : k ≤ n)
    (P : Policy n k) (Delta : Real) (hDelta : 0 ≤ Delta)
    (hsmall : (k : Real) * Delta ≤ 1 / (2 : Real) ^ 13)
    (hfeedback : |4 * Delta| ≤ 1 / 16)
    (B : Real) (i : Fin n) (hi : i ∈ confidenceCandidates n k hkn)
    (probability : Real)
    (hprobability : probability ≤
      ((confidencePlantedProcess P hkn Delta hfeedback B i).law T).real
        (observableConfidenceScoreEvent hkn Delta B i)) :
    MsetsLower.Lower.HasRegretLowerTail hkn P T (Delta * T / 8) probability := by
  obtain ⟨table, htable⟩ := exists_fixed_planted_score_regret
    hk hkn P Delta hDelta hsmall hfeedback B i hi probability hprobability
  refine ⟨(confidencePlantedTableLossProcess hk hkn T Delta hDelta
    hsmall B i).at table, ?_⟩
  unfold MsetsLower.Lower.regretTailProbability
  apply (ENNReal.ofReal_le_iff_le_toReal (measure_ne_top _ _)).2
  simpa [measureReal_def] using htable

/-! ## Literal confidence proposition -/

/-- `prop:lower-confidence`, including the large-reference-penalty branch,
the planted change-of-measure branch, finite-table fixing, and the final
constant conversion. -/
theorem lower_confidence
    {n k T : Nat} (hk : 1 ≤ k) (hhalf : k ≤ n / 2)
    {delta : Real} (hdelta_pos : 0 < delta)
    (hdelta_small : delta ≤ 1 / (2 : Real) ^ 36)
    (hhorizon :
      4 * (n : Real) * (k : Real) ^ 2 *
          MsetsLower.Lower.confidenceLog delta ≤ (T : Real)) :
    MsetsLower.Lower.ConfidenceConclusion n k T
      (hhalf.trans (Nat.div_le_self n 2)) delta := by
  let hkn : k ≤ n := hhalf.trans (Nat.div_le_self n 2)
  let N : Real := (confidenceCandidates n k hkn).card
  let L : Real := MsetsLower.Lower.confidenceLog delta
  let Delta : Real := confidenceDelta N L T
  let B : Real := confidenceBudget N L T
  intro P
  have hparams := confidence_stochastic_parameter_package
    hk hkn hhalf hdelta_pos hdelta_small hhorizon
  rcases hparams with
    ⟨hN, hDelta_pos, hscale, hB, hB_nonneg, hT, hfeedback,
      hDelta_def, hkDelta, hkT⟩
  have hcandidates : (confidenceCandidates n k hkn).Nonempty := by
    exact Finset.card_pos.mp (lt_of_lt_of_le (by omega : 0 < 2) hN)
  have hsmall : (k : Real) * Delta ≤ 1 / (2 : Real) ^ 13 := by
    norm_num at hkDelta ⊢
    linarith
  have hdelta_one : delta ≤ 1 := hdelta_small.trans (by norm_num)
  have hL_nonneg : 0 ≤ L := by
    dsimp [L]
    exact MsetsLower.Lower.confidenceLog_nonneg hdelta_pos hdelta_one
  have hT_pos : 0 < (T : Real) := by exact_mod_cast hT
  have hN_nonneg : 0 ≤ N := by
    dsimp [N]
    positivity
  have hn_nonneg : 0 ≤ (n : Real) := by positivity
  have hNhalf : (n : Real) / 2 ≤ N := by
    have hn2kNat : 2 * k ≤ n := by omega
    have hn2k : (2 : Real) * k ≤ n := by exact_mod_cast hn2kNat
    have hNformula : N = (n : Real) - k + 1 := by
      dsimp [N]
      rw [card_confidenceCandidates hk hkn, Nat.cast_add,
        Nat.cast_sub hkn, Nat.cast_one]
    rw [hNformula]
    nlinarith
  let penaltyEvent : Set (History n k T) :=
    {h | B ≤ cumulativePenalty hkn T h}
  by_cases hlarge : delta ≤
      ((confidenceReferenceProcess P hkn).law T).real penaltyEvent
  · have hbase := lower_confidence_reference_penalty_tail
      hk hkn P B delta hcandidates hlarge
    have hDeltaEight := confidenceDelta_mul_time_div_eight
      hN_nonneg hL_nonneg hT_pos
    have hB' : B = Delta * (T : Real) / 16 := by
      simpa [B, Delta, N, L] using hB
    have hBformula :
        B = confidenceConstant / 16 * Real.sqrt (N * T * L) := by
      rw [hB']
      rw [show Delta * (T : Real) / 16 =
          (Delta * (T : Real) / 8) / 2 by ring,
        hDeltaEight]
      ring
    have hthreshold :
        (1 / (2 : Real) ^ 17) *
            Real.sqrt ((n : Real) * T * L) ≤ B := by
      rw [hBformula]
      exact confidence_budget_dominates_target
        hn_nonneg (by positivity) hL_nonneg hNhalf
    exact hbase.mono (by
      simpa [MsetsLower.Lower.confidenceTailConstant, L] using hthreshold) le_rfl
  · have hpenaltyFailure :
        ((confidenceReferenceProcess P hkn).law T).real
          {h | B ≤ cumulativePenalty hkn T h} < delta := by
      change ((confidenceReferenceProcess P hkn).law T).real penaltyEvent < delta
      exact lt_of_not_ge hlarge
    obtain ⟨hfeedback', i, hi, hprobability, hthreshold⟩ :=
      lower_confidence_stochastic_before_fixing
        hk hhalf P hdelta_pos hdelta_small hhorizon (by
          simpa [hkn, N, L, Delta, B] using hpenaltyFailure)
    have hbase := lower_confidence_planted_score_tail
      hk hkn P Delta hDelta_pos.le hsmall hfeedback' B i hi delta
        (by simpa [hkn, N, L, Delta, B] using hprobability)
    exact hbase.mono (by
      simpa [MsetsLower.Lower.confidenceTailConstant, L] using hthreshold) le_rfl

#print axioms confidenceReference_source_observation_mixture
#print axioms confidencePlanted_source_observation_mixture
#print axioms confidenceReferenceTableMixture_eq_process
#print axioms confidencePlantedTableMixture_eq_process
#print axioms exists_fixed_parametric_regret_of_ae_history_event
#print axioms ae_runLaw_protocolHistoryCompatible
#print axioms exists_fixed_reference_penalty_regret
#print axioms exists_fixed_planted_score_regret
#print axioms lower_confidence_reference_penalty_tail
#print axioms lower_confidence_planted_score_tail
#print axioms lower_confidence

end

end MsetsLower.Lower.Confidence
