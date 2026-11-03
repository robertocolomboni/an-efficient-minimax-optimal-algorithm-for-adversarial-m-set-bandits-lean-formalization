import MsetsPaper.Lower.DenseCommonNoiseProcess

/-!
# Finite-table/fresh-noise bridge: explicit table decomposition

This module develops the operational identification, without replacing the
uniform pre-sampled table by an assumed history law. All table coordinates are
bounded noise values and all feedbacks are computed item losses.
-/

namespace MsetsPaper.Lower.DenseCommonNoise

open MsetsLower MsetsLower.Feedback MsetsLower.Lower MeasureTheory ProbabilityTheory Set
open scoped ENNReal ProbabilityTheory BigOperators

noncomputable section

def noiseSplit (T : ℕ) : (Fin (T + 1) → Noise) ≃ᵐ (Noise × (Fin T → Noise)) :=
  MeasurableEquiv.piFinSuccAbove (fun _ => Noise) (Fin.last T)

def noiseSnoc {T : ℕ} (Z : Fin T → Noise) (z : Noise) : Fin (T + 1) → Noise :=
  (noiseSplit T).symm (z, Z)

@[simp] theorem noiseSnoc_last {T : ℕ} (Z : Fin T → Noise) (z : Noise) :
    noiseSnoc Z z (Fin.last T) = z := by
  exact Fin.insertNth_apply_same (α := fun _ : Fin (T + 1) => Noise) (Fin.last T) z Z

@[simp] theorem noiseSnoc_castSucc {T : ℕ} (Z : Fin T → Noise) (z : Noise)
    (t : Fin T) : noiseSnoc Z z t.castSucc = Z t := by
  change Fin.insertNth (α := fun _ : Fin (T + 1) => Noise)
    (Fin.last T) z Z t.castSucc = Z t
  have h := Fin.insertNth_apply_succAbove (α := fun _ : Fin (T + 1) => Noise)
    (Fin.last T) z Z t
  simpa only [Fin.succAbove_last] using h

theorem measurable_noiseSnoc (T : ℕ) :
    Measurable (fun x : (Fin T → Noise) × Noise => noiseSnoc x.1 x.2) :=
  (noiseSplit T).symm.measurable.comp measurable_swap

theorem noiseSnoc_measurePreserving (T : ℕ) :
    MeasurePreserving (fun x : (Fin T → Noise) × Noise => noiseSnoc x.1 x.2)
      ((noiseTableMeasure T).prod noiseMeasure) (noiseTableMeasure (T + 1)) := by
  have h := measurePreserving_piFinSuccAbove (fun _ : Fin (T + 1) => noiseMeasure)
    (Fin.last T)
  exact h.symm.comp Measure.measurePreserving_swap

theorem lintegral_noiseTable_snoc {T : ℕ} {f : (Fin (T + 1) → Noise) → ℝ≥0∞}
    (hf : Measurable f) :
    (∫⁻ Z, f Z ∂noiseTableMeasure (T + 1)) =
      ∫⁻ Z, ∫⁻ z, f (noiseSnoc Z z) ∂noiseMeasure ∂noiseTableMeasure T := by
  rw [← (noiseSnoc_measurePreserving T).lintegral_comp hf]
  exact MeasureTheory.lintegral_prod _ (hf.comp (measurable_noiseSnoc T)).aemeasurable

theorem tableNoise_snoc_prefix {m T t : ℕ} (U : Signs m) (Z : Fin T → Noise)
    (z : Noise) (ht : t < T) :
    tableNoise (U, noiseSnoc Z z) t = tableNoise (U, Z) t := by
  simp only [tableNoise, dif_pos ht, dif_pos (show t < T + 1 by omega)]
  exact congrArg Subtype.val (noiseSnoc_castSucc Z z ⟨t, ht⟩)

theorem tableNoise_snoc_last {m T : ℕ} (U : Signs m) (Z : Fin T → Noise) (z : Noise) :
    tableNoise (U, noiseSnoc Z z) T = z.val := by
  simp only [tableNoise, dif_pos (show T < T + 1 by omega)]
  exact congrArg Subtype.val (noiseSnoc_last Z z)

/-- Equality of deterministic loss processes up to the observation horizon
entails equality of the actual randomized-policy run laws. -/
theorem runLaw_eq_of_prefix {d m : ℕ} (P : Policy d m) (L K : LossProcess d m) :
    ∀ T : ℕ, (∀ t, t < T → ∀ h : History d m t, L.itemLoss t h = K.itemLoss t h) →
      runLaw P L T = runLaw P K T := by
  intro T
  induction T with
  | zero => intro _; rfl
  | succ T ih =>
      intro heq
      have hk : roundKernel P L T = roundKernel P K T := by
        ext h s hs
        rw [roundKernel_apply P L T h hs, roundKernel_apply P K T h hs]
        simp only [heq T (by omega) h]
      rw [runLaw_succ, runLaw_succ, ih (fun t ht => heq t (by omega)), hk]

theorem table_runLaw_snoc_prefix {d m T : ℕ}
    (P : Policy d m) (hm : 0 < m) (eta : ℝ) (heta : 0 ≤ eta) (hs : eta ≤ 1 / 16)
    (U : Signs m) (Z : Fin T → Noise) (z : Noise) :
    runLaw P ((tableLossProcess hm eta heta hs (T + 1)).at (U, noiseSnoc Z z)) T =
      runLaw P ((tableLossProcess hm eta heta hs T).at (U, Z)) T := by
  apply runLaw_eq_of_prefix
  intro t ht h
  change itemLoss m eta (tableNoise (U, noiseSnoc Z z) t) (signVector U) =
    itemLoss m eta (tableNoise (U, Z) t) (signVector U)
  rw [tableNoise_snoc_prefix U Z z ht]

def sourceObservation {d m : ℕ} (eta : ℝ) (U : Fin d → ℝ)
    (az : MSetAction d m × Noise) : MSetAction d m × ℝ :=
  (az.1, actionLoss az.1 (itemLoss m eta az.2.val U))

theorem measurable_sourceObservation {d m : ℕ} (eta : ℝ) (U : Fin d → ℝ) :
    Measurable (sourceObservation (m := m) eta U) := by
  apply measurable_fst.prodMk
  apply measurable_from_prod_countable_right
  intro a
  apply measurable_actionLoss a
  apply measurable_pi_lambda
  intro i
  unfold itemLoss shape
  fun_prop

/-- An actual policy action and an independent fresh uniform noise produce
exactly the observable kernel used in the sequential KL proof. -/
theorem sourceObservation_law {d m : ℕ} (P : Policy d m) (hm : 0 < m)
    (eta : ℝ) (heta : 0 ≤ eta) (hs : eta ≤ 1 / 16)
    (U : Fin d → ℝ) (hU : ∀ i, |U i| ≤ 1) (t : ℕ) (h : History d m t) :
    ((P.kernel t h).prod noiseMeasure).map (sourceObservation eta U) =
      observableRoundKernel P eta U t h := by
  letI := latentFeedbackKernel_isMarkov hm heta hs U hU t
  letI : IsMarkovKernel (latentRoundKernel P eta U t) := by
    unfold latentRoundKernel; infer_instance
  ext s hset
  rw [Measure.map_apply (measurable_sourceObservation eta U) hset,
    Measure.prod_apply ((measurable_sourceObservation eta U) hset),
    observableRoundKernel,
    Kernel.map_apply' _ observationShift.measurable h hset,
    latentRoundKernel, Kernel.compProd_apply (observationShift.measurable hset)]
  apply lintegral_congr
  intro a
  have hscalar : Measurable (fun z : Noise => actionLoss a (itemLoss m eta z.val U)) := by
    exact measurable_snd.comp ((measurable_sourceObservation eta U).comp
      (measurable_const.prodMk measurable_id))
  have heq := congrArg (fun μ : Measure ℝ => μ (Prod.mk a ⁻¹' s))
    (actual_feedback_law hm heta hs U hU a)
  rw [Measure.map_apply hscalar (measurable_prodMk_left hset), feedbackLaw,
    Measure.map_apply feedbackShift.measurable (measurable_prodMk_left hset)] at heq
  exact heq

/-- Averaging the final table coordinate is the fresh-noise observable kernel.
The order action/noise is exchanged only under their independent product law. -/
theorem average_snoc_observationKernel {d m T : ℕ}
    (P : Policy d m) (hm : 0 < m) (eta : ℝ) (heta : 0 ≤ eta) (hs : eta ≤ 1 / 16)
    (U : Signs m) (Z : Fin T → Noise) (h : History d m T)
    (s : Set (MSetAction d m × ℝ)) (hset : MeasurableSet s) :
    (∫⁻ z, observationKernel P
      ((tableLossProcess hm eta heta hs (T + 1)).at (U, noiseSnoc Z z)) T h s
      ∂noiseMeasure) = observableRoundKernel P eta (signVector U) T h s := by
  let g := sourceObservation (m := m) eta (signVector (d := d) U)
  have hg : Measurable g := measurable_sourceObservation eta (signVector U)
  have hmap : ∀ z : Noise, observationKernel P
      ((tableLossProcess hm eta heta hs (T + 1)).at (U, noiseSnoc Z z)) T h s =
        (P.kernel T h) {a | g (a, z) ∈ s} := by
    intro z
    rw [observationKernel_apply _ _ _ _ hset]
    congr 1
    ext a
    change (a, actionLoss a (itemLoss m eta (tableNoise (U, noiseSnoc Z z) T)
      (signVector U))) ∈ s ↔ g (a, z) ∈ s
    rw [tableNoise_snoc_last]
    rfl
  simp_rw [hmap]
  calc
    _ = ((P.kernel T h).prod noiseMeasure) (g ⁻¹' s) :=
      (Measure.prod_apply_symm (hg hset)).symm
    _ = (((P.kernel T h).prod noiseMeasure).map g) s :=
      (Measure.map_apply hg hset).symm
    _ = _ := congrArg (fun μ : Measure (MSetAction d m × ℝ) => μ s)
      (sourceObservation_law P hm eta heta hs (signVector U) (abs_signVector_le U) T h)

def fixedSignRunKernel {d m : ℕ} (P : Policy d m) (hm : 0 < m)
    (eta : ℝ) (heta : 0 ≤ eta) (hs : eta ≤ 1 / 16) (U : Signs m) (T : ℕ) :
    Kernel (Fin T → Noise) (History d m T) :=
  (parametricRunKernel P (tableLossProcess hm eta heta hs T) T).comap
    (fun Z => (U, Z)) (measurable_const.prodMk measurable_id)

instance fixedSignRunKernel_isMarkov {d m : ℕ} (P : Policy d m) (hm : 0 < m)
    (eta : ℝ) (heta : 0 ≤ eta) (hs : eta ≤ 1 / 16) (U : Signs m) (T : ℕ) :
    IsMarkovKernel (fixedSignRunKernel P hm eta heta hs U T) := by
  letI := parametricRunKernel_isMarkov P (tableLossProcess hm eta heta hs T) T
  unfold fixedSignRunKernel
  infer_instance

@[simp] theorem fixedSignRunKernel_apply {d m T : ℕ} (P : Policy d m) (hm : 0 < m)
    (eta : ℝ) (heta : 0 ≤ eta) (hs : eta ≤ 1 / 16) (U : Signs m) (Z : Fin T → Noise) :
    fixedSignRunKernel P hm eta heta hs U T Z =
      runLaw P ((tableLossProcess hm eta heta hs T).at (U, Z)) T :=
  parametricRunKernel_apply _ _ _ _

@[simp] theorem fixedSignRunKernel_apply_set {d m T : ℕ} (P : Policy d m) (hm : 0 < m)
    (eta : ℝ) (heta : 0 ≤ eta) (hs : eta ≤ 1 / 16) (U : Signs m) (Z : Fin T → Noise)
    (s : Set (History d m T)) :
    fixedSignRunKernel P hm eta heta hs U T Z s =
      runLaw P ((tableLossProcess hm eta heta hs T).at (U, Z)) T s :=
  congrArg (fun μ : Measure (History d m T) => μ s)
    (fixedSignRunKernel_apply P hm eta heta hs U Z)

def noiseMixture {d m : ℕ} (P : Policy d m) (hm : 0 < m)
    (eta : ℝ) (heta : 0 ≤ eta) (hs : eta ≤ 1 / 16) (U : Signs m) (T : ℕ) :
    Measure (History d m T) :=
  fixedSignRunKernel P hm eta heta hs U T ∘ₘ noiseTableMeasure T

instance noiseMixture_isProbabilityMeasure {d m : ℕ} (P : Policy d m) (hm : 0 < m)
    (eta : ℝ) (heta : 0 ≤ eta) (hs : eta ≤ 1 / 16) (U : Signs m) (T : ℕ) :
    IsProbabilityMeasure (noiseMixture P hm eta heta hs U T) := by
  unfold noiseMixture
  infer_instance

theorem swap_snoc_observation {d m T : ℕ} (P : Policy d m) (hm : 0 < m)
    (eta : ℝ) (heta : 0 ≤ eta) (hs : eta ≤ 1 / 16) (U : Signs m) (Z : Fin T → Noise)
    (μ : Measure (History d m T)) [SFinite μ]
    (s : Set (History d m (T + 1))) (hset : MeasurableSet s) :
    (∫⁻ z, ∫⁻ h, observationKernel P
      ((tableLossProcess hm eta heta hs (T + 1)).at (U, noiseSnoc Z z)) T h
      (Prod.mk h ⁻¹' s) ∂μ ∂noiseMeasure) =
      ∫⁻ h, ∫⁻ z, observationKernel P
        ((tableLossProcess hm eta heta hs (T + 1)).at (U, noiseSnoc Z z)) T h
        (Prod.mk h ⁻¹' s) ∂noiseMeasure ∂μ := by
  let L := tableLossProcess (d := d) hm eta heta hs (T + 1)
  let f : Noise × History d m T → ℝ≥0∞ := fun x =>
    observationKernel P (L.at (U, noiseSnoc Z x.1)) T x.2 (Prod.mk x.2 ⁻¹' s)
  have hfeq : f = fun x => parametricRoundKernel P L T ((U, noiseSnoc Z x.1), x.2) s := by
    funext x
    rw [parametricRoundKernel_apply]
    rw [roundKernel_apply P _ T x.2 hset]
    exact observationKernel_apply P _ T x.2 (measurable_prodMk_left hset)
  have hinput : Measurable (fun x : Noise × History d m T =>
      ((U, noiseSnoc Z x.1), x.2)) :=
    (measurable_const.prodMk ((measurable_noiseSnoc T).comp
      (measurable_const.prodMk measurable_fst))).prodMk measurable_snd
  have hf : Measurable f := by
    rw [hfeq]
    exact (Kernel.measurable_coe (parametricRoundKernel P L T) hset).comp hinput
  calc
    _ = ∫⁻ x, f x ∂noiseMeasure.prod μ :=
      (MeasureTheory.lintegral_prod _ hf.aemeasurable).symm
    _ = _ := MeasureTheory.lintegral_prod_symm' f hf

/-- Exact identity of the finite uniform-table mixture and fresh-noise
observable histories, for every policy and every fixed sign vector. -/
theorem noiseMixture_eq_observableProcess {d m : ℕ} (P : Policy d m) (hm : 0 < m)
    (eta : ℝ) (heta : 0 ≤ eta) (hs : eta ≤ 1 / 16) (U : Signs m) :
    ∀ T : ℕ, noiseMixture P hm eta heta hs U T =
      (observableProcess P hm eta heta hs (signVector U) (abs_signVector_le U)).law T := by
  intro T
  induction T with
  | zero =>
      ext s hset
      rw [noiseMixture, Measure.bind_apply hset (Kernel.aemeasurable _)]
      simp_rw [fixedSignRunKernel_apply_set (T := 0) P hm eta heta hs U]
      simp [runLaw, HistoryKernelProcess.law]
  | succ T ih =>
      letI := observableRoundKernel_isMarkov P hm heta hs
        (signVector U) (abs_signVector_le U) T
      ext s hset
      rw [noiseMixture, Measure.bind_apply hset (Kernel.aemeasurable _),
        lintegral_noiseTable_snoc (Kernel.measurable_coe _ hset)]
      simp_rw [fixedSignRunKernel_apply_set (T := T + 1) P hm eta heta hs U]
      have hsucc (Z : Fin T → Noise) (z : Noise) :
          runLaw P ((tableLossProcess hm eta heta hs (T + 1)).at (U, noiseSnoc Z z))
              (T + 1) s =
            ∫⁻ h, observationKernel P
              ((tableLossProcess hm eta heta hs (T + 1)).at (U, noiseSnoc Z z)) T h
              (Prod.mk h ⁻¹' s)
              ∂runLaw P ((tableLossProcess hm eta heta hs T).at (U, Z)) T := by
        rw [runLaw_succ_eq_compProd, table_runLaw_snoc_prefix]
        exact Measure.compProd_apply hset
      simp_rw [hsucc, swap_snoc_observation P hm eta heta hs U _ _ s hset]
      have hobs (Z : Fin T → Noise) (h : History d m T) :=
        average_snoc_observationKernel P hm eta heta hs U Z h
          (Prod.mk h ⁻¹' s) (measurable_prodMk_left hset)
      simp_rw [hobs]
      have hq : Measurable (fun h : History d m T =>
          observableRoundKernel P eta (signVector U) T h (Prod.mk h ⁻¹' s)) :=
        Kernel.measurable_kernel_prodMk_left (κ := observableRoundKernel P eta (signVector U) T) hset
      simp_rw [← fixedSignRunKernel_apply P hm eta heta hs U]
      rw [← Measure.lintegral_bind (Kernel.aemeasurable _) hq.aemeasurable]
      change (∫⁻ h, observableRoundKernel P eta (signVector U) T h (Prod.mk h ⁻¹' s)
        ∂noiseMixture P hm eta heta hs U T) = _
      rw [ih, HistoryKernelProcess.law_succ]
      change (∫⁻ h, observableRoundKernel P eta (signVector U) T h (Prod.mk h ⁻¹' s)
        ∂(observableProcess P hm eta heta hs (signVector U) (abs_signVector_le U)).law T) =
        (((observableProcess P hm eta heta hs (signVector U) (abs_signVector_le U)).law T) ⊗ₘ
          observableRoundKernel P eta (signVector U) T) s
      rw [Measure.compProd_apply hset]

end

end MsetsPaper.Lower.DenseCommonNoise
