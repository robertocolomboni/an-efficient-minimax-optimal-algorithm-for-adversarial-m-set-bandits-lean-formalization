import MsetsPaper.Lower.SparseCappedInformation
import MsetsPaper.Lower.DenseCommonNoiseTableBridge

/-!
# Finite-table/fresh-noise bridge: explicit table decomposition

This module develops the operational identification, without replacing the
uniform pre-sampled table by an assumed history law. All table coordinates are
bounded noise values and all feedbacks are computed item losses.
-/

namespace MsetsPaper.Lower.SparseCapped

open MsetsLower MsetsLower.Feedback MsetsLower.Lower MeasureTheory ProbabilityTheory Set
open scoped ENNReal ProbabilityTheory BigOperators

noncomputable section

open DenseCommonNoise (noiseSnoc noiseSnoc_castSucc noiseSnoc_last
  measurable_noiseSnoc noiseMeasure noiseTableMeasure lintegral_noiseTable_snoc
  runLaw_eq_of_prefix observationShift feedbackShift)

theorem tableNoise_snoc_prefix {d T t : ℕ} (U : Bits d) (Z : Fin T → Noise)
    (z : Noise) (ht : t < T) :
    tableNoise (U, noiseSnoc Z z) t = tableNoise (U, Z) t := by
  simp only [tableNoise, dif_pos ht, dif_pos (show t < T + 1 by omega)]
  exact congrArg Subtype.val (noiseSnoc_castSucc Z z ⟨t, ht⟩)

theorem tableNoise_snoc_last {d T : ℕ} (U : Bits d) (Z : Fin T → Noise) (z : Noise) :
    tableNoise (U, noiseSnoc Z z) T = z.val := by
  simp only [tableNoise, dif_pos (show T < T + 1 by omega)]
  exact congrArg Subtype.val (noiseSnoc_last Z z)

theorem table_runLaw_snoc_prefix {d m T : ℕ}
    (P : Policy d m) (hm : 0 < m) (c : ℕ) (eta : ℝ) (heta : 0 ≤ eta) (hs : eta ≤ 1 / 16)
    (U : Bits d) (Z : Fin T → Noise) (z : Noise) :
    runLaw P ((tableLossProcess hm c eta heta hs (T + 1)).at (U, noiseSnoc Z z)) T =
      runLaw P ((tableLossProcess hm c eta heta hs T).at (U, Z)) T := by
  apply runLaw_eq_of_prefix
  intro t ht h
  change itemLoss c eta (tableNoise (U, noiseSnoc Z z) t) U t h =
    itemLoss c eta (tableNoise (U, Z) t) U t h
  rw [tableNoise_snoc_prefix U Z z ht]

/-- Fresh source observation with the active mask frozen at the previous history. -/
def sourceObservation {d m : ℕ} (c : ℕ) (eta : ℝ) (U : Bits d)
    (t : ℕ) (h : History d m t)
    (az : MSetAction d m × Noise) : MSetAction d m × ℝ :=
  DenseCommonNoise.sourceObservation eta (activeVector c U t h) az

theorem measurable_sourceObservation {d m : ℕ} (c : ℕ) (eta : ℝ) (U : Bits d)
    (t : ℕ) (h : History d m t) :
    Measurable (sourceObservation c eta U t h) :=
  DenseCommonNoise.measurable_sourceObservation eta (activeVector c U t h)

/-- The common randomized policy kernel is unchanged between the two bit worlds. -/
theorem sourceObservation_law {d m : ℕ} (P : Policy d m) (hm : 0 < m) (c : ℕ)
    (eta : ℝ) (heta : 0 ≤ eta) (hs : eta ≤ 1 / 16)
    (U : Bits d) (t : ℕ) (h : History d m t) :
    ((P.kernel t h).prod noiseMeasure).map (sourceObservation c eta U t h) =
      observableRoundKernel P c eta U t h := by
  letI := latentFeedbackKernel_isMarkov hm c heta hs U t
  letI : IsMarkovKernel (latentRoundKernel P c eta U t) := by
    unfold latentRoundKernel; infer_instance
  ext s hset
  rw [Measure.map_apply (measurable_sourceObservation c eta U t h) hset,
    Measure.prod_apply ((measurable_sourceObservation c eta U t h) hset),
    observableRoundKernel,
    Kernel.map_apply' _ observationShift.measurable h hset,
    latentRoundKernel, Kernel.compProd_apply (observationShift.measurable hset)]
  apply lintegral_congr
  intro a
  have hscalar : Measurable (fun z : Noise => actionLoss a (itemLoss c eta z.val U t h)) :=
    measurable_snd.comp ((measurable_sourceObservation c eta U t h).comp
      (measurable_const.prodMk measurable_id))
  have heq := congrArg (fun μ : Measure ℝ => μ (Prod.mk a ⁻¹' s))
    (actual_feedback_law hm c heta hs U t h a)
  rw [Measure.map_apply hscalar (measurable_prodMk_left hset),
    Measure.map_apply feedbackShift.measurable (measurable_prodMk_left hset)] at heq
  exact heq

/-- Averaging the final table coordinate is the fresh-noise observable kernel.
The order action/noise is exchanged only under their independent product law. -/
theorem average_snoc_observationKernel {d m T : ℕ}
    (P : Policy d m) (hm : 0 < m) (c : ℕ) (eta : ℝ) (heta : 0 ≤ eta) (hs : eta ≤ 1 / 16)
    (U : Bits d) (Z : Fin T → Noise) (h : History d m T)
    (s : Set (MSetAction d m × ℝ)) (hset : MeasurableSet s) :
    (∫⁻ z, observationKernel P
      ((tableLossProcess hm c eta heta hs (T + 1)).at (U, noiseSnoc Z z)) T h s
      ∂noiseMeasure) = observableRoundKernel P c eta U T h s := by
  let g := sourceObservation c eta U T h
  have hg : Measurable g := measurable_sourceObservation c eta U T h
  have hmap : ∀ z : Noise, observationKernel P
      ((tableLossProcess hm c eta heta hs (T + 1)).at (U, noiseSnoc Z z)) T h s =
        (P.kernel T h) {a | g (a, z) ∈ s} := by
    intro z
    rw [observationKernel_apply _ _ _ _ hset]
    congr 1
    ext a
    change (a, actionLoss a (itemLoss c eta (tableNoise (U, noiseSnoc Z z) T) U T h)) ∈ s ↔
      g (a, z) ∈ s
    rw [tableNoise_snoc_last]
    rfl
  simp_rw [hmap]
  calc
    _ = ((P.kernel T h).prod noiseMeasure) (g ⁻¹' s) :=
      (Measure.prod_apply_symm (hg hset)).symm
    _ = (((P.kernel T h).prod noiseMeasure).map g) s :=
      (Measure.map_apply hg hset).symm
    _ = _ := congrArg (fun μ : Measure (MSetAction d m × ℝ) => μ s)
      (sourceObservation_law P hm c eta heta hs U T h)

def fixedBitsRunKernel {d m : ℕ} (P : Policy d m) (hm : 0 < m) (c : ℕ)
    (eta : ℝ) (heta : 0 ≤ eta) (hs : eta ≤ 1 / 16) (U : Bits d) (T : ℕ) :
    Kernel (Fin T → Noise) (History d m T) :=
  (parametricRunKernel P (tableLossProcess hm c eta heta hs T) T).comap
    (fun Z => (U, Z)) (measurable_const.prodMk measurable_id)

instance fixedBitsRunKernel_isMarkov {d m : ℕ} (P : Policy d m) (hm : 0 < m) (c : ℕ)
    (eta : ℝ) (heta : 0 ≤ eta) (hs : eta ≤ 1 / 16) (U : Bits d) (T : ℕ) :
    IsMarkovKernel (fixedBitsRunKernel P hm c eta heta hs U T) := by
  letI := parametricRunKernel_isMarkov P (tableLossProcess hm c eta heta hs T) T
  unfold fixedBitsRunKernel
  infer_instance

@[simp] theorem fixedBitsRunKernel_apply {d m T : ℕ} (P : Policy d m) (hm : 0 < m) (c : ℕ)
    (eta : ℝ) (heta : 0 ≤ eta) (hs : eta ≤ 1 / 16) (U : Bits d) (Z : Fin T → Noise) :
    fixedBitsRunKernel P hm c eta heta hs U T Z =
      runLaw P ((tableLossProcess hm c eta heta hs T).at (U, Z)) T :=
  parametricRunKernel_apply _ _ _ _

@[simp] theorem fixedBitsRunKernel_apply_set {d m T : ℕ} (P : Policy d m) (hm : 0 < m)
    (c : ℕ) (eta : ℝ) (heta : 0 ≤ eta) (hs : eta ≤ 1 / 16) (U : Bits d)
    (Z : Fin T → Noise) (s : Set (History d m T)) :
    fixedBitsRunKernel P hm c eta heta hs U T Z s =
      runLaw P ((tableLossProcess hm c eta heta hs T).at (U, Z)) T s :=
  congrArg (fun μ : Measure (History d m T) => μ s)
    (fixedBitsRunKernel_apply P hm c eta heta hs U Z)

def noiseMixture {d m : ℕ} (P : Policy d m) (hm : 0 < m) (c : ℕ)
    (eta : ℝ) (heta : 0 ≤ eta) (hs : eta ≤ 1 / 16) (U : Bits d) (T : ℕ) :
    Measure (History d m T) :=
  fixedBitsRunKernel P hm c eta heta hs U T ∘ₘ noiseTableMeasure T

instance noiseMixture_isProbabilityMeasure {d m : ℕ} (P : Policy d m) (hm : 0 < m) (c : ℕ)
    (eta : ℝ) (heta : 0 ≤ eta) (hs : eta ≤ 1 / 16) (U : Bits d) (T : ℕ) :
    IsProbabilityMeasure (noiseMixture P hm c eta heta hs U T) := by
  unfold noiseMixture
  infer_instance

theorem swap_snoc_observation {d m T : ℕ} (P : Policy d m) (hm : 0 < m) (c : ℕ)
    (eta : ℝ) (heta : 0 ≤ eta) (hs : eta ≤ 1 / 16) (U : Bits d) (Z : Fin T → Noise)
    (μ : Measure (History d m T)) [SFinite μ]
    (s : Set (History d m (T + 1))) (hset : MeasurableSet s) :
    (∫⁻ z, ∫⁻ h, observationKernel P
      ((tableLossProcess hm c eta heta hs (T + 1)).at (U, noiseSnoc Z z)) T h
      (Prod.mk h ⁻¹' s) ∂μ ∂noiseMeasure) =
      ∫⁻ h, ∫⁻ z, observationKernel P
        ((tableLossProcess hm c eta heta hs (T + 1)).at (U, noiseSnoc Z z)) T h
        (Prod.mk h ⁻¹' s) ∂noiseMeasure ∂μ := by
  let L := tableLossProcess (d := d) hm c eta heta hs (T + 1)
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
observable histories, for every policy and every fixed bit vector. -/
theorem noiseMixture_eq_observableProcess {d m : ℕ} (P : Policy d m) (hm : 0 < m) (c : ℕ)
    (eta : ℝ) (heta : 0 ≤ eta) (hs : eta ≤ 1 / 16) (U : Bits d) :
    ∀ T : ℕ, noiseMixture P hm c eta heta hs U T =
      (observableProcess P hm c eta heta hs U).law T := by
  intro T
  induction T with
  | zero =>
      ext s hset
      rw [noiseMixture, Measure.bind_apply hset (Kernel.aemeasurable _)]
      simp_rw [fixedBitsRunKernel_apply_set (T := 0) P hm c eta heta hs U]
      simp [runLaw, HistoryKernelProcess.law]
  | succ T ih =>
      letI := observableRoundKernel_isMarkov P hm c heta hs U T
      ext s hset
      rw [noiseMixture, Measure.bind_apply hset (Kernel.aemeasurable _),
        lintegral_noiseTable_snoc (Kernel.measurable_coe _ hset)]
      simp_rw [fixedBitsRunKernel_apply_set (T := T + 1) P hm c eta heta hs U]
      have hsucc (Z : Fin T → Noise) (z : Noise) :
          runLaw P ((tableLossProcess hm c eta heta hs (T + 1)).at (U, noiseSnoc Z z))
              (T + 1) s =
            ∫⁻ h, observationKernel P
              ((tableLossProcess hm c eta heta hs (T + 1)).at (U, noiseSnoc Z z)) T h
              (Prod.mk h ⁻¹' s)
              ∂runLaw P ((tableLossProcess hm c eta heta hs T).at (U, Z)) T := by
        rw [runLaw_succ_eq_compProd, table_runLaw_snoc_prefix]
        exact Measure.compProd_apply hset
      simp_rw [hsucc, swap_snoc_observation P hm c eta heta hs U _ _ s hset]
      have hobs (Z : Fin T → Noise) (h : History d m T) :=
        average_snoc_observationKernel P hm c eta heta hs U Z h
          (Prod.mk h ⁻¹' s) (measurable_prodMk_left hset)
      simp_rw [hobs]
      have hq : Measurable (fun h : History d m T =>
          observableRoundKernel P c eta U T h (Prod.mk h ⁻¹' s)) :=
        Kernel.measurable_kernel_prodMk_left (κ := observableRoundKernel P c eta U T) hset
      simp_rw [← fixedBitsRunKernel_apply P hm c eta heta hs U]
      rw [← Measure.lintegral_bind (Kernel.aemeasurable _) hq.aemeasurable]
      change (∫⁻ h, observableRoundKernel P c eta U T h (Prod.mk h ⁻¹' s)
        ∂noiseMixture P hm c eta heta hs U T) = _
      rw [ih, HistoryKernelProcess.law_succ]
      change (∫⁻ h, observableRoundKernel P c eta U T h (Prod.mk h ⁻¹' s)
        ∂(observableProcess P hm c eta heta hs U).law T) =
        (((observableProcess P hm c eta heta hs U).law T) ⊗ₘ
          observableRoundKernel P c eta U T) s
      rw [Measure.compProd_apply hset]

theorem noiseMixture_bit_KL_le_expectedCappedCount {d m T : ℕ}
    (P : Policy d m) (hm : 0 < m) (hmd : m ≤ d) (c : ℕ)
    {eta : ℝ} (heta : 0 ≤ eta) (hs : eta ≤ 1 / 16) (U : Bits d) (i : Fin d) :
    InformationTheory.klDiv
      (noiseMixture P hm c eta heta hs (Function.update U i false) T)
      (noiseMixture P hm c eta heta hs (Function.update U i true) T) ≤
      ENNReal.ofReal (128 * (eta / m) ^ 2) *
        ENNReal.ofReal (∫ h, (cappedCount c i T h : ℝ)
          ∂noiseMixture P hm c eta heta hs (Function.update U i false) T) := by
  simp_rw [noiseMixture_eq_observableProcess]
  exact observable_bit_KL_le_expectedCappedCount P hm hmd c heta hs U i

/-- The displayed information budget for the original finite-table experiment. -/
theorem noiseMixture_bit_KL_le_log {d m T : ℕ}
    (P : Policy d m) (hm : 0 < m) (hmd : m ≤ d) (hT : 64 * d ^ 2 ≤ T)
    (U : Bits d) (i : Fin d) :
    InformationTheory.klDiv
      (noiseMixture P hm (selectionCap d m T) (perturbation d m T)
        (perturbation_nonneg d m T) (perturbation_lt_sixteenth hm hmd hT).le
        (Function.update U i false) T)
      (noiseMixture P hm (selectionCap d m T) (perturbation d m T)
        (perturbation_nonneg d m T) (perturbation_lt_sixteenth hm hmd hT).le
        (Function.update U i true) T) ≤
      ENNReal.ofReal ((1 / (2 : ℝ) ^ 29) * Real.log (1 / ratio d m)) := by
  simp_rw [noiseMixture_eq_observableProcess]
  convert observable_bit_KL_le_cap (T := T) P hm hmd (selectionCap d m T)
    (perturbation_nonneg d m T) (perturbation_lt_sixteenth hm hmd hT).le U i using 1
  rw [capped_bit_budget_identity hm hmd hT]

end

end MsetsPaper.Lower.SparseCapped


