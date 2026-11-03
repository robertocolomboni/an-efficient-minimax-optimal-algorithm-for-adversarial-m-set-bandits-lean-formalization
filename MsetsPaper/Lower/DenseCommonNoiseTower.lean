import MsetsPaper.Lower.DenseCommonNoiseJoint
import MsetsPaper.Lower.DenseCommonNoiseCounts
import MsetsPaper.Lower.DenseCommonNoiseSignAveraging

/-! # Fresh-noise tower calculation for the actual dense score

The lemmas in this module concern the original deterministic-table run law.
They supply the explicit one-step decomposition needed for averaging the
noise table. The full learner-score expectation theorem is assembled separately.
-/

namespace MsetsPaper.Lower.DenseCommonNoise

open MsetsLower MsetsLower.Feedback MsetsLower.Lower MeasureTheory ProbabilityTheory Set
open scoped ENNReal ProbabilityTheory BigOperators

noncomputable section

theorem integral_noiseTable_snoc {T : ℕ} {f : (Fin (T + 1) → Noise) → ℝ}
    (hf : Integrable f (noiseTableMeasure (T + 1))) :
    (∫ Z, f Z ∂noiseTableMeasure (T + 1)) =
      ∫ Z, ∫ z, f (noiseSnoc Z z) ∂noiseMeasure ∂noiseTableMeasure T := by
  let e : ((Fin T → Noise) × Noise) ≃ᵐ (Fin (T + 1) → Noise) :=
    MeasurableEquiv.prodComm.trans (noiseSplit T).symm
  have hpres : MeasurePreserving e ((noiseTableMeasure T).prod noiseMeasure)
      (noiseTableMeasure (T + 1)) := noiseSnoc_measurePreserving T
  rw [← hpres.integral_comp' f]
  exact integral_prod _ (hpres.integrable_comp_of_integrable hf)

theorem learnerScore_snoc_prefix {d m T : ℕ} (U : Signs m) (Z : Fin T → Noise) (z : Noise) :
    ∀ t : ℕ, t ≤ T → ∀ h : History d m t,
      learnerScore (U, noiseSnoc Z z) t h = learnerScore (U, Z) t h := by
  intro t
  induction t with
  | zero => intro _ h; rfl
  | succ t ih =>
      intro ht h
      simp only [learnerScore]
      rw [ih (by omega) h.1, tableNoise_snoc_prefix U Z z (by omega)]

theorem observationKernel_eq_action_map {d m : ℕ}
    (P : Policy d m) (L : LossProcess d m) (t : ℕ) (h : History d m t) :
    observationKernel P L t h =
      (P.kernel t h).map (fun a => (a, actionLoss a (L.itemLoss t h))) := by
  ext s hs
  rw [observationKernel_apply P L t h hs,
    Measure.map_apply (measurable_of_finite _) hs]
  rfl

theorem measurable_expected_actionSign {d m : ℕ} (P : Policy d m)
    (U : Fin d → ℝ) (t : ℕ) :
    Measurable (fun h : History d m t => ∫ a, actionLoss a U ∂P.kernel t h) :=
  (measurable_of_finite (fun a : MSetAction d m => actionLoss a U)).stronglyMeasurable
    |>.integral_kernel |>.measurable

theorem abs_expected_actionSign_le {d m : ℕ} (P : Policy d m)
    (U : Fin d → ℝ) (hU : ∀ i, |U i| ≤ 1) (t : ℕ) (h : History d m t) :
    |∫ a, actionLoss a U ∂P.kernel t h| ≤ (m : ℝ) := by
  simpa [Real.norm_eq_abs] using
    (norm_integral_le_of_norm_le_const (μ := P.kernel t h) (f := fun a => actionLoss a U)
      (C := (m : ℝ)) (ae_of_all _ fun a => by
        simpa only [Real.norm_eq_abs] using abs_action_sign_sum_le a U hU))

theorem integrable_expected_actionSign {d m t : ℕ} (P : Policy d m)
    (U : Fin d → ℝ) (hU : ∀ i, |U i| ≤ 1)
    (μ : Measure (History d m t)) [IsFiniteMeasure μ] :
    Integrable (fun h => ∫ a, actionLoss a U ∂P.kernel t h) μ :=
  Integrable.of_bound (measurable_expected_actionSign P U t).aestronglyMeasurable m
    (ae_of_all _ fun h => by
      simpa only [Real.norm_eq_abs] using abs_expected_actionSign_le P U hU t h)

/-- Once the table is fixed, the one-step score is the old score plus the
literal fresh-coordinate shape times the policy's expected action sign sum. -/
theorem integral_learnerScore_runLaw_snoc {d m T : ℕ}
    (P : Policy d m) (hm : 0 < m) (eta : ℝ) (heta : 0 ≤ eta) (hs : eta ≤ 1 / 16)
    (U : Signs m) (Z : Fin T → Noise) (z : Noise) :
    (∫ h, learnerScore (U, noiseSnoc Z z) (T + 1) h
      ∂runLaw P ((tableLossProcess hm eta heta hs (T + 1)).at (U, noiseSnoc Z z)) (T + 1)) =
      (∫ h, learnerScore (U, Z) T h
        ∂runLaw P ((tableLossProcess hm eta heta hs T).at (U, Z)) T) +
      shape z.val * (∫ h, ∫ a, actionLoss a (signVector U) ∂P.kernel T h
        ∂runLaw P ((tableLossProcess hm eta heta hs T).at (U, Z)) T) := by
  let L := (tableLossProcess (d := d) hm eta heta hs (T + 1)).at (U, noiseSnoc Z z)
  let μ : Measure (History d m T) := runLaw P ((tableLossProcess hm eta heta hs T).at (U, Z)) T
  letI : IsProbabilityMeasure μ := by dsimp [μ]; infer_instance
  letI : IsFiniteMeasure μ := by infer_instance
  letI : SFinite μ := by infer_instance
  have hf : Measurable (fun h : History d m (T + 1) =>
      learnerScore (U, noiseSnoc Z z) (T + 1) h) :=
    (measurable_learnerScore (T + 1)).comp (measurable_const.prodMk measurable_id)
  have hfi : Integrable (fun h : History d m (T + 1) =>
      learnerScore (U, noiseSnoc Z z) (T + 1) h) (μ ⊗ₘ observationKernel P L T) := by
    have hν : μ ⊗ₘ observationKernel P L T = runLaw P L (T + 1) := by
      rw [runLaw_succ_eq_compProd]
      congr 1
      exact (table_runLaw_snoc_prefix P hm eta heta hs U Z z).symm
    rw [hν]
    letI : IsProbabilityMeasure (runLaw P L (T + 1)) := runLaw_isProbabilityMeasure P L (T + 1)
    exact Integrable.of_bound (μ := runLaw P L (T + 1))
      hf.aestronglyMeasurable ((m : ℝ) * (T + 1))
      (ae_of_all _ fun h => by
        simpa [Real.norm_eq_abs] using abs_learnerScore_le (U, noiseSnoc Z z) (T + 1) h)
  rw [runLaw_succ_eq_compProd, table_runLaw_snoc_prefix]
  change (∫ h, learnerScore (U, noiseSnoc Z z) (T + 1) h ∂μ ⊗ₘ observationKernel P L T) = _
  have htower : (∫ h, learnerScore (U, noiseSnoc Z z) (T + 1) h
      ∂μ ⊗ₘ observationKernel P L T) =
      ∫ h, ∫ ay, learnerScore (U, noiseSnoc Z z) (T + 1) (h, ay)
        ∂observationKernel P L T h ∂μ := by
    dsimp only [μ] at hfi ⊢
    exact Measure.integral_compProd hfi
  rw [htower]
  have hinner (h : History d m T) :
      (∫ ay, learnerScore (U, noiseSnoc Z z) (T + 1) (h, ay)
        ∂observationKernel P L T h) =
      learnerScore (U, Z) T h + shape z.val * ∫ a, actionLoss a (signVector U) ∂P.kernel T h := by
    have hfay : Measurable (fun ay : MSetAction d m × ℝ =>
        learnerScore (U, noiseSnoc Z z) (T + 1) (h, ay)) := hf.comp measurable_prodMk_left
    rw [observationKernel_eq_action_map,
      integral_map (measurable_of_finite _).aemeasurable hfay.aestronglyMeasurable]
    simp only [learnerScore, learnerScore_snoc_prefix U Z z T le_rfl,
      tableNoise_snoc_last]
    rw [integral_add (integrable_const _) (Integrable.of_finite.const_mul _), integral_const_mul]
    simp
  simp_rw [hinner]
  have hprev : Integrable (fun h : History d m T => learnerScore (U, Z) T h) μ := by
    dsimp only [μ]
    exact Integrable.of_bound
      ((measurable_learnerScore T).comp (measurable_const.prodMk measurable_id)).aestronglyMeasurable
      ((m : ℝ) * T) (ae_of_all _ fun h => by
        simpa only [Real.norm_eq_abs] using abs_learnerScore_le (U, Z) T h)
  have havg : Integrable (fun h : History d m T =>
      ∫ a, actionLoss a (signVector U) ∂P.kernel T h) μ := by
    dsimp only [μ]
    exact integrable_expected_actionSign P (signVector U) (abs_signVector_le U) _
  rw [integral_add hprev (havg.const_mul _),
    integral_const_mul]

theorem abs_actionSum_le {d m : ℕ} (U : Fin d → ℝ) (hU : ∀ i, |U i| ≤ 1) :
    ∀ t : ℕ, ∀ h : History d m t,
      |History.actionSum (fun a => actionLoss a U) t h| ≤ (m : ℝ) * t := by
  intro t
  induction t with
  | zero => intro h; simp [History.actionSum]
  | succ t ih =>
      intro h
      rw [History.actionSum_succ]
      calc
        _ ≤ |History.actionSum (fun a => actionLoss a U) t h.1| + |actionLoss h.2.1 U| :=
          abs_add_le _ _
        _ ≤ (m : ℝ) * t + m := add_le_add (ih h.1) (abs_action_sign_sum_le h.2.1 U hU)
        _ = _ := by push_cast; ring

theorem integrable_tableRunIntegral {d m T : ℕ}
    (P : Policy d m) (hm : 0 < m) (eta : ℝ) (heta : 0 ≤ eta) (hs : eta ≤ 1 / 16)
    (U : Signs m) (f : (Fin T → Noise) × History d m T → ℝ)
    (hf : Measurable f) (C : ℝ) (hC : ∀ Z h, |f (Z, h)| ≤ C) :
    Integrable (fun Z => ∫ h, f (Z, h)
      ∂runLaw P ((tableLossProcess hm eta heta hs T).at (U, Z)) T) (noiseTableMeasure T) := by
  let κ := fixedSignRunKernel P hm eta heta hs U T
  have hmeas : Measurable (fun Z => ∫ h, f (Z, h) ∂κ Z) :=
    hf.stronglyMeasurable.integral_kernel_prod_right'.measurable
  have hbound (Z : Fin T → Noise) : |∫ h, f (Z, h) ∂κ Z| ≤ C := by
    dsimp [κ]
    simpa [Real.norm_eq_abs] using norm_integral_le_of_norm_le_const
      (μ := fixedSignRunKernel P hm eta heta hs U T Z) (f := fun h => f (Z, h))
      (ae_of_all _ fun h => by simpa only [Real.norm_eq_abs] using hC Z h)
  simpa only [κ, fixedSignRunKernel_apply] using
    (Integrable.of_bound (μ := noiseTableMeasure T) hmeas.aestronglyMeasurable C
      (ae_of_all _ fun Z => by simpa only [Real.norm_eq_abs] using hbound Z))

theorem integral_actionSum_runLaw_snoc {d m T : ℕ}
    (P : Policy d m) (hm : 0 < m) (eta : ℝ) (heta : 0 ≤ eta) (hs : eta ≤ 1 / 16)
    (U : Signs m) (Z : Fin T → Noise) (z : Noise) :
    (∫ h, History.actionSum (fun a => actionLoss a (signVector U)) (T + 1) h
      ∂runLaw P ((tableLossProcess hm eta heta hs (T + 1)).at (U, noiseSnoc Z z)) (T + 1)) =
      (∫ h, History.actionSum (fun a => actionLoss a (signVector U)) T h
        ∂runLaw P ((tableLossProcess hm eta heta hs T).at (U, Z)) T) +
      (∫ h, ∫ a, actionLoss a (signVector U) ∂P.kernel T h
        ∂runLaw P ((tableLossProcess hm eta heta hs T).at (U, Z)) T) := by
  let L := (tableLossProcess (d := d) hm eta heta hs (T + 1)).at (U, noiseSnoc Z z)
  let μ : Measure (History d m T) := runLaw P ((tableLossProcess hm eta heta hs T).at (U, Z)) T
  have hf := History.measurable_actionSum_of_finite
    (fun a : MSetAction d m => actionLoss a (signVector U)) (T + 1)
  have hfi : Integrable (fun h : History d m (T + 1) =>
      History.actionSum (fun a => actionLoss a (signVector U)) (T + 1) h)
      (μ ⊗ₘ observationKernel P L T) := by
    have hν : μ ⊗ₘ observationKernel P L T = runLaw P L (T + 1) := by
      rw [runLaw_succ_eq_compProd]
      congr 1
      exact (table_runLaw_snoc_prefix P hm eta heta hs U Z z).symm
    rw [hν]
    exact Integrable.of_bound (μ := runLaw P L (T + 1)) hf.aestronglyMeasurable
      ((m : ℝ) * (T + 1)) (ae_of_all _ fun h => by
        simpa [Real.norm_eq_abs] using abs_actionSum_le (signVector U) (abs_signVector_le U) (T+1) h)
  rw [runLaw_succ_eq_compProd, table_runLaw_snoc_prefix]
  change (∫ h, History.actionSum (fun a => actionLoss a (signVector U)) (T + 1) h
    ∂μ ⊗ₘ observationKernel P L T) = _
  have htower : (∫ h, History.actionSum (fun a => actionLoss a (signVector U)) (T + 1) h
      ∂μ ⊗ₘ observationKernel P L T) =
      ∫ h, ∫ ay, History.actionSum (fun a => actionLoss a (signVector U)) (T + 1) (h, ay)
        ∂observationKernel P L T h ∂μ := by
    dsimp only [μ] at hfi ⊢
    exact Measure.integral_compProd hfi
  rw [htower]
  have hinner (h : History d m T) :
      (∫ ay, History.actionSum (fun a => actionLoss a (signVector U)) (T + 1) (h, ay)
        ∂observationKernel P L T h) =
      History.actionSum (fun a => actionLoss a (signVector U)) T h +
        ∫ a, actionLoss a (signVector U) ∂P.kernel T h := by
    have hfay : Measurable (fun ay : MSetAction d m × ℝ =>
        History.actionSum (fun a => actionLoss a (signVector U)) (T + 1) (h, ay)) :=
      hf.comp measurable_prodMk_left
    rw [observationKernel_eq_action_map,
      integral_map (measurable_of_finite _).aemeasurable hfay.aestronglyMeasurable]
    simp only [History.actionSum_succ]
    rw [integral_add (integrable_const _) Integrable.of_finite]
    simp
  simp_rw [hinner]
  have hprev : Integrable (fun h : History d m T =>
      History.actionSum (fun a => actionLoss a (signVector U)) T h) μ := by
    dsimp only [μ]
    exact Integrable.of_bound
      (History.measurable_actionSum_of_finite _ T).aestronglyMeasurable ((m : ℝ) * T)
      (ae_of_all _ fun h => by
        simpa only [Real.norm_eq_abs] using abs_actionSum_le (signVector U) (abs_signVector_le U) T h)
  have havg : Integrable (fun h : History d m T =>
      ∫ a, actionLoss a (signVector U) ∂P.kernel T h) μ := by
    dsimp only [μ]
    exact integrable_expected_actionSign P (signVector U) (abs_signVector_le U) _
  exact integral_add hprev havg

end

end MsetsPaper.Lower.DenseCommonNoise
