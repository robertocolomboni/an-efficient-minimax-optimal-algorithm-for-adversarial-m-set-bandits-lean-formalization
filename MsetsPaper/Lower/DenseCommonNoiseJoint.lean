import MsetsPaper.Lower.DenseCommonNoiseMoments
import Mathlib.Probability.Kernel.Composition.IntegralCompProd

/-! # Genuine joint-law score statistics and their integrability -/

namespace MsetsPaper.Lower.DenseCommonNoise

open MsetsLower MsetsLower.Feedback MsetsLower.Lower MeasureTheory ProbabilityTheory Set
open scoped ENNReal ProbabilityTheory BigOperators

noncomputable section

theorem jointLaw_eq_compProd {d m : ℕ} (P : Policy d m) (hm : 0 < m)
    (eta : ℝ) (heta : 0 ≤ eta) (hs : eta ≤ 1 / 16) (T t : ℕ) :
    jointLaw P hm eta heta hs T t =
      tableMeasure m T ⊗ₘ parametricRunKernel P (tableLossProcess hm eta heta hs T) t := by
  letI := parametricRunKernel_isMarkov P (tableLossProcess hm eta heta hs T) t
  ext s hset
  rw [jointLaw, Measure.bind_apply hset (Kernel.aemeasurable _), Measure.compProd_apply hset]
  apply lintegral_congr
  intro xi
  rw [parametricRunWithParameterKernel_apply,
    Measure.map_apply measurable_prodMk_left hset, parametricRunKernel_apply]

theorem jointLaw_map_table {d m : ℕ} (P : Policy d m) (hm : 0 < m)
    (eta : ℝ) (heta : 0 ≤ eta) (hs : eta ≤ 1 / 16) (T t : ℕ) :
    (jointLaw P hm eta heta hs T t).map Prod.fst = tableMeasure m T := by
  letI := parametricRunKernel_isMarkov P (tableLossProcess hm eta heta hs T) t
  rw [jointLaw_eq_compProd]
  exact Measure.fst_compProd _ _

theorem measurable_shapeSum {m T : ℕ} (t : ℕ) :
    Measurable (fun xi : Table m T => shapeSum xi t) := by
  unfold shapeSum
  exact Finset.measurable_sum _ fun r _ => measurable_shape.comp (measurable_tableNoise r)

theorem measurable_comparatorScore {d m T : ℕ} (h2m : 2 * m ≤ d) (t : ℕ) :
    Measurable (fun xi : Table m T => pairedSignScore h2m (signVector xi.1) * shapeSum xi t) :=
  ((measurable_of_finite (fun U : Signs m => pairedSignScore h2m (signVector U))).comp
    measurable_fst).mul (measurable_shapeSum t)

set_option maxHeartbeats 800000 in
-- The recursive history measurability proof needs additional elaboration time in Lean 4.35.
theorem measurable_learnerScore {d m T : ℕ} :
    ∀ t : ℕ, Measurable (fun x : Table m T × History d m t => learnerScore x.1 t x.2) := by
  intro t
  induction t with
  | zero => exact measurable_const
  | succ t ih =>
      have hp : Measurable (fun x : Table m T × History d m (t + 1) =>
          (x.1, x.2.1)) := measurable_fst.prodMk measurable_snd.fst
      have ha : Measurable (fun x : Table m T × History d m (t + 1) =>
          (x.1.1, x.2.2.1)) := measurable_fst.fst.prodMk measurable_snd.snd.fst
      change Measurable (fun x : Table m T × History d m (t + 1) =>
        learnerScore x.1 t x.2.1 +
          shape (tableNoise x.1 t) * actionLoss x.2.2.1 (signVector x.1.1))
      have hshape : Measurable (fun x : Table m T × History d m (t + 1) =>
          shape (tableNoise x.1 t)) :=
        (measurable_shape.comp (measurable_tableNoise (m := m) (T := T) t)).comp
          measurable_fst
      have hsign : Measurable (fun ua : Signs m × MSetAction d m =>
          actionLoss ua.2 (signVector ua.1)) := measurable_of_finite _
      exact (ih.comp hp).add (hshape.mul (hsign.comp ha))

theorem measurable_deficit {d m T : ℕ} (h2m : 2 * m ≤ d) (t : ℕ) :
    Measurable (fun x : Table m T × History d m t => deficit h2m x.1 t x.2) :=
  ((measurable_comparatorScore h2m t).comp measurable_fst).sub (measurable_learnerScore t)

theorem abs_comparatorScore_le {d m T : ℕ} (h2m : 2 * m ≤ d) (xi : Table m T) (t : ℕ) :
    |pairedSignScore h2m (signVector xi.1) * shapeSum xi t| ≤ (m : ℝ) * t := by
  have hG := shapeSum_mem_Icc xi t
  have hsign : |pairedSignScore h2m (signVector xi.1)| ≤ (m : ℝ) := by
    rw [← actionLoss_pairedComparator]
    exact abs_action_sign_sum_le _ _ (abs_signVector_le xi.1)
  rw [abs_mul, abs_of_nonneg hG.1]
  exact mul_le_mul hsign hG.2 hG.1 (Nat.cast_nonneg m)

theorem integrable_learnerScore {d m T t : ℕ}
    (μ : Measure (Table m T × History d m t)) [IsFiniteMeasure μ] :
    Integrable (fun x => learnerScore x.1 t x.2) μ :=
  Integrable.of_bound (measurable_learnerScore t).aestronglyMeasurable ((m : ℝ) * t)
    (ae_of_all _ fun x => by simpa only [Real.norm_eq_abs] using abs_learnerScore_le x.1 t x.2)

theorem integrable_comparatorScore {d m T t : ℕ} (h2m : 2 * m ≤ d)
    (μ : Measure (Table m T × History d m t)) [IsFiniteMeasure μ] :
    Integrable (fun x => pairedSignScore h2m (signVector x.1.1) * shapeSum x.1 t) μ :=
  Integrable.of_bound ((measurable_comparatorScore h2m t).comp measurable_fst).aestronglyMeasurable
    ((m : ℝ) * t) (ae_of_all _ fun x => by
      simpa only [Real.norm_eq_abs] using abs_comparatorScore_le h2m x.1 t)

theorem integrable_deficit {d m T t : ℕ} (h2m : 2 * m ≤ d)
    (μ : Measure (Table m T × History d m t)) [IsFiniteMeasure μ] :
    Integrable (fun x => deficit h2m x.1 t x.2) μ :=
  (integrable_comparatorScore h2m μ).sub (integrable_learnerScore μ)

/-- The comparator calculation remains true in the full interaction law,
including the learner's private randomization. -/
theorem integral_comparatorScore_joint {d m T : ℕ}
    (P : Policy d m) (hm : 0 < m) (h2m : 2 * m ≤ d)
    (eta : ℝ) (heta : 0 ≤ eta) (hs : eta ≤ 1 / 16) :
    (∫ x, pairedSignScore h2m (signVector x.1.1) * shapeSum x.1 T
      ∂jointLaw P hm eta heta hs T T) = (m : ℝ) * T / 3 := by
  rw [← integral_comparatorScore h2m]
  rw [← jointLaw_map_table P hm eta heta hs T T]
  exact (integral_map measurable_fst.aemeasurable
    (measurable_comparatorScore h2m T).aestronglyMeasurable).symm

end

end MsetsPaper.Lower.DenseCommonNoise
