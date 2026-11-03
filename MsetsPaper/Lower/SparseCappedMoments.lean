import MsetsPaper.Lower.SparseCappedLaw
import MsetsPaper.Lower.SparseCappedParameters
import MsetsPaper.Lower.DenseCommonNoiseMoments

/-! # Score measurability and genuine joint-law expectations for P2 -/

namespace MsetsPaper.Lower.SparseCapped

open MsetsLower MsetsLower.History MsetsLower.Feedback MsetsLower.Lower
open MeasureTheory ProbabilityTheory Set
open scoped BigOperators ProbabilityTheory

noncomputable section

theorem measurable_activeVector_joint {d m T : ℕ} (c t : ℕ) :
    Measurable (fun x : Table d T × History d m t => activeVector c x.1.1 t x.2) := by
  apply measurable_pi_lambda
  intro i
  exact ((measurable_activeIndicator c t i).comp measurable_snd).mul
    ((measurable_of_finite (fun U : Bits d => bitValue (U i))).comp measurable_fst.fst)

theorem measurable_itemScore {d m T : ℕ} (c : ℕ) (i : Fin d) :
    ∀ t, Measurable (fun x : Table d T × History d m t => itemScore c x.1 t x.2 i) := by
  intro t
  induction t with
  | zero => exact measurable_const
  | succ t ih =>
    have hp : Measurable (fun x : Table d T × History d m (t + 1) => (x.1, x.2.1)) :=
      measurable_fst.prodMk measurable_snd.fst
    exact (ih.comp hp).add
      (((measurable_shape.comp (measurable_tableNoise t)).comp measurable_fst).mul
        (((measurable_activeVector_joint c t).eval (a := i)).comp hp))

set_option maxHeartbeats 800000 in
-- The recursive history measurability proof needs additional elaboration time in Lean 4.35.
theorem measurable_learnerScore {d m T : ℕ} (c : ℕ) :
    ∀ t, Measurable (fun x : Table d T × History d m t => learnerScore c x.1 t x.2) := by
  intro t
  induction t with
  | zero => exact measurable_const
  | succ t ih =>
    have hp : Measurable (fun x : Table d T × History d m (t + 1) => (x.1, x.2.1)) :=
      measurable_fst.prodMk measurable_snd.fst
    have hpa : Measurable (fun x : Table d T × History d m (t + 1) =>
        ((x.1, x.2.1), x.2.2.1)) := hp.prodMk measurable_snd.snd.fst
    exact (ih.comp hp).add
      (((measurable_shape.comp (measurable_tableNoise t)).comp measurable_fst).mul
        ((measurable_actionLoss_joint (measurable_activeVector_joint c t)).comp hpa))

theorem measurable_topScore {d m T : ℕ} (c t : ℕ) :
    Measurable (fun x : Table d T × History d m t => topScore m (itemScore c x.1 t x.2)) := by
  change Measurable (fun x : Table d T × History d m t =>
    ⨆ a : MSetAction d m, actionLoss a (itemScore c x.1 t x.2))
  apply Measurable.iSup
  intro a
  exact measurable_actionLoss a (Measurable.of_eval fun i => measurable_itemScore c i t)

theorem measurable_deficit {d m T : ℕ} (c t : ℕ) :
    Measurable (fun x : Table d T × History d m t => deficit c x.1 t x.2) :=
  (measurable_topScore c t).sub (measurable_learnerScore c t)

theorem sum_bits_mem_Icc {d : ℕ} (U : Bits d) :
    (∑ i : Fin d, bitValue (U i)) ∈ Icc (0 : ℝ) d := by
  constructor
  · exact Finset.sum_nonneg fun i _ => (bitValue_mem_Icc (U i)).1
  · calc
      _ ≤ ∑ _i : Fin d, (1 : ℝ) := Finset.sum_le_sum fun i _ => (bitValue_mem_Icc (U i)).2
      _ = (d : ℝ) := by simp

theorem integrable_sum_bits {d m T t : ℕ}
    (μ : Measure (Table d T × History d m t)) [IsFiniteMeasure μ] :
    Integrable (fun x => ∑ i : Fin d, bitValue (x.1.1 i)) μ :=
  Integrable.of_mem_Icc 0 d
    (((measurable_of_finite (fun U : Bits d => ∑ i : Fin d, bitValue (U i))).comp
      measurable_fst.fst).aemeasurable) (ae_of_all _ fun x => sum_bits_mem_Icc x.1.1)

theorem learnerScore_mem_Icc {d m T : ℕ} (hmd : m ≤ d) (c : ℕ) (xi : Table d T)
    (t : ℕ) (h : History d m t) : learnerScore c xi t h ∈ Icc (0 : ℝ) ((c : ℝ) * d) := by
  refine ⟨learnerScore_nonneg c xi t h, (learnerScore_le_cap_mul_bits hmd c xi t h).trans ?_⟩
  exact mul_le_mul_of_nonneg_left (sum_bits_mem_Icc xi.1).2 (Nat.cast_nonneg c)

theorem integrable_learnerScore {d m T t : ℕ} (hmd : m ≤ d) (c : ℕ)
    (μ : Measure (Table d T × History d m t)) [IsFiniteMeasure μ] :
    Integrable (fun x => learnerScore c x.1 t x.2) μ :=
  Integrable.of_mem_Icc 0 ((c : ℝ) * d) (measurable_learnerScore c t).aemeasurable
    (ae_of_all _ fun x => learnerScore_mem_Icc hmd c x.1 t x.2)

theorem integrable_topScore {d m T t : ℕ} (hmd : m ≤ d) (c : ℕ)
    (μ : Measure (Table d T × History d m t)) [IsFiniteMeasure μ] :
    Integrable (fun x => topScore m (itemScore c x.1 t x.2)) μ := by
  apply Integrable.of_mem_Icc 0 ((m : ℝ) * t) (measurable_topScore c t).aemeasurable
  exact ae_of_all _ fun x => ⟨(topScore_mem_Icc hmd c x.1 t x.2).1,
    (topScore_mem_Icc hmd c x.1 t x.2).2.trans
      (mul_le_mul_of_nonneg_left (shapeSum_mem_Icc x.1 t).2 (Nat.cast_nonneg m))⟩

theorem integrable_deficit {d m T t : ℕ} (hmd : m ≤ d) (c : ℕ)
    (μ : Measure (Table d T × History d m t)) [IsFiniteMeasure μ] :
    Integrable (fun x => deficit c x.1 t x.2) μ :=
  (integrable_topScore hmd c μ).sub (integrable_learnerScore hmd c μ)

theorem jointLaw_map_bits {d m : ℕ} (P : Policy d m) (hm : 0 < m) (c : ℕ)
    (eta : ℝ) (heta : 0 ≤ eta) (hs : eta ≤ 1 / 16) (T t : ℕ) :
    (jointLaw P hm c eta heta hs T t).map (fun x => x.1.1) = bitsMeasure d := by
  change (jointLaw P hm c eta heta hs T t).map
    ((fun xi : Table d T => xi.1) ∘ (fun x : Table d T × History d m t => x.1)) = _
  rw [← Measure.map_map measurable_fst measurable_fst, jointLaw_map_table]
  simp [tableMeasure]

theorem integral_sum_bits_joint {d m : ℕ} (P : Policy d m) (hm : 0 < m) (c : ℕ)
    (eta : ℝ) (heta : 0 ≤ eta) (hs : eta ≤ 1 / 16) (T t : ℕ) :
    (∫ x, ∑ i : Fin d, bitValue (x.1.1 i) ∂jointLaw P hm c eta heta hs T t) =
      (d : ℝ) / 256 := by
  have hf : Measurable (fun U : Bits d => ∑ i : Fin d, bitValue (U i)) :=
    measurable_of_finite _
  rw [← integral_sum_bits d, ← jointLaw_map_bits P hm c eta heta hs T t]
  exact (integral_map (μ := jointLaw P hm c eta heta hs T t)
    (show Measurable (fun x : Table d T × History d m t => x.1.1) from
      measurable_fst.fst).aemeasurable
    hf.aestronglyMeasurable).symm

/-- E S_L <= c*d/256 under the actual joint interaction, with no independence
assumption about the learner's score and the hidden bits. -/
theorem integral_learnerScore_le {d m : ℕ} (P : Policy d m) (hm : 0 < m)
    (hmd : m ≤ d) (c : ℕ) (eta : ℝ) (heta : 0 ≤ eta) (hs : eta ≤ 1 / 16) (T t : ℕ) :
    (∫ x, learnerScore c x.1 t x.2 ∂jointLaw P hm c eta heta hs T t) ≤ (c : ℝ) * d / 256 := by
  calc
    _ ≤ ∫ x, (c : ℝ) * ∑ i : Fin d, bitValue (x.1.1 i)
        ∂jointLaw P hm c eta heta hs T t :=
      integral_mono (integrable_learnerScore hmd c _)
        ((integrable_sum_bits _).const_mul _)
        (fun x => learnerScore_le_cap_mul_bits hmd c x.1 t x.2)
    _ = _ := by rw [integral_const_mul, integral_sum_bits_joint]; ring

theorem integral_learnerScore_le_nine {d m T : ℕ}
    (P : Policy d m) (hm : 0 < m) (hmd : m ≤ d) (hT : 64 * d ^ 2 ≤ T) :
    (∫ x, learnerScore (selectionCap d m T) x.1 T x.2
      ∂jointLaw P hm (selectionCap d m T) (perturbation d m T)
        (perturbation_nonneg d m T) (perturbation_lt_sixteenth hm hmd hT).le T T) ≤
      (9 / 256 : ℝ) * m * T := by
  apply (integral_learnerScore_le P hm hmd (selectionCap d m T)
    (perturbation d m T) (perturbation_nonneg d m T)
    (perturbation_lt_sixteenth hm hmd hT).le T T).trans
  have hd0 : (d : ℝ) ≠ 0 := by exact_mod_cast Nat.ne_of_gt (lt_of_lt_of_le hm hmd)
  calc
    _ ≤ (9 * T * ratio d m) * d / 256 :=
      div_le_div_of_nonneg_right
        (mul_le_mul_of_nonneg_right (selectionCap_upper hm hmd hT) (Nat.cast_nonneg d))
        (by norm_num)
    _ = _ := by unfold ratio; field_simp

end

end MsetsPaper.Lower.SparseCapped
