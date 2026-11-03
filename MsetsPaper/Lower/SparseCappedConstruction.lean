import MsetsPaper.Lower.SparseCounting
import MsetsPaper.Lower.DenseCommonNoise
import MsetsPaper.Lower.FeedbackSharp
import MsetsLower.Core.HistoryStats

/-!
# P2: the Bernoulli/capped common-noise adversary

This is the adaptive construction in `paper/main.tex`. Activity
is determined from preceding selections, not from hidden bits or current
noise. Fixing its bit/noise table yields an admissible non-anticipating loss
process. Numerical parameter choices and sequential information estimates
are separate obligations, not premises of a lower-tail certificate.
-/

namespace MsetsPaper.Lower.SparseCapped

open MsetsLower MsetsLower.History MsetsLower.Feedback MsetsLower.Lower
open MeasureTheory ProbabilityTheory InformationTheory Set
open scoped BigOperators ENNReal ProbabilityTheory

noncomputable section

abbrev Bits (d : ℕ) := Fin d → Bool

def bitValue (u : Bool) : ℝ := if u then 1 else 0

theorem bitValue_mem_Icc (u : Bool) : bitValue u ∈ Icc (0 : ℝ) 1 := by
  cases u <;> norm_num [bitValue]

/-- Activity at zero-based round t, determined before its action is sampled. -/
def activeIndicator {d m : ℕ} (c t : ℕ) (h : History d m t) (i : Fin d) : ℝ :=
  if selectedCount i t h < (c : ℝ) then 1 else 0

theorem activeIndicator_mem_Icc {d m : ℕ} (c t : ℕ) (h : History d m t) (i : Fin d) :
    activeIndicator c t h i ∈ Icc (0 : ℝ) 1 := by
  unfold activeIndicator
  split <;> norm_num

theorem measurable_activeIndicator {d m : ℕ} (c t : ℕ) (i : Fin d) :
    Measurable (fun h : History d m t => activeIndicator c t h i) :=
  Measurable.ite (measurableSet_lt (measurable_selectedCount i t) measurable_const)
    measurable_const measurable_const

def activeVector {d m : ℕ} (c : ℕ) (U : Bits d) (t : ℕ) (h : History d m t)
    (i : Fin d) : ℝ := activeIndicator c t h i * bitValue (U i)

theorem activeVector_mem_Icc {d m : ℕ} (c : ℕ) (U : Bits d) (t : ℕ)
    (h : History d m t) (i : Fin d) : activeVector c U t h i ∈ Icc (0 : ℝ) 1 := by
  have ha := activeIndicator_mem_Icc c t h i
  have hu := bitValue_mem_Icc (U i)
  exact ⟨mul_nonneg ha.1 hu.1, (mul_le_mul ha.2 hu.2 hu.1 (by norm_num)).trans_eq (by norm_num)⟩

theorem abs_activeVector_le {d m : ℕ} (c : ℕ) (U : Bits d) (t : ℕ)
    (h : History d m t) (i : Fin d) : |activeVector c U t h i| ≤ 1 := by
  rw [abs_of_nonneg (activeVector_mem_Icc c U t h i).1]
  exact (activeVector_mem_Icc c U t h i).2

def itemLoss {d m : ℕ} (c : ℕ) (eta z : ℝ) (U : Bits d)
    (t : ℕ) (h : History d m t) (i : Fin d) : ℝ :=
  DenseCommonNoise.itemLoss m eta z (activeVector c U t h) i

theorem itemLoss_eq_manuscript {d m : ℕ} (c : ℕ) (eta z : ℝ) (U : Bits d)
    (t : ℕ) (h : History d m t) (i : Fin d) :
    itemLoss c eta z U t h i = (1 + z) / (2 * m) -
      eta / m * shape z * activeIndicator c t h i * bitValue (U i) := by
  unfold itemLoss DenseCommonNoise.itemLoss activeVector
  ring

theorem itemLoss_mem_Icc {d m : ℕ} (hm : 0 < m) (c : ℕ)
    {eta z : ℝ} (heta : 0 ≤ eta) (hs : eta ≤ 1 / 16) (hz : z ∈ Icc (-1 : ℝ) 1)
    (U : Bits d) (t : ℕ) (h : History d m t) (i : Fin d) :
    itemLoss c eta z U t h i ∈ Icc (0 : ℝ) (1 / m) :=
  DenseCommonNoise.itemLoss_mem_Icc hm heta hs hz _ (abs_activeVector_le c U t h) i

def feedbackParameter {d m : ℕ} (c : ℕ) (eta : ℝ) (U : Bits d)
    (t : ℕ) (h : History d m t) (a : MSetAction d m) : ℝ :=
  DenseCommonNoise.feedbackParameter eta (activeVector c U t h) a

theorem abs_feedbackParameter_le {d m : ℕ} (hm : 0 < m) (c : ℕ)
    {eta : ℝ} (heta : 0 ≤ eta) (U : Bits d) (t : ℕ)
    (h : History d m t) (a : MSetAction d m) :
    |feedbackParameter c eta U t h a| ≤ eta :=
  DenseCommonNoise.abs_feedbackParameter_le hm heta _ (abs_activeVector_le c U t h) a

theorem actionLoss_feedback_identity {d m : ℕ} (hm : 0 < m) (c : ℕ)
    (eta z : ℝ) (U : Bits d) (t : ℕ) (h : History d m t) (a : MSetAction d m) :
    actionLoss a (itemLoss c eta z U t h) =
      1 / 2 + feedbackMap (feedbackParameter c eta U t h a) z :=
  DenseCommonNoise.actionLoss_feedback_identity hm eta z _ a

theorem actionLoss_mem_Icc {d m : ℕ} (hm : 0 < m) (c : ℕ)
    {eta z : ℝ} (heta : 0 ≤ eta) (hs : eta ≤ 1 / 16) (hz : z ∈ Icc (-1 : ℝ) 1)
    (U : Bits d) (t : ℕ) (h : History d m t) (a : MSetAction d m) :
    actionLoss a (itemLoss c eta z U t h) ∈ Icc (0 : ℝ) 1 :=
  DenseCommonNoise.actionLoss_mem_Icc hm heta hs hz _ (abs_activeVector_le c U t h) a

abbrev Noise := DenseCommonNoise.Noise
abbrev Table (d T : ℕ) := Bits d × (Fin T → Noise)

def tableNoise {d T : ℕ} (xi : Table d T) (t : ℕ) : ℝ :=
  if ht : t < T then (xi.2 ⟨t, ht⟩).val else 0

theorem tableNoise_mem_Icc {d T : ℕ} (xi : Table d T) (t : ℕ) :
    tableNoise xi t ∈ Icc (-1 : ℝ) 1 := by
  unfold tableNoise
  split
  · exact (xi.2 _).property
  · norm_num

theorem measurable_tableNoise {d T : ℕ} (t : ℕ) :
    Measurable (fun xi : Table d T => tableNoise xi t) := by
  unfold tableNoise
  split
  · exact measurable_subtype_coe.comp ((measurable_pi_apply _).comp measurable_snd)
  · exact measurable_const

/-- The actual jointly measurable adaptive table family. Its normalization
fields follow from the literal feedback map, not from an input certificate. -/
def tableLossProcess {d m : ℕ} (hm : 0 < m) (c : ℕ)
    (eta : ℝ) (heta : 0 ≤ eta) (hs : eta ≤ 1 / 16) (T : ℕ) :
    ParametricLossProcess (Table d T) d m where
  itemLoss t xi h := itemLoss c eta (tableNoise xi t) xi.1 t h
  measurable_itemLoss t := by
    apply measurable_pi_lambda
    intro i
    have hz : Measurable (fun x : Table d T × History d m t => tableNoise x.1 t) :=
      (measurable_tableNoise t).comp measurable_fst
    have ha : Measurable (fun x : Table d T × History d m t => activeIndicator c t x.2 i) :=
      (measurable_activeIndicator c t i).comp measurable_snd
    have hu : Measurable (fun x : Table d T × History d m t => bitValue (x.1.1 i)) :=
      (measurable_of_finite (fun U : Bits d => bitValue (U i))).comp measurable_fst.fst
    unfold itemLoss DenseCommonNoise.itemLoss activeVector shape
    fun_prop
  action_nonneg xi t h a :=
    (actionLoss_mem_Icc hm c heta hs (tableNoise_mem_Icc xi t) xi.1 t h a).1
  action_le_one xi t h a :=
    (actionLoss_mem_Icc hm c heta hs (tableNoise_mem_Icc xi t) xi.1 t h a).2

theorem tableLossProcess_item_mem_Icc {d m : ℕ} (hm : 0 < m) (c : ℕ)
    (eta : ℝ) (heta : 0 ≤ eta) (hs : eta ≤ 1 / 16)
    (T : ℕ) (xi : Table d T) (t : ℕ) (h : History d m t) (i : Fin d) :
    ((tableLossProcess hm c eta heta hs T).at xi).itemLoss t h i ∈ Icc (0 : ℝ) (1 / m) :=
  itemLoss_mem_Icc hm c heta hs (tableNoise_mem_Icc xi t) xi.1 t h i

theorem feedbackParameter_bit_difference {d m : ℕ} (c : ℕ) (eta : ℝ)
    (U : Bits d) (i : Fin d) (t : ℕ) (h : History d m t) (a : MSetAction d m) :
    feedbackParameter c eta (Function.update U i false) t h a -
      feedbackParameter c eta (Function.update U i true) t h a =
        eta / m * activeIndicator c t h i * selectedIndicator i a := by
  classical
  have hsum : actionLoss a (activeVector c (Function.update U i false) t h) -
      actionLoss a (activeVector c (Function.update U i true) t h) =
        -(activeIndicator c t h i * selectedIndicator i a) := by
    rw [actionLoss_eq_finset_sum, actionLoss_eq_finset_sum, ← Finset.sum_sub_distrib]
    calc
      _ = ∑ j ∈ a.val, if j = i then -activeIndicator c t h i else 0 := by
        apply Finset.sum_congr rfl
        intro j _
        by_cases hji : j = i
        · subst j; simp [activeVector, bitValue]
        · simp [activeVector, Function.update, hji]
      _ = _ := by by_cases hi : i ∈ a.val <;> simp [hi, selectedIndicator]
  unfold feedbackParameter DenseCommonNoise.feedbackParameter
  rw [← mul_sub, hsum]
  ring

theorem feedbackParameter_bit_difference_sq {d m : ℕ} (c : ℕ) (eta : ℝ)
    (U : Bits d) (i : Fin d) (t : ℕ) (h : History d m t) (a : MSetAction d m) :
    (feedbackParameter c eta (Function.update U i false) t h a -
      feedbackParameter c eta (Function.update U i true) t h a) ^ 2 =
        (eta / m) ^ 2 * activeIndicator c t h i * selectedIndicator i a := by
  rw [feedbackParameter_bit_difference]
  unfold activeIndicator selectedIndicator
  split_ifs <;> ring

/-- L12 applied to the actual history-dependent parameter: information is
charged only for a selected item which has not yet reached its cap. -/
theorem feedback_bit_KL_le {d m : ℕ} (hm : 0 < m) (c : ℕ)
    {eta : ℝ} (heta : 0 ≤ eta) (hs : eta ≤ 1 / 16)
    (U : Bits d) (i : Fin d) (t : ℕ) (h : History d m t) (a : MSetAction d m) :
    klDiv (feedbackDensityMeasure (feedbackParameter c eta (Function.update U i false) t h a))
      (feedbackDensityMeasure (feedbackParameter c eta (Function.update U i true) t h a)) ≤
        ENNReal.ofReal (128 * (eta / m) ^ 2 * activeIndicator c t h i * selectedIndicator i a) := by
  have hu := (abs_feedbackParameter_le hm c heta (Function.update U i false) t h a).trans hs
  have hv := (abs_feedbackParameter_le hm c heta (Function.update U i true) t h a).trans hs
  have hkl := FeedbackSharp.klDiv_feedbackDensityMeasure_le_eighty hu hv
  rw [feedbackParameter_bit_difference_sq] at hkl
  apply hkl.trans (ENNReal.ofReal_le_ofReal _)
  have ha := (activeIndicator_mem_Icc c t h i).1
  have hx := (selectedIndicator_mem_Icc i a).1
  nlinarith [mul_nonneg (mul_nonneg (sq_nonneg (eta / m)) ha) hx]

end

end MsetsPaper.Lower.SparseCapped
