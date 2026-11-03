import MsetsPaper.Lower.DenseCommonNoiseLaw
import MsetsPaper.Lower.FeedbackSharp
import MsetsLower.Lower.Dense.AdaptiveLaw

/-!
# One-step information and exact numerical scale for the new dense construction

The import of `Dense.AdaptiveLaw` is used only for its general theorem that KL
is invariant under a measurable embedding. No old paired-item law, loss process,
information bound, or lower-bound witness is used.

The bounds here concern the actual common-noise feedback for a fixed action.
The sequential chain rule and the identification with the table experiment are
separate obligations; this module does not assert the final P3 conclusion.
-/

namespace MsetsPaper.Lower.DenseCommonNoise

open MsetsLower MsetsLower.Feedback MsetsLower.Lower MeasureTheory
open ProbabilityTheory InformationTheory Set
open scoped ENNReal ProbabilityTheory BigOperators

noncomputable section

def feedbackShift : ℝ ≃ᵐ ℝ where
  toEquiv :=
    { toFun := fun y => 1 / 2 + y
      invFun := fun y => y - 1 / 2
      left_inv := by intro y; dsimp; ring
      right_inv := by intro y; dsimp; ring }
  measurable_toFun := measurable_const.add measurable_id
  measurable_invFun := measurable_id.sub measurable_const

/-- The conditional observed feedback law for a fixed action. -/
def feedbackLaw {d m : ℕ} (eta : ℝ) (U : Fin d → ℝ) (a : MSetAction d m) : Measure ℝ :=
  (feedbackDensityMeasure (feedbackParameter eta U a)).map feedbackShift

/-- The law above is exactly obtained by sampling the genuine uniform noise
and computing the actual aggregate loss. -/
theorem actual_feedback_law {d m : ℕ} (hm : 0 < m)
    {eta : ℝ} (heta : 0 ≤ eta) (hetaSmall : eta ≤ 1 / 16)
    (U : Fin d → ℝ) (hU : ∀ i, |U i| ≤ 1) (a : MSetAction d m) :
    noiseMeasure.map (fun z : Noise => actionLoss a (itemLoss m eta z.val U)) =
      feedbackLaw eta U a := by
  have hu := (abs_feedbackParameter_le hm heta U hU a).trans hetaSmall
  unfold feedbackLaw
  rw [← feedbackPushforwardMeasure_eq_densityMeasure hu, feedbackPushforwardMeasure,
    Measure.map_map feedbackShift.measurable (continuous_feedbackMap _).measurable,
    ← map_noiseMeasure,
    Measure.map_map (feedbackShift.measurable.comp (continuous_feedbackMap _).measurable)
      measurable_subtype_coe]
  congr 1
  funext z
  exact actionLoss_feedback_identity hm eta z.val U a

/-- Translation by `1/2` does not change the one-step KL divergence. -/
theorem klDiv_feedbackLaw_eq {d m : ℕ} (eta : ℝ) (U V : Fin d → ℝ)
    (a : MSetAction d m)
    (hU : |feedbackParameter eta U a| ≤ 1 / 16)
    (hV : |feedbackParameter eta V a| ≤ 1 / 16) :
    klDiv (feedbackLaw eta U a) (feedbackLaw eta V a) =
      klDiv (feedbackDensityMeasure (feedbackParameter eta U a))
        (feedbackDensityMeasure (feedbackParameter eta V a)) := by
  letI : IsProbabilityMeasure (feedbackDensityMeasure (feedbackParameter eta U a)) :=
    ⟨feedbackDensityMeasure_apply_univ hU⟩
  letI : IsProbabilityMeasure (feedbackDensityMeasure (feedbackParameter eta V a)) :=
    ⟨feedbackDensityMeasure_apply_univ hV⟩
  exact MsetsLower.Lower.Dense.klDiv_map_measurableEmbedding
    feedbackShift.measurableEmbedding _ _

theorem update_signs_bounded {d : ℕ} (U : Fin d → ℝ) (hU : ∀ j, |U j| ≤ 1)
    (i : Fin d) {v : ℝ} (hv : |v| ≤ 1) :
    ∀ j, |Function.update U i v j| ≤ 1 := by
  intro j
  by_cases hji : j = i
  · simpa [hji] using hv
  · simpa [Function.update, hji] using hU j

/-- Flipping a selected coordinate changes the action sign sum by exactly two;
flipping an unselected coordinate does not change it. -/
theorem action_sign_sum_plus_sub_minus {d m : ℕ}
    (U : Fin d → ℝ) (i : Fin d) (a : MSetAction d m) :
    actionLoss a (Function.update U i 1) - actionLoss a (Function.update U i (-1)) =
      if i ∈ a.val then 2 else 0 := by
  classical
  rw [actionLoss_eq_finset_sum, actionLoss_eq_finset_sum, ← Finset.sum_sub_distrib]
  calc
    (∑ j ∈ a.val, (Function.update U i 1 j - Function.update U i (-1) j)) =
        ∑ j ∈ a.val, if j = i then (2 : ℝ) else 0 := by
      apply Finset.sum_congr rfl
      intro j _
      by_cases hji : j = i
      · subst j
        norm_num
      · simp [Function.update, hji]
    _ = if i ∈ a.val then 2 else 0 := by simp

/-- Exact squared parameter difference, including the action indicator. -/
theorem feedbackParameter_flip_sq {d m : ℕ}
    (eta : ℝ) (U : Fin d → ℝ) (i : Fin d) (a : MSetAction d m) :
    (feedbackParameter eta (Function.update U i 1) a -
      feedbackParameter eta (Function.update U i (-1)) a) ^ 2 =
      (2 * eta / m) ^ 2 * (if i ∈ a.val then 1 else 0) := by
  unfold feedbackParameter
  rw [← mul_sub, action_sign_sum_plus_sub_minus]
  by_cases hi : i ∈ a.val <;> simp [hi] <;> ring

/-- The manuscript's exact conditional flip-KL bound, for its actual scalar
feedback law. The common action need not have been chosen deterministically. -/
theorem klDiv_feedback_flip_le {d m : ℕ} (hm : 0 < m)
    {eta : ℝ} (heta : 0 ≤ eta) (hetaSmall : eta ≤ 1 / 16)
    (U : Fin d → ℝ) (hU : ∀ j, |U j| ≤ 1) (i : Fin d) (a : MSetAction d m) :
    klDiv (feedbackLaw eta (Function.update U i 1) a)
      (feedbackLaw eta (Function.update U i (-1)) a) ≤
      ENNReal.ofReal (128 * (2 * eta / m) ^ 2 * (if i ∈ a.val then 1 else 0)) := by
  have hp := (abs_feedbackParameter_le hm heta (Function.update U i 1)
    (update_signs_bounded U hU i (by norm_num)) a).trans hetaSmall
  have hn := (abs_feedbackParameter_le hm heta (Function.update U i (-1))
    (update_signs_bounded U hU i (by norm_num)) a).trans hetaSmall
  rw [klDiv_feedbackLaw_eq eta _ _ a hp hn]
  have hkl := FeedbackSharp.klDiv_feedbackDensityMeasure_le_one_twenty_eight hp hn
  rw [feedbackParameter_flip_sq] at hkl
  simpa only [mul_assoc] using hkl

def eta (m T : ℕ) : ℝ := m / (128 * Real.sqrt T)

theorem eta_pos {m T : ℕ} (hm : 0 < m) (hT : 0 < T) : 0 < eta m T := by
  unfold eta
  positivity

/-- The manuscript's admissible feedback parameter bound from its horizon. -/
theorem eta_le_one_div_256 {d m T : ℕ} (hm : 0 < m) (h2m : 2 * m ≤ d)
    (hT : d ^ 2 ≤ T) : eta m T ≤ 1 / 256 := by
  have hd : 0 < d := by omega
  have ht : 0 < T := lt_of_lt_of_le (pow_pos hd 2) hT
  have hsqrt : 0 < Real.sqrt (T : ℝ) := by positivity
  have hsquare := Real.sq_sqrt (show (0 : ℝ) ≤ T by positivity)
  have hTd : (d : ℝ) ^ 2 ≤ T := by exact_mod_cast hT
  have hmd : 2 * (m : ℝ) ≤ d := by exact_mod_cast h2m
  have hdR : (0 : ℝ) ≤ d := by positivity
  have hdSqrt : (d : ℝ) ≤ Real.sqrt T := by nlinarith
  unfold eta
  apply (div_le_iff₀ (mul_pos (by norm_num) hsqrt)).2
  nlinarith

/-- Exact accumulated flip budget after substituting the new dense scale.
This arithmetic is not a substitute for the sequential chain-rule proof. -/
theorem total_flip_budget {m T : ℕ} (hm : 0 < m) (hT : 0 < T) :
    128 * (2 * eta m T / m) ^ 2 * T = (1 : ℝ) / 32 := by
  have hm0 : (m : ℝ) ≠ 0 := by exact_mod_cast Nat.ne_of_gt hm
  have hT0 : (T : ℝ) ≠ 0 := by exact_mod_cast Nat.ne_of_gt hT
  have hs0 : Real.sqrt (T : ℝ) ≠ 0 := ne_of_gt (by positivity)
  have hs := Real.sq_sqrt (show (0 : ℝ) ≤ T by positivity)
  unfold eta
  field_simp
  nlinarith

end

end MsetsPaper.Lower.DenseCommonNoise
