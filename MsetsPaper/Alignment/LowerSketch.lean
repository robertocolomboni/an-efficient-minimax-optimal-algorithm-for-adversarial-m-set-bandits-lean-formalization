import MsetsPaper.Alignment.LowerDefinitive

/-!
# Additional equations of the definitive lower-bound sketch

The appendix relaxes L12's 80 to 128. The expanded sketch retains 80 in
three displayed sequential information bounds. These are actual bounds for
the same observable processes, not numerical comparisons of final rates.
The existing arbitrary-policy laws also cover every fixed private seed by
specializing the policy to the already defined `PolicySeed.fixedPolicy`.
-/

namespace MsetsPaper.Alignment.LowerSketch

open MsetsLower MsetsLower.Lower MsetsLower.Feedback
open MsetsPaper.Lower MeasureTheory ProbabilityTheory InformationTheory Set
open scoped ENNReal ProbabilityTheory BigOperators

noncomputable section

/-- Integrate a genuine per-round information charge and sum it into the
expected number of selections. The chain rule is an equality for these laws. -/
theorem count_KL_of_round_bound {d m T : ℕ}
    (P : Policy d m) (K L : HistoryKernelProcess d m) (i : Fin d) (κ : ℝ)
    (hκ : 0 ≤ κ) (hfst : ∀ t, Kernel.fst (K.kernel t) = P.kernel t)
    (hr : ∀ t, K.roundKL L t ≤
      ∫⁻ ha, ENNReal.ofReal (κ * History.selectedIndicator i ha.2)
        ∂(K.law t ⊗ₘ P.kernel t)) :
    klDiv (K.law T) (L.law T) ≤ ENNReal.ofReal κ *
      ENNReal.ofReal (∫ h, History.selectedCount i T h ∂K.law T) := by
  have hr' (t : ℕ) : K.roundKL L t ≤ ENNReal.ofReal κ *
      ∫⁻ ha, DenseCommonNoise.selectedENN i ha.2 ∂(K.law t ⊗ₘ P.kernel t) := by
    apply (hr t).trans_eq
    simp only [DenseCommonNoise.selectedENN, ENNReal.ofReal_mul hκ]
    exact lintegral_const_mul _
      ((measurable_of_finite (DenseCommonNoise.selectedENN i)).comp measurable_snd)
  rw [K.klDiv_law_eq_sum_roundKL L T]
  calc
    _ ≤ ∑ t ∈ Finset.range T, ENNReal.ofReal κ *
        ∫⁻ ha, DenseCommonNoise.selectedENN i ha.2 ∂(K.law t ⊗ₘ P.kernel t) :=
      Finset.sum_le_sum fun t _ => hr' t
    _ = ENNReal.ofReal κ * ∫⁻ h, ENNReal.ofReal (History.selectedCount i T h) ∂K.law T := by
      rw [← Finset.mul_sum,
        ConfidenceOblivious.lintegral_selectedCount_eq_sum_general P K hfst i T]
    _ = _ := by
      congr 1
      symm
      apply ofReal_integral_eq_lintegral_ofReal
      · exact Integrable.of_mem_Icc 0 (T : ℝ)
          (History.measurable_selectedCount (m := m) i T).aemeasurable
          (ae_of_all _ (History.selectedCount_mem_Icc i T))
      · exact ae_of_all _ fun h => (History.selectedCount_mem_Icc i T h).1

namespace Dense

open DenseCommonNoise

/-- Sketch: each sign flip costs at most 80(2η/m)^2, only when selected. -/
theorem round_KL_eighty {d m : ℕ} (P : Policy d m) (hm : 0 < m)
    {eta : ℝ} (heta : 0 ≤ eta) (hs : eta ≤ 1 / 16)
    (U : Fin d → ℝ) (hU : ∀ j, |U j| ≤ 1) (i : Fin d) (t : ℕ) :
    (observableProcess P hm eta heta hs (Function.update U i 1)
      (update_signs_bounded U hU i (by norm_num))).roundKL
      (observableProcess P hm eta heta hs (Function.update U i (-1))
        (update_signs_bounded U hU i (by norm_num))) t ≤
      ∫⁻ ha, ENNReal.ofReal (80 * (2 * eta / m) ^ 2 * History.selectedIndicator i ha.2)
        ∂((observableProcess P hm eta heta hs (Function.update U i 1)
          (update_signs_bounded U hU i (by norm_num))).law t ⊗ₘ P.kernel t) := by
  rw [observable_roundKL_eq]
  apply lintegral_mono
  intro ha
  have hp := (abs_feedbackParameter_le hm heta (Function.update U i 1)
    (update_signs_bounded U hU i (by norm_num)) ha.2).trans hs
  have hn := (abs_feedbackParameter_le hm heta (Function.update U i (-1))
    (update_signs_bounded U hU i (by norm_num)) ha.2).trans hs
  have hkl := FeedbackSharp.klDiv_feedbackDensityMeasure_le_eighty hp hn
  rw [feedbackParameter_flip_sq] at hkl
  simpa only [mul_assoc, History.selectedIndicator] using hkl

/-- The sketch's displayed KL bound with the expected selection count. -/
theorem history_KL_eighty_expectedCount {d m T : ℕ} (P : Policy d m) (hm : 0 < m)
    {eta : ℝ} (heta : 0 ≤ eta) (hs : eta ≤ 1 / 16)
    (U : Fin d → ℝ) (hU : ∀ j, |U j| ≤ 1) (i : Fin d) :
    klDiv
      ((observableProcess P hm eta heta hs (Function.update U i 1)
        (update_signs_bounded U hU i (by norm_num))).law T)
      ((observableProcess P hm eta heta hs (Function.update U i (-1))
        (update_signs_bounded U hU i (by norm_num))).law T) ≤
      ENNReal.ofReal (80 * (2 * eta / m) ^ 2) *
        ENNReal.ofReal (∫ h, History.selectedCount i T h
          ∂(observableProcess P hm eta heta hs (Function.update U i 1)
            (update_signs_bounded U hU i (by norm_num))).law T) := by
  apply count_KL_of_round_bound P _ _ i _ (by positivity)
  · exact observableRoundKernel_fst P hm heta hs (Function.update U i 1)
      (update_signs_bounded U hU i (by norm_num))
  · exact round_KL_eighty P hm heta hs U hU i

/-- The exact Top_m identity asserted by the sketch, beyond the appendix's
one-sided comparison with a paired comparator. -/
theorem regret_eq_topScore {d m : ℕ} (hm : 0 < m) (hmd : m ≤ d)
    (eta : ℝ) (heta : 0 ≤ eta) (hs : eta ≤ 1 / 16)
    (T : ℕ) (xi : Table m T) (t : ℕ) (h : History d m t) :
    pathRegret ((tableLossProcess hm eta heta hs T).at xi) t h =
      eta / m * (SparseCapped.topScore m
        (fun i : Fin d => signVector xi.1 i * shapeSum xi t) - learnerScore xi t h) := by
  letI := nonempty_MSetAction hmd
  let S : Fin d → ℝ := fun i => signVector xi.1 i * shapeSum xi t
  have hscore (a : MSetAction d m) : actionLoss a S =
      actionLoss a (signVector xi.1) * shapeSum xi t := by
    simp only [actionLoss_eq_finset_sum, S, Finset.sum_mul]
  have hk : 0 ≤ eta / (m : ℝ) := div_nonneg heta (Nat.cast_nonneg m)
  have hbest : bestComparatorCumulativeLoss ((tableLossProcess hm eta heta hs T).at xi) t h =
      commonLossSum xi t - eta / m * SparseCapped.topScore m S := by
    obtain ⟨a, ha⟩ := SparseCapped.topScore_attained hmd S
    apply le_antisymm
    · have hb := csInf_le (Set.finite_range
          (comparatorCumulativeLoss ((tableLossProcess hm eta heta hs T).at xi) t h)).bddBelow
          (Set.mem_range_self a)
      rw [comparatorCumulativeLoss_eq_common_sub_score, ← hscore, ha] at hb
      exact hb
    · apply le_csInf (Set.range_nonempty _)
      rintro y ⟨a, rfl⟩
      rw [comparatorCumulativeLoss_eq_common_sub_score, ← hscore]
      exact sub_le_sub_left (mul_le_mul_of_nonneg_left
        (SparseCapped.actionLoss_le_topScore S a) hk) _
  rw [pathRegret, realizedCumulativeLoss_eq_common_sub_score, hbest]
  dsimp only [S]
  ring

/-- The paired comparator is a feasible m-set, so its score is at most Top_m. -/
theorem paired_score_le_topScore {d m : ℕ} (h2m : 2 * m ≤ d)
    (U : Fin d → ℝ) (G : ℝ) :
    pairedSignScore h2m U * G ≤ SparseCapped.topScore m (fun i => U i * G) := by
  have h := SparseCapped.actionLoss_le_topScore (fun i => U i * G) (pairedComparator h2m U)
  have heq : actionLoss (pairedComparator h2m U) (fun i => U i * G) =
      actionLoss (pairedComparator h2m U) U * G := by
    simp only [actionLoss_eq_finset_sum, Finset.sum_mul]
  rwa [heq, actionLoss_pairedComparator] at h

end Dense

namespace Sparse

open SparseCapped

/-- The active-selection parameter difference is squared exactly once. -/
theorem feedback_bit_KL_eighty {d m : ℕ} (hm : 0 < m) (c : ℕ)
    {eta : ℝ} (heta : 0 ≤ eta) (hs : eta ≤ 1 / 16)
    (U : Bits d) (i : Fin d) (t : ℕ) (h : History d m t) (a : MSetAction d m) :
    klDiv (feedbackDensityMeasure (feedbackParameter c eta (Function.update U i false) t h a))
      (feedbackDensityMeasure (feedbackParameter c eta (Function.update U i true) t h a)) ≤
      ENNReal.ofReal (80 * (eta / m) ^ 2 * activeIndicator c t h i * History.selectedIndicator i a) := by
  have hu := (abs_feedbackParameter_le hm c heta (Function.update U i false) t h a).trans hs
  have hv := (abs_feedbackParameter_le hm c heta (Function.update U i true) t h a).trans hs
  have hkl := FeedbackSharp.klDiv_feedbackDensityMeasure_le_eighty hu hv
  rw [feedbackParameter_bit_difference_sq] at hkl
  simpa only [mul_assoc] using hkl

theorem round_KL_eighty {d m : ℕ} (P : Policy d m) (hm : 0 < m) (c : ℕ)
    {eta : ℝ} (heta : 0 ≤ eta) (hs : eta ≤ 1 / 16) (U : Bits d) (i : Fin d) (t : ℕ) :
    (observableProcess P hm c eta heta hs (Function.update U i false)).roundKL
      (observableProcess P hm c eta heta hs (Function.update U i true)) t ≤
      ∫⁻ ha, ENNReal.ofReal
        (80 * (eta / m) ^ 2 * activeIndicator c t ha.1 i * History.selectedIndicator i ha.2)
        ∂((observableProcess P hm c eta heta hs (Function.update U i false)).law t ⊗ₘ P.kernel t) := by
  rw [observable_roundKL_eq]
  exact lintegral_mono fun ha => feedback_bit_KL_eighty hm c heta hs U i t ha.1 ha.2

/-- Exact coefficient-80 sequential budget, using the actual capped count. -/
theorem history_KL_eighty_expectedCappedCount {d m T : ℕ}
    (P : Policy d m) (hm : 0 < m) (hmd : m ≤ d) (c : ℕ)
    {eta : ℝ} (heta : 0 ≤ eta) (hs : eta ≤ 1 / 16) (U : Bits d) (i : Fin d) :
    klDiv ((observableProcess P hm c eta heta hs (Function.update U i false)).law T)
      ((observableProcess P hm c eta heta hs (Function.update U i true)).law T) ≤
      ENNReal.ofReal (80 * (eta / m) ^ 2) *
        ENNReal.ofReal (∫ h, (cappedCount c i T h : ℝ)
          ∂(observableProcess P hm c eta heta hs (Function.update U i false)).law T) := by
  let K := observableProcess P hm c eta heta hs (Function.update U i false)
  let L := observableProcess P hm c eta heta hs (Function.update U i true)
  let κ := ENNReal.ofReal (80 * (eta / m) ^ 2)
  have hr (t : ℕ) : K.roundKL L t ≤
      κ * ∫⁻ ha, activeSelectedENN c i t ha ∂(K.law t ⊗ₘ P.kernel t) := by
    apply (round_KL_eighty P hm c heta hs U i t).trans_eq
    calc
      _ = ∫⁻ ha, κ * activeSelectedENN c i t ha ∂(K.law t ⊗ₘ P.kernel t) := by
        apply lintegral_congr
        intro ha
        rw [show 80 * (eta / m) ^ 2 * activeIndicator c t ha.1 i * History.selectedIndicator i ha.2 =
          (80 * (eta / m) ^ 2) * (activeIndicator c t ha.1 i * History.selectedIndicator i ha.2) by ring]
        exact ENNReal.ofReal_mul (by positivity)
      _ = _ := lintegral_const_mul κ (measurable_activeSelectedENN c i t)
  change klDiv (K.law T) (L.law T) ≤ _
  rw [K.klDiv_law_eq_sum_roundKL L T]
  calc
    _ ≤ ∑ t ∈ Finset.range T, κ * ∫⁻ ha, activeSelectedENN c i t ha ∂(K.law t ⊗ₘ P.kernel t) :=
      Finset.sum_le_sum fun t _ => hr t
    _ = κ * ∫⁻ h, ENNReal.ofReal (cappedCount c i T h : ℝ) ∂K.law T := by
      rw [← Finset.mul_sum]
      congr 1
      exact (lintegral_cappedCount_eq_sum P hm c heta hs _ i T).symm
    _ = _ := by
      congr 1
      symm
      apply ofReal_integral_eq_lintegral_ofReal
      · exact Integrable.of_mem_Icc 0 (c : ℝ) (measurable_cast_cappedCount c i T).aemeasurable
          (ae_of_all _ fun h => ⟨Nat.cast_nonneg _, by exact_mod_cast cappedCount_le_cap hmd c i T h⟩)
      · exact ae_of_all _ fun h => Nat.cast_nonneg _

theorem history_KL_eighty_cap {d m T : ℕ}
    (P : Policy d m) (hm : 0 < m) (hmd : m ≤ d) (c : ℕ)
    {eta : ℝ} (heta : 0 ≤ eta) (hs : eta ≤ 1 / 16) (U : Bits d) (i : Fin d) :
    klDiv ((observableProcess P hm c eta heta hs (Function.update U i false)).law T)
      ((observableProcess P hm c eta heta hs (Function.update U i true)).law T) ≤
      ENNReal.ofReal (80 * (eta / m) ^ 2 * c) := by
  apply (history_KL_eighty_expectedCappedCount P hm hmd c heta hs U i).trans
  rw [ENNReal.ofReal_mul (by positivity : (0 : ℝ) ≤ 80 * (eta / m) ^ 2)]
  apply mul_le_mul_right
  apply ENNReal.ofReal_le_ofReal
  calc
    _ ≤ ∫ _h : History d m T, (c : ℝ)
        ∂(observableProcess P hm c eta heta hs (Function.update U i false)).law T := by
      apply integral_mono
      · exact Integrable.of_mem_Icc 0 (c : ℝ) (measurable_cast_cappedCount c i T).aemeasurable
          (ae_of_all _ fun h => ⟨Nat.cast_nonneg _, by exact_mod_cast cappedCount_le_cap hmd c i T h⟩)
      · exact integrable_const _
      · intro h
        change (cappedCount c i T h : ℝ) ≤ (c : ℝ)
        exact_mod_cast cappedCount_le_cap hmd c i T h
    _ = (c : ℝ) := by simp

end Sparse

namespace Confidence

open ConfidenceOblivious MsetsLower.Lower.Confidence MsetsPaper.Probability.PolicySeed

/-- The affine transformation of the confidence feedback leaves the common
support unchanged; only a selected planted coordinate incurs information. -/
theorem round_KL_eighty {d m : ℕ} (P : Policy d m) (hm : 1 ≤ m) (hmd : m ≤ d)
    (Delta : ℝ) (hDelta : 0 ≤ Delta) (hsmall : (m : ℝ) * Delta ≤ 1 / 2 ^ 13)
    (i : Fin d) (t : ℕ) :
    (referenceProcess P hm hmd Delta hDelta hsmall).roundKL
      (plantedProcess P hm hmd Delta hDelta hsmall i) t ≤
      ∫⁻ ha, ENNReal.ofReal (80 * (4 * Delta) ^ 2 * History.selectedIndicator i ha.2)
        ∂((referenceProcess P hm hmd Delta hDelta hsmall).law t ⊗ₘ P.kernel t) := by
  unfold referenceProcess plantedProcess
  rw [fresh_roundKL_eq]
  apply lintegral_mono
  intro ha
  dsimp only
  have hp : |DenseCommonNoise.feedbackParameter (4 * m * Delta) (oneHot i) ha.2| ≤ 1 / 16 :=
    (DenseCommonNoise.abs_feedbackParameter_le hm (feedback_scale_admissible hDelta hsmall).1
      (oneHot i) (abs_oneHot_le i) ha.2).trans (feedback_scale_admissible hDelta hsmall).2
  rw [feedbackParameter_zero]
  have hkl := FeedbackSharp.klDiv_feedbackDensityMeasure_le_eighty
    (by norm_num : |(0 : ℝ)| ≤ 1 / 16) hp
  rw [feedbackParameter_oneHot hm] at hkl ⊢
  by_cases hi : i ∈ ha.2.val <;> simpa [hi, History.selectedIndicator] using hkl

theorem history_KL_eighty_expectedCount {d m T : ℕ}
    (P : Policy d m) (hm : 1 ≤ m) (hmd : m ≤ d)
    (Delta : ℝ) (hDelta : 0 ≤ Delta) (hsmall : (m : ℝ) * Delta ≤ 1 / 2 ^ 13) (i : Fin d) :
    klDiv ((referenceProcess P hm hmd Delta hDelta hsmall).law T)
      ((plantedProcess P hm hmd Delta hDelta hsmall i).law T) ≤
      ENNReal.ofReal (80 * (4 * Delta) ^ 2) *
        ENNReal.ofReal (∫ h, History.selectedCount i T h
          ∂(referenceProcess P hm hmd Delta hDelta hsmall).law T) := by
  apply count_KL_of_round_bound P _ _ i _ (by positivity)
  · exact freshRoundKernel_fst P hm hmd (feedback_scale_admissible hDelta hsmall).1
      (feedback_scale_admissible hDelta hsmall).2 (fun _ => 0) (by intro j; norm_num)
  · exact round_KL_eighty P hm hmd Delta hDelta hsmall i

theorem history_KL_eighty_real {d m T : ℕ}
    (P : Policy d m) (hm : 1 ≤ m) (hmd : m ≤ d)
    (Delta : ℝ) (hDelta : 0 ≤ Delta) (hsmall : (m : ℝ) * Delta ≤ 1 / 2 ^ 13) (i : Fin d) :
    (klDiv ((referenceProcess P hm hmd Delta hDelta hsmall).law T)
      ((plantedProcess P hm hmd Delta hDelta hsmall i).law T)).toReal ≤
      80 * (4 * Delta) ^ 2 * (∫ h, History.selectedCount i T h
        ∂(referenceProcess P hm hmd Delta hDelta hsmall).law T) := by
  have h := ENNReal.toReal_mono
    (ENNReal.mul_ne_top ENNReal.ofReal_ne_top ENNReal.ofReal_ne_top)
    (history_KL_eighty_expectedCount (T := T) P hm hmd Delta hDelta hsmall i)
  have hnonneg : 0 ≤ ∫ h, History.selectedCount i T h
      ∂(referenceProcess P hm hmd Delta hDelta hsmall).law T :=
    integral_nonneg fun h => (History.selectedCount_mem_Icc i T h).1
  simpa only [ENNReal.toReal_mul, ENNReal.toReal_ofReal (by positivity : (0 : ℝ) ≤ 80 * (4 * Delta) ^ 2),
    ENNReal.toReal_ofReal hnonneg] using h

/-- The actual stopped learner gives the sketch's coefficient-80 averaged
history KL, with the explicit 1+mΔ factor before the O(Δ²T/|V|) notation. -/
theorem auxiliary_average_KL_eighty {d m T : ℕ}
    (P : Policy d m) (hm : 1 ≤ m) (hmd : m ≤ d) (hT : 0 < T)
    (Delta : ℝ) (hDelta : 0 < Delta) (hsmall : (m : ℝ) * Delta ≤ 1 / 2 ^ 13)
    (r : Seeds T) (j : Fin d) (hj : j ∈ confidenceCandidates d m hmd) :
    let A := auxiliaryPolicy P hmd r (Delta * T / 8) (coreComparator hm hmd j hj)
    (∑ i ∈ confidenceCandidates d m hmd,
      (klDiv ((referenceProcess A hm hmd Delta hDelta.le hsmall).law T)
        ((plantedProcess A hm hmd Delta hDelta.le hsmall i).law T)).toReal) /
      (confidenceCandidates d m hmd).card ≤
      80 * (4 * Delta) ^ 2 / (confidenceCandidates d m hmd).card * (T * (1 + m * Delta)) := by
  dsimp only
  let A := auxiliaryPolicy P hmd r (Delta * T / 8) (coreComparator hm hmd j hj)
  have hs := Finset.sum_le_sum (s := confidenceCandidates d m hmd) (fun i _ =>
    history_KL_eighty_real (T := T) A hm hmd Delta hDelta.le hsmall i)
  rw [← Finset.mul_sum] at hs
  have hb := mul_le_mul_of_nonneg_left
    (auxiliary_reference_expected_totalCount_le P hm hmd hT Delta hDelta hsmall r j hj)
    (by positivity : (0 : ℝ) ≤ 80 * (4 * Delta) ^ 2)
  have hd := div_le_div_of_nonneg_right (hs.trans hb)
    (show (0 : ℝ) ≤ (confidenceCandidates d m hmd).card by positivity)
  exact hd.trans_eq (by ring)

end Confidence
end
end MsetsPaper.Alignment.LowerSketch
