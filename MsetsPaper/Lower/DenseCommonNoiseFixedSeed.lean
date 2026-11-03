import MsetsPaper.Lower.DenseCommonNoiseSignAveraging
import MsetsPaper.Lower.DenseCommonNoiseCounts
import MsetsPaper.Probability.PolicySeedFixed

/-! # Dense sign testing with the private seed fixed first

Every comparison below is made for one fixed master seed. At each history
the action is the deterministic `fixedChoose`; only the common noise is
random. The seed is averaged in the score-mean module after these bounds.
-/

namespace MsetsPaper.Lower.DenseCommonNoise

open MsetsLower MsetsLower.Feedback MsetsLower.Lower MeasureTheory
open ProbabilityTheory InformationTheory Set MsetsPaper.Probability.PolicySeed
open scoped ENNReal ProbabilityTheory BigOperators

noncomputable section

/-- Fixing the seed removes the action integral: the two sign laws use
exactly the same deterministic action at each common history. -/
theorem fixedSeed_roundKL_eq {d m S : ℕ}
    (P : Policy d m) (hmd : m ≤ d) (r : Seeds S) (hm : 0 < m)
    {eta : ℝ} (he : 0 ≤ eta) (hs : eta ≤ 1 / 16)
    (U V : Fin d → ℝ) (hU : ∀ i, |U i| ≤ 1) (hV : ∀ i, |V i| ≤ 1) (t : ℕ) :
    (observableProcess (fixedPolicy P hmd r) hm eta he hs U hU).roundKL
      (observableProcess (fixedPolicy P hmd r) hm eta he hs V hV) t =
      ∫⁻ h, klDiv
        (feedbackDensityMeasure (feedbackParameter eta U (fixedChoose P hmd r t h)))
        (feedbackDensityMeasure (feedbackParameter eta V (fixedChoose P hmd r t h)))
        ∂(observableProcess (fixedPolicy P hmd r) hm eta he hs U hU).law t := by
  rw [observable_roundKL_eq]
  have hf : Measurable (fun ha : History d m t × MSetAction d m =>
      klDiv (feedbackDensityMeasure (feedbackParameter eta U ha.2))
        (feedbackDensityMeasure (feedbackParameter eta V ha.2))) :=
    (measurable_of_finite (fun a : MSetAction d m =>
      klDiv (feedbackDensityMeasure (feedbackParameter eta U a))
        (feedbackDensityMeasure (feedbackParameter eta V a)))).comp measurable_snd
  rw [Measure.lintegral_compProd hf]
  apply lintegral_congr
  intro h
  change (∫⁻ a, klDiv (feedbackDensityMeasure (feedbackParameter eta U a))
    (feedbackDensityMeasure (feedbackParameter eta V a)) ∂Measure.dirac (fixedChoose P hmd r t h)) = _
  exact lintegral_dirac' _ (measurable_of_finite _)

theorem fixedSeed_roundKL_flip_le_indicator {d m S : ℕ}
    (P : Policy d m) (hmd : m ≤ d) (r : Seeds S) (hm : 0 < m)
    {eta : ℝ} (he : 0 ≤ eta) (hs : eta ≤ 1 / 16)
    (U : Fin d → ℝ) (hU : ∀ j, |U j| ≤ 1) (i : Fin d) (t : ℕ) :
    (observableProcess (fixedPolicy P hmd r) hm eta he hs (Function.update U i 1)
      (update_signs_bounded U hU i (by norm_num))).roundKL
      (observableProcess (fixedPolicy P hmd r) hm eta he hs (Function.update U i (-1))
        (update_signs_bounded U hU i (by norm_num))) t ≤
      ∫⁻ h, ENNReal.ofReal (128 * (2 * eta / m) ^ 2 *
        (if i ∈ (fixedChoose P hmd r t h).val then 1 else 0))
        ∂(observableProcess (fixedPolicy P hmd r) hm eta he hs (Function.update U i 1)
          (update_signs_bounded U hU i (by norm_num))).law t := by
  rw [fixedSeed_roundKL_eq]
  apply lintegral_mono
  intro h
  have hp := (abs_feedbackParameter_le hm he (Function.update U i 1)
    (update_signs_bounded U hU i (by norm_num)) (fixedChoose P hmd r t h)).trans hs
  have hn := (abs_feedbackParameter_le hm he (Function.update U i (-1))
    (update_signs_bounded U hU i (by norm_num)) (fixedChoose P hmd r t h)).trans hs
  have hkl := FeedbackSharp.klDiv_feedbackDensityMeasure_le_one_twenty_eight hp hn
  rw [feedbackParameter_flip_sq] at hkl
  simpa only [mul_assoc] using hkl

/-- Retain the paper's expected-selection-count budget before replacing
the count by the horizon. The common action is still deterministic. -/
theorem fixedSeed_flip_KL_le_expectedCount {d m S T : ℕ}
    (P : Policy d m) (hmd : m ≤ d) (r : Seeds S) (hm : 0 < m)
    {eta : ℝ} (he : 0 ≤ eta) (hs : eta ≤ 1 / 16)
    (U : Fin d → ℝ) (hU : ∀ j, |U j| ≤ 1) (i : Fin d) :
    klDiv
      ((observableProcess (fixedPolicy P hmd r) hm eta he hs (Function.update U i 1)
        (update_signs_bounded U hU i (by norm_num))).law T)
      ((observableProcess (fixedPolicy P hmd r) hm eta he hs (Function.update U i (-1))
        (update_signs_bounded U hU i (by norm_num))).law T) ≤
      ENNReal.ofReal (128 * (2 * eta / m) ^ 2) *
        ENNReal.ofReal (∫ h, History.selectedCount i T h
          ∂(observableProcess (fixedPolicy P hmd r) hm eta he hs (Function.update U i 1)
            (update_signs_bounded U hU i (by norm_num))).law T) := by
  let Q := fixedPolicy P hmd r
  let K := observableProcess Q hm eta he hs (Function.update U i 1)
    (update_signs_bounded U hU i (by norm_num))
  let L := observableProcess Q hm eta he hs (Function.update U i (-1))
    (update_signs_bounded U hU i (by norm_num))
  let c := ENNReal.ofReal (128 * (2 * eta / m) ^ 2)
  have hc (t : ℕ) :
      (∫⁻ ha, selectedENN i ha.2 ∂(K.law t ⊗ₘ Q.kernel t)) =
        ∫⁻ h, selectedENN i (fixedChoose P hmd r t h) ∂K.law t := by
    have hf : Measurable (fun ha : History d m t × MSetAction d m => selectedENN i ha.2) :=
      (measurable_of_finite (selectedENN (m := m) i)).comp measurable_snd
    rw [Measure.lintegral_compProd hf]
    apply lintegral_congr
    intro h
    change (∫⁻ a, selectedENN i a ∂Measure.dirac (fixedChoose P hmd r t h)) = _
    exact lintegral_dirac' _ (measurable_of_finite _)
  have hr (t : ℕ) : K.roundKL L t ≤
      c * ∫⁻ ha, selectedENN i ha.2 ∂(K.law t ⊗ₘ Q.kernel t) := by
    rw [hc]
    apply (fixedSeed_roundKL_flip_le_indicator P hmd r hm he hs U hU i t).trans_eq
    calc
      _ = ∫⁻ h, c * selectedENN i (fixedChoose P hmd r t h) ∂K.law t := by
        apply lintegral_congr
        intro h
        simp only [selectedENN, History.selectedIndicator,
          ENNReal.ofReal_mul (by positivity : (0 : ℝ) ≤ 128 * (2 * eta / m) ^ 2)]
        rfl
      _ = _ := lintegral_const_mul c
        ((measurable_of_finite (selectedENN i)).comp (measurable_fixedChoose P hmd r t))
  change klDiv (K.law T) (L.law T) ≤ _
  rw [K.klDiv_law_eq_sum_roundKL L T]
  calc
    _ ≤ ∑ t ∈ Finset.range T, c * ∫⁻ ha, selectedENN i ha.2 ∂(K.law t ⊗ₘ Q.kernel t) :=
      Finset.sum_le_sum fun t _ => hr t
    _ = c * ∫⁻ h, ENNReal.ofReal (History.selectedCount i T h) ∂K.law T := by
      rw [← Finset.mul_sum]
      congr 1
      exact (lintegral_selectedCount_eq_sum Q hm he hs _ _ i T).symm
    _ = _ := by
      congr 1
      symm
      apply ofReal_integral_eq_lintegral_ofReal
      · exact Integrable.of_mem_Icc 0 (T : ℝ)
          (History.measurable_selectedCount (m := m) i T).aemeasurable
          (ae_of_all _ (History.selectedCount_mem_Icc i T))
      · exact ae_of_all _ fun h => (History.selectedCount_mem_Icc i T h).1

theorem fixedSeed_flip_KL_le_one_div_32 {d m T : ℕ}
    (P : Policy d m) (hmd : m ≤ d) (r : Seeds T)
    (hm : 0 < m) (h2m : 2 * m ≤ d) (hT : d ^ 2 ≤ T)
    (U : Fin d → ℝ) (hU : ∀ j, |U j| ≤ 1) (i : Fin d) :
    let ht : 0 < T := lt_of_lt_of_le (pow_pos (by omega : 0 < d) 2) hT
    let he := (eta_pos hm ht).le
    let hs := (eta_le_one_div_256 hm h2m hT).trans (by norm_num : (1:ℝ)/256 ≤ 1/16)
    klDiv
      ((observableProcess (fixedPolicy P hmd r) hm (eta m T) he hs (Function.update U i 1)
        (update_signs_bounded U hU i (by norm_num))).law T)
      ((observableProcess (fixedPolicy P hmd r) hm (eta m T) he hs (Function.update U i (-1))
        (update_signs_bounded U hU i (by norm_num))).law T) ≤
      ENNReal.ofReal ((1 : ℝ) / 32) := by
  dsimp only
  have ht : 0 < T := lt_of_lt_of_le (pow_pos (by omega : 0 < d) 2) hT
  have he := (eta_pos hm ht).le
  have hs := (eta_le_one_div_256 hm h2m hT).trans (by norm_num : (1:ℝ)/256 ≤ 1/16)
  have h := fixedSeed_flip_KL_le_expectedCount (T := T) P hmd r hm he hs U hU i
  have hcount : (∫ h, History.selectedCount i T h
      ∂(observableProcess (fixedPolicy P hmd r) hm (eta m T) he hs (Function.update U i 1)
        (update_signs_bounded U hU i (by norm_num))).law T) ≤ (T : ℝ) := by
    calc
      _ ≤ ∫ _h, (T : ℝ)
          ∂(observableProcess (fixedPolicy P hmd r) hm (eta m T) he hs (Function.update U i 1)
            (update_signs_bounded U hU i (by norm_num))).law T :=
        integral_mono (Integrable.of_mem_Icc 0 (T : ℝ)
          (History.measurable_selectedCount (m := m) i T).aemeasurable
          (ae_of_all _ (History.selectedCount_mem_Icc i T))) (integrable_const _)
          (fun h => (History.selectedCount_mem_Icc i T h).2)
      _ = _ := by simp
  apply h.trans
  calc
    _ ≤ ENNReal.ofReal (128 * (2 * eta m T / m) ^ 2) * ENNReal.ofReal (T : ℝ) :=
      mul_le_mul_right (ENNReal.ofReal_le_ofReal hcount) _
    _ = ENNReal.ofReal (128 * (2 * eta m T / m) ^ 2 * T) :=
      (ENNReal.ofReal_mul (by positivity)).symm
    _ = _ := by rw [total_flip_budget hm ht]

/-- The same selected-count function is compared under the two noise laws,
after the seed has been fixed. Pinsker is applied before any seed average. -/
theorem fixedSeed_flip_count_bias_le {d m T : ℕ}
    (P : Policy d m) (hmd : m ≤ d) (r : Seeds T)
    (hm : 0 < m) (h2m : 2 * m ≤ d) (hT : d ^ 2 ≤ T)
    (U : Fin d → ℝ) (hU : ∀ j, |U j| ≤ 1) (i : Fin d) :
    let ht : 0 < T := lt_of_lt_of_le (pow_pos (by omega : 0 < d) 2) hT
    let he := (eta_pos hm ht).le
    let hs := (eta_le_one_div_256 hm h2m hT).trans (by norm_num : (1:ℝ)/256 ≤ 1/16)
    |((∫ h, History.selectedCount i T h
      ∂(observableProcess (fixedPolicy P hmd r) hm (eta m T) he hs (Function.update U i 1)
        (update_signs_bounded U hU i (by norm_num))).law T) -
      ∫ h, History.selectedCount i T h
      ∂(observableProcess (fixedPolicy P hmd r) hm (eta m T) he hs (Function.update U i (-1))
        (update_signs_bounded U hU i (by norm_num))).law T) / 2| ≤ (T : ℝ) / 16 := by
  dsimp only
  apply count_bias_le_of_tv i
  exact tv_le_one_eighth_of_kl _ _ (fixedSeed_flip_KL_le_one_div_32 P hmd r hm h2m hT U hU i)

theorem fixedSeed_integral_sign_expectedSelections_le {d m T : ℕ}
    (P : Policy d m) (hmd : m ≤ d) (r : Seeds T)
    (hm : 0 < m) (h2m : 2 * m ≤ d) (hT : d ^ 2 ≤ T) (i : Fin (2 * m)) :
    let ht : 0 < T := lt_of_lt_of_le (pow_pos (by omega : 0 < d) 2) hT
    let he := (eta_pos hm ht).le
    let hs := (eta_le_one_div_256 hm h2m hT).trans (by norm_num : (1:ℝ)/256 ≤ 1/16)
    (∫ U : Signs m, signValue (U i) *
      expectedSelections (fixedPolicy P hmd r) hm (eta m T) he hs U T
        (Fin.castLE h2m i) ∂signsMeasure m) ≤ (T : ℝ) / 16 := by
  dsimp only
  apply sign_mixture_le_of_pair_bound
  intro U
  have h := fixedSeed_flip_count_bias_le P hmd r hm h2m hT
    (signVector U) (abs_signVector_le U) (Fin.castLE h2m i)
  dsimp only at h
  have hle := (le_abs_self _).trans h
  unfold expectedSelections
  rw [noiseMixture_eq_observableProcess, noiseMixture_eq_observableProcess]
  simpa [signVector_update h2m, signValue] using hle

theorem fixedSeed_two_thirds_integral_signedCount_le {d m T : ℕ}
    (P : Policy d m) (hmd : m ≤ d) (r : Seeds T)
    (hm : 0 < m) (h2m : 2 * m ≤ d) (hT : d ^ 2 ≤ T) :
    let ht : 0 < T := lt_of_lt_of_le (pow_pos (by omega : 0 < d) 2) hT
    let he := (eta_pos hm ht).le
    let hs := (eta_le_one_div_256 hm h2m hT).trans (by norm_num : (1:ℝ)/256 ≤ 1/16)
    (2 / 3 : ℝ) * (∫ U : Signs m, ∑ i : Fin (2 * m), signValue (U i) *
      expectedSelections (fixedPolicy P hmd r) hm (eta m T) he hs U T
        (Fin.castLE h2m i) ∂signsMeasure m) ≤ (m : ℝ) * T / 12 := by
  dsimp only
  rw [integral_finsetSum _ (fun _ _ => Integrable.of_finite)]
  calc
    _ ≤ (2 / 3 : ℝ) * ∑ _i : Fin (2 * m), ((T : ℝ) / 16) :=
      mul_le_mul_of_nonneg_left (Finset.sum_le_sum fun i _ =>
        fixedSeed_integral_sign_expectedSelections_le P hmd r hm h2m hT i) (by norm_num)
    _ = _ := by simp; ring

end
end MsetsPaper.Lower.DenseCommonNoise
