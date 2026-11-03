import MsetsPaper.Lower.DenseCommonNoiseProcess
import MsetsLower.Lower.Dense.Assouad
import MsetsLower.Core.HistoryStats

/-!
# Pinsker and the common selection statistic in the dense construction

Only the general internally proved Pinsker theorem and total-variation dual
estimate are reused from the old dense library. The probability laws below
are the new common-noise feedback processes, not the old paired Bernoulli laws.
The final sign-prior averaging and fresh-noise tower identity remain separate.
-/

namespace MsetsPaper.Lower.DenseCommonNoise

open MsetsLower MsetsLower.Feedback MsetsLower.Lower MsetsLower.Probability
open MeasureTheory ProbabilityTheory InformationTheory Set
open scoped ENNReal ProbabilityTheory BigOperators

noncomputable section

/-- Centering a statistic in `[0,B]` gives the sharp range-length version
of the total-variation estimate (not the weaker `2B` version). -/
theorem abs_integral_sub_le_range_mul_tv
    {Ω : Type*} [MeasurableSpace Ω] (μ ν : Measure Ω)
    [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    {f : Ω → ℝ} {B : ℝ} (hf : Measurable f)
    (hbound : ∀ x, f x ∈ Icc 0 B) :
    |(∫ x, f x ∂μ) - ∫ x, f x ∂ν| ≤ B * totalVariationDistance μ ν := by
  have hfiμ : Integrable f μ := Integrable.of_mem_Icc 0 B hf.aemeasurable (ae_of_all _ hbound)
  have hfiν : Integrable f ν := Integrable.of_mem_Icc 0 B hf.aemeasurable (ae_of_all _ hbound)
  have hcenter : ∀ x, |f x - B / 2| ≤ B / 2 := by
    intro x
    rw [abs_le]
    constructor <;> linarith [(hbound x).1, (hbound x).2]
  have h := abs_integral_sub_integral_le_two_mul_totalVariationDistance μ ν
    (hf.sub measurable_const) hcenter
  simp only [Pi.sub_apply] at h
  rw [integral_sub hfiμ (integrable_const _), integral_sub hfiν (integrable_const _)] at h
  simp only [integral_const, probReal_univ, one_smul] at h
  have hleft : (∫ x, f x ∂μ) - B / 2 - ((∫ x, f x ∂ν) - B / 2) =
      (∫ x, f x ∂μ) - ∫ x, f x ∂ν := by ring
  have hright : 2 * (B / 2) = B := by ring
  simpa only [hleft, hright] using h

/-- Native KL at most `1/32` entails TV at most `1/8` with the standard
probability-theory normalization. Finiteness is derived, never postulated. -/
theorem tv_le_one_eighth_of_kl
    {Ω : Type*} [MeasurableSpace Ω] (μ ν : Measure Ω)
    [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    (hkl : klDiv μ ν ≤ ENNReal.ofReal ((1 : ℝ) / 32)) :
    totalVariationDistance μ ν ≤ (1 : ℝ) / 8 := by
  have hfinite : klDiv μ ν ≠ ∞ := ne_top_of_le_ne_top ENNReal.ofReal_ne_top hkl
  have hp := Dense.totalVariationDistance_pinsker_sq μ ν hfinite
  have hr := ENNReal.toReal_mono (by simp : ENNReal.ofReal ((1 : ℝ) / 32) ≠ ∞) hkl
  norm_num at hr
  nlinarith [totalVariationDistance_nonneg μ ν]

/-- Pinsker for the two genuine observable common-noise processes. -/
theorem observable_flip_TV_le_one_eighth {d m T : ℕ}
    (P : Policy d m) (hm : 0 < m) (h2m : 2 * m ≤ d) (hT : d ^ 2 ≤ T)
    (U : Fin d → ℝ) (hU : ∀ j, |U j| ≤ 1) (i : Fin d) :
    let ht : 0 < T := lt_of_lt_of_le (pow_pos (by omega : 0 < d) 2) hT
    let he := (eta_pos hm ht).le
    let hs := (eta_le_one_div_256 hm h2m hT).trans (by norm_num : (1:ℝ)/256 ≤ 1/16)
    totalVariationDistance
      ((observableProcess P hm (eta m T) he hs (Function.update U i 1)
        (update_signs_bounded U hU i (by norm_num))).law T)
      ((observableProcess P hm (eta m T) he hs (Function.update U i (-1))
        (update_signs_bounded U hU i (by norm_num))).law T) ≤ (1 : ℝ) / 8 := by
  dsimp only
  exact tv_le_one_eighth_of_kl _ _ (observable_flip_KL_le_one_div_32 P hm h2m hT U hU i)

theorem count_bias_le_of_tv {d m T : ℕ} (i : Fin d)
    (μ ν : Measure (History d m T)) [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    (htv : totalVariationDistance μ ν ≤ (1 : ℝ) / 8) :
    |((∫ h, History.selectedCount i T h ∂μ) -
      ∫ h, History.selectedCount i T h ∂ν) / 2| ≤ (T : ℝ) / 16 := by
  have hdiff := abs_integral_sub_le_range_mul_tv μ ν
    (f := History.selectedCount (m := m) i T) (B := (T : ℝ))
    (History.measurable_selectedCount (m := m) i T)
    (History.selectedCount_mem_Icc (m := m) i T)
  have hprod := mul_le_mul_of_nonneg_left htv (show (0 : ℝ) ≤ T by positivity)
  rw [abs_div, abs_of_pos (by norm_num : (0 : ℝ) < 2)]
  linarith

/-- The selection count is the SAME measurable history statistic under the
two laws. Its half-difference is the sign-mixture bias before averaging the
other signs, and is bounded by `T/16` as in the manuscript. -/
theorem observable_flip_count_bias_le {d m T : ℕ}
    (P : Policy d m) (hm : 0 < m) (h2m : 2 * m ≤ d) (hT : d ^ 2 ≤ T)
    (U : Fin d → ℝ) (hU : ∀ j, |U j| ≤ 1) (i : Fin d) :
    let ht : 0 < T := lt_of_lt_of_le (pow_pos (by omega : 0 < d) 2) hT
    let he := (eta_pos hm ht).le
    let hs := (eta_le_one_div_256 hm h2m hT).trans (by norm_num : (1:ℝ)/256 ≤ 1/16)
    |((∫ h, History.selectedCount i T h
      ∂(observableProcess P hm (eta m T) he hs (Function.update U i 1)
        (update_signs_bounded U hU i (by norm_num))).law T) -
      ∫ h, History.selectedCount i T h
      ∂(observableProcess P hm (eta m T) he hs (Function.update U i (-1))
        (update_signs_bounded U hU i (by norm_num))).law T) / 2| ≤ (T : ℝ) / 16 := by
  dsimp only
  exact count_bias_le_of_tv i _ _ (observable_flip_TV_le_one_eighth P hm h2m hT U hU i)

end

end MsetsPaper.Lower.DenseCommonNoise
