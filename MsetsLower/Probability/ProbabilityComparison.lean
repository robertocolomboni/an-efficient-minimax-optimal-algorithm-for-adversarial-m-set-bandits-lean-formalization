import MsetsLower.Prelude
import Mathlib.InformationTheory.KullbackLeibler.Basic

/-!
# Probability comparison from relative entropy

This file formalizes `lem:probability-comparison`.  The intermediate result is
the binary data-processing inequality for the measurable partition `E, Eᶜ`.
-/

namespace MsetsLower.Probability

open MeasureTheory Set Real
open scoped ENNReal

noncomputable section

/-- Binary entropy in nats, with Mathlib's endpoint convention `log 0 = 0`. -/
private def binaryEntropy (a : ℝ) : ℝ :=
  a * log a⁻¹ + (1 - a) * log (1 - a)⁻¹

private lemma binaryEntropy_le_log_two
    {a : ℝ} (ha0 : 0 ≤ a) (ha1 : a ≤ 1) :
    binaryEntropy a ≤ log 2 := by
  rcases ha0.eq_or_lt with rfl | ha_pos
  · simp [binaryEntropy]
    positivity
  rcases ha1.eq_or_lt with rfl | ha_lt
  · simp [binaryEntropy]
    positivity
  have hcomp_pos : 0 < 1 - a := sub_pos.mpr ha_lt
  have hconcave := strictConcaveOn_log_Ioi.concaveOn.2
    (inv_pos.mpr ha_pos) (inv_pos.mpr hcomp_pos)
    ha_pos.le hcomp_pos.le (by ring)
  calc
    binaryEntropy a ≤
        log (a * a⁻¹ + (1 - a) * (1 - a)⁻¹) := by
      simpa [binaryEntropy, smul_eq_mul] using hconcave
    _ = log 2 := by
      rw [mul_inv_cancel₀ ha_pos.ne', mul_inv_cancel₀ hcomp_pos.ne',
        one_add_one_eq_two]

private lemma mass_mul_klFun_le_setIntegral
    {Ω : Type*} [MeasurableSpace Ω]
    (P Q : Measure Ω) [IsProbabilityMeasure P] [IsProbabilityMeasure Q]
    {E : Set Ω}
    (hPQ : P ≪ Q) (hllr : Integrable (llr P Q) P)
    (hQE : 0 < Q.real E) :
    Q.real E * InformationTheory.klFun (P.real E / Q.real E) ≤
      ∫ ω in E,
        InformationTheory.klFun ((P.rnDeriv Q ω).toReal) ∂Q := by
  let r : Ω → ℝ := fun ω => (P.rnDeriv Q ω).toReal
  have hQEnn : Q E ≠ 0 := by
    intro hzero
    have : Q.real E = 0 := by simp [measureReal_def, hzero]
    linarith
  have hQEtop : Q E ≠ ∞ := measure_ne_top Q E
  have hr_nonneg : ∀ᵐ ω ∂Q.restrict E, r ω ∈ Ici (0 : ℝ) :=
    ae_of_all _ fun _ => ENNReal.toReal_nonneg
  have hr_int : IntegrableOn r E Q :=
    Measure.integrable_toReal_rnDeriv.integrableOn
  have hkl_int_global :
      Integrable (fun ω => InformationTheory.klFun (r ω)) Q := by
    simpa [r] using
      (InformationTheory.integrable_klFun_rnDeriv_iff hPQ).2 hllr
  have hkl_int :
      IntegrableOn (InformationTheory.klFun ∘ r) E Q := by
    simpa [Function.comp_def] using hkl_int_global.integrableOn
  have hJensen := InformationTheory.convexOn_klFun.map_set_average_le
    InformationTheory.continuous_klFun.continuousOn isClosed_Ici
    hQEnn hQEtop hr_nonneg hr_int hkl_int
  have hr_mass : (∫ ω in E, r ω ∂Q) = P.real E := by
    simpa [r] using Measure.setIntegral_toReal_rnDeriv hPQ E
  rw [setAverage_eq, setAverage_eq, hr_mass] at hJensen
  simp only [smul_eq_mul] at hJensen
  calc
    Q.real E * InformationTheory.klFun (P.real E / Q.real E) =
        Q.real E * InformationTheory.klFun ((Q.real E)⁻¹ * P.real E) := by
      rw [div_eq_inv_mul]
    _ ≤ Q.real E *
        ((Q.real E)⁻¹ *
          ∫ ω in E,
            InformationTheory.klFun ((P.rnDeriv Q ω).toReal) ∂Q) :=
      mul_le_mul_of_nonneg_left (by simpa [r] using hJensen) hQE.le
    _ = ∫ ω in E,
          InformationTheory.klFun ((P.rnDeriv Q ω).toReal) ∂Q := by
      rw [← mul_assoc, mul_inv_cancel₀ hQE.ne', one_mul]

/-- Binary data processing for the two atoms `E` and `Eᶜ`, stated in the
`klFun` form that remains valid at the endpoints of `P(E)`. -/
theorem binary_klFun_le_toReal_klDiv
    {Ω : Type*} [MeasurableSpace Ω]
    (P Q : Measure Ω) [IsProbabilityMeasure P] [IsProbabilityMeasure Q]
    {E : Set Ω} (hE : MeasurableSet E)
    (hPQ : P ≪ Q) (hllr : Integrable (llr P Q) P)
    (hQE_pos : 0 < Q.real E) (hQE_lt_one : Q.real E < 1) :
    Q.real E * InformationTheory.klFun (P.real E / Q.real E) +
        (1 - Q.real E) *
          InformationTheory.klFun ((1 - P.real E) / (1 - Q.real E)) ≤
      (InformationTheory.klDiv P Q).toReal := by
  have hcomp := mass_mul_klFun_le_setIntegral P Q (E := Eᶜ) hPQ hllr
    (by simpa [probReal_compl_eq_one_sub hE] using sub_pos.mpr hQE_lt_one)
  have hmain := mass_mul_klFun_le_setIntegral P Q (E := E) hPQ hllr hQE_pos
  rw [probReal_compl_eq_one_sub hE, probReal_compl_eq_one_sub hE] at hcomp
  have hkl_int :
      Integrable
        (fun ω => InformationTheory.klFun ((P.rnDeriv Q ω).toReal)) Q :=
    (InformationTheory.integrable_klFun_rnDeriv_iff hPQ).2 hllr
  calc
    Q.real E * InformationTheory.klFun (P.real E / Q.real E) +
        (1 - Q.real E) *
          InformationTheory.klFun ((1 - P.real E) / (1 - Q.real E)) ≤
        (∫ ω in E,
          InformationTheory.klFun ((P.rnDeriv Q ω).toReal) ∂Q) +
        ∫ ω in Eᶜ,
          InformationTheory.klFun ((P.rnDeriv Q ω).toReal) ∂Q :=
      add_le_add hmain hcomp
    _ = ∫ ω,
          InformationTheory.klFun ((P.rnDeriv Q ω).toReal) ∂Q :=
      integral_add_compl hE hkl_int
    _ = (InformationTheory.klDiv P Q).toReal := by
      rw [InformationTheory.toReal_klDiv_eq_integral_klFun hPQ]

private lemma binary_klFun_lower_bound
    {a b : ℝ} (ha0 : 0 ≤ a) (ha1 : a ≤ 1)
    (hb0 : 0 < b) (hb1 : b < 1) :
    a * log (1 / b) - log 2 ≤
      b * InformationTheory.klFun (a / b) +
        (1 - b) * InformationTheory.klFun ((1 - a) / (1 - b)) := by
  rcases ha0.eq_or_lt with rfl | ha_pos
  · have hnonneg :
        0 ≤ b * InformationTheory.klFun (0 / b) +
          (1 - b) * InformationTheory.klFun ((1 - 0) / (1 - b)) := by
      exact add_nonneg
        (mul_nonneg hb0.le
          (InformationTheory.klFun_nonneg (div_nonneg (by norm_num) hb0.le)))
        (mul_nonneg (sub_nonneg.mpr hb1.le)
          (InformationTheory.klFun_nonneg
            (div_nonneg (by norm_num) (sub_nonneg.mpr hb1.le))))
    have hlog_two : 0 ≤ log 2 := log_nonneg (by norm_num)
    simpa using (le_trans (neg_nonpos.mpr hlog_two) hnonneg)
  rcases ha1.eq_or_lt with rfl | ha_lt
  · have hb_ne : b ≠ 0 := hb0.ne'
    have hcomp_ne : 1 - b ≠ 0 := (sub_pos.mpr hb1).ne'
    have hid :
        b * InformationTheory.klFun (1 / b) +
            (1 - b) * InformationTheory.klFun ((1 - 1) / (1 - b)) =
          log (1 / b) := by
      rw [InformationTheory.klFun_apply, InformationTheory.klFun_apply,
        Real.log_div one_ne_zero hb_ne]
      simp
      field_simp
      ring
    rw [hid]
    have hlog_two : 0 ≤ log 2 := log_nonneg (by norm_num)
    linarith
  have hcomp_a_pos : 0 < 1 - a := sub_pos.mpr ha_lt
  have hcomp_b_pos : 0 < 1 - b := sub_pos.mpr hb1
  have hid :
      b * InformationTheory.klFun (a / b) +
          (1 - b) * InformationTheory.klFun ((1 - a) / (1 - b)) =
        -binaryEntropy a - a * log b - (1 - a) * log (1 - b) := by
    rw [InformationTheory.klFun_apply, InformationTheory.klFun_apply,
      binaryEntropy, Real.log_div ha_pos.ne' hb0.ne',
      Real.log_div hcomp_a_pos.ne' hcomp_b_pos.ne',
      Real.log_inv, Real.log_inv]
    field_simp
    ring
  have hentropy := binaryEntropy_le_log_two ha0 ha1
  have hlog_comp : log (1 - b) ≤ 0 :=
    log_nonpos hcomp_b_pos.le (by linarith)
  have hterm : 0 ≤ -(1 - a) * log (1 - b) :=
    mul_nonneg_of_nonpos_of_nonpos (neg_nonpos.mpr hcomp_a_pos.le) hlog_comp
  rw [hid, one_div, Real.log_inv]
  linarith

/-- `lem:probability-comparison`: if `P(E) ≥ p`, the KL divergence is at
most `(p / 4) log (1 / δ)`, and `δ ≤ 2 ^ (-2 / p)`, then `Q(E) ≥ δ`.

The KL hypothesis is kept in `ℝ≥0∞`, so it excludes both failure of absolute
continuity and non-integrability exactly as the manuscript's extended-real
convention does. -/
theorem probability_comparison
    {Ω : Type*} [MeasurableSpace Ω]
    (P Q : Measure Ω) [IsProbabilityMeasure P] [IsProbabilityMeasure Q]
    {E : Set Ω} (hE : MeasurableSet E)
    {p δ : ℝ} (hp_pos : 0 < p) (_hp_le_one : p ≤ 1)
    (hPE : p ≤ P.real E)
    (hKL : InformationTheory.klDiv P Q ≤
      ENNReal.ofReal (p / 4 * log (1 / δ)))
    (hδ_pos : 0 < δ)
    (hδ_upper : δ ≤ (2 : ℝ) ^ (-2 / p)) :
    δ ≤ Q.real E := by
  have hexponent_neg : -2 / p < 0 := by
    have : 0 < 2 / p := div_pos (by norm_num) hp_pos
    have hneg : -(2 / p) < 0 := neg_neg_of_pos this
    simpa only [neg_div] using hneg
  have hthreshold_lt_one : (2 : ℝ) ^ (-2 / p) < 1 :=
    Real.rpow_lt_one_of_one_lt_of_neg (by norm_num) hexponent_neg
  have hδ_lt_one : δ < 1 := hδ_upper.trans_lt hthreshold_lt_one
  have hlog_pos : 0 < log (1 / δ) :=
    log_pos (one_lt_one_div hδ_pos hδ_lt_one)
  have hKL_finite : InformationTheory.klDiv P Q ≠ ∞ :=
    ne_top_of_le_ne_top ENNReal.ofReal_ne_top hKL
  obtain ⟨hPQ, hllr⟩ :=
    InformationTheory.klDiv_ne_top_iff.mp hKL_finite
  have hPE_pos : 0 < P.real E := hp_pos.trans_le hPE
  have hQE_pos : 0 < Q.real E := by
    have hQE_ne : Q.real E ≠ 0 := by
      intro hzero
      have hQzero : Q E = 0 := (measureReal_eq_zero_iff).mp hzero
      have hPzero : P E = 0 := hPQ hQzero
      have hPreal_zero : P.real E = 0 := (measureReal_eq_zero_iff).2 hPzero
      exact hPE_pos.ne' hPreal_zero
    exact lt_of_le_of_ne measureReal_nonneg (Ne.symm hQE_ne)
  have hlog_delta_bound : log δ ≤ (-2 / p) * log 2 := by
    have h := Real.log_le_log hδ_pos hδ_upper
    rw [Real.log_rpow (by norm_num : (0 : ℝ) < 2)] at h
    exact h
  have hneg_log_delta_bound :
      (2 / p) * log 2 ≤ -log δ := by
    calc
      (2 / p) * log 2 = -((-2 / p) * log 2) := by ring
      _ ≤ -log δ := neg_le_neg hlog_delta_bound
  have hlog_two_bound : log 2 ≤ p / 2 * log (1 / δ) := by
    calc
      log 2 = (p / 2) * ((2 / p) * log 2) := by
        field_simp [hp_pos.ne']
      _ ≤ (p / 2) * (-log δ) :=
        mul_le_mul_of_nonneg_left hneg_log_delta_bound
          (div_nonneg hp_pos.le (by norm_num))
      _ = p / 2 * log (1 / δ) := by
        rw [one_div, Real.log_inv]
  have hP_le_one : P.real E ≤ 1 := by
    calc
      P.real E ≤ P.real univ := measureReal_mono (subset_univ E)
      _ = 1 := probReal_univ
  have hKL_real_upper :
      (InformationTheory.klDiv P Q).toReal ≤
        p / 4 * log (1 / δ) :=
    ENNReal.toReal_le_of_le_ofReal
      (mul_nonneg (div_nonneg hp_pos.le (by norm_num)) hlog_pos.le) hKL
  by_contra hconclusion
  have hQE_lt_delta : Q.real E < δ := lt_of_not_ge hconclusion
  have hQE_lt_one : Q.real E < 1 := hQE_lt_delta.trans hδ_lt_one
  have hdata := binary_klFun_le_toReal_klDiv
    P Q hE hPQ hllr hQE_pos hQE_lt_one
  have hlower := binary_klFun_lower_bound
    measureReal_nonneg hP_le_one hQE_pos hQE_lt_one
  have hbinary_lower :
      p * log (1 / δ) - log 2 <
        (InformationTheory.klDiv P Q).toReal := by
    have hinv_lt : 1 / δ < 1 / Q.real E :=
      one_div_lt_one_div_of_lt hQE_pos hQE_lt_delta
    have hlog_lt : log (1 / δ) < log (1 / Q.real E) :=
      Real.log_lt_log (one_div_pos.mpr hδ_pos) hinv_lt
    have hmul_lt :
        p * log (1 / δ) < P.real E * log (1 / Q.real E) := by
      calc
        p * log (1 / δ) ≤ P.real E * log (1 / δ) :=
          mul_le_mul_of_nonneg_right hPE hlog_pos.le
        _ < P.real E * log (1 / Q.real E) :=
          mul_lt_mul_of_pos_left hlog_lt hPE_pos
    exact (sub_lt_sub_right hmul_lt (log 2)).trans_le (hlower.trans hdata)
  have hhalf_lower :
      p / 2 * log (1 / δ) ≤
        p * log (1 / δ) - log 2 := by
    linarith
  have hKL_real_lower :
      p / 2 * log (1 / δ) <
        (InformationTheory.klDiv P Q).toReal :=
    hhalf_lower.trans_lt hbinary_lower
  have hquarter_lt_half :
      p / 4 * log (1 / δ) < p / 2 * log (1 / δ) := by
    nlinarith
  exact lt_asymm (hKL_real_upper.trans_lt hquarter_lt_half) hKL_real_lower

end

end MsetsLower.Probability
