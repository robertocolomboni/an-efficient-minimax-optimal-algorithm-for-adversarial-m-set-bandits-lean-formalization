import MsetsPaper.Probability.BinaryKL

/-! # Integral joint convexity of compatible binary KL over arbitrary seeds

No discreteness of the mixing probability space is assumed. The perspective
inequality is proved by integrating its supporting affine function; compatible
zero-mass endpoints are handled separately, without dividing by zero.
-/

namespace MsetsPaper.Probability

open MeasureTheory InformationTheory Set Real
open scoped ENNReal BigOperators

noncomputable section

theorem klFun_supporting_line {x c : ℝ} (hx : 0 ≤ x) (hc : 0 < c) :
    klFun c + Real.log c * (x - c) ≤ klFun x := by
  by_cases hx0 : x = 0
  · subst x
    rw [klFun_apply, klFun_apply]
    simp only [zero_mul, zero_sub]
    nlinarith
  have hnon := mul_nonneg hc.le (klFun_nonneg (div_nonneg hx hc.le))
  have hid : c * klFun (x / c) = klFun x - klFun c - Real.log c * (x - c) := by
    simp only [klFun_apply, Real.log_div hx0 hc.ne']
    field_simp
    ring
  rw [hid] at hnon
  linarith

theorem klFun_perspective_affine_lower {p q c : ℝ}
    (hp : 0 ≤ p) (hq : 0 ≤ q) (hzero : q = 0 → p = 0) (hc : 0 < c) :
    p * Real.log c + q * (1 - c) ≤ q * klFun (p / q) := by
  by_cases hq0 : q = 0
  · simp [hq0, hzero hq0]
  have hh := mul_le_mul_of_nonneg_left (klFun_supporting_line (div_nonneg hp hq) hc) hq
  refine le_trans (le_of_eq ?_) hh
  rw [klFun_apply]
  field_simp
  ring

theorem klFun_perspective_integral_le {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) (p q : Ω → ℝ)
    (hp : ∀ x, 0 ≤ p x) (hq : ∀ x, 0 ≤ q x)
    (hzero : ∀ x, q x = 0 → p x = 0)
    (hpi : Integrable p μ) (hqi : Integrable q μ)
    (hFi : Integrable (fun x => q x * klFun (p x / q x)) μ) :
    (∫ x, q x ∂μ) * klFun ((∫ x, p x ∂μ) / (∫ x, q x ∂μ)) ≤
      ∫ x, q x * klFun (p x / q x) ∂μ := by
  let A := ∫ x, p x ∂μ
  let B := ∫ x, q x ∂μ
  have hA0 : 0 ≤ A := integral_nonneg hp
  have hB0 : 0 ≤ B := integral_nonneg hq
  by_cases hB : B = 0
  · change B * _ ≤ _
    rw [hB, zero_mul]
    exact integral_nonneg fun x => mul_nonneg (hq x) (klFun_nonneg (div_nonneg (hp x) (hq x)))
  by_cases hA : A = 0
  · have hpzero : p =ᵐ[μ] 0 := (integral_eq_zero_iff_of_nonneg hp hpi).mp hA
    have hF : (fun x => q x * klFun (p x / q x)) =ᵐ[μ] q := by
      filter_upwards [hpzero] with x hx
      simp [hx, klFun_zero]
    change B * klFun (A / B) ≤ _
    rw [hA, zero_div, klFun_zero, mul_one, integral_congr_ae hF]
  have hApos : 0 < A := lt_of_le_of_ne hA0 (Ne.symm hA)
  have hBpos : 0 < B := lt_of_le_of_ne hB0 (Ne.symm hB)
  have hmono := integral_mono ((hpi.mul_const (Real.log (A / B))).add
    (hqi.mul_const (1 - A / B))) hFi
    (fun x => klFun_perspective_affine_lower (hp x) (hq x) (hzero x) (div_pos hApos hBpos))
  change (∫ x, p x * Real.log (A / B) + q x * (1 - A / B) ∂μ) ≤ _ at hmono
  rw [integral_add (hpi.mul_const _) (hqi.mul_const _), integral_mul_const,
    integral_mul_const] at hmono
  change B * klFun (A / B) ≤ _
  refine le_trans (le_of_eq ?_) hmono
  rw [klFun_apply]
  dsimp only [A, B] at hB ⊢
  field_simp
  ring

theorem measurable_binaryKL {Ω : Type*} [MeasurableSpace Ω] {p q : Ω → ℝ}
    (hp : Measurable p) (hq : Measurable q) :
    Measurable (fun x => binaryKL (p x) (q x)) := by
  unfold binaryKL
  exact (hq.mul (measurable_klFun.comp (hp.div hq))).add
    ((measurable_const.sub hq).mul (measurable_klFun.comp
      ((measurable_const.sub hp).div (measurable_const.sub hq))))

theorem BinaryCompatible_integral {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ] (p q : Ω → ℝ)
    (hpm : Measurable p) (hqm : Measurable q)
    (hp : ∀ x, p x ∈ Icc (0 : ℝ) 1) (hq : ∀ x, q x ∈ Icc (0 : ℝ) 1)
    (hc : ∀ x, BinaryCompatible (p x) (q x)) :
    BinaryCompatible (∫ x, p x ∂μ) (∫ x, q x ∂μ) := by
  have hpi : Integrable p μ := Integrable.of_mem_Icc 0 1 hpm.aemeasurable (ae_of_all _ hp)
  have hqi : Integrable q μ := Integrable.of_mem_Icc 0 1 hqm.aemeasurable (ae_of_all _ hq)
  constructor
  · intro hz
    have hqzero := (integral_eq_zero_iff_of_nonneg (fun x => (hq x).1) hqi).mp hz
    have hpzero : p =ᵐ[μ] 0 := by
      filter_upwards [hqzero] with x hx
      exact (hc x).1 hx
    simpa using integral_congr_ae hpzero
  · intro ho
    have hcqi : Integrable (fun x => 1 - q x) μ := (integrable_const 1).sub hqi
    have hcz : (∫ x, (1 - q x) ∂μ) = 0 := by rw [integral_sub (integrable_const 1) hqi, ho]; simp
    have hqone := (integral_eq_zero_iff_of_nonneg (fun x => sub_nonneg.mpr (hq x).2) hcqi).mp hcz
    have hpone : p =ᵐ[μ] (fun _ => 1) := by
      filter_upwards [hqone] with x hx
      exact (hc x).2 (by change 1 - q x = 0 at hx; linarith)
    simpa using integral_congr_ae hpone

/-- Joint convexity for an arbitrary mixing probability law, including
compatible zero and one endpoints. Integrability of the binary divergence is
required explicitly; the default value of a divergent real integral is not used. -/
theorem binaryKL_integral_mixture {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ] (p q : Ω → ℝ)
    (hpm : Measurable p) (hqm : Measurable q)
    (hp : ∀ x, p x ∈ Icc (0 : ℝ) 1) (hq : ∀ x, q x ∈ Icc (0 : ℝ) 1)
    (hc : ∀ x, BinaryCompatible (p x) (q x))
    (hKL : Integrable (fun x => binaryKL (p x) (q x)) μ) :
    binaryKL (∫ x, p x ∂μ) (∫ x, q x ∂μ) ≤ ∫ x, binaryKL (p x) (q x) ∂μ := by
  have hpi : Integrable p μ := Integrable.of_mem_Icc 0 1 hpm.aemeasurable (ae_of_all _ hp)
  have hqi : Integrable q μ := Integrable.of_mem_Icc 0 1 hqm.aemeasurable (ae_of_all _ hq)
  have hmain0 (x : Ω) : 0 ≤ q x * klFun (p x / q x) :=
    mul_nonneg (hq x).1 (klFun_nonneg (div_nonneg (hp x).1 (hq x).1))
  have hcomp0 (x : Ω) : 0 ≤ (1 - q x) * klFun ((1 - p x) / (1 - q x)) :=
    mul_nonneg (sub_nonneg.mpr (hq x).2)
      (klFun_nonneg (div_nonneg (sub_nonneg.mpr (hp x).2) (sub_nonneg.mpr (hq x).2)))
  have hmaini : Integrable (fun x => q x * klFun (p x / q x)) μ := by
    apply hKL.mono' ((hqm.mul (measurable_klFun.comp (hpm.div hqm))).aestronglyMeasurable)
    exact ae_of_all _ fun x => by
      change |q x * klFun (p x / q x)| ≤ _
      rw [abs_of_nonneg (hmain0 x)]
      exact le_add_of_nonneg_right (hcomp0 x)
  have hcompi : Integrable (fun x => (1 - q x) * klFun ((1 - p x) / (1 - q x))) μ := by
    apply hKL.mono' (((measurable_const.sub hqm).mul (measurable_klFun.comp
      ((measurable_const.sub hpm).div (measurable_const.sub hqm)))).aestronglyMeasurable)
    exact ae_of_all _ fun x => by
      change |(1 - q x) * klFun ((1 - p x) / (1 - q x))| ≤ _
      rw [abs_of_nonneg (hcomp0 x)]
      exact le_add_of_nonneg_left (hmain0 x)
  have hmain := klFun_perspective_integral_le μ p q (fun x => (hp x).1) (fun x => (hq x).1)
    (fun x => (hc x).1) hpi hqi hmaini
  have hcomp := klFun_perspective_integral_le μ (fun x => 1 - p x) (fun x => 1 - q x)
    (fun x => sub_nonneg.mpr (hp x).2) (fun x => sub_nonneg.mpr (hq x).2)
    (fun x hx => by rw [(hc x).2 (by linarith)]; ring)
    ((integrable_const 1).sub hpi) ((integrable_const 1).sub hqi) hcompi
  simp only [integral_sub (integrable_const 1) hpi, integral_sub (integrable_const 1) hqi,
    integral_const, probReal_univ, one_smul] at hcomp
  change _ ≤ ∫ x, q x * klFun (p x / q x) + (1 - q x) * klFun ((1 - p x) / (1 - q x)) ∂μ
  rw [integral_add hmaini hcompi]
  exact add_le_add hmain hcomp

theorem binaryKL_integral_le_integral_bound {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ] (p q B : Ω → ℝ)
    (hpm : Measurable p) (hqm : Measurable q)
    (hp : ∀ x, p x ∈ Icc (0 : ℝ) 1) (hq : ∀ x, q x ∈ Icc (0 : ℝ) 1)
    (hc : ∀ x, BinaryCompatible (p x) (q x)) (hBi : Integrable B μ)
    (hbound : ∀ x, binaryKL (p x) (q x) ≤ B x) :
    binaryKL (∫ x, p x ∂μ) (∫ x, q x ∂μ) ≤ ∫ x, B x ∂μ := by
  have hKL : Integrable (fun x => binaryKL (p x) (q x)) μ := by
    apply hBi.mono' (measurable_binaryKL hpm hqm).aestronglyMeasurable
    exact ae_of_all _ fun x => by
      rw [Real.norm_eq_abs, abs_of_nonneg (binaryKL_nonneg (hp x) (hq x))]
      exact hbound x
  exact (binaryKL_integral_mixture μ p q hpm hqm hp hq hc hKL).trans
    (integral_mono hKL hBi hbound)

end
end MsetsPaper.Probability
