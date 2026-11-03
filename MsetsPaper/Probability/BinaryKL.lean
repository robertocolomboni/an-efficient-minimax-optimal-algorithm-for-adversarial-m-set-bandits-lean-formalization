import MsetsLower.Probability.ProbabilityComparison
import Mathlib.Analysis.Convex.Jensen

/-! # Binary KL, including compatible zero-mass endpoints

The real-valued formula is only used with explicitly proved absolute-
continuity compatibility. Infinite native KL is never silently converted to
zero. Finite mixtures use the perspective Jensen inequality proved below.
-/

noncomputable section
open MeasureTheory InformationTheory Set Real
open scoped ENNReal BigOperators

namespace MsetsPaper.Probability

def binaryKL (a b : ℝ) : ℝ :=
  b * klFun (a / b) + (1 - b) * klFun ((1 - a) / (1 - b))

def BinaryCompatible (a b : ℝ) : Prop :=
  (b = 0 → a = 0) ∧ (b = 1 → a = 1)

theorem binaryKL_nonneg {a b : ℝ} (ha : a ∈ Icc (0 : ℝ) 1) (hb : b ∈ Icc (0 : ℝ) 1) :
    0 ≤ binaryKL a b := by
  exact add_nonneg (mul_nonneg hb.1 (klFun_nonneg (div_nonneg ha.1 hb.1)))
    (mul_nonneg (sub_nonneg.mpr hb.2)
      (klFun_nonneg (div_nonneg (sub_nonneg.mpr ha.2) (sub_nonneg.mpr hb.2))))

@[simp] theorem binaryKL_zero_zero : binaryKL 0 0 = 0 := by simp [binaryKL, klFun_apply]
@[simp] theorem binaryKL_one_one : binaryKL 1 1 = 0 := by simp [binaryKL, klFun_apply]

theorem klFun_perspective_sum_le {ι : Type*} [Fintype ι]
    (p q : ι → ℝ) (hp : ∀ i, 0 ≤ p i) (hq : ∀ i, 0 ≤ q i)
    (hzero : ∀ i, q i = 0 → p i = 0) :
    (∑ i, q i) * klFun ((∑ i, p i) / (∑ i, q i)) ≤ ∑ i, q i * klFun (p i / q i) := by
  classical
  let B := ∑ i, q i
  have hB0 : 0 ≤ B := Finset.sum_nonneg (fun i _ ↦ hq i)
  by_cases hB : B = 0
  · change B * _ ≤ _
    rw [hB, zero_mul]
    exact Finset.sum_nonneg (fun i _ ↦ mul_nonneg (hq i) (klFun_nonneg (div_nonneg (hp i) (hq i))))
  have hBpos : 0 < B := lt_of_le_of_ne hB0 (Ne.symm hB)
  have hw : ∑ i, q i / B = 1 := by rw [← Finset.sum_div]; exact div_self hB
  have hJ := convexOn_klFun.map_sum_le (t := Finset.univ)
    (w := fun i ↦ q i / B) (p := fun i ↦ p i / q i)
    (fun i _ ↦ div_nonneg (hq i) hB0) hw
    (fun i _ ↦ div_nonneg (hp i) (hq i))
  simp only [smul_eq_mul] at hJ
  have hm : (∑ i, q i / B * (p i / q i)) = (∑ i, p i) / B := by
    rw [Finset.sum_div]
    apply Finset.sum_congr rfl
    intro i _
    by_cases hqi : q i = 0
    · simp [hqi, hzero i hqi]
    · field_simp
  rw [hm] at hJ
  have hscaled := mul_le_mul_of_nonneg_left hJ hB0
  change B * _ ≤ _
  refine hscaled.trans_eq ?_
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i _
  field_simp

theorem klFun_perspective_smul (w a b : ℝ) :
    (w * b) * klFun ((w * a) / (w * b)) = w * (b * klFun (a / b)) := by
  by_cases hw : w = 0
  · simp [hw]
  · rw [mul_div_mul_left _ _ hw]
    ring

theorem binaryKL_finite_mixture {ι : Type*} [Fintype ι]
    (w p q : ι → ℝ) (hw : ∀ i, 0 ≤ w i) (hwsum : ∑ i, w i = 1)
    (hp : ∀ i, p i ∈ Icc (0 : ℝ) 1) (hq : ∀ i, q i ∈ Icc (0 : ℝ) 1)
    (hc : ∀ i, BinaryCompatible (p i) (q i)) :
    binaryKL (∑ i, w i * p i) (∑ i, w i * q i) ≤ ∑ i, w i * binaryKL (p i) (q i) := by
  have hmain := klFun_perspective_sum_le (fun i ↦ w i * p i) (fun i ↦ w i * q i)
    (fun i ↦ mul_nonneg (hw i) (hp i).1) (fun i ↦ mul_nonneg (hw i) (hq i).1)
    (fun i hz ↦ by
      rcases mul_eq_zero.mp hz with hh | hh
      · simp [hh]
      · simp [(hc i).1 hh])
  have hcomp := klFun_perspective_sum_le (fun i ↦ w i * (1 - p i)) (fun i ↦ w i * (1 - q i))
    (fun i ↦ mul_nonneg (hw i) (sub_nonneg.mpr (hp i).2))
    (fun i ↦ mul_nonneg (hw i) (sub_nonneg.mpr (hq i).2))
    (fun i hz ↦ by
      rcases mul_eq_zero.mp hz with hh | hh
      · simp [hh]
      · have hq1 : q i = 1 := by linarith
        simp [(hc i).2 hq1])
  have hpcomp : ∑ i, w i * (1 - p i) = 1 - ∑ i, w i * p i := by
    simp only [mul_sub, mul_one, Finset.sum_sub_distrib, hwsum]
  have hqcomp : ∑ i, w i * (1 - q i) = 1 - ∑ i, w i * q i := by
    simp only [mul_sub, mul_one, Finset.sum_sub_distrib, hwsum]
  rw [hpcomp, hqcomp] at hcomp
  simp_rw [klFun_perspective_smul] at hmain hcomp
  unfold binaryKL
  simp only [mul_add, Finset.sum_add_distrib]
  exact add_le_add hmain hcomp

theorem BinaryCompatible_finite_mixture {ι : Type*} [Fintype ι]
    (w p q : ι → ℝ) (hw : ∀ i, 0 ≤ w i) (hwsum : ∑ i, w i = 1)
    (hp : ∀ i, p i ∈ Icc (0 : ℝ) 1) (hq : ∀ i, q i ∈ Icc (0 : ℝ) 1)
    (hc : ∀ i, BinaryCompatible (p i) (q i)) :
    BinaryCompatible (∑ i, w i * p i) (∑ i, w i * q i) := by
  classical
  have hzero (f g : ι → ℝ) (hg : ∀ i, 0 ≤ g i)
      (hfg : ∀ i, g i = 0 → f i = 0) (h : ∑ i, w i * g i = 0) :
      ∑ i, w i * f i = 0 := by
    apply Finset.sum_eq_zero
    intro i hi
    have hgi : w i * g i = 0 :=
      (Finset.sum_eq_zero_iff_of_nonneg (fun j _ ↦ mul_nonneg (hw j) (hg j))).mp h i hi
    rcases mul_eq_zero.mp hgi with hh | hh
    · simp [hh]
    · simp [hfg i hh]
  constructor
  · exact hzero p q (fun i ↦ (hq i).1) (fun i ↦ (hc i).1)
  · intro h
    have hqcomp : ∑ i, w i * (1 - q i) = 0 := by
      simp only [mul_sub, mul_one, Finset.sum_sub_distrib, hwsum, h, sub_self]
    have hpcomp := hzero (fun i ↦ 1 - p i) (fun i ↦ 1 - q i)
      (fun i ↦ sub_nonneg.mpr (hq i).2)
      (fun i hi ↦ by
        have hh : q i = 1 := by linarith
        rw [(hc i).2 hh]
        ring) hqcomp
    simp only [mul_sub, mul_one, Finset.sum_sub_distrib, hwsum] at hpcomp
    linarith

theorem binaryKL_event_compatible {Ω : Type*} [MeasurableSpace Ω]
    (P Q : Measure Ω) [IsProbabilityMeasure P] [IsProbabilityMeasure Q]
    {E : Set Ω} (hE : MeasurableSet E) (hPQ : P ≪ Q) :
    BinaryCompatible (P.real E) (Q.real E) := by
  have hz {S : Set Ω} (h : Q.real S = 0) : P.real S = 0 :=
    (measureReal_eq_zero_iff).mpr (hPQ ((measureReal_eq_zero_iff).mp h))
  constructor
  · exact hz
  · intro h
    have hc : Q.real Eᶜ = 0 := by rw [probReal_compl_eq_one_sub hE, h]; ring
    have hp := hz hc
    rw [probReal_compl_eq_one_sub hE] at hp
    linarith

/-- Event data processing, with finite native KL as an essential premise. -/
theorem binaryKL_event_le_klDiv {Ω : Type*} [MeasurableSpace Ω]
    (P Q : Measure Ω) [IsProbabilityMeasure P] [IsProbabilityMeasure Q]
    {E : Set Ω} (hE : MeasurableSet E) (hfinite : klDiv P Q ≠ ∞) :
    binaryKL (P.real E) (Q.real E) ≤ (klDiv P Q).toReal := by
  obtain ⟨hPQ, hllr⟩ := klDiv_ne_top_iff.mp hfinite
  have hc := binaryKL_event_compatible P Q hE hPQ
  by_cases hz : Q.real E = 0
  · rw [hc.1 hz, hz, binaryKL_zero_zero]
    exact ENNReal.toReal_nonneg
  by_cases ho : Q.real E = 1
  · rw [hc.2 ho, ho, binaryKL_one_one]
    exact ENNReal.toReal_nonneg
  exact MsetsLower.Probability.binary_klFun_le_toReal_klDiv P Q hE hPQ hllr
    (lt_of_le_of_ne measureReal_nonneg (Ne.symm hz))
    (lt_of_le_of_ne (by
      calc Q.real E ≤ Q.real Set.univ := measureReal_mono (Set.subset_univ E)
           _ = 1 := probReal_univ) ho)

def binaryEntropy (a : ℝ) : ℝ :=
  a * log a⁻¹ + (1 - a) * log (1 - a)⁻¹

theorem binaryEntropy_le_log_two {a : ℝ} (ha0 : 0 ≤ a) (ha1 : a ≤ 1) :
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
    binaryEntropy a ≤ log (a * a⁻¹ + (1 - a) * (1 - a)⁻¹) := by
      simpa [binaryEntropy, smul_eq_mul] using hconcave
    _ = log 2 := by
      rw [mul_inv_cancel₀ ha_pos.ne', mul_inv_cancel₀ hcomp_pos.ne', one_add_one_eq_two]

theorem binaryKL_lower_bound {a b : ℝ} (ha0 : 0 ≤ a) (ha1 : a ≤ 1)
    (hb0 : 0 < b) (hb1 : b < 1) :
    a * log (1 / b) - log 2 ≤ binaryKL a b := by
  rcases ha0.eq_or_lt with rfl | ha_pos
  · have hnonneg := binaryKL_nonneg (a := 0) (b := b) (by constructor <;> norm_num)
      ⟨hb0.le, hb1.le⟩
    have hlog_two : 0 ≤ log 2 := log_nonneg (by norm_num)
    simpa using (le_trans (neg_nonpos.mpr hlog_two) hnonneg)
  rcases ha1.eq_or_lt with rfl | ha_lt
  · have hb_ne : b ≠ 0 := hb0.ne'
    have hcomp_ne : 1 - b ≠ 0 := (sub_pos.mpr hb1).ne'
    have hid : binaryKL 1 b = log (1 / b) := by
      rw [binaryKL, klFun_apply, klFun_apply, Real.log_div one_ne_zero hb_ne]
      simp
      field_simp
      ring
    rw [hid]
    have hlog_two : 0 ≤ log 2 := log_nonneg (by norm_num)
    linarith
  have hcomp_a_pos : 0 < 1 - a := sub_pos.mpr ha_lt
  have hcomp_b_pos : 0 < 1 - b := sub_pos.mpr hb1
  have hid : binaryKL a b =
      -binaryEntropy a - a * log b - (1 - a) * log (1 - b) := by
    rw [binaryKL, klFun_apply, klFun_apply, binaryEntropy,
      Real.log_div ha_pos.ne' hb0.ne', Real.log_div hcomp_a_pos.ne' hcomp_b_pos.ne',
      Real.log_inv, Real.log_inv]
    field_simp
    ring
  have hentropy := binaryEntropy_le_log_two ha0 ha1
  have hlog_comp : log (1 - b) ≤ 0 := log_nonpos hcomp_b_pos.le (by linarith)
  have hterm : 0 ≤ -(1 - a) * log (1 - b) :=
    mul_nonneg_of_nonpos_of_nonpos (neg_nonpos.mpr hcomp_a_pos.le) hlog_comp
  rw [hid, one_div, Real.log_inv]
  linarith

end MsetsPaper.Probability
