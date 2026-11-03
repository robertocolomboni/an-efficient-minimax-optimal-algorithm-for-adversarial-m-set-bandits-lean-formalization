import MsetsPaper.Lower.ConfidenceOblivious

/-! # Exact constants and admissibility for the new confidence proposition -/

namespace MsetsPaper.Lower.ConfidenceOblivious

open MsetsLower MsetsLower.Lower MsetsLower.Lower.Confidence
open MeasureTheory Set

noncomputable section

theorem candidate_card_bounds {d m : ℕ} (hm : 1 ≤ m) (h2m : 2 * m ≤ d)
    (hmd : m ≤ d) :
    2 ≤ (confidenceCandidates d m hmd).card ∧
      (confidenceCandidates d m hmd).card ≤ d ∧
      d ≤ 2 * (confidenceCandidates d m hmd).card := by
  rw [card_confidenceCandidates hm hmd]
  omega

theorem log_inverse_positive {delta : ℝ} (hdelta : 0 < delta)
    (hsmall : delta ≤ (2 : ℝ) ^ (-36 : ℤ)) : 0 < Real.log (1 / delta) := by
  have hlt : delta < 1 := hsmall.trans_lt (by norm_num)
  exact Real.log_pos ((lt_div_iff₀ hdelta).2 (by simpa using hlt))

theorem log_inverse_ge_thirty_six_log_two {delta : ℝ} (hdelta : 0 < delta)
    (hsmall : delta ≤ (2 : ℝ) ^ (-36 : ℤ)) :
    36 * Real.log 2 ≤ Real.log (1 / delta) := by
  have hp : (0 : ℝ) < 2 ^ 36 := by positivity
  have hpow : (2 : ℝ) ^ 36 ≤ 1 / delta := by
    apply (le_div_iff₀ hdelta).2
    have h := mul_le_mul_of_nonneg_left hsmall hp.le
    norm_num at h ⊢
    exact h
  have h := Real.log_le_log hp hpow
  simpa only [Real.log_pow, Nat.cast_ofNat] using h

def gap {d m : ℕ} (hmd : m ≤ d) (T : ℕ) (delta : ℝ) : ℝ :=
  confidenceDelta ((confidenceCandidates d m hmd).card : ℝ) (Real.log (1 / delta)) T

theorem horizon_pos {d m T : ℕ} (hm : 1 ≤ m) (h2m : 2 * m ≤ d)
    {delta : ℝ} (hdelta : 0 < delta) (hsmall : delta ≤ (2 : ℝ) ^ (-36 : ℤ))
    (hT : 4 * (d : ℝ) * (m : ℝ) ^ 2 * Real.log (1 / delta) ≤ T) : 0 < T := by
  have hd : 0 < d := by omega
  have hlog := log_inverse_positive hdelta hsmall
  have htR : (0 : ℝ) < T := lt_of_lt_of_le (by positivity) hT
  exact_mod_cast htR

theorem gap_pos {d m T : ℕ} (hm : 1 ≤ m) (h2m : 2 * m ≤ d) (hmd : m ≤ d)
    {delta : ℝ} (hdelta : 0 < delta) (hsmall : delta ≤ (2 : ℝ) ^ (-36 : ℤ))
    (hT : 0 < T) : 0 < gap hmd T delta := by
  have hN : 0 < (confidenceCandidates d m hmd).card :=
    lt_of_lt_of_le (by norm_num) (candidate_card_bounds hm h2m hmd).1
  have hlog := log_inverse_positive hdelta hsmall
  unfold gap confidenceDelta confidenceConstant
  positivity

theorem gap_scaled_sqrt_identity {d m T : ℕ} (hmd : m ≤ d) (delta : ℝ) :
    (m : ℝ) * gap hmd T delta = (2 : ℝ) ^ (-12 : ℤ) *
      Real.sqrt ((m : ℝ) ^ 2 * (confidenceCandidates d m hmd).card * Real.log (1 / delta) / T) := by
  have heq : (m : ℝ) ^ 2 * (confidenceCandidates d m hmd).card * Real.log (1 / delta) / T =
      (m : ℝ) ^ 2 * ((confidenceCandidates d m hmd).card * Real.log (1 / delta) / T) := by ring
  rw [heq, Real.sqrt_mul (sq_nonneg (m : ℝ)), Real.sqrt_sq_eq_abs, abs_of_nonneg (Nat.cast_nonneg m)]
  unfold gap confidenceDelta confidenceConstant
  rw [show (2 : ℝ) ^ (-12 : ℤ) = 1 / 2 ^ 12 by norm_num]
  ring

theorem gap_small_sqrt_chain {d m T : ℕ} (hm : 1 ≤ m) (h2m : 2 * m ≤ d) (hmd : m ≤ d)
    {delta : ℝ} (hdelta : 0 < delta) (hdsmall : delta ≤ (2 : ℝ) ^ (-36 : ℤ))
    (hT : 4 * (d : ℝ) * (m : ℝ) ^ 2 * Real.log (1 / delta) ≤ T) :
    (m : ℝ) * gap hmd T delta ≤ (2 : ℝ) ^ (-13 : ℤ) *
      Real.sqrt ((confidenceCandidates d m hmd).card / (d : ℝ)) ∧
      (2 : ℝ) ^ (-13 : ℤ) * Real.sqrt ((confidenceCandidates d m hmd).card / (d : ℝ)) ≤
        (2 : ℝ) ^ (-13 : ℤ) := by
  have hd : (0 : ℝ) < d := by exact_mod_cast (show 0 < d by omega)
  have ht : (0 : ℝ) < T := by exact_mod_cast horizon_pos hm h2m hdelta hdsmall hT
  have hN0 : (0 : ℝ) ≤ (confidenceCandidates d m hmd).card := by positivity
  have hNle : ((confidenceCandidates d m hmd).card : ℝ) ≤ d := by
    exact_mod_cast (candidate_card_bounds hm h2m hmd).2.1
  have harg : (m : ℝ) ^ 2 * (confidenceCandidates d m hmd).card * Real.log (1 / delta) / T ≤
      ((confidenceCandidates d m hmd).card : ℝ) / (4 * d) := by
    apply (div_le_div_iff₀ ht (by positivity : (0 : ℝ) < 4 * d)).mpr
    have hh := mul_le_mul_of_nonneg_left hT hN0
    nlinarith
  have hsqrt := Real.sqrt_le_sqrt harg
  have harg_eq : ((confidenceCandidates d m hmd).card : ℝ) / (4 * d) =
      (((confidenceCandidates d m hmd).card : ℝ) / d) / 4 := by ring
  rw [harg_eq, Real.sqrt_div (div_nonneg hN0 hd.le)] at hsqrt
  rw [show Real.sqrt (4 : ℝ) = 2 by
    nlinarith [Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 4), Real.sqrt_nonneg (4 : ℝ)]] at hsqrt
  constructor
  · rw [gap_scaled_sqrt_identity]
    have hh := mul_le_mul_of_nonneg_left hsqrt (by norm_num : (0 : ℝ) ≤ 1 / 4096)
    norm_num only [show (2 : ℝ) ^ (-12 : ℤ) = 1 / 4096 by norm_num,
      show (2 : ℝ) ^ (-13 : ℤ) = 1 / 8192 by norm_num]
    linarith
  · have hs : Real.sqrt (((confidenceCandidates d m hmd).card : ℝ) / d) ≤ 1 :=
      Real.sqrt_le_one.mpr ((div_le_one hd).mpr hNle)
    exact (mul_le_mul_of_nonneg_left hs (by positivity)).trans_eq (mul_one _)

theorem gap_small {d m T : ℕ} (hm : 1 ≤ m) (h2m : 2 * m ≤ d) (hmd : m ≤ d)
    {delta : ℝ} (hdelta : 0 < delta) (hsmall : delta ≤ (2 : ℝ) ^ (-36 : ℤ))
    (hT : 4 * (d : ℝ) * (m : ℝ) ^ 2 * Real.log (1 / delta) ≤ T) :
    (m : ℝ) * gap hmd T delta ≤ (2 : ℝ) ^ (-13 : ℤ) ∧
      4 * gap hmd T delta ≤ (2 : ℝ) ^ (-11 : ℤ) := by
  have hchain := gap_small_sqrt_chain hm h2m hmd hdelta hsmall hT
  have hmg := hchain.1.trans hchain.2
  have hmR : (1 : ℝ) ≤ m := by exact_mod_cast hm
  have hp := (gap_pos hm h2m hmd hdelta hsmall (horizon_pos hm h2m hdelta hsmall hT)).le
  constructor
  · exact hmg
  · norm_num at hmg ⊢
    nlinarith


theorem gap_square_time_div_candidates {d m T : ℕ}
    (hm : 1 ≤ m) (h2m : 2 * m ≤ d) (hmd : m ≤ d)
    {delta : ℝ} (hdelta : 0 < delta) (hsmall : delta ≤ (2 : ℝ) ^ (-36 : ℤ)) (hT : 0 < T) :
    (gap hmd T delta) ^ 2 * T / (confidenceCandidates d m hmd).card =
      (2 : ℝ) ^ (-24 : ℤ) * Real.log (1 / delta) := by
  have hN : 0 < (confidenceCandidates d m hmd).card :=
    lt_of_lt_of_le (by norm_num) (candidate_card_bounds hm h2m hmd).1
  have hN0 : ((confidenceCandidates d m hmd).card : ℝ) ≠ 0 := by
    exact_mod_cast Nat.ne_of_gt hN
  have hT0 : (T : ℝ) ≠ 0 := by exact_mod_cast Nat.ne_of_gt hT
  have hlog := log_inverse_positive hdelta hsmall
  have hsq := Real.sq_sqrt (show (0 : ℝ) ≤
    (confidenceCandidates d m hmd).card * Real.log (1 / delta) / T by positivity)
  unfold gap confidenceDelta confidenceConstant
  rw [mul_pow, hsq]
  norm_num
  field_simp

theorem gap_time_div_eight {d m T : ℕ} (hmd : m ≤ d) {delta : ℝ}
    (hlog : 0 ≤ Real.log (1 / delta)) (hT : 0 < T) :
    gap hmd T delta * T / 8 = (2 : ℝ) ^ (-15 : ℤ) *
      Real.sqrt ((confidenceCandidates d m hmd).card * T * Real.log (1 / delta)) := by
  have htR : (0 : ℝ) ≤ T := by positivity
  have hs : Real.sqrt (((confidenceCandidates d m hmd).card : ℝ) * Real.log (1 / delta) / T) * T =
      Real.sqrt ((confidenceCandidates d m hmd).card * T * Real.log (1 / delta)) := by
    have hsqrt0 : Real.sqrt (T : ℝ) ≠ 0 := ne_of_gt (by positivity)
    have hA : (0 : ℝ) ≤ (confidenceCandidates d m hmd).card * Real.log (1 / delta) := by positivity
    calc
      _ = (Real.sqrt ((confidenceCandidates d m hmd).card * Real.log (1 / delta)) /
          Real.sqrt T) * T := by rw [Real.sqrt_div hA]
      _ = Real.sqrt ((confidenceCandidates d m hmd).card * Real.log (1 / delta)) *
          Real.sqrt T := by
        field_simp
        rw [Real.sq_sqrt htR]
      _ = Real.sqrt (((confidenceCandidates d m hmd).card : ℝ) * Real.log (1 / delta) * T) :=
        (Real.sqrt_mul hA _).symm
      _ = _ := by congr 1; ring
  unfold gap confidenceDelta
  rw [show confidenceConstant * Real.sqrt
    (((confidenceCandidates d m hmd).card : ℝ) * Real.log (1 / delta) / T) * T / 8 =
      confidenceConstant / 8 * (Real.sqrt
        (((confidenceCandidates d m hmd).card : ℝ) * Real.log (1 / delta) / T) * T) by ring,
    hs]
  norm_num [confidenceConstant]

theorem gap_threshold_dominates_target {d m T : ℕ}
    (hm : 1 ≤ m) (h2m : 2 * m ≤ d) (hmd : m ≤ d) {delta : ℝ}
    (hlog : 0 ≤ Real.log (1 / delta)) (hT : 0 < T) :
    (2 : ℝ) ^ (-16 : ℤ) * Real.sqrt ((d : ℝ) * T * Real.log (1 / delta)) ≤
      gap hmd T delta * T / 8 := by
  rw [gap_time_div_eight hmd hlog hT]
  have hN : (d : ℝ) / 2 ≤ (confidenceCandidates d m hmd).card := by
    have h := (candidate_card_bounds hm h2m hmd).2.2
    have hc : (d : ℝ) ≤ 2 * ((confidenceCandidates d m hmd).card : ℝ) := by exact_mod_cast h
    linarith
  have h := confidence_score_dominates_target
    (Nat.cast_nonneg d) (Nat.cast_nonneg T) hlog hN
  norm_num [confidenceConstant] at h ⊢
  exact h

end

end MsetsPaper.Lower.ConfidenceOblivious
