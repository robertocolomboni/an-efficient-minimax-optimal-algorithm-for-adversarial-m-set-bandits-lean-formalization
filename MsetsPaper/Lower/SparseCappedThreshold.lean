import MsetsPaper.Lower.SparseCappedSurvivalArithmetic
import Mathlib.Data.Nat.Choose.Sum
import Mathlib.Data.Nat.Factorial.BigOperators

/-! # Binomial complexity and the exact final sparse threshold -/

namespace MsetsPaper.Lower.SparseCapped

open Real
open scoped BigOperators

theorem choose_mul_ratio_pow_le {d m : ℕ} (hm : 0 < m) (hmd : m ≤ d) :
    (d.choose m : ℝ) * ratio d m ^ m ≤ (1 + ratio d m) ^ d := by
  have hr := (ratio_pos hm hmd).le
  have h := Finset.single_le_sum
    (s := Finset.range (d + 1))
    (f := fun k => ratio d m ^ k * (1 : ℝ) ^ (d - k) * d.choose k)
    (fun k _ => by positivity) (Finset.mem_range.mpr (Nat.lt_succ_of_le hmd))
  rw [← add_pow] at h
  simpa only [one_pow, mul_one, mul_comm, add_comm, one_mul] using h

/-- The binomial coefficient bound precedes taking logarithms. -/
theorem choose_le_exp_ratio_pow {d m : ℕ} (hm : 0 < m) (hmd : m ≤ d) :
    (d.choose m : ℝ) ≤ (exp 1 * d / m) ^ m := by
  have hr := ratio_pos hm hmd
  have hmR : (0 : ℝ) < m := by exact_mod_cast hm
  have hdR : (0 : ℝ) < d := by exact_mod_cast lt_of_lt_of_le hm hmd
  have hpow := pow_le_pow_left₀ (by positivity : 0 ≤ 1 + ratio d m)
    (show 1 + ratio d m ≤ exp (ratio d m) by simpa [add_comm] using add_one_le_exp (ratio d m)) d
  have hcancel : (d : ℝ) * ratio d m = m := by unfold ratio; field_simp
  have h := (choose_mul_ratio_pow_le hm hmd).trans hpow
  rw [← exp_nat_mul, hcancel, ← mul_one (m : ℝ), exp_nat_mul] at h
  apply (mul_le_mul_iff_of_pos_right (pow_pos hr m)).mp
  calc
    _ ≤ (exp 1) ^ m := h
    _ = (exp 1 * d / m) ^ m * ratio d m ^ m := by
      rw [← mul_pow]
      congr 1
      unfold ratio
      field_simp

/-- Logarithmic form of the preceding binomial bound. -/
theorem log_choose_le_entropy {d m : ℕ} (hm : 0 < m) (hmd : m ≤ d) :
    log (d.choose m : ℝ) ≤ (m : ℝ) * (1 + log (1 / ratio d m)) := by
  have hmR : (0 : ℝ) < m := by exact_mod_cast hm
  have hdR : (0 : ℝ) < d := by exact_mod_cast lt_of_lt_of_le hm hmd
  have hchoose : (0 : ℝ) < d.choose m := by exact_mod_cast Nat.choose_pos hmd
  have h := log_le_log hchoose (choose_le_exp_ratio_pow hm hmd)
  rw [log_pow, log_div (by positivity) hmR.ne', log_mul (exp_ne_zero 1) hdR.ne', log_exp] at h
  simpa only [ratio, one_div, log_inv, log_div hmR.ne' hdR.ne', neg_sub,
    ← add_sub_assoc] using h

/-- Each factor (d-i)/(m-i) is at least d/m. -/
theorem ratio_inverse_pow_le_choose {d m : ℕ} (hm : 0 < m) (hmd : m ≤ d) :
    (1 / ratio d m) ^ m ≤ (d.choose m : ℝ) := by
  have hmR : (0 : ℝ) < m := by exact_mod_cast hm
  have hdR : (0 : ℝ) < d := by exact_mod_cast lt_of_lt_of_le hm hmd
  have hprod : (∏ i ∈ Finset.range m, (d : ℝ) / m) ≤
      ∏ i ∈ Finset.range m, ((d - i : ℕ) : ℝ) / (m - i : ℕ) := by
    apply Finset.prod_le_prod₀
    · intro i hi; positivity
    · intro i hi
      have him : i < m := Finset.mem_range.mp hi
      have hid : i ≤ d := (Nat.le_of_lt him).trans hmd
      have hmi : (0 : ℝ) < (m - i : ℕ) := by exact_mod_cast Nat.sub_pos_of_lt him
      apply (div_le_div_iff₀ hmR hmi).mpr
      rw [Nat.cast_sub (Nat.le_of_lt him), Nat.cast_sub hid]
      have hmdR : (m : ℝ) ≤ d := by exact_mod_cast hmd
      nlinarith [mul_nonneg (sub_nonneg.mpr hmdR) (Nat.cast_nonneg i)]
  rw [Finset.prod_const, Finset.card_range, Finset.prod_div_distrib] at hprod
  have hnum : (∏ i ∈ Finset.range m, ((d - i : ℕ) : ℝ)) =
      (m.factorial : ℝ) * (d.choose m : ℝ) := by
    exact_mod_cast (Nat.descFactorial_eq_prod_range d m).symm.trans
      (Nat.descFactorial_eq_factorial_mul_choose d m)
  have hden : (∏ i ∈ Finset.range m, ((m - i : ℕ) : ℝ)) = (m.factorial : ℝ) := by
    exact_mod_cast (Nat.descFactorial_eq_prod_range m m).symm.trans (Nat.descFactorial_self m)
  rw [hnum, hden, mul_div_cancel_left₀ _ (by exact_mod_cast (Nat.factorial_pos m).ne')] at hprod
  convert hprod using 1 <;> unfold ratio <;> congr 1 <;> field_simp

theorem log_choose_ge_entropy {d m : ℕ} (hm : 0 < m) (hmd : m ≤ d) :
    (m : ℝ) * log (1 / ratio d m) ≤ log (d.choose m : ℝ) := by
  have h := log_le_log (pow_pos (one_div_pos.mpr (ratio_pos hm hmd)) m)
    (ratio_inverse_pow_le_choose hm hmd)
  simpa only [log_pow] using h

theorem log_choose_ge_mul_log_div {d m : ℕ} (hm : 0 < m) (hmd : m ≤ d) :
    (m : ℝ) * log ((d : ℝ) / m) ≤ log (d.choose m : ℝ) := by
  have hratio : 1 / ratio d m = (d : ℝ) / m := by simp [ratio, one_div, inv_div]
  simpa only [hratio] using log_choose_ge_entropy hm hmd

theorem log_choose_le_two_mul_log_ratio {d m : ℕ}
    (hm : 0 < m) (hmd : m ≤ d) (hs : ratio d m ≤ 1 / (2 : ℝ) ^ 32) :
    log (d.choose m : ℝ) ≤ 2 * m * log (1 / ratio d m) := by
  have hlog := sparse_log_ratio_ge (ratio_pos hm hmd) hs
  have hlogtwo := one_sub_inv_le_log_of_pos (by norm_num : (0 : ℝ) < 2)
  have hlogone : 1 ≤ log (1 / ratio d m) := by norm_num at hlogtwo; linarith
  have h := log_choose_le_entropy hm hmd
  have hmul := mul_le_mul_of_nonneg_left hlogone (Nat.cast_nonneg m)
  nlinarith

theorem perturbation_time_sq_lower {d m T : ℕ} (hm : 0 < m) (hmd : m ≤ d)
    (hT : 64 * d ^ 2 ≤ T) :
    (d : ℝ) * m * T * log (1 / ratio d m) / (9 * (2 : ℝ) ^ 36) ≤
      (perturbation d m T * T) ^ 2 := by
  have hd : (0 : ℝ) < d := by exact_mod_cast lt_of_lt_of_le hm hmd
  have hmR : (0 : ℝ) < m := by exact_mod_cast hm
  have hdN : 0 < d := lt_of_lt_of_le hm hmd
  have hTN : 0 < T := lt_of_lt_of_le (by positivity : 0 < 64 * d ^ 2) hT
  have ht : (0 : ℝ) < T := by exact_mod_cast hTN
  have hc : (0 : ℝ) < selectionCap d m T := by
    exact_mod_cast selectionCap_pos hm hmd hT
  have hlog := log_inverse_ratio_nonneg hm hmd
  calc
    _ = (m : ℝ) ^ 2 * log (1 / ratio d m) * T ^ 2 /
        ((2 : ℝ) ^ 36 * (9 * T * ratio d m)) := by
      unfold ratio
      field_simp
    _ ≤ (m : ℝ) ^ 2 * log (1 / ratio d m) * T ^ 2 /
        ((2 : ℝ) ^ 36 * selectionCap d m T) := by
      apply div_le_div_of_nonneg_left (by positivity) (by positivity)
      exact mul_le_mul_of_nonneg_left (selectionCap_upper hm hmd hT) (by positivity)
    _ = _ := by rw [mul_pow, perturbation_sq hm hmd]; ring

theorem perturbation_time_sq_upper {d m T : ℕ} (hm : 0 < m) (hmd : m ≤ d)
    (hT : 64 * d ^ 2 ≤ T) :
    (perturbation d m T * T) ^ 2 ≤
      (d : ℝ) * m * T * log (1 / ratio d m) / (8 * (2 : ℝ) ^ 36) := by
  have hd : (0 : ℝ) < d := by exact_mod_cast lt_of_lt_of_le hm hmd
  have hmR : (0 : ℝ) < m := by exact_mod_cast hm
  have hdN : 0 < d := lt_of_lt_of_le hm hmd
  have ht : (0 : ℝ) < T := by
    exact_mod_cast (lt_of_lt_of_le (by positivity : 0 < 64 * d ^ 2) hT)
  have hc : (0 : ℝ) < selectionCap d m T := by exact_mod_cast selectionCap_pos hm hmd hT
  have hr := ratio_pos hm hmd
  have hlog := log_inverse_ratio_nonneg hm hmd
  calc
    _ = (m : ℝ) ^ 2 * log (1 / ratio d m) * T ^ 2 /
        ((2 : ℝ) ^ 36 * selectionCap d m T) := by rw [mul_pow, perturbation_sq hm hmd]; ring
    _ ≤ (m : ℝ) ^ 2 * log (1 / ratio d m) * T ^ 2 /
        ((2 : ℝ) ^ 36 * (8 * T * ratio d m)) := by
      apply div_le_div_of_nonneg_left (by positivity) (by positivity)
      exact mul_le_mul_of_nonneg_left (selectionCap_lower d m T) (by positivity)
    _ = _ := by unfold ratio; field_simp

/-- Uniform two-sided constants for both asymptotic comparisons in the sparse
sketch, with the actual ceiling-defined cap and perturbation. -/
theorem sparse_scale_two_sided {d m T : ℕ}
    (hm : 0 < m) (hmd : m ≤ d) (hT : 64 * d ^ 2 ≤ T)
    (hs : ratio d m ≤ 1 / (2 : ℝ) ^ 32) :
    ((m : ℝ) * log (1 / ratio d m) ≤ log (d.choose m : ℝ) ∧
      log (d.choose m : ℝ) ≤ 2 * m * log (1 / ratio d m)) ∧
    ((1 / (2 : ℝ) ^ 21) * sqrt ((d : ℝ) * m * T * log (1 / ratio d m)) ≤
        perturbation d m T * T ∧
      perturbation d m T * T ≤
        (1 / (2 : ℝ) ^ 18) * sqrt ((d : ℝ) * m * T * log (1 / ratio d m))) ∧
    ((1 / (2 : ℝ) ^ 21) * sqrt ((d : ℝ) * T * log (d.choose m : ℝ)) ≤
        perturbation d m T * T ∧
      perturbation d m T * T ≤
        (1 / (2 : ℝ) ^ 18) * sqrt ((d : ℝ) * T * log (d.choose m : ℝ))) := by
  have hlo := log_choose_ge_entropy hm hmd
  have hhi := log_choose_le_two_mul_log_ratio hm hmd hs
  have hlog := log_inverse_ratio_nonneg hm hmd
  have hA : 0 ≤ (d : ℝ) * m * T * log (1 / ratio d m) := by positivity
  have hc : (1 : ℝ) ≤ d.choose m := by exact_mod_cast Nat.choose_pos hmd
  have hB : 0 ≤ (d : ℝ) * T * log (d.choose m : ℝ) :=
    mul_nonneg (by positivity) (log_nonneg hc)
  have hAB := mul_le_mul_of_nonneg_left hlo (by positivity : (0 : ℝ) ≤ d * T)
  have hBA := mul_le_mul_of_nonneg_left hhi (by positivity : (0 : ℝ) ≤ d * T)
  have heta0 : 0 ≤ perturbation d m T * T := mul_nonneg (perturbation_nonneg d m T) (Nat.cast_nonneg T)
  have hetaLo := perturbation_time_sq_lower hm hmd hT
  have hetaHi := perturbation_time_sq_upper hm hmd hT
  have hsA := sq_sqrt hA
  have hsB := sq_sqrt hB
  have hnA := sqrt_nonneg ((d : ℝ) * m * T * log (1 / ratio d m))
  have hnB := sqrt_nonneg ((d : ℝ) * T * log (d.choose m : ℝ))
  refine ⟨⟨hlo, hhi⟩, ⟨?_, ?_⟩, ⟨?_, ?_⟩⟩ <;>
    norm_num only at hetaLo hetaHi ⊢ <;> nlinarith

theorem sparse_threshold_comparisons {d m T : ℕ}
    (hm : 0 < m) (hmd : m ≤ d) (hT : 64 * d ^ 2 ≤ T)
    (hs : ratio d m ≤ 1 / (2 : ℝ) ^ 32) :
    (1 / (2 : ℝ) ^ 21) / sqrt 18 * sqrt ((d : ℝ) * T * log (d.choose m : ℝ)) ≤
      perturbation d m T * T / 8 ∧
    (1 / (2 : ℝ) ^ 24) * sqrt ((d : ℝ) * T * log (d.choose m : ℝ)) ≤
      (1 / (2 : ℝ) ^ 21) / sqrt 18 * sqrt ((d : ℝ) * T * log (d.choose m : ℝ)) := by
  have hchoose1 : (1 : ℝ) ≤ d.choose m := by exact_mod_cast Nat.choose_pos hmd
  have hB : 0 ≤ (d : ℝ) * T * log (d.choose m : ℝ) := by
    exact mul_nonneg (by positivity) (log_nonneg hchoose1)
  have hBbound := mul_le_mul_of_nonneg_left (log_choose_le_two_mul_log_ratio hm hmd hs)
    (by positivity : (0 : ℝ) ≤ d * T)
  have heta := perturbation_time_sq_lower hm hmd hT
  have he := perturbation_nonneg d m T
  have hs18 : 0 < sqrt (18 : ℝ) := by positivity
  have hsq18 := sq_sqrt (by norm_num : (0 : ℝ) ≤ 18)
  have hsqB := sq_sqrt hB
  have htargetSq : ((1 / (2 : ℝ) ^ 21) / sqrt 18 *
      sqrt ((d : ℝ) * T * log (d.choose m : ℝ))) ^ 2 =
      ((d : ℝ) * T * log (d.choose m : ℝ)) / (18 * (2 : ℝ) ^ 42) := by
    rw [mul_pow, div_pow, div_pow, hsq18, hsqB]
    norm_num
    ring
  constructor
  · have htgt : 0 ≤ (1 / (2 : ℝ) ^ 21) / sqrt 18 *
        sqrt ((d : ℝ) * T * log (d.choose m : ℝ)) := by positivity
    have hright : 0 ≤ perturbation d m T * T / 8 := by positivity
    nlinarith
  · apply mul_le_mul_of_nonneg_right _ (sqrt_nonneg _)
    apply (le_div_iff₀ hs18).2
    have hsbound : sqrt (18 : ℝ) ≤ 8 := by nlinarith
    norm_num
    nlinarith

end MsetsPaper.Lower.SparseCapped
