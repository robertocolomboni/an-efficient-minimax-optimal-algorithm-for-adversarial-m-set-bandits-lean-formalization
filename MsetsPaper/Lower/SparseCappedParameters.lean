import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Algebra.Order.Floor.Ring
import Mathlib.Tactic

/-! # Literal numerical parameter choices for P2 -/

namespace MsetsPaper.Lower.SparseCapped

noncomputable section

def ratio (d m : ℕ) : ℝ := (m : ℝ) / d

def selectionCap (d m T : ℕ) : ℕ := ⌈8 * (T : ℝ) * ratio d m⌉₊

def perturbation (d m T : ℕ) : ℝ :=
  (m : ℝ) * Real.sqrt ((1 / (2 : ℝ) ^ 36) * Real.log (1 / ratio d m) / selectionCap d m T)

theorem ratio_pos {d m : ℕ} (hm : 0 < m) (hmd : m ≤ d) : 0 < ratio d m := by
  unfold ratio
  exact div_pos (by exact_mod_cast hm) (by exact_mod_cast lt_of_lt_of_le hm hmd)

theorem ratio_le_one {d m : ℕ} (hm : 0 < m) (hmd : m ≤ d) : ratio d m ≤ 1 := by
  unfold ratio
  exact (div_le_one (by exact_mod_cast lt_of_lt_of_le hm hmd)).2 (by exact_mod_cast hmd)

theorem log_inverse_ratio_nonneg {d m : ℕ} (hm : 0 < m) (hmd : m ≤ d) :
    0 ≤ Real.log (1 / ratio d m) :=
  Real.log_nonneg ((one_le_div (ratio_pos hm hmd)).2 (ratio_le_one hm hmd))

theorem horizon_mul_ratio_ge_one {d m T : ℕ} (hm : 0 < m) (hmd : m ≤ d)
    (hT : 64 * d ^ 2 ≤ T) : 1 ≤ (T : ℝ) * ratio d m := by
  have hd : 0 < d := lt_of_lt_of_le hm hmd
  have hTd : d ≤ T := by nlinarith
  have hTm : d ≤ T * m := hTd.trans (Nat.le_mul_of_pos_right T hm)
  have hdR : (0 : ℝ) < d := by exact_mod_cast hd
  rw [ratio, ← mul_div_assoc]
  apply (one_le_div hdR).2
  exact_mod_cast hTm

theorem selectionCap_lower (d m T : ℕ) :
    8 * (T : ℝ) * ratio d m ≤ (selectionCap d m T : ℝ) := Nat.le_ceil _

theorem selectionCap_pos {d m T : ℕ} (hm : 0 < m) (hmd : m ≤ d)
    (hT : 64 * d ^ 2 ≤ T) : 0 < selectionCap d m T := by
  have hTr := horizon_mul_ratio_ge_one hm hmd hT
  have hc := selectionCap_lower d m T
  have : (0 : ℝ) < selectionCap d m T := by nlinarith
  exact_mod_cast this

theorem selectionCap_upper {d m T : ℕ} (hm : 0 < m) (hmd : m ≤ d)
    (hT : 64 * d ^ 2 ≤ T) : (selectionCap d m T : ℝ) ≤ 9 * (T : ℝ) * ratio d m := by
  have hTr := horizon_mul_ratio_ge_one hm hmd hT
  have hc := Nat.ceil_lt_add_one (show 0 ≤ 8 * (T : ℝ) * ratio d m by
    nlinarith)
  change (selectionCap d m T : ℝ) < _ at hc
  nlinarith

theorem selectionCap_budget {d m T : ℕ} (hm : 0 < m) (hmd : m ≤ d) :
    8 * T * m ≤ selectionCap d m T * d := by
  have hdR : (0 : ℝ) < d := by exact_mod_cast lt_of_lt_of_le hm hmd
  have hc := mul_le_mul_of_nonneg_right (selectionCap_lower d m T) hdR.le
  have heq : 8 * (T : ℝ) * ratio d m * d = 8 * (T : ℝ) * m := by
    unfold ratio
    field_simp
  rw [heq] at hc
  exact_mod_cast hc

theorem selectionCap_large {d m T : ℕ} (hm : 0 < m) (hmd : m ≤ d)
    (hT : 64 * d ^ 2 ≤ T) : (512 : ℝ) * d * m ≤ selectionCap d m T := by
  have hdR : (0 : ℝ) < d := by exact_mod_cast lt_of_lt_of_le hm hmd
  have hc : (8 : ℝ) * T * m ≤ (selectionCap d m T : ℝ) * d := by
    exact_mod_cast selectionCap_budget (T := T) hm hmd
  have hTR : (64 : ℝ) * d ^ 2 ≤ T := by exact_mod_cast hT
  apply le_of_mul_le_mul_right (a := (d : ℝ)) _ hdR
  have hx := mul_le_mul_of_nonneg_right hTR (show (0 : ℝ) ≤ 8 * m by positivity)
  nlinarith

theorem perturbation_nonneg (d m T : ℕ) : 0 ≤ perturbation d m T := by
  unfold perturbation
  positivity

theorem perturbation_sq {d m T : ℕ} (hm : 0 < m) (hmd : m ≤ d) :
    perturbation d m T ^ 2 =
      (m : ℝ) ^ 2 * Real.log (1 / ratio d m) / ((2 : ℝ) ^ 36 * selectionCap d m T) := by
  have hrad : 0 ≤ (1 / (2 : ℝ) ^ 36) * Real.log (1 / ratio d m) / selectionCap d m T :=
    div_nonneg (mul_nonneg (by positivity) (log_inverse_ratio_nonneg hm hmd)) (Nat.cast_nonneg _)
  rw [perturbation, mul_pow, Real.sq_sqrt hrad]
  ring

theorem ratio_mul_log_inverse_le_one {d m : ℕ} (hm : 0 < m) (hmd : m ≤ d) :
    ratio d m * Real.log (1 / ratio d m) ≤ 1 := by
  have hr := ratio_pos hm hmd
  have hlog := Real.log_le_sub_one_of_pos (one_div_pos.mpr hr)
  have hmul := mul_le_mul_of_nonneg_left hlog hr.le
  have hcancel : ratio d m * (1 / ratio d m) = 1 := by field_simp
  nlinarith

/-- Each successive denominator bound in the manuscript's admissibility calculation. -/
theorem perturbation_square_chain {d m T : ℕ} (hm : 0 < m) (hmd : m ≤ d)
    (hT : 64 * d ^ 2 ≤ T) :
    perturbation d m T ^ 2 ≤
      (m : ℝ) ^ 2 * Real.log (1 / ratio d m) / ((2 : ℝ) ^ 39 * T * ratio d m) ∧
    (m : ℝ) ^ 2 * Real.log (1 / ratio d m) / ((2 : ℝ) ^ 39 * T * ratio d m) ≤
      (m : ℝ) ^ 2 * Real.log (1 / ratio d m) / ((2 : ℝ) ^ 45 * d ^ 2 * ratio d m) ∧
    (m : ℝ) ^ 2 * Real.log (1 / ratio d m) / ((2 : ℝ) ^ 45 * d ^ 2 * ratio d m) =
      (1 / (2 : ℝ) ^ 45) * ratio d m * Real.log (1 / ratio d m) := by
  have hdR : (0 : ℝ) < d := by exact_mod_cast lt_of_lt_of_le hm hmd
  have hmR : (0 : ℝ) < m := by exact_mod_cast hm
  have hr := ratio_pos hm hmd
  have hTr := horizon_mul_ratio_ge_one hm hmd hT
  have hnum : 0 ≤ (m : ℝ) ^ 2 * Real.log (1 / ratio d m) :=
    mul_nonneg (sq_nonneg _) (log_inverse_ratio_nonneg hm hmd)
  have hTR : (64 : ℝ) * d ^ 2 ≤ T := by exact_mod_cast hT
  refine ⟨?_, ?_, ?_⟩
  · rw [perturbation_sq hm hmd]
    apply div_le_div_of_nonneg_left hnum (by nlinarith [hr])
    nlinarith [selectionCap_lower d m T]
  · apply div_le_div_of_nonneg_left hnum (by positivity)
    have hx := mul_le_mul_of_nonneg_right hTR hr.le
    nlinarith
  · unfold ratio
    field_simp

/-- The displayed final square bound that ensures all feedback parameters
lie strictly inside the support-preserving interval of L12. -/
theorem perturbation_sq_le {d m T : ℕ} (hm : 0 < m) (hmd : m ≤ d)
    (hT : 64 * d ^ 2 ≤ T) : perturbation d m T ^ 2 ≤ 1 / (2 : ℝ) ^ 45 := by
  obtain ⟨hfirst, hsecond, hidentity⟩ := perturbation_square_chain hm hmd hT
  have hratio := mul_le_mul_of_nonneg_left (ratio_mul_log_inverse_le_one hm hmd)
    (show 0 ≤ 1 / (2 : ℝ) ^ 45 by positivity)
  calc
    _ ≤ _ := hfirst
    _ ≤ _ := hsecond
    _ = _ := hidentity
    _ ≤ _ := by nlinarith


theorem perturbation_lt_sixteenth {d m T : ℕ} (hm : 0 < m) (hmd : m ≤ d)
    (hT : 64 * d ^ 2 ≤ T) : perturbation d m T < 1 / 16 := by
  have hs := perturbation_sq_le hm hmd hT
  nlinarith [sq_nonneg (perturbation d m T - 1 / 16)]

/-- The exact capped bit-information budget after substituting eta. -/
theorem capped_bit_budget_identity {d m T : ℕ} (hm : 0 < m) (hmd : m ≤ d)
    (hT : 64 * d ^ 2 ≤ T) :
    128 * (perturbation d m T / m) ^ 2 * selectionCap d m T =
      (1 / (2 : ℝ) ^ 29) * Real.log (1 / ratio d m) := by
  have hm0 : (m : ℝ) ≠ 0 := by exact_mod_cast Nat.ne_of_gt hm
  have hc0 : (selectionCap d m T : ℝ) ≠ 0 := by
    exact_mod_cast Nat.ne_of_gt (selectionCap_pos hm hmd hT)
  rw [div_pow, perturbation_sq hm hmd]
  field_simp
  ring

end

end MsetsPaper.Lower.SparseCapped
