import MsetsPaper.Lower.SparseCappedParameters

/-! # Exact scalar arithmetic after binary entropy reduction in P2 -/

namespace MsetsPaper.Lower.SparseCapped

open Real

theorem sparse_log_ratio_ge {r : ℝ} (hr : 0 < r) (hs : r ≤ 1 / (2 : ℝ) ^ 32) :
    32 * log 2 ≤ log (1 / r) := by
  have h := log_le_log hr hs
  rw [one_div, log_inv, log_pow] at h
  rw [one_div, log_inv]
  norm_num at h
  linarith

/-- Each displayed quotient step. The entropy inequality is the input supplied
by the binary-KL lemma, not an assumed probability-of-survival conclusion. -/
theorem sparse_entropy_quotient_chain {a b r : ℝ}
    (ha : 0 ≤ a) (hb : 0 < b) (hr : 0 < r) (hs : r ≤ 1 / (2 : ℝ) ^ 32)
    (hbsmall : b ≤ 256 * r)
    (hentropy : a * log (1 / b) - log 2 ≤
      (1 / (2 : ℝ) ^ 29) * log (1 / r)) :
    a ≤ ((1 / (2 : ℝ) ^ 29) * log (1 / r) + log 2) /
        (log (1 / r) - 8 * log 2) ∧
    ((1 / (2 : ℝ) ^ 29) * log (1 / r) + log 2) /
        (log (1 / r) - 8 * log 2) ≤
      (4 / 3 : ℝ) * (1 / (2 : ℝ) ^ 29 + 1 / 32) ∧
    (4 / 3 : ℝ) * (1 / (2 : ℝ) ^ 29 + 1 / 32) ≤ 3 / 64 := by
  have hlog := sparse_log_ratio_ge hr hs
  have hlogtwo : 0 < log (2 : ℝ) := log_pos (by norm_num)
  have hden : 0 < log (1 / r) - 8 * log 2 := by linarith
  have hbLog : log (1 / r) - 8 * log 2 ≤ log (1 / b) := by
    have h := log_le_log hb hbsmall
    rw [log_mul (by norm_num : (256 : ℝ) ≠ 0) hr.ne'] at h
    have h256 : log (256 : ℝ) = 8 * log 2 := by
      rw [show (256 : ℝ) = 2 ^ 8 by norm_num, log_pow]
      norm_num
    rw [h256] at h
    simp only [one_div, log_inv]
    linarith
  refine ⟨?_, ?_, by norm_num⟩
  · apply (le_div_iff₀ hden).2
    have hmul := mul_le_mul_of_nonneg_left hbLog ha
    linarith
  · apply (div_le_iff₀ hden).2
    nlinarith

theorem sparse_entropy_probability_le {a b r : ℝ}
    (ha : 0 ≤ a) (hb : 0 < b) (hr : 0 < r) (hs : r ≤ 1 / (2 : ℝ) ^ 32)
    (hbsmall : b ≤ 256 * r)
    (hentropy : a * log (1 / b) - log 2 ≤
      (1 / (2 : ℝ) ^ 29) * log (1 / r)) : a ≤ 3 / 64 := by
  obtain ⟨h₁, h₂, h₃⟩ := sparse_entropy_quotient_chain ha hb hr hs hbsmall hentropy
  exact h₁.trans (h₂.trans h₃)

theorem sparse_counting_probability_le {p a r : ℝ}
    (hp : 0 ≤ p) (hr : r ≤ 1 / 8) (ha : a ≤ 3 / 64)
    (hcount : (7 / 8 - r) * p ≤ (255 / 256 : ℝ) * a) :
    p ≤ (4 / 3 : ℝ) * a ∧ (4 / 3 : ℝ) * a ≤ 1 / 16 := by
  constructor
  · have hleft : (3 / 4 : ℝ) * p ≤ (7 / 8 - r) * p :=
      mul_le_mul_of_nonneg_right (by linarith) hp
    have ha0 : 0 ≤ a := by nlinarith
    nlinarith
  · linarith

end MsetsPaper.Lower.SparseCapped
