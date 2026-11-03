import Mathlib.Analysis.SpecialFunctions.Log.NegMulLog
import Mathlib.Tactic

/-!
# Finite relative entropy and normalized exponential updates

The definitions are the actual finite sums used by the manuscript.  A comparator
may have zero coordinates: its contribution to relative entropy is then zero.
All applications require the reference law to be strictly positive.
-/

noncomputable section

open scoped BigOperators

namespace MsetsPaper.Upper

variable {α : Type*} [Fintype α]

def finiteExpectation (p f : α → ℝ) : ℝ := ∑ x, p x * f x

/-- Finite KL divergence, with the usual zero-mass contribution equal to zero. -/
def finiteKL (q p : α → ℝ) : ℝ := ∑ x, q x * Real.log (q x / p x)

theorem zero_mul_log_ratio (p : ℝ) : (0 : ℝ) * Real.log (0 / p) = 0 := by simp

theorem finiteKL_eq_sum_mul_log_sub_log (q p : α → ℝ) (hp : ∀ x, 0 < p x) :
    finiteKL q p = ∑ x, q x * (Real.log (q x) - Real.log (p x)) := by
  classical
  apply Finset.sum_congr rfl
  intro x _
  by_cases hq : q x = 0
  · simp [hq]
  · rw [Real.log_div hq (hp x).ne']

/-- Pointwise Gibbs inequality, including a zero numerator. -/
theorem sub_le_mul_log_ratio {q p : ℝ} (hq : 0 ≤ q) (hp : 0 < p) :
    q - p ≤ q * Real.log (q / p) := by
  have h := mul_le_mul_of_nonneg_left
    (Real.self_sub_one_le_mul_log (div_nonneg hq hp.le)) hp.le
  have hc : p * (q / p) = q := by field_simp
  simpa only [mul_sub, mul_one, ← mul_assoc, hc] using h

theorem finiteKL_nonneg (q p : α → ℝ) (hq : ∀ x, 0 ≤ q x)
    (hqsum : ∑ x, q x = 1) (hp : ∀ x, 0 < p x) (hpsum : ∑ x, p x = 1) :
    0 ≤ finiteKL q p := by
  classical
  have h := Finset.sum_le_sum (fun x (_ : x ∈ (Finset.univ : Finset α)) =>
    sub_le_mul_log_ratio (hq x) (hp x))
  simpa only [Finset.sum_sub_distrib, hqsum, hpsum, sub_self, finiteKL] using h

/-- The normalizer is the actual exponential moment under `p`. -/
def mwNormalizer (p z : α → ℝ) (eta : ℝ) : ℝ :=
  finiteExpectation p (fun x => Real.exp (-eta * z x))

def mwUpdate (p z : α → ℝ) (eta : ℝ) (x : α) : ℝ :=
  p x * Real.exp (-eta * z x) / mwNormalizer p z eta

theorem mwNormalizer_pos (p z : α → ℝ) (eta : ℝ)
    (hp : ∀ x, 0 < p x) (hpsum : ∑ x, p x = 1) : 0 < mwNormalizer p z eta := by
  classical
  have hn : (Finset.univ : Finset α).Nonempty := by
    by_contra h
    rw [Finset.not_nonempty_iff_eq_empty.mp h, Finset.sum_empty] at hpsum
    norm_num at hpsum
  exact Finset.sum_pos (fun x _ => mul_pos (hp x) (Real.exp_pos _)) hn

theorem mwUpdate_pos (p z : α → ℝ) (eta : ℝ)
    (hp : ∀ x, 0 < p x) (hpsum : ∑ x, p x = 1) (x : α) :
    0 < mwUpdate p z eta x :=
  div_pos (mul_pos (hp x) (Real.exp_pos _)) (mwNormalizer_pos p z eta hp hpsum)

theorem sum_mwUpdate (p z : α → ℝ) (eta : ℝ)
    (hp : ∀ x, 0 < p x) (hpsum : ∑ x, p x = 1) :
    ∑ x, mwUpdate p z eta x = 1 := by
  classical
  unfold mwUpdate
  rw [← Finset.sum_div]
  exact div_self (mwNormalizer_pos p z eta hp hpsum).ne'

theorem log_mwUpdate (p z : α → ℝ) (eta : ℝ)
    (hp : ∀ x, 0 < p x) (hpsum : ∑ x, p x = 1) (x : α) :
    Real.log (mwUpdate p z eta x) =
      Real.log (p x) - eta * z x - Real.log (mwNormalizer p z eta) := by
  rw [mwUpdate, Real.log_div (mul_pos (hp x) (Real.exp_pos _)).ne'
    (mwNormalizer_pos p z eta hp hpsum).ne',
    Real.log_mul (hp x).ne' (Real.exp_pos _).ne', Real.log_exp]
  ring

/-- Exact KL identity for the normalized update; no full-support premise on `q`. -/
theorem finiteKL_mwUpdate (q p z : α → ℝ) (eta : ℝ)
    (hqsum : ∑ x, q x = 1) (hp : ∀ x, 0 < p x) (hpsum : ∑ x, p x = 1) :
    finiteKL q (mwUpdate p z eta) = finiteKL q p +
      eta * finiteExpectation q z + Real.log (mwNormalizer p z eta) := by
  classical
  rw [finiteKL_eq_sum_mul_log_sub_log q _ (mwUpdate_pos p z eta hp hpsum),
    finiteKL_eq_sum_mul_log_sub_log q p hp]
  simp_rw [log_mwUpdate p z eta hp hpsum]
  calc
    (∑ x, q x * (Real.log (q x) -
        (Real.log (p x) - eta * z x - Real.log (mwNormalizer p z eta)))) =
        ∑ x, (q x * (Real.log (q x) - Real.log (p x)) +
          eta * (q x * z x) + q x * Real.log (mwNormalizer p z eta)) := by
      apply Finset.sum_congr rfl
      intro x _
      ring
    _ = _ := by
      rw [Finset.sum_add_distrib, Finset.sum_add_distrib,
        ← Finset.mul_sum, ← Finset.sum_mul, hqsum, one_mul]
      rfl

end MsetsPaper.Upper
