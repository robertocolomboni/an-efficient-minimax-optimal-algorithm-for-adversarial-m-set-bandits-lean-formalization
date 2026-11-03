import MsetsPaper.Upper.OMD
import MsetsPaper.Upper.SmoothedComparator

/-! # P1: bounded multiplicative-weights log ratios and uniform-KL growth -/

noncomputable section
open scoped BigOperators
open MsetsLower

namespace MsetsPaper.Upper

section Finite
variable {α : Type*} [Fintype α]

theorem mwNormalizer_bounded (p z : α → ℝ) (eta c : ℝ)
    (hp : ∀ x, 0 ≤ p x) (hpsum : ∑ x, p x = 1)
    (hbound : ∀ x, |eta * z x| ≤ c) :
    Real.exp (-c) ≤ mwNormalizer p z eta ∧ mwNormalizer p z eta ≤ Real.exp c := by
  have hlo := Finset.sum_le_sum (s := Finset.univ) (fun x _ ↦
    mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr (by
      linarith [(abs_le.mp (hbound x)).2] : -c ≤ -eta * z x)) (hp x))
  have hhi := Finset.sum_le_sum (s := Finset.univ) (fun x _ ↦
    mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr (by
      linarith [(abs_le.mp (hbound x)).1] : -eta * z x ≤ c)) (hp x))
  simpa only [← Finset.sum_mul, hpsum, one_mul, mwNormalizer, finiteExpectation] using
    And.intro hlo hhi

theorem abs_log_mwNormalizer_le (p z : α → ℝ) (eta c : ℝ)
    (hp : ∀ x, 0 < p x) (hpsum : ∑ x, p x = 1)
    (hbound : ∀ x, |eta * z x| ≤ c) : |Real.log (mwNormalizer p z eta)| ≤ c := by
  obtain ⟨hlo, hhi⟩ := mwNormalizer_bounded p z eta c (fun x ↦ (hp x).le) hpsum hbound
  have hloglo := Real.log_le_log (Real.exp_pos (-c)) hlo
  have hloghi := Real.log_le_log (mwNormalizer_pos p z eta hp hpsum) hhi
  rw [Real.log_exp] at hloglo hloghi
  exact abs_le.mpr ⟨hloglo, hloghi⟩

theorem abs_log_mwUpdate_ratio_le (p z : α → ℝ) (eta c : ℝ)
    (hp : ∀ x, 0 < p x) (hpsum : ∑ x, p x = 1)
    (hbound : ∀ x, |eta * z x| ≤ c) (x : α) :
    |Real.log (mwUpdate p z eta x / p x)| ≤ 2 * c := by
  rw [Real.log_div (mwUpdate_pos p z eta hp hpsum x).ne' (hp x).ne',
    log_mwUpdate p z eta hp hpsum]
  have hlog := abs_log_mwNormalizer_le p z eta c hp hpsum hbound
  have hb := hbound x
  apply abs_le.mpr
  constructor <;> linarith [(abs_le.mp hb).1, (abs_le.mp hb).2,
    (abs_le.mp hlog).1, (abs_le.mp hlog).2]

theorem finiteKL_change_reference (q p r : α → ℝ)
    (hp : ∀ x, 0 < p x) (hr : ∀ x, 0 < r x) :
    finiteKL q r = finiteKL q p - finiteExpectation q (fun x ↦ Real.log (r x / p x)) := by
  rw [finiteKL_eq_sum_mul_log_sub_log q r hr, finiteKL_eq_sum_mul_log_sub_log q p hp]
  simp_rw [Real.log_div (hr _).ne' (hp _).ne']
  unfold finiteExpectation
  rw [← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro x _
  ring

theorem finiteKL_mwUpdate_le_of_bound (q p z : α → ℝ) (eta c : ℝ)
    (hq : ∀ x, 0 ≤ q x) (hqsum : ∑ x, q x = 1)
    (hp : ∀ x, 0 < p x) (hpsum : ∑ x, p x = 1)
    (hbound : ∀ x, |eta * z x| ≤ c) :
    finiteKL q (mwUpdate p z eta) ≤ finiteKL q p + 2 * c := by
  rw [finiteKL_change_reference q p _ hp (mwUpdate_pos p z eta hp hpsum)]
  have hsum := Finset.sum_le_sum (s := Finset.univ) (fun x _ ↦
    mul_le_mul_of_nonneg_left
      (abs_le.mp (abs_log_mwUpdate_ratio_le p z eta c hp hpsum hbound x)).1 (hq x))
  simp only [← Finset.sum_mul, hqsum, one_mul] at hsum
  change -(2 * c) ≤ finiteExpectation q _ at hsum
  linarith

end Finite

variable {d m : ℕ}

theorem unprojected_uniform_KL_le (theta ell : Fin d → ℝ)
    (hmpos : 1 ≤ m) (hmtop : m ≤ d - 1) {eta : ℝ}
    (heta : 0 < eta) (hsmall : eta ≤ 1 / 64)
    (hlo : ∀ i, (128 * eta * d / 2) * ((m : ℝ) / d) ≤ weightedMarginal (m := m) theta i)
    (hhi : ∀ i, weightedMarginal (m := m) theta i ≤
      1 - (128 * eta * d / 2) * (1 - (m : ℝ) / d))
    (a : Action d m) (hloss : ∀ b : Action d m, |actionLoss b ell| ≤ 1) :
    finiteKL (weightedLaw (m := m) (0 : Fin d → ℝ))
      (weightedLaw (theta - eta • surrogateVector theta ell eta a)) ≤
    finiteKL (weightedLaw (m := m) (0 : Fin d → ℝ)) (weightedLaw theta) + 1 / 2 := by
  have hmd : m ≤ d := by omega
  have hb : ∀ b : Action d m, |eta * surrogate theta ell eta a b| ≤ 1 / 4 := by
    intro b
    rw [abs_mul, abs_of_pos heta]
    exact bounded_increments theta ell hmpos hmtop heta hsmall hloss hlo hhi a b
  have h := finiteKL_mwUpdate_le_of_bound
    (weightedLaw (m := m) (0 : Fin d → ℝ)) (weightedLaw theta)
    (surrogate theta ell eta a) eta (1 / 4)
    (fun b ↦ (weightedLaw_pos _ hmd b).le) (sum_weightedLaw _ hmd)
    (weightedLaw_pos theta hmd) (sum_weightedLaw theta hmd) hb
  rw [mwUpdate_surrogate_weightedLaw theta ell eta hmd a] at h
  norm_num at h ⊢
  exact h

end MsetsPaper.Upper
