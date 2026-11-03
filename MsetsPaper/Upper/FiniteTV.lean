import MsetsPaper.Upper.FinitePinsker

/-! # Finite total variation and its exact Pinsker normalization -/

noncomputable section
open scoped BigOperators

namespace MsetsPaper.Upper

variable {α : Type*} [Fintype α]

def finiteTV (p q : α → ℝ) : ℝ := (∑ x, |q x - p x|) / 2

theorem finiteTV_nonneg (p q : α → ℝ) : 0 ≤ finiteTV p q := by
  exact div_nonneg (Finset.sum_nonneg fun x _ => abs_nonneg _) (by norm_num)

theorem finite_event_le_TV (p q : α → ℝ)
    (hpsum : ∑ x, p x = 1) (hqsum : ∑ x, q x = 1) (S : Finset α) :
    |(∑ x ∈ S, q x) - ∑ x ∈ S, p x| ≤ finiteTV p q := by
  classical
  have hz : (∑ x ∈ S, (q x - p x)) + (∑ x ∈ Sᶜ, (q x - p x)) = 0 := by
    rw [Finset.sum_add_sum_compl, Finset.sum_sub_distrib, hqsum, hpsum]
    ring
  have hsplit := Finset.sum_add_sum_compl S (fun x => |q x - p x|)
  have hS := Finset.abs_sum_le_sum_abs (fun x => q x - p x) S
  have hSc := Finset.abs_sum_le_sum_abs (fun x => q x - p x) Sᶜ
  have hcomp : (∑ x ∈ Sᶜ, (q x - p x)) = -(∑ x ∈ S, (q x - p x)) := by linarith
  rw [hcomp, abs_neg] at hSc
  rw [← Finset.sum_sub_distrib]
  unfold finiteTV
  linarith

theorem finiteTV_event_eq (p q : α → ℝ)
    (hpsum : ∑ x, p x = 1) (hqsum : ∑ x, q x = 1) :
    ∃ S : Finset α, finiteTV p q = (∑ x ∈ S, q x) - ∑ x ∈ S, p x := by
  classical
  let S : Finset α := Finset.univ.filter (fun x => p x ≤ q x)
  have hplus : (∑ x ∈ S, |q x - p x|) = ∑ x ∈ S, (q x - p x) := by
    apply Finset.sum_congr rfl
    intro x hx
    exact abs_of_nonneg (sub_nonneg.mpr (Finset.mem_filter.mp hx).2)
  have hminus : (∑ x ∈ Sᶜ, |q x - p x|) = -(∑ x ∈ Sᶜ, (q x - p x)) := by
    rw [← Finset.sum_neg_distrib]
    apply Finset.sum_congr rfl
    intro x hx
    have hn : ¬p x ≤ q x := by simpa [S] using hx
    exact abs_of_nonpos (by linarith)
  have hsplit := Finset.sum_add_sum_compl S (fun x => |q x - p x|)
  rw [hplus, hminus] at hsplit
  have hzero : (∑ x ∈ S, (q x - p x)) + (∑ x ∈ Sᶜ, (q x - p x)) = 0 := by
    rw [Finset.sum_add_sum_compl, Finset.sum_sub_distrib, hqsum, hpsum]
    ring
  refine ⟨S, ?_⟩
  rw [← Finset.sum_sub_distrib]
  unfold finiteTV
  linarith

theorem finiteTV_pinsker_sq (p q : α → ℝ)
    (hp : ∀ x, 0 < p x) (hq : ∀ x, 0 < q x)
    (hpsum : ∑ x, p x = 1) (hqsum : ∑ x, q x = 1) :
    2 * (finiteTV p q) ^ 2 ≤ finiteKL q p := by
  obtain ⟨S, hS⟩ := finiteTV_event_eq p q hpsum hqsum
  rw [hS]
  exact finite_event_pinsker_sq p q hp hq hpsum hqsum S

theorem finiteTV_le_sqrt_KL (p q : α → ℝ)
    (hp : ∀ x, 0 < p x) (hq : ∀ x, 0 < q x)
    (hpsum : ∑ x, p x = 1) (hqsum : ∑ x, q x = 1)
    (tau : ℝ) (hKL : finiteKL q p ≤ tau) : finiteTV p q ≤ Real.sqrt (tau / 2) := by
  have h := finiteTV_pinsker_sq p q hp hq hpsum hqsum
  apply Real.le_sqrt_of_sq_le
  linarith

variable {d m : ℕ}

theorem weightedMarginal_distance_le_TV (theta psi : Fin d → ℝ) (hmd : m ≤ d)
    (i : Fin d) : |weightedMarginal (m := m) theta i - weightedMarginal (m := m) psi i| ≤
      finiteTV (weightedLaw (m := m) psi) (weightedLaw theta) := by
  classical
  let S : Finset (Action d m) := Finset.univ.filter (fun x => i ∈ x.val)
  have hmarg (v : Fin d → ℝ) : (∑ x ∈ S, weightedLaw (m := m) v x) =
      weightedMarginal (m := m) v i := by
    simp [S, weightedMarginal, marginal, MsetsLower.History.selectedIndicator, Finset.sum_filter]
  have h := finite_event_le_TV (weightedLaw (m := m) psi) (weightedLaw theta)
    (sum_weightedLaw psi hmd) (sum_weightedLaw theta hmd) S
  simpa only [hmarg] using h

/-- The marginal error follows through the actual total-variation distance:
first Pinsker bounds TV, then the coordinate-selection event bounds a marginal. -/
theorem weightedMarginal_distance_of_KL_via_TV (theta psi : Fin d → ℝ)
    (hmd : m ≤ d) (tau : ℝ)
    (hKL : finiteKL (weightedLaw (m := m) theta) (weightedLaw psi) ≤ tau)
    (i : Fin d) :
    |weightedMarginal (m := m) theta i - weightedMarginal (m := m) psi i| ≤
      Real.sqrt (tau / 2) := by
  have hTV := finiteTV_le_sqrt_KL (weightedLaw (m := m) psi) (weightedLaw theta)
    (weightedLaw_pos psi hmd) (weightedLaw_pos theta hmd)
    (sum_weightedLaw psi hmd) (sum_weightedLaw theta hmd) tau hKL
  exact (weightedMarginal_distance_le_TV theta psi hmd i).trans hTV

end MsetsPaper.Upper
