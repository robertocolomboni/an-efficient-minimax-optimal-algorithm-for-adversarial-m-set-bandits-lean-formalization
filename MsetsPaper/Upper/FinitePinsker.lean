import MsetsPaper.Upper.ProjectionApproximation
import MsetsLower.Lower.Dense.Assouad

/-!
# Pinsker for the finite probabilities used by the upper bound

Binary Pinsker is an already proved theorem of the vendored lower-bound
project. The finite coarse-graining argument is proved here from Gibbs.
-/

noncomputable section
open scoped BigOperators

namespace MsetsPaper.Upper

variable {α : Type*} [Fintype α]

theorem finite_log_sum (p q : α → ℝ) (hp : ∀ x, 0 < p x) (hq : ∀ x, 0 < q x)
    (S : Finset α) :
    (∑ x ∈ S, q x) * Real.log ((∑ x ∈ S, q x) / (∑ x ∈ S, p x)) ≤
      ∑ x ∈ S, q x * Real.log (q x / p x) := by
  classical
  by_cases hS : S.Nonempty
  · let P := ∑ x ∈ S, p x
    let Q := ∑ x ∈ S, q x
    have hP : 0 < P := Finset.sum_pos (fun x _ => hp x) hS
    have hQ : 0 < Q := Finset.sum_pos (fun x _ => hq x) hS
    have hratio : 0 < Q / P := div_pos hQ hP
    have hlog (x : α) : Real.log (q x / (p x * (Q / P))) =
        Real.log (q x / p x) - Real.log (Q / P) := by
      rw [Real.log_div (hq x).ne' (mul_pos (hp x) hratio).ne',
        Real.log_mul (hp x).ne' hratio.ne', Real.log_div (hq x).ne' (hp x).ne']
      ring
    have h := Finset.sum_le_sum fun x (_ : x ∈ S) =>
      sub_le_mul_log_ratio (hq x).le (mul_pos (hp x) hratio)
    simp_rw [hlog, mul_sub] at h
    simp only [Finset.sum_sub_distrib, ← Finset.sum_mul] at h
    change Q - P * (Q / P) ≤ (∑ x ∈ S, q x * Real.log (q x / p x)) - Q * Real.log (Q / P) at h
    have hc : P * (Q / P) = Q := by field_simp
    rw [hc] at h
    dsimp [P, Q] at *
    linarith
  · rw [Finset.not_nonempty_iff_eq_empty.mp hS]
    simp

theorem finite_event_pinsker_sq (p q : α → ℝ)
    (hp : ∀ x, 0 < p x) (hq : ∀ x, 0 < q x)
    (hpsum : ∑ x, p x = 1) (hqsum : ∑ x, q x = 1) (S : Finset α) :
    2 * ((∑ x ∈ S, q x) - ∑ x ∈ S, p x) ^ 2 ≤ finiteKL q p := by
  classical
  have hKL := finiteKL_nonneg q p (fun x => (hq x).le) hqsum hp hpsum
  by_cases hS : S.Nonempty
  swap
  · simpa [Finset.not_nonempty_iff_eq_empty.mp hS] using hKL
  by_cases hSc : Sᶜ.Nonempty
  swap
  · have hSu : S = Finset.univ := by simpa using Finset.not_nonempty_iff_eq_empty.mp hSc
    simpa [hSu, hqsum, hpsum] using hKL
  let P := ∑ x ∈ S, p x
  let Q := ∑ x ∈ S, q x
  have hP : 0 < P := Finset.sum_pos (fun x _ => hp x) hS
  have hQ : 0 < Q := Finset.sum_pos (fun x _ => hq x) hS
  have hPc : (∑ x ∈ Sᶜ, p x) = 1 - P := by
    have h := Finset.sum_add_sum_compl S p
    rw [hpsum] at h
    dsimp [P]
    linarith
  have hQc : (∑ x ∈ Sᶜ, q x) = 1 - Q := by
    have h := Finset.sum_add_sum_compl S q
    rw [hqsum] at h
    dsimp [Q]
    linarith
  have hP1 : P < 1 := by
    have h := Finset.sum_pos (fun x (_ : x ∈ Sᶜ) => hp x) hSc
    rw [hPc] at h
    linarith
  have hQ1 : Q < 1 := by
    have h := Finset.sum_pos (fun x (_ : x ∈ Sᶜ) => hq x) hSc
    rw [hQc] at h
    linarith
  have hfirst := finite_log_sum p q hp hq S
  have hsecond := finite_log_sum p q hp hq Sᶜ
  rw [hPc, hQc] at hsecond
  have hpartition := Finset.sum_add_sum_compl S (fun x => q x * Real.log (q x / p x))
  change (∑ x ∈ S, q x * Real.log (q x / p x)) +
    (∑ x ∈ Sᶜ, q x * Real.log (q x / p x)) = finiteKL q p at hpartition
  have hbinary := MsetsLower.Lower.Dense.binary_pinsker ⟨hQ.le, hQ1.le⟩ hP hP1
  have hformula : MsetsLower.Lower.Dense.binaryCoarseKL Q P =
      Q * Real.log (Q / P) + (1 - Q) * Real.log ((1 - Q) / (1 - P)) := by
    unfold MsetsLower.Lower.Dense.binaryCoarseKL InformationTheory.klFun
    field_simp [hP.ne', (sub_pos.mpr hP1).ne']
    <;> ring
  rw [hformula] at hbinary
  change 2 * (Q - P) ^ 2 ≤ finiteKL q p
  change Q * Real.log (Q / P) ≤ _ at hfirst
  linarith

variable {d m : ℕ}

theorem weightedMarginal_pinsker_sq (theta psi : Fin d → ℝ) (hmd : m ≤ d) (i : Fin d) :
    2 * (weightedMarginal (m := m) theta i - weightedMarginal (m := m) psi i) ^ 2 ≤
      finiteKL (weightedLaw (m := m) theta) (weightedLaw psi) := by
  classical
  let S : Finset (Action d m) := Finset.univ.filter (fun x => i ∈ x.val)
  have hmarg (v : Fin d → ℝ) : (∑ x ∈ S, weightedLaw (m := m) v x) =
      weightedMarginal (m := m) v i := by
    simp [S, weightedMarginal, marginal, MsetsLower.History.selectedIndicator, Finset.sum_filter]
  have h := finite_event_pinsker_sq (weightedLaw (m := m) psi) (weightedLaw theta)
    (weightedLaw_pos psi hmd) (weightedLaw_pos theta hmd)
    (sum_weightedLaw psi hmd) (sum_weightedLaw theta hmd) S
  simpa only [hmarg] using h

theorem weightedMarginal_distance_of_KL (theta psi : Fin d → ℝ) (hmd : m ≤ d)
    (tau : ℝ) (hKL : finiteKL (weightedLaw (m := m) theta) (weightedLaw psi) ≤ tau)
    (i : Fin d) :
    |weightedMarginal (m := m) theta i - weightedMarginal (m := m) psi i| ≤
      Real.sqrt (tau / 2) := by
  have h := weightedMarginal_pinsker_sq theta psi hmd i
  apply Real.le_sqrt_of_sq_le
  rw [sq_abs]
  linarith

end MsetsPaper.Upper
