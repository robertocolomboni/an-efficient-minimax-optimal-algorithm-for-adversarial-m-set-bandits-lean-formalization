import MsetsPaper.Probability.FiniteExponential

/-!
# The two-sided predictable exponential-moment argument

This is L5's two exponential supermartingales, Markov inequality at rho/2,
and the union bound. No conditional concentration theorem is assumed.
-/

namespace MsetsPaper.Probability

open scoped BigOperators

variable {α : Type} [Fintype α]

theorem compensated_mgf (P : BranchingLaw α) (t : ℕ) (h : ActionTree α t)
    (x : α → ℝ) (v : ℝ)
    (hmgf : ∑ a, P.next t h a * Real.exp (x a) ≤ Real.exp v) :
    ∑ a, P.next t h a * Real.exp (x a - v) ≤ 1 := by
  simp only [Real.exp_sub, ← mul_div_assoc, ← Finset.sum_div]
  exact (div_le_one (Real.exp_pos v)).mpr hmgf

theorem two_sided_predictable_high_probability (P : BranchingLaw α)
    (x : (t : ℕ) → ActionTree α t → α → ℝ)
    (v : (t : ℕ) → ActionTree α t → ℝ) (T : ℕ)
    {eta : ℝ} (heta : 0 < eta)
    (hmgf : ∀ t < T, ∀ h s, (s = 1 ∨ s = -1) →
      ∑ a, P.next t h a * Real.exp (s * eta * x t h a) ≤
        Real.exp (eta ^ 2 / 4 * v t h))
    {rho : ℝ} (hrho : 0 < rho) :
    1 - rho ≤ P.probability T {h |
      |pathSum x T h| ≤ eta / 4 * pathSum (fun t h _ ↦ v t h) T h +
        Real.log (2 / rho) / eta} := by
  let V := fun t h (_ : α) ↦ v t h
  let g := fun (s : ℝ) t h a ↦ s * eta * x t h a - eta ^ 2 / 4 * v t h
  have htail (s : ℝ) (hs : s = 1 ∨ s = -1) :
      P.probability T {h | Real.log (2 / rho) ≤ pathSum (g s) T h} ≤ rho / 2 := by
    have h := exponential_log_tail_upto P (g s) T
      (fun t ht h ↦ compensated_mgf P t h _ _ (hmgf t ht h s hs))
      (show 0 < rho / 2 by positivity)
    have hid : 1 / (rho / 2) = 2 / rho := by ring
    simpa only [hid] using h
  have hsum (s : ℝ) (h : ActionTree α T) : pathSum (g s) T h =
      s * eta * pathSum x T h - eta ^ 2 / 4 * pathSum V T h := by
    have h := pathSum_linear x V (s * eta) (-(eta ^ 2 / 4)) T h
    simpa only [g, V, sub_eq_add_neg, neg_mul] using h
  apply P.probability_le_of_compl_bound
  have hsub : ({h | |pathSum x T h| ≤ eta / 4 * pathSum V T h +
      Real.log (2 / rho) / eta} : Set (ActionTree α T))ᶜ ⊆
      {h | Real.log (2 / rho) ≤ pathSum (g 1) T h} ∪
      {h | Real.log (2 / rho) ≤ pathSum (g (-1)) T h} := by
    intro h hh
    have hnot : ¬ |pathSum x T h| ≤ eta / 4 * pathSum V T h +
        Real.log (2 / rho) / eta := hh
    have hid : eta * (Real.log (2 / rho) / eta) = Real.log (2 / rho) := by
      field_simp
    by_cases hx : 0 ≤ pathSum x T h
    · left
      change Real.log (2 / rho) ≤ pathSum (g 1) T h
      rw [hsum]
      rw [abs_of_nonneg hx] at hnot
      have hb := mul_lt_mul_of_pos_left (lt_of_not_ge hnot) heta
      nlinarith
    · right
      change Real.log (2 / rho) ≤ pathSum (g (-1)) T h
      rw [hsum]
      rw [abs_of_neg (lt_of_not_ge hx)] at hnot
      have hb := mul_lt_mul_of_pos_left (lt_of_not_ge hnot) heta
      nlinarith
  refine (P.probability_mono T _ _ hsub).trans ?_
  refine (P.probability_union_le T _ _).trans ?_
  have hpos := htail 1 (Or.inl rfl)
  have hneg := htail (-1) (Or.inr rfl)
  linarith

end MsetsPaper.Probability
