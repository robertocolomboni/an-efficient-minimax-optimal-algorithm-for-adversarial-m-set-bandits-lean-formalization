import MsetsPaper.Upper.ESPDP

/-! # Single and pair inclusion probabilities computed by deletion ESPs -/

noncomputable section
open scoped BigOperators
open MsetsLower MsetsLower.History

namespace MsetsPaper.Upper

variable {d m : ℕ}

theorem weightedLaw_containing (theta : Fin d → ℝ) (J : Finset (Fin d))
    (hJm : J.card ≤ m) :
    (∑ a : Action d m, if J ⊆ a.val then weightedLaw theta a else 0) =
      (∏ i ∈ J, Real.exp (theta i)) *
        esp (fun i => Real.exp (theta i)) (Finset.univ \ J) (m - J.card) /
        partition (m := m) theta := by
  simp only [weightedLaw, actionLoss_eq_finset_sum, Real.exp_sum]
  have heq : (∑ a : Action d m,
      if J ⊆ a.val then (∏ i ∈ a.val, Real.exp (theta i)) / partition (m := m) theta else 0) =
      (∑ a : Action d m, if J ⊆ a.val then ∏ i ∈ a.val, Real.exp (theta i) else 0) /
        partition (m := m) theta := by
    rw [Finset.sum_div]
    apply Finset.sum_congr rfl
    intro a _
    split_ifs <;> simp
  rw [heq, sum_actions_eq_powerset (m := m)
    (fun S => if J ⊆ S then ∏ i ∈ S, Real.exp (theta i) else 0)]
  rw [esp_containing _ _ _ (Finset.subset_univ _) _ hJm]

theorem weightedMarginal_eq_esp (theta : Fin d → ℝ) (hm : 1 ≤ m) (i : Fin d) :
    weightedMarginal (m := m) theta i = Real.exp (theta i) *
      esp (fun j => Real.exp (theta j)) (Finset.univ.erase i) (m - 1) /
      partition (m := m) theta := by
  have h := weightedLaw_containing (m := m) theta {i} (by simpa using hm)
  simpa [weightedMarginal, marginal, selectedIndicator, mul_ite, Finset.sdiff_singleton_eq_erase]
    using h

theorem secondMoment_diagonal_eq_marginal (theta : Fin d → ℝ) (i : Fin d) :
    secondMoment (weightedLaw (m := m) theta) i i = weightedMarginal (m := m) theta i := by
  unfold secondMoment weightedMarginal marginal
  apply Finset.sum_congr rfl
  intro a _
  by_cases hi : i ∈ a.val <;> simp [selectedIndicator, hi]

theorem secondMoment_offdiag_eq_esp (theta : Fin d → ℝ) (hm : 2 ≤ m)
    (i j : Fin d) (hij : i ≠ j) :
    secondMoment (weightedLaw (m := m) theta) i j =
      Real.exp (theta i) * Real.exp (theta j) *
        esp (fun k => Real.exp (theta k)) (Finset.univ \ {i, j}) (m - 2) /
        partition (m := m) theta := by
  have h := weightedLaw_containing (m := m) theta {i, j} (by simpa [hij] using hm)
  have h' : (∑ a : Action d m,
      if ({i, j} : Finset (Fin d)) ⊆ a.val then weightedLaw theta a else 0) =
      Real.exp (theta i) * Real.exp (theta j) *
        esp (fun k => Real.exp (theta k)) (Finset.univ \ {i, j}) (m - 2) /
        partition (m := m) theta := by simpa [hij] using h
  rw [← h']
  unfold secondMoment
  apply Finset.sum_congr rfl
  intro a _
  by_cases hi : i ∈ a.val <;> by_cases hj : j ∈ a.val <;>
    simp [selectedIndicator, Finset.insert_subset_iff, Finset.singleton_subset_iff, hi, hj]

/-- Rank one is handled separately: natural subtraction must not turn -1 into 0. -/
theorem secondMoment_rank_one_offdiag (theta : Fin d → ℝ) (i j : Fin d) (hij : i ≠ j) :
    secondMoment (weightedLaw (m := 1) theta) i j = 0 := by
  unfold secondMoment
  apply Finset.sum_eq_zero
  intro a _
  by_cases hi : i ∈ a.val
  · have hj : j ∉ a.val := by
      intro hj
      have hsub : ({i, j} : Finset (Fin d)) ⊆ a.val :=
        Finset.insert_subset_iff.mpr ⟨hi, Finset.singleton_subset_iff.mpr hj⟩
      have hc := Finset.card_le_card hsub
      simp [hij, a.property] at hc
    simp [selectedIndicator, hj]
  · simp [selectedIndicator, hi]

end MsetsPaper.Upper
