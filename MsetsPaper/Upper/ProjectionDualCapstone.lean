import MsetsPaper.Upper.ProjectionDualOptimality

/-! # Lemma L7: concrete existence, convexity, projection and subgradient -/

noncomputable section
open scoped BigOperators
open Matrix

namespace MsetsPaper.Upper

variable {d m : ℕ}

theorem projection_box_bounds (hmpos : 1 ≤ m) (hmtop : m ≤ d - 1)
    (lam : ℝ) (hlam : 0 < lam) (hlamhalf : lam ≤ 1 / 2) :
    (∀ i, 0 ≤ projectionLower d m lam i ∧ projectionLower d m lam i ≤ 1) ∧
    (∀ i, 0 ≤ projectionUpper d m lam i ∧ projectionUpper d m lam i ≤ 1) ∧
    (∀ i, projectionLower d m lam i ≤ projectionUpper d m lam i) := by
  have hd : (0 : ℝ) < d := by exact_mod_cast (show 0 < d by omega)
  have hm : (0 : ℝ) < m := by exact_mod_cast (show 0 < m by omega)
  have hmd : (m : ℝ) < d := by exact_mod_cast (show m < d by omega)
  have hr : 0 < (m : ℝ) / d := div_pos hm hd
  have hr1 : (m : ℝ) / d < 1 := (div_lt_one hd).mpr hmd
  dsimp [projectionLower, projectionUpper]
  refine ⟨?_, ?_, ?_⟩ <;> intro i
  · constructor <;> nlinarith
  · constructor <;> nlinarith
  · linarith

/-- Full mathematical statement of the manuscript's projection-dual lemma.
The conclusion refers to the actual normalized weighted m-set laws; there is no
optimal multiplier, feasibility or projection certificate among the premises. -/
theorem projection_dual_lemma (theta : Fin d → ℝ)
    (hmpos : 1 ≤ m) (hmtop : m ≤ d - 1)
    (lam : ℝ) (hlam : 0 < lam) (hlamhalf : lam ≤ 1 / 2) :
    let a := projectionLower d m lam
    let b := projectionUpper d m lam
    ConvexOn ℝ Set.univ (projectionDual (m := m) theta a b) ∧
    (∃ v, ∀ u, projectionDual (m := m) theta a b v ≤ projectionDual (m := m) theta a b u) ∧
    (∀ v, (∀ u, projectionDual (m := m) theta a b v ≤ projectionDual (m := m) theta a b u) →
      (∀ i, a i ≤ weightedMarginal (m := m) (theta + v) i ∧
        weightedMarginal (m := m) (theta + v) i ≤ b i) ∧
      (∀ q : Action d m → ℝ, (∀ x, 0 ≤ q x) → (∑ x, q x) = 1 →
        (∀ i, a i ≤ marginal q i ∧ marginal q i ≤ b i) →
        finiteKL (weightedLaw (m := m) (theta + v)) (weightedLaw theta) ≤
          finiteKL q (weightedLaw theta))) ∧
    (∀ u v, projectionDual (m := m) theta a b v +
      projectionSubgradient (m := m) theta a b v ⬝ᵥ (u - v) ≤
        projectionDual (m := m) theta a b u) ∧
    (∀ v, ‖projectionSubgradient (m := m) theta a b v‖ ≤ 1) := by
  obtain ⟨ha, hb, hab⟩ := projection_box_bounds hmpos hmtop lam hlam hlamhalf
  have hmd : m ≤ d := by omega
  refine ⟨projectionDual_convex theta _ _ hmd hab,
    projectionDual_exists theta hmpos hmtop lam hlam hlamhalf, ?_, ?_, ?_⟩
  · intro v hmin
    exact projectionDual_minimum_is_KL_projection theta _ _ v hmd hab hmin
  · intro u v
    exact projectionDual_subgradient theta _ _ u v hmd hab
  · intro v
    exact projectionSubgradient_norm_le_one theta _ _ v hmpos hmtop ha hb

end MsetsPaper.Upper
