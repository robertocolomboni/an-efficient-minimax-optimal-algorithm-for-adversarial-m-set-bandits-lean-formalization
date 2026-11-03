import MsetsPaper.Alignment.ExtendedKL

/-! Release interface for L7. The full conjunction uses the manuscript's
measure-theoretic extended KL; finiteness and conversion from the finite
probability formula are proved by the existing positive-reference bridge. -/

noncomputable section
open scoped BigOperators
open Matrix MsetsPaper.Upper

namespace MsetsPaper.Alignment.Implementation

variable {d m : ℕ}

/-- L7 with all its conclusions in one interface and genuine extended KL. -/
theorem projection_dual_paper (theta : Fin d → ℝ)
    (hm : 1 ≤ m) (hmtop : m ≤ d - 1) (lam : ℝ)
    (hlam : 0 < lam) (hlamhalf : lam ≤ 1 / 2) :
    let a := projectionLower d m lam
    let b := projectionUpper d m lam
    ConvexOn ℝ Set.univ (projectionDual (m := m) theta a b) ∧
    (∃ v, ∀ u, projectionDual (m := m) theta a b v ≤
      projectionDual (m := m) theta a b u) ∧
    (∀ v, (∀ u, projectionDual (m := m) theta a b v ≤
      projectionDual (m := m) theta a b u) →
      SmoothingPolytope lam (weightedLaw (m := m) (theta + v)) ∧
      (∀ q : Action d m → ℝ, SmoothingPolytope lam q →
        paperKL (weightedLaw (m := m) (theta + v)) (weightedLaw theta) ≤
          paperKL q (weightedLaw theta))) ∧
    (∀ u v, projectionDual (m := m) theta a b v +
      projectionSubgradient (m := m) theta a b v ⬝ᵥ (u - v) ≤
        projectionDual (m := m) theta a b u) ∧
    (∀ v, ‖projectionSubgradient (m := m) theta a b v‖ ≤ 1) := by
  have h := projection_dual theta hm hmtop lam hlam hlamhalf
  exact ⟨h.1, h.2.1,
    fun v hmin => projection_minimizes_extendedKL theta hm hmtop lam hlam hlamhalf v hmin,
    h.2.2.2.1, h.2.2.2.2⟩

end MsetsPaper.Alignment.Implementation
