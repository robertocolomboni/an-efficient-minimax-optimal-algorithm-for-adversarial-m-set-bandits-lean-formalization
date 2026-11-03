import MsetsPaper.Upper.ProjectionDualSubgradient

/-! The full coordinate-interval formulation in the paper, without selecting
the midpoint at zero. The algorithm's midpoint is an existing specialization
of the same general supporting-hyperplane proof. -/

noncomputable section
open Matrix MsetsPaper.Upper

namespace MsetsPaper.Alignment

theorem projectionDual_all_coordinate_subgradients {d m : ℕ}
    (theta a b u v g : Fin d → ℝ) (hmd : m ≤ d) (hab : ∀ i, a i ≤ b i)
    (hpos : ∀ i, 0 < v i → g i = weightedMarginal (m := m) (theta + v) i - a i)
    (hneg : ∀ i, v i < 0 → g i = weightedMarginal (m := m) (theta + v) i - b i)
    (hzero : ∀ i, v i = 0 →
      weightedMarginal (m := m) (theta + v) i - b i ≤ g i ∧
        g i ≤ weightedMarginal (m := m) (theta + v) i - a i) :
    projectionDual (m := m) theta a b v + g ⬝ᵥ (u - v) ≤
      projectionDual (m := m) theta a b u := by
  let s : Fin d → ℝ := fun i ↦ g i - weightedMarginal (m := m) (theta + v) i
  have hs : ∀ i, v i = 0 → -b i ≤ s i ∧ s i ≤ -a i := by
    intro i hi
    dsimp [s]
    constructor <;> linarith [(hzero i hi).1, (hzero i hi).2]
  have heq : projectionSubgradientWithZero (m := m) theta a b v s = g := by
    ext i
    unfold projectionSubgradientWithZero scalarProjectionSlopeWithZero
    by_cases hp : 0 < v i
    · rw [if_pos hp, hpos i hp]
      ring
    · rw [if_neg hp]
      by_cases hn : v i < 0
      · rw [if_pos hn, hneg i hn]
        ring
      · rw [if_neg hn]
        dsimp [s]
        ring
  simpa only [heq] using projectionDual_subgradient_with_zero theta a b u v s hmd hab hs

end MsetsPaper.Alignment
