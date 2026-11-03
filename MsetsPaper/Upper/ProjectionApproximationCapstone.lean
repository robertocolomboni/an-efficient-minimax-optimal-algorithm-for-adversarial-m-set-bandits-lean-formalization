import MsetsPaper.Upper.ProjectionAccuracy
import MsetsPaper.Upper.ProjectionJensen

/-!
# The mathematical guarantee of Lemma L8, with exact paper parameters

This is the implication from a dual point of the required accuracy to the
claimed projection guarantees. It does NOT claim that the ellipsoid algorithm
computes such a point, or any running-time/space bound.
-/

noncomputable section
open scoped BigOperators

namespace MsetsPaper.Upper

def projectionRadius (d : ℕ) (T : ℝ) : ℝ := 4 * d * T
def projectionTolerance (d : ℕ) (eta T : ℝ) : ℝ :=
  (eta / T) ^ 2 / (2 * (projectionRadius d T) ^ 2)

theorem projection_tolerance_sqrt_exact (d : ℕ) (hd : 1 ≤ d) (eta T : ℝ)
    (heta : 0 < eta) (hetaMax : eta ≤ 1 / (256 * (d : ℝ))) (hT : 1 ≤ T) :
    Real.sqrt (projectionTolerance d eta T / 2) = eta / (8 * d * T ^ 2) := by
  have hdpos : (0 : ℝ) < d := by exact_mod_cast (show 0 < d by omega)
  have hTpos : 0 < T := by linarith
  have hsquare : projectionTolerance d eta T / 2 = (eta / (8 * d * T ^ 2)) ^ 2 := by
    unfold projectionTolerance projectionRadius
    ring
  rw [hsquare, Real.sqrt_sq (by positivity)]

theorem projection_parameter_bounds (d : ℕ) (hd : 1 ≤ d) (eta T : ℝ)
    (heta : 0 < eta) (hetaMax : eta ≤ 1 / (256 * (d : ℝ))) (hT : 1 ≤ T) :
    0 < 128 * eta * d ∧ 128 * eta * d ≤ 1 / 2 ∧
    0 ≤ eta / T ∧ eta / T ≤ 1 ∧ 1 ≤ projectionRadius d T ∧
    Real.sqrt (projectionTolerance d eta T / 2) ≤ (128 * eta * d) / (2 * (d : ℝ)) ∧
    projectionRadius d T * Real.sqrt (projectionTolerance d eta T / 2) +
      projectionTolerance d eta T ≤ eta / T := by
  have hd1 : (1 : ℝ) ≤ d := by exact_mod_cast hd
  have hdpos : (0 : ℝ) < d := by linarith
  have hTpos : 0 < T := by linarith
  have hrate := (le_div_iff₀ (show (0 : ℝ) < 256 * d by positivity)).mp hetaMax
  have hlam : 0 < 128 * eta * d := by positivity
  have hlamhalf : 128 * eta * d ≤ 1 / 2 := by nlinarith
  have heta1 : eta ≤ 1 := by
    have hprod := mul_le_mul_of_nonneg_left hd1 heta.le
    nlinarith
  have heps0 : 0 ≤ eta / T := by positivity
  have hepsEta : eta / T ≤ eta := by
    apply (div_le_iff₀ hTpos).mpr
    nlinarith
  have heps1 : eta / T ≤ 1 := hepsEta.trans heta1
  have hR1 : 1 ≤ projectionRadius d T := by
    unfold projectionRadius
    nlinarith [mul_le_mul hd1 hT (by norm_num : (0 : ℝ) ≤ 1) (by positivity : (0 : ℝ) ≤ d)]
  obtain ⟨_, hbudget⟩ := projection_accuracy_budget (eta / T) (projectionRadius d T)
    heps0 heps1 hR1
  have hsqrt := projection_tolerance_sqrt_exact d hd eta T heta hetaMax hT
  have hden : 1 ≤ 8 * (d : ℝ) * T ^ 2 := by
    have hT2 : 1 ≤ T ^ 2 := by nlinarith
    nlinarith [mul_le_mul hd1 hT2 (by norm_num : (0 : ℝ) ≤ 1) hdpos.le]
  have hlarge : (128 * eta * d) / (2 * (d : ℝ)) = 64 * eta := by field_simp; ring
  refine ⟨hlam, hlamhalf, heps0, heps1, hR1, ?_, hbudget⟩
  rw [hsqrt, hlarge]
  apply (div_le_iff₀ (show (0 : ℝ) < 8 * d * T ^ 2 by positivity)).mpr
  nlinarith [mul_le_mul_of_nonneg_left hden heta.le]

variable {d m : ℕ}

/-- All mathematical claims about the returned point in L8, with the exact
lambda, epsilon, R and tau of the paper. The sole computational premise is
the explicit approximate-minimum property on the L1 ball; no projection,
marginal feasibility or Pythagorean conclusion is hidden in that premise. -/
theorem approximate_projection_of_dual_accuracy (theta v : Fin d → ℝ)
    (hmpos : 1 ≤ m) (hmtop : m ≤ d - 1) (eta T : ℝ)
    (heta : 0 < eta) (hetaMax : eta ≤ 1 / (256 * (d : ℝ))) (hT : 1 ≤ T)
    (hKL : finiteKL (weightedLaw (m := m) (0 : Fin d → ℝ)) (weightedLaw theta) ≤ T)
    (hvR : coordinateL1 v ≤ projectionRadius d T)
    (haccuracy : ∀ u, coordinateL1 u ≤ projectionRadius d T →
      projectionDual (m := m) theta (projectionLower d m (128 * eta * d))
        (projectionUpper d m (128 * eta * d)) v ≤
      projectionDual (m := m) theta (projectionLower d m (128 * eta * d))
        (projectionUpper d m (128 * eta * d)) u + projectionTolerance d eta T) :
    (∀ i, projectionLower d m ((128 * eta * d) / 2) i ≤
        weightedMarginal (m := m) (theta + v) i ∧
      weightedMarginal (m := m) (theta + v) i ≤
        projectionUpper d m ((128 * eta * d) / 2) i) ∧
    (∀ q : Action d m → ℝ, (∀ x, 0 ≤ q x) → (∑ x, q x) = 1 →
      (∀ i, projectionLower d m (128 * eta * d) i ≤ marginal q i ∧
        marginal q i ≤ projectionUpper d m (128 * eta * d) i) →
      finiteKL q (weightedLaw (m := m) (theta + v)) +
        finiteKL (weightedLaw (m := m) (theta + v)) (weightedLaw theta) ≤
      finiteKL q (weightedLaw theta) + eta / T) := by
  have hd : 1 ≤ d := by omega
  have hmd : m ≤ d := by omega
  obtain ⟨hlam, hlamhalf, _, _, _, hdelta, hbudget⟩ :=
    projection_parameter_bounds d hd eta T heta hetaMax hT
  obtain ⟨vstar, hmin⟩ := projectionDual_exists theta hmpos hmtop
    (128 * eta * d) hlam hlamhalf
  have hstar := projectionDual_minimum_radius_via_Jensen theta vstar hmpos hmtop
    (128 * eta * d) T hlamhalf hKL hmin
  have hstarR : coordinateL1 vstar ≤ projectionRadius d T := by
    unfold projectionRadius
    have hd0 : (0 : ℝ) ≤ d := Nat.cast_nonneg _
    nlinarith [mul_nonneg hd0 (show 0 ≤ T by linarith)]
  have hgap : projectionDual (m := m) theta (projectionLower d m (128 * eta * d))
      (projectionUpper d m (128 * eta * d)) v -
      projectionDual (m := m) theta (projectionLower d m (128 * eta * d))
      (projectionUpper d m (128 * eta * d)) vstar ≤ projectionTolerance d eta T := by
    linarith [haccuracy vstar hstarR]
  refine ⟨projection_gap_half_box theta vstar v hmpos hmtop (128 * eta * d)
    hlam hlamhalf hmin _ hgap hdelta, ?_⟩
  intro q _hq hqsum hqbox
  have hab := (projection_box_bounds hmpos hmtop (128 * eta * d) hlam hlamhalf).2.2
  have h := projection_gap_pythagorean_bound theta _ _ vstar v hmd hab hmin
    (projectionTolerance d eta T) (projectionRadius d T) hgap hvR q hqsum hqbox
  linarith

end MsetsPaper.Upper
