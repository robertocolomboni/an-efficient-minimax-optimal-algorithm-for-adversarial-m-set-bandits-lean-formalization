import MsetsPaper.Upper.FiniteTV

/-! # Feasibility and Pythagorean error from an actual dual objective gap -/

noncomputable section
open scoped BigOperators
open Matrix

namespace MsetsPaper.Upper

variable {d m : ℕ}

theorem finiteKL_three_point_weightedLaw (theta v : Fin d → ℝ)
    (q : Action d m → ℝ) (hqsum : ∑ x, q x = 1) (hmd : m ≤ d) :
    finiteKL q (weightedLaw (m := m) (theta + v)) +
      finiteKL (weightedLaw (m := m) (theta + v)) (weightedLaw theta) -
        finiteKL q (weightedLaw theta) =
      (weightedMarginal (m := m) (theta + v) - marginal q) ⬝ᵥ v := by
  have hq := finiteKL_weightedLaw_shift q hqsum theta v hmd
  have hp := finiteKL_weightedLaw_shift (weightedLaw (m := m) (theta + v))
    (sum_weightedLaw (theta + v) hmd) theta v hmd
  rw [finiteKL_self] at hp
  simp only [dotProduct, Pi.sub_apply, sub_mul, Finset.sum_sub_distrib]
  change _ = marginal (weightedLaw (m := m) (theta + v)) ⬝ᵥ v - marginal q ⬝ᵥ v
  linarith

theorem marginal_dot_le_projectionSlack (a b mu nu v : Fin d → ℝ)
    (hnu : ∀ i, a i ≤ nu i ∧ nu i ≤ b i) :
    (mu - nu) ⬝ᵥ v ≤ projectionSlack a b mu v := by
  apply Finset.sum_le_sum
  intro i _
  have hp := mul_nonneg (le_max_right (v i) 0) (sub_nonneg.mpr (hnu i).1)
  have hn := mul_nonneg (le_max_right (-v i) 0) (sub_nonneg.mpr (hnu i).2)
  have hv := congrArg (fun x : ℝ => (mu i - nu i) * x)
    (positivePart_sub_negativePart (v i))
  change (mu i - nu i) * v i ≤ _
  nlinarith only [hp, hn, hv]

theorem dot_le_coordinateL1_mul (x v : Fin d → ℝ) (delta : ℝ)
    (hx : ∀ i, |x i| ≤ delta) : x ⬝ᵥ v ≤ coordinateL1 v * delta := by
  unfold dotProduct coordinateL1
  rw [Finset.sum_mul]
  apply Finset.sum_le_sum
  intro i _
  calc
    x i * v i ≤ |x i * v i| := le_abs_self _
    _ = |x i| * |v i| := abs_mul _ _
    _ ≤ delta * |v i| := mul_le_mul_of_nonneg_right (hx i) (abs_nonneg _)
    _ = |v i| * delta := mul_comm _ _

/-- Every sufficiently accurate dual point satisfies the quantitative
Pythagorean inequality. An algorithm producing the point is a separate task. -/
theorem projection_gap_pythagorean_bound (theta a b vstar v : Fin d → ℝ)
    (hmd : m ≤ d) (hab : ∀ i, a i ≤ b i)
    (hmin : ∀ u, projectionDual (m := m) theta a b vstar ≤ projectionDual (m := m) theta a b u)
    (tau R : ℝ) (hgap : projectionDual (m := m) theta a b v -
      projectionDual (m := m) theta a b vstar ≤ tau) (hvR : coordinateL1 v ≤ R)
    (q : Action d m → ℝ) (hqsum : ∑ x, q x = 1)
    (hqbox : ∀ i, a i ≤ marginal q i ∧ marginal q i ≤ b i) :
    finiteKL q (weightedLaw (m := m) (theta + v)) +
      finiteKL (weightedLaw (m := m) (theta + v)) (weightedLaw theta) ≤
        finiteKL q (weightedLaw theta) + R * Real.sqrt (tau / 2) + tau := by
  obtain ⟨hKL, hslack⟩ := projectionDual_gap_controls_KL_and_slack theta a b vstar v
    hmd hab hmin tau hgap
  have hdist : ∀ i, |(weightedMarginal (m := m) (theta + v) -
      weightedMarginal (m := m) (theta + vstar)) i| ≤ Real.sqrt (tau / 2) := by
    intro i
    simpa only [Pi.sub_apply, abs_sub_comm] using
      weightedMarginal_distance_of_KL_via_TV (theta + vstar) (theta + v) hmd tau hKL i
  have hholder := dot_le_coordinateL1_mul _ v (Real.sqrt (tau / 2)) hdist
  have hqdot := marginal_dot_le_projectionSlack a b
    (weightedMarginal (m := m) (theta + vstar)) (marginal q) v hqbox
  have hsplit : (weightedMarginal (m := m) (theta + v) - marginal q) ⬝ᵥ v =
      (weightedMarginal (m := m) (theta + v) - weightedMarginal (m := m) (theta + vstar)) ⬝ᵥ v +
        (weightedMarginal (m := m) (theta + vstar) - marginal q) ⬝ᵥ v := by
    simp only [dotProduct, Pi.sub_apply, sub_mul, Finset.sum_sub_distrib]
    ring
  have hr := mul_le_mul_of_nonneg_right hvR (Real.sqrt_nonneg (tau / 2))
  have hthree := finiteKL_three_point_weightedLaw theta v q hqsum hmd
  rw [hsplit] at hthree
  linarith

theorem projection_gap_half_box (theta vstar v : Fin d → ℝ)
    (hmpos : 1 ≤ m) (hmtop : m ≤ d - 1) (lam : ℝ) (hlam : 0 < lam)
    (hlamhalf : lam ≤ 1 / 2)
    (hmin : ∀ u, projectionDual (m := m) theta (projectionLower d m lam)
      (projectionUpper d m lam) vstar ≤ projectionDual (m := m) theta
        (projectionLower d m lam) (projectionUpper d m lam) u)
    (tau : ℝ) (hgap : projectionDual (m := m) theta (projectionLower d m lam)
      (projectionUpper d m lam) v - projectionDual (m := m) theta
        (projectionLower d m lam) (projectionUpper d m lam) vstar ≤ tau)
    (haccuracy : Real.sqrt (tau / 2) ≤ lam / (2 * (d : ℝ))) :
    ∀ i, projectionLower d m (lam / 2) i ≤ weightedMarginal (m := m) (theta + v) i ∧
      weightedMarginal (m := m) (theta + v) i ≤ projectionUpper d m (lam / 2) i := by
  have hmd : m ≤ d := by omega
  have hd : (0 : ℝ) < d := by exact_mod_cast (show 0 < d by omega)
  have hm : (1 : ℝ) ≤ m := by exact_mod_cast hmpos
  have hdm : (m : ℝ) + 1 ≤ d := by exact_mod_cast (show m + 1 ≤ d by omega)
  obtain ⟨_, _, hab⟩ := projection_box_bounds hmpos hmtop lam hlam hlamhalf
  have hKL := (projectionDual_gap_controls_KL_and_slack theta _ _ vstar v
    hmd hab hmin tau hgap).1
  intro i
  have hbox := (projectionDual_minimum_is_KL_projection theta _ _ vstar hmd hab hmin).1 i
  have hdist := (weightedMarginal_distance_of_KL_via_TV (theta + vstar) (theta + v)
    hmd tau hKL i).trans
    haccuracy
  rw [abs_sub_le_iff] at hdist
  have hrlo : 1 / (d : ℝ) ≤ (m : ℝ) / d :=
    (div_le_div_iff_of_pos_right hd).mpr hm
  have hrhi : 1 / (d : ℝ) ≤ 1 - (m : ℝ) / d := by
    apply (div_le_iff₀ hd).mpr
    have hmul : ((m : ℝ) / d) * d = m := div_mul_cancel₀ _ hd.ne'
    nlinarith
  have hslo := mul_le_mul_of_nonneg_left hrlo (show 0 ≤ lam / 2 by positivity)
  have hshi := mul_le_mul_of_nonneg_left hrhi (show 0 ≤ lam / 2 by positivity)
  have hscale : (lam / 2) * (1 / (d : ℝ)) = lam / (2 * (d : ℝ)) := by ring
  rw [hscale] at hslo hshi
  dsimp [projectionLower, projectionUpper] at hbox ⊢
  constructor <;> nlinarith [hbox.1, hbox.2, hdist.1, hdist.2]

/-- Exact square-root substitution and the final epsilon budget in L8. -/
theorem projection_accuracy_budget (eps R : ℝ) (heps : 0 ≤ eps) (heps1 : eps ≤ 1)
    (hR : 1 ≤ R) :
    Real.sqrt ((eps ^ 2 / (2 * R ^ 2)) / 2) = eps / (2 * R) ∧
    R * Real.sqrt ((eps ^ 2 / (2 * R ^ 2)) / 2) + eps ^ 2 / (2 * R ^ 2) ≤ eps := by
  have hRpos : 0 < R := by linarith
  have hsquare : (eps ^ 2 / (2 * R ^ 2)) / 2 = (eps / (2 * R)) ^ 2 := by ring
  have hsqrt : Real.sqrt ((eps ^ 2 / (2 * R ^ 2)) / 2) = eps / (2 * R) := by
    rw [hsquare, Real.sqrt_sq (by positivity)]
  refine ⟨hsqrt, ?_⟩
  rw [hsqrt]
  have hmain : R * (eps / (2 * R)) = eps / 2 := by field_simp
  rw [hmain]
  have hrem : eps ^ 2 / (2 * R ^ 2) ≤ eps / 2 := by
    apply (div_le_iff₀ (by positivity : (0 : ℝ) < 2 * R ^ 2)).mpr
    have hR2 : 1 ≤ R ^ 2 := by nlinarith
    have hprod := mul_le_mul_of_nonneg_left hR2 heps
    nlinarith
  linarith

end MsetsPaper.Upper
