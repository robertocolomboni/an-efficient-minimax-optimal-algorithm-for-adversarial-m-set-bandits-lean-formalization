import MsetsPaper.Upper.ProjectionDualCapstone

/-!
# Mathematical error estimates for approximate projection

This module proves estimates for the actual dual objective and weighted laws.
It does not postulate or certify an ellipsoid implementation.
-/

noncomputable section
open scoped BigOperators
open Matrix

namespace MsetsPaper.Upper

variable {d m : ℕ}

def coordinateL1 (v : Fin d → ℝ) : ℝ := ∑ i, |v i|

theorem uniform_KL_logPartition (theta : Fin d → ℝ)
    (hmpos : 1 ≤ m) (hmtop : m ≤ d - 1) :
    finiteKL (weightedLaw (m := m) (0 : Fin d → ℝ)) (weightedLaw theta) =
      logPartition (m := m) theta - logPartition (m := m) (0 : Fin d → ℝ) -
        ((m : ℝ) / d) * (∑ i, theta i) := by
  have hmd : m ≤ d := by omega
  have h := finiteKL_weightedLaw_shift (weightedLaw (m := m) (0 : Fin d → ℝ))
    (sum_weightedLaw 0 hmd) (0 : Fin d → ℝ) theta hmd
  rw [zero_add, finiteKL_self] at h
  have hmarg : marginal (weightedLaw (m := m) (0 : Fin d → ℝ)) ⬝ᵥ theta =
      ((m : ℝ) / d) * (∑ i, theta i) := by
    change weightedMarginal (m := m) (0 : Fin d → ℝ) ⬝ᵥ theta = _
    simp only [dotProduct, weightedMarginal_zero_eq hmpos hmtop, Finset.mul_sum]
  rw [hmarg] at h
  linarith

/-- The manuscript's uniform-law/Jensen lower bound. It is derived here from
the proved KL supporting inequality, with the identical constants. -/
theorem projectionDual_lower_bound_uniform_KL (theta a b v : Fin d → ℝ)
    (hmpos : 1 ≤ m) (hmtop : m ≤ d - 1) (eps : ℝ)
    (hlo : ∀ i, eps ≤ (m : ℝ) / d - a i)
    (hhi : ∀ i, eps ≤ b i - (m : ℝ) / d) :
    logPartition (m := m) theta -
        finiteKL (weightedLaw (m := m) (0 : Fin d → ℝ)) (weightedLaw theta) +
      eps * coordinateL1 v ≤ projectionDual (m := m) theta a b v := by
  have h := projectionDual_coercive theta a b hmpos hmtop eps hlo hhi v
  rw [uniform_KL_logPartition theta hmpos hmtop]
  dsimp [coordinateL1]
  linarith

theorem projection_uniform_slack_explicit (hmpos : 1 ≤ m) (hmtop : m ≤ d - 1)
    (lam : ℝ) (hlamhalf : lam ≤ 1 / 2) :
    (∀ i, 1 / (2 * (d : ℝ)) ≤ (m : ℝ) / d - projectionLower d m lam i) ∧
    (∀ i, 1 / (2 * (d : ℝ)) ≤ projectionUpper d m lam i - (m : ℝ) / d) := by
  have hd : (0 : ℝ) < d := by exact_mod_cast (show 0 < d by omega)
  have hm : (1 : ℝ) ≤ m := by exact_mod_cast hmpos
  have hmd : (m : ℝ) + 1 ≤ d := by exact_mod_cast (show m + 1 ≤ d by omega)
  have hrlo : 1 / (d : ℝ) ≤ (m : ℝ) / d :=
    (div_le_div_iff_of_pos_right hd).mpr hm
  have hrhi : 1 / (d : ℝ) ≤ 1 - (m : ℝ) / d := by
    apply (div_le_iff₀ hd).mpr
    have hmul : ((m : ℝ) / d) * d = m := div_mul_cancel₀ _ hd.ne'
    nlinarith
  have hscale : (1 / (d : ℝ)) / 2 = 1 / (2 * (d : ℝ)) := by ring
  have hr0 : 0 ≤ (m : ℝ) / d := (one_div_pos.mpr hd).le.trans hrlo
  have hr1 : 0 ≤ 1 - (m : ℝ) / d := (one_div_pos.mpr hd).le.trans hrhi
  constructor <;> intro i <;> dsimp [projectionLower, projectionUpper]
  · have hprod := mul_nonneg (show 0 ≤ 1 / 2 - lam by linarith) hr0
    nlinarith
  · have hprod := mul_nonneg (show 0 ≤ 1 / 2 - lam by linarith) hr1
    nlinarith

/-- Every minimizer lies within the paper's radius R/2 = 2 d T. -/
theorem projectionDual_minimum_radius (theta v : Fin d → ℝ)
    (hmpos : 1 ≤ m) (hmtop : m ≤ d - 1) (lam T : ℝ) (hlamhalf : lam ≤ 1 / 2)
    (hKL : finiteKL (weightedLaw (m := m) (0 : Fin d → ℝ)) (weightedLaw theta) ≤ T)
    (hmin : ∀ u, projectionDual (m := m) theta (projectionLower d m lam)
      (projectionUpper d m lam) v ≤ projectionDual (m := m) theta
        (projectionLower d m lam) (projectionUpper d m lam) u) :
    coordinateL1 v ≤ 2 * d * T := by
  have hd : (0 : ℝ) < d := by exact_mod_cast (show 0 < d by omega)
  obtain ⟨hlo, hhi⟩ := projection_uniform_slack_explicit hmpos hmtop lam hlamhalf
  have h := projectionDual_lower_bound_uniform_KL theta _ _ v hmpos hmtop
    (1 / (2 * (d : ℝ))) hlo hhi
  have hzero := hmin 0
  simp only [projectionDual, add_zero, projectionPenalty, Pi.zero_apply, neg_zero,
    max_self, mul_zero, Finset.sum_const_zero, add_zero] at hzero
  change projectionDual (m := m) theta (projectionLower d m lam)
    (projectionUpper d m lam) v ≤ logPartition (m := m) theta at hzero
  rw [show 1 / (2 * (d : ℝ)) * coordinateL1 v = coordinateL1 v / (2 * (d : ℝ)) by ring] at h
  have hL : coordinateL1 v / (2 * (d : ℝ)) ≤ T := by linarith
  have hbound := (div_le_iff₀ (mul_pos (by norm_num : (0 : ℝ) < 2) hd)).mp hL
  nlinarith

def projectionSlack (a b mu v : Fin d → ℝ) : ℝ :=
  ∑ i, (max (v i) 0 * (mu i - a i) + max (-v i) 0 * (b i - mu i))

theorem projectionSlack_identity (a b mu v : Fin d → ℝ) :
    projectionSlack a b mu v = projectionPenalty a b v + mu ⬝ᵥ v := by
  unfold projectionSlack projectionPenalty dotProduct
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro i _
  have hv := positivePart_sub_negativePart (v i)
  have hmul := congrArg (fun x : ℝ => mu i * x) hv
  nlinarith only [hmul]

theorem projectionSlack_nonneg (a b mu v : Fin d → ℝ)
    (hmu : ∀ i, a i ≤ mu i ∧ mu i ≤ b i) : 0 ≤ projectionSlack a b mu v := by
  apply Finset.sum_nonneg
  intro i _
  exact add_nonneg
    (mul_nonneg (le_max_right _ _) (sub_nonneg.mpr (hmu i).1))
    (mul_nonneg (le_max_right _ _) (sub_nonneg.mpr (hmu i).2))

theorem projectionSlack_at_minimum (theta a b vstar : Fin d → ℝ) (hmd : m ≤ d)
    (hab : ∀ i, a i ≤ b i)
    (hmin : ∀ u, projectionDual (m := m) theta a b vstar ≤ projectionDual (m := m) theta a b u) :
    projectionSlack a b (weightedMarginal (m := m) (theta + vstar)) vstar = 0 := by
  apply Finset.sum_eq_zero
  intro i _
  have h := projectionDual_minimum_conditions theta a b vstar hmd hab hmin i
  rw [h.2.2.1, h.2.2.2, add_zero]

theorem weightedLaw_KL_logPartition (psi xi : Fin d → ℝ) (hmd : m ≤ d) :
    finiteKL (weightedLaw (m := m) psi) (weightedLaw xi) =
      logPartition (m := m) xi - logPartition (m := m) psi -
        weightedMarginal (m := m) psi ⬝ᵥ (xi - psi) := by
  have h := finiteKL_weightedLaw_shift (weightedLaw (m := m) psi)
    (sum_weightedLaw psi hmd) psi (xi - psi) hmd
  rw [show psi + (xi - psi) = xi by abel, finiteKL_self] at h
  change _ = _ - _ - marginal (weightedLaw (m := m) psi) ⬝ᵥ (xi - psi)
  linarith

/-- Exact dual gap decomposition, including both nonnegative constraint terms. -/
theorem projectionDual_gap_identity (theta a b vstar v : Fin d → ℝ) (hmd : m ≤ d)
    (hab : ∀ i, a i ≤ b i)
    (hmin : ∀ u, projectionDual (m := m) theta a b vstar ≤ projectionDual (m := m) theta a b u) :
    projectionDual (m := m) theta a b v - projectionDual (m := m) theta a b vstar =
      finiteKL (weightedLaw (m := m) (theta + vstar)) (weightedLaw (theta + v)) +
        projectionSlack a b (weightedMarginal (m := m) (theta + vstar)) v := by
  have hs := projectionSlack_at_minimum theta a b vstar hmd hab hmin
  rw [projectionSlack_identity] at hs
  rw [weightedLaw_KL_logPartition _ _ hmd, projectionSlack_identity]
  rw [show (theta + v) - (theta + vstar) = v - vstar by abel]
  have hd : weightedMarginal (m := m) (theta + vstar) ⬝ᵥ (v - vstar) =
      weightedMarginal (m := m) (theta + vstar) ⬝ᵥ v -
        weightedMarginal (m := m) (theta + vstar) ⬝ᵥ vstar := by
    simp only [dotProduct, Pi.sub_apply, mul_sub, Finset.sum_sub_distrib]
  rw [hd]
  unfold projectionDual
  linarith

theorem projectionDual_gap_controls_KL_and_slack (theta a b vstar v : Fin d → ℝ)
    (hmd : m ≤ d) (hab : ∀ i, a i ≤ b i)
    (hmin : ∀ u, projectionDual (m := m) theta a b vstar ≤ projectionDual (m := m) theta a b u)
    (tau : ℝ) (hgap : projectionDual (m := m) theta a b v -
      projectionDual (m := m) theta a b vstar ≤ tau) :
    finiteKL (weightedLaw (m := m) (theta + vstar)) (weightedLaw (theta + v)) ≤ tau ∧
      projectionSlack a b (weightedMarginal (m := m) (theta + vstar)) v ≤ tau := by
  rw [projectionDual_gap_identity theta a b vstar v hmd hab hmin] at hgap
  have hmu : ∀ i, a i ≤ weightedMarginal (m := m) (theta + vstar) i ∧
      weightedMarginal (m := m) (theta + vstar) i ≤ b i :=
    (projectionDual_minimum_is_KL_projection theta a b vstar hmd hab hmin).1
  have hs := projectionSlack_nonneg a b _ v hmu
  have hKL := finiteKL_nonneg (weightedLaw (m := m) (theta + vstar))
    (weightedLaw (theta + v)) (fun x => (weightedLaw_pos (theta + vstar) hmd x).le)
    (sum_weightedLaw (theta + vstar) hmd) (weightedLaw_pos (theta + v) hmd)
    (sum_weightedLaw (theta + v) hmd)
  exact ⟨by linarith, by linarith⟩

end MsetsPaper.Upper
