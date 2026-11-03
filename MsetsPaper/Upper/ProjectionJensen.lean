import MsetsPaper.Upper.ProjectionApproximation
import Mathlib.Analysis.Convex.SpecificFunctions.Basic
import Mathlib.Analysis.Convex.Jensen

/-! # The uniform change-of-measure/Jensen calculation displayed in L8 -/

noncomputable section
open scoped BigOperators
open Matrix

namespace MsetsPaper.Upper

variable {d m : ℕ}

theorem partition_shift_ratio (theta v : Fin d → ℝ) :
    partition (m := m) (theta + v) / partition (m := m) theta =
      finiteExpectation (weightedLaw (m := m) theta) (fun x => Real.exp (MsetsLower.actionLoss x v)) := by
  have hadd (x : Action d m) : MsetsLower.actionLoss x (theta + v) =
      MsetsLower.actionLoss x theta + MsetsLower.actionLoss x v := by
    simpa using actionLoss_add_smul x theta v 1
  unfold finiteExpectation weightedLaw
  rw [partition, Finset.sum_div]
  apply Finset.sum_congr rfl
  intro x _
  rw [hadd, Real.exp_add]
  ring

theorem uniform_change_of_measure (theta v : Fin d → ℝ) (hmd : m ≤ d) :
    finiteExpectation (weightedLaw (m := m) (0 : Fin d → ℝ))
      (fun x => (weightedLaw theta x / weightedLaw (m := m) (0 : Fin d → ℝ) x) *
        Real.exp (MsetsLower.actionLoss x v)) =
    finiteExpectation (weightedLaw (m := m) theta)
      (fun x => Real.exp (MsetsLower.actionLoss x v)) := by
  apply Finset.sum_congr rfl
  intro x _
  have hu := (weightedLaw_pos (m := m) (0 : Fin d → ℝ) hmd x).ne'
  field_simp

theorem logPartition_shift_log_expectation (theta v : Fin d → ℝ) (hmd : m ≤ d) :
    logPartition (m := m) (theta + v) - logPartition (m := m) theta =
      Real.log (finiteExpectation (weightedLaw (m := m) theta)
        (fun x => Real.exp (MsetsLower.actionLoss x v))) := by
  rw [← partition_shift_ratio, Real.log_div (partition_pos (theta + v) hmd).ne'
    (partition_pos theta hmd).ne']
  rfl

/-- This uses literal concave Jensen on the change-of-measure terms from the
paper, not a supplied Jensen conclusion or a separate optimization oracle. -/
theorem uniform_Jensen_logPartition (theta v : Fin d → ℝ)
    (hmpos : 1 ≤ m) (hmtop : m ≤ d - 1) :
    -finiteKL (weightedLaw (m := m) (0 : Fin d → ℝ)) (weightedLaw theta) +
        ((m : ℝ) / d) * (∑ i, v i) ≤
      logPartition (m := m) (theta + v) - logPartition (m := m) theta := by
  have hmd : m ≤ d := by omega
  let U := weightedLaw (m := m) (0 : Fin d → ℝ)
  let Z : Action d m → ℝ := fun x => (weightedLaw theta x / U x) *
    Real.exp (MsetsLower.actionLoss x v)
  have hU : ∀ x, 0 < U x := weightedLaw_pos _ hmd
  have hp := weightedLaw_pos (m := m) theta hmd
  have hZ : ∀ x, Z x ∈ Set.Ioi (0 : ℝ) := fun x =>
    mul_pos (div_pos (hp x) (hU x)) (Real.exp_pos _)
  have hJ := strictConcaveOn_log_Ioi.concaveOn.le_map_sum
    (t := Finset.univ) (w := U) (p := Z) (fun x _ => (hU x).le)
    (sum_weightedLaw (m := m) (0 : Fin d → ℝ) hmd) (fun x _ => hZ x)
  simp only [smul_eq_mul] at hJ
  have hlog (x : Action d m) : Real.log (Z x) =
      -Real.log (U x / weightedLaw theta x) + MsetsLower.actionLoss x v := by
    dsimp [Z]
    rw [Real.log_mul (div_pos (hp x) (hU x)).ne' (Real.exp_pos _).ne', Real.log_exp,
      Real.log_div (hp x).ne' (hU x).ne', Real.log_div (hU x).ne' (hp x).ne']
    ring
  simp_rw [hlog, mul_add, mul_neg] at hJ
  simp only [Finset.sum_add_distrib, Finset.sum_neg_distrib] at hJ
  have hmean : (∑ x : Action d m, U x * MsetsLower.actionLoss x v) =
      ((m : ℝ) / d) * (∑ i, v i) := by
    rw [show (∑ x : Action d m, U x * MsetsLower.actionLoss x v) =
      marginal U ⬝ᵥ v from mean_actionLoss U v]
    change weightedMarginal (m := m) (0 : Fin d → ℝ) ⬝ᵥ v = _
    simp only [dotProduct, weightedMarginal_zero_eq hmpos hmtop, Finset.mul_sum]
  rw [hmean] at hJ
  change -finiteKL U (weightedLaw theta) + _ ≤ Real.log (finiteExpectation U Z) at hJ
  have hchange := uniform_change_of_measure theta v hmd
  change finiteExpectation U Z = _ at hchange
  rw [hchange, ← logPartition_shift_log_expectation theta v hmd] at hJ
  exact hJ

theorem projection_uniform_penalty_identity (d m : ℕ) (lam : ℝ) (v : Fin d → ℝ) :
    ((m : ℝ) / d) * (∑ i, v i) +
      projectionPenalty (projectionLower d m lam) (projectionUpper d m lam) v =
      (1 - lam) * (((m : ℝ) / d) * (∑ i, max (v i) 0) +
        (1 - (m : ℝ) / d) * (∑ i, max (-v i) 0)) := by
  unfold projectionPenalty
  rw [Finset.mul_sum, ← Finset.sum_add_distrib]
  have hterm (i : Fin d) : ((m : ℝ) / d) * v i +
      (-projectionLower d m lam i * max (v i) 0 + projectionUpper d m lam i * max (-v i) 0) =
      (1 - lam) * (((m : ℝ) / d) * max (v i) 0 + (1 - (m : ℝ) / d) * max (-v i) 0) := by
    dsimp [projectionLower, projectionUpper]
    have h := positivePart_sub_negativePart (v i)
    linear_combination -((m : ℝ) / d) * h
  change (∑ i, (((m : ℝ) / d) * v i +
    (-projectionLower d m lam i * max (v i) 0 + projectionUpper d m lam i * max (-v i) 0))) = _
  simp_rw [hterm]
  simp only [mul_add, Finset.mul_sum, Finset.sum_add_distrib]

theorem projectionDual_lower_bound_sharp (theta v : Fin d → ℝ)
    (hmpos : 1 ≤ m) (hmtop : m ≤ d - 1) (lam : ℝ) :
    logPartition (m := m) theta -
      finiteKL (weightedLaw (m := m) (0 : Fin d → ℝ)) (weightedLaw theta) +
      (1 - lam) * (((m : ℝ) / d) * (∑ i, max (v i) 0) +
        (1 - (m : ℝ) / d) * (∑ i, max (-v i) 0)) ≤
      projectionDual (m := m) theta (projectionLower d m lam) (projectionUpper d m lam) v := by
  have h := uniform_Jensen_logPartition theta v hmpos hmtop
  rw [← projection_uniform_penalty_identity d m lam v]
  unfold projectionDual
  linarith

/-- A general uniform-slack consequence of the change-of-measure/Jensen
calculation. The production radius below uses the sharper signed-part bound. -/
theorem projectionDual_lower_bound_uniform_KL_via_Jensen (theta a b v : Fin d → ℝ)
    (hmpos : 1 ≤ m) (hmtop : m ≤ d - 1) (eps : ℝ)
    (hlo : ∀ i, eps ≤ (m : ℝ) / d - a i)
    (hhi : ∀ i, eps ≤ b i - (m : ℝ) / d) :
    logPartition (m := m) theta -
        finiteKL (weightedLaw (m := m) (0 : Fin d → ℝ)) (weightedLaw theta) +
      eps * coordinateL1 v ≤ projectionDual (m := m) theta a b v := by
  have hJ := uniform_Jensen_logPartition theta v hmpos hmtop
  have hc := Finset.sum_le_sum fun i (_ : i ∈ (Finset.univ : Finset (Fin d))) =>
    scalarProjectionPenalty_coercive (a i) (b i) ((m : ℝ) / d) eps (v i)
      (hlo i) (hhi i)
  simp only [Finset.sum_add_distrib, ← Finset.mul_sum] at hc
  change eps * coordinateL1 v ≤
    ((m : ℝ) / d) * (∑ i, v i) + projectionPenalty a b v at hc
  unfold projectionDual
  linarith

theorem projectionDual_minimum_radius_sharp (theta v : Fin d → ℝ)
    (hmpos : 1 ≤ m) (hmtop : m ≤ d - 1) (lam T : ℝ) (hlamhalf : lam ≤ 1 / 2)
    (hKL : finiteKL (weightedLaw (m := m) (0 : Fin d → ℝ)) (weightedLaw theta) ≤ T)
    (hmin : ∀ u, projectionDual (m := m) theta (projectionLower d m lam)
      (projectionUpper d m lam) v ≤ projectionDual (m := m) theta
        (projectionLower d m lam) (projectionUpper d m lam) u) :
    coordinateL1 v ≤ T / ((1 - lam) * min ((m : ℝ) / d) (1 - (m : ℝ) / d)) := by
  have hd : (0 : ℝ) < d := by exact_mod_cast (show 0 < d by omega)
  have hm : (0 : ℝ) < m := by exact_mod_cast (show 0 < m by omega)
  have hmd : (m : ℝ) < d := by exact_mod_cast (show m < d by omega)
  have hr : 0 < (m : ℝ) / d := div_pos hm hd
  have hr1 : (m : ℝ) / d < 1 := (div_lt_one hd).mpr hmd
  let eps := (1 - lam) * min ((m : ℝ) / d) (1 - (m : ℝ) / d)
  have heps : 0 < eps := mul_pos (by linarith) (lt_min hr (by linarith))
  have habs (x : ℝ) : |x| = max x 0 + max (-x) 0 := by
    by_cases hx : 0 ≤ x
    · rw [abs_of_nonneg hx, max_eq_left hx, max_eq_right (by linarith)]
      ring
    · have hx' : x ≤ 0 := le_of_not_ge hx
      rw [abs_of_nonpos hx', max_eq_right hx', max_eq_left (by linarith)]
      ring
  have hsplit : coordinateL1 v = (∑ i, max (v i) 0) + (∑ i, max (-v i) 0) := by
    simp only [coordinateL1, habs, Finset.sum_add_distrib]
  have hpos : 0 ≤ ∑ i, max (v i) 0 := Finset.sum_nonneg fun _ _ => le_max_right _ _
  have hneg : 0 ≤ ∑ i, max (-v i) 0 := Finset.sum_nonneg fun _ _ => le_max_right _ _
  have hweighted : min ((m : ℝ) / d) (1 - (m : ℝ) / d) * coordinateL1 v ≤
      ((m : ℝ) / d) * (∑ i, max (v i) 0) +
        (1 - (m : ℝ) / d) * (∑ i, max (-v i) 0) := by
    rw [hsplit, mul_add]
    exact add_le_add (mul_le_mul_of_nonneg_right (min_le_left _ _) hpos)
      (mul_le_mul_of_nonneg_right (min_le_right _ _) hneg)
  have hscaled := mul_le_mul_of_nonneg_left hweighted (show 0 ≤ 1 - lam by linarith)
  have h := projectionDual_lower_bound_sharp theta v hmpos hmtop lam
  have hzero := hmin 0
  have hG0 : projectionDual (m := m) theta (projectionLower d m lam)
      (projectionUpper d m lam) 0 = logPartition (m := m) theta := by
    simp [projectionDual, projectionPenalty]
  rw [hG0] at hzero
  change coordinateL1 v ≤ T / eps
  apply (le_div_iff₀ heps).mpr
  dsimp only [eps]
  nlinarith

/-- The actual search uses the paper's fractional radius first, then bounds
the fraction by `2*d*T` using `min (m/d) (1-m/d) >= 1/d`. -/
theorem projectionDual_minimum_radius_via_Jensen (theta v : Fin d → ℝ)
    (hmpos : 1 ≤ m) (hmtop : m ≤ d - 1) (lam T : ℝ) (hlamhalf : lam ≤ 1 / 2)
    (hKL : finiteKL (weightedLaw (m := m) (0 : Fin d → ℝ)) (weightedLaw theta) ≤ T)
    (hmin : ∀ u, projectionDual (m := m) theta (projectionLower d m lam)
      (projectionUpper d m lam) v ≤ projectionDual (m := m) theta
        (projectionLower d m lam) (projectionUpper d m lam) u) :
    coordinateL1 v ≤ 2 * d * T := by
  have hd : (0 : ℝ) < d := by exact_mod_cast (show 0 < d by omega)
  have hsharp := projectionDual_minimum_radius_sharp theta v hmpos hmtop
    lam T hlamhalf hKL hmin
  have hrlo : (1 : ℝ) / d ≤ (m : ℝ) / d :=
    (div_le_div_iff_of_pos_right hd).mpr (by exact_mod_cast hmpos)
  have hrhi : (1 : ℝ) / d ≤ 1 - (m : ℝ) / d := by
    apply (div_le_iff₀ hd).mpr
    have hmdiv := div_mul_cancel₀ (m : ℝ) hd.ne'
    have hmd : (m : ℝ) + 1 ≤ d := by exact_mod_cast (show m + 1 ≤ d by omega)
    nlinarith
  let eps := (1 - lam) * min ((m : ℝ) / d) (1 - (m : ℝ) / d)
  have heps : 1 / (2 * (d : ℝ)) ≤ eps := by
    calc
      _ = (1 / 2 : ℝ) * (1 / d) := by ring
      _ ≤ eps := mul_le_mul (by linarith) (le_min hrlo hrhi)
        (by positivity) (by linarith)
  have hepspos : 0 < eps := lt_of_lt_of_le (by positivity) heps
  have hL1 : 0 ≤ coordinateL1 v := Finset.sum_nonneg fun _ _ => abs_nonneg _
  have hproduct : coordinateL1 v * eps ≤ T := (le_div_iff₀ hepspos).mp hsharp
  have hT : 0 ≤ T := (mul_nonneg hL1 hepspos.le).trans hproduct
  have hfraction : T / eps ≤ 2 * d * T := by
    calc
      T / eps ≤ T / (1 / (2 * (d : ℝ))) :=
        div_le_div_of_nonneg_left hT (by positivity) heps
      _ = 2 * d * T := by
        simp only [div_eq_mul_inv, one_mul, inv_inv]
        ring
  exact hsharp.trans hfraction

end MsetsPaper.Upper
