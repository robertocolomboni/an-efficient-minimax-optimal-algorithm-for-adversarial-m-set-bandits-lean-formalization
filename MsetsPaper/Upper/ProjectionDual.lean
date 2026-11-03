import MsetsPaper.Upper.Estimator
import MsetsPaper.Upper.FiniteKL
import Mathlib.Analysis.Convex.Function

/-!
# The concrete KL projection dual: exact finite-dimensional identities

The Lagrangian identity and minimization over probability laws are proved for
the actual exponential family. They do not assert existence of optimal dual
multipliers: that is a separate result, not a certificate supplied as a premise.
-/

noncomputable section
open scoped BigOperators
open Matrix MsetsLower MsetsLower.History

namespace MsetsPaper.Upper

variable {d m : ℕ}

def logPartition (theta : Fin d → ℝ) : ℝ := Real.log (partition (m := m) theta)

def projectionPenalty (a b v : Fin d → ℝ) : ℝ :=
  ∑ i, (-a i * max (v i) 0 + b i * max (-v i) 0)

def projectionDual (theta a b v : Fin d → ℝ) : ℝ :=
  logPartition (m := m) (theta + v) + projectionPenalty a b v

def projectionLagrangian (theta a b alpha beta : Fin d → ℝ) (q : Action d m → ℝ) : ℝ :=
  finiteKL q (weightedLaw theta) +
    ∑ i, (alpha i * (a i - marginal q i) + beta i * (marginal q i - b i))

def projectionMultiplierDual (theta a b alpha beta : Fin d → ℝ) : ℝ :=
  logPartition (m := m) theta - logPartition (m := m) (theta + (alpha - beta)) +
    ∑ i, (a i * alpha i - b i * beta i)

theorem log_weightedLaw (theta : Fin d → ℝ) (hmd : m ≤ d) (x : Action d m) :
    Real.log (weightedLaw theta x) = actionLoss x theta - logPartition (m := m) theta := by
  rw [weightedLaw, Real.log_div (Real.exp_pos _).ne' (partition_pos theta hmd).ne',
    Real.log_exp]
  rfl

theorem mean_actionLoss (q : Action d m → ℝ) (v : Fin d → ℝ) :
    finiteExpectation q (fun x => actionLoss x v) = marginal q ⬝ᵥ v := by
  unfold finiteExpectation
  simp_rw [← dot_indicator_eq_actionLoss, dotProduct_comm v]
  exact mean_indicator_dot q v

/-- The logarithmic change of reference law, with zero comparator masses allowed. -/
theorem finiteKL_weightedLaw_shift (q : Action d m → ℝ) (hqsum : ∑ x, q x = 1)
    (theta v : Fin d → ℝ) (hmd : m ≤ d) :
    finiteKL q (weightedLaw (theta + v)) = finiteKL q (weightedLaw theta) -
      marginal q ⬝ᵥ v + logPartition (m := m) (theta + v) - logPartition (m := m) theta := by
  rw [finiteKL_eq_sum_mul_log_sub_log q _ (weightedLaw_pos (theta + v) hmd),
    finiteKL_eq_sum_mul_log_sub_log q _ (weightedLaw_pos theta hmd)]
  have hadd (x : Action d m) : actionLoss x (theta + v) =
      actionLoss x theta + actionLoss x v := actionLoss_add x theta v
  simp_rw [log_weightedLaw (theta + v) hmd, log_weightedLaw theta hmd, hadd]
  calc
    (∑ x, q x * (Real.log (q x) -
        (actionLoss x theta + actionLoss x v - logPartition (m := m) (theta + v)))) =
      (∑ x, q x * (Real.log (q x) -
          (actionLoss x theta - logPartition (m := m) theta))) -
      (∑ x, q x * actionLoss x v) +
      (∑ x, q x * logPartition (m := m) (theta + v)) -
      (∑ x, q x * logPartition (m := m) theta) := by
        simp only [← Finset.sum_sub_distrib, ← Finset.sum_add_distrib]
        apply Finset.sum_congr rfl
        intro x _
        ring
    _ = _ := by
      rw [← Finset.sum_mul, ← Finset.sum_mul, hqsum, one_mul, one_mul]
      rw [show (∑ x, q x * actionLoss x v) = marginal q ⬝ᵥ v from mean_actionLoss q v]

/-- Every displayed Lagrangian rewrite in the paper reduces to this exact identity. -/
theorem projectionLagrangian_identity (q : Action d m → ℝ) (hqsum : ∑ x, q x = 1)
    (theta a b alpha beta : Fin d → ℝ) (hmd : m ≤ d) :
    projectionLagrangian theta a b alpha beta q =
      finiteKL q (weightedLaw (theta + (alpha - beta))) +
        projectionMultiplierDual (m := m) theta a b alpha beta := by
  rw [projectionLagrangian, projectionMultiplierDual,
    finiteKL_weightedLaw_shift q hqsum theta (alpha - beta) hmd]
  have heq : (∑ i, (alpha i * (a i - marginal q i) + beta i * (marginal q i - b i))) =
      -(marginal q ⬝ᵥ (alpha - beta)) + ∑ i, (a i * alpha i - b i * beta i) := by
    simp only [dotProduct, Pi.sub_apply, ← Finset.sum_neg_distrib, ← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro i _
    ring
  rw [heq]
  ring

theorem projectionMultiplierDual_le_lagrangian (q : Action d m → ℝ)
    (hq : ∀ x, 0 ≤ q x) (hqsum : ∑ x, q x = 1)
    (theta a b alpha beta : Fin d → ℝ) (hmd : m ≤ d) :
    projectionMultiplierDual (m := m) theta a b alpha beta ≤
      projectionLagrangian theta a b alpha beta q := by
  rw [projectionLagrangian_identity q hqsum _ _ _ _ _ hmd]
  exact le_add_of_nonneg_left (finiteKL_nonneg q _ hq hqsum
    (weightedLaw_pos _ hmd) (sum_weightedLaw _ hmd))

theorem finiteKL_self (p : Action d m → ℝ) : finiteKL p p = 0 := by
  unfold finiteKL
  apply Finset.sum_eq_zero
  intro x _
  by_cases hx : p x = 0 <;> simp [hx]

/-- The minimum for fixed multipliers is actually attained by p_(theta+alpha-beta). -/
theorem projectionLagrangian_at_weightedLaw (theta a b alpha beta : Fin d → ℝ)
    (hmd : m ≤ d) :
    projectionLagrangian theta a b alpha beta
        (weightedLaw (m := m) (theta + (alpha - beta))) =
      projectionMultiplierDual (m := m) theta a b alpha beta := by
  rw [projectionLagrangian_identity _ (sum_weightedLaw _ hmd) _ _ _ _ _ hmd,
    finiteKL_self, zero_add]

/-- This is minimization over p for FIXED multipliers, not existence of optimal
dual multipliers or a primal projection. -/
theorem projectionLagrangian_minimized (theta a b alpha beta : Fin d → ℝ)
    (hmd : m ≤ d) (q : Action d m → ℝ) (hq : ∀ x, 0 ≤ q x) (hqsum : ∑ x, q x = 1) :
    projectionLagrangian theta a b alpha beta
        (weightedLaw (m := m) (theta + (alpha - beta))) ≤
      projectionLagrangian theta a b alpha beta q := by
  rw [projectionLagrangian_at_weightedLaw _ _ _ _ _ hmd]
  exact projectionMultiplierDual_le_lagrangian q hq hqsum _ _ _ _ _ hmd

theorem positivePart_sub_negativePart (x : ℝ) : max x 0 - max (-x) 0 = x := by
  by_cases hx : 0 ≤ x
  · rw [max_eq_left hx, max_eq_right (by linarith)]
    ring
  · rw [max_eq_right (by linarith), max_eq_left (by linarith)]
    ring

theorem remove_common_multiplier (alpha beta : ℝ) (ha : 0 ≤ alpha) (hb : 0 ≤ beta) :
    alpha - min alpha beta = max (alpha - beta) 0 ∧
      beta - min alpha beta = max (beta - alpha) 0 := by
  by_cases h : alpha ≤ beta
  · rw [min_eq_left h, max_eq_right (by linarith), max_eq_left (by linarith)]
    exact ⟨by ring, rfl⟩
  · rw [min_eq_right (by linarith), max_eq_left (by linarith),
      max_eq_right (by linarith)]
    exact ⟨rfl, by ring⟩

/-- Exact improvement obtained by removing overlapping nonnegative multipliers. -/
theorem projectionMultiplierDual_remove_common (theta a b alpha beta : Fin d → ℝ)
    (halpha : ∀ i, 0 ≤ alpha i) (hbeta : ∀ i, 0 ≤ beta i) :
    projectionMultiplierDual (m := m) theta a b
        (fun i => max (alpha i - beta i) 0) (fun i => max (beta i - alpha i) 0) =
      projectionMultiplierDual (m := m) theta a b alpha beta +
        ∑ i, (b i - a i) * min (alpha i) (beta i) := by
  have hv : (fun i => max (alpha i - beta i) 0) -
      (fun i => max (beta i - alpha i) 0) = alpha - beta := by
    ext i
    simpa only [Pi.sub_apply, neg_sub] using positivePart_sub_negativePart (alpha i - beta i)
  simp only [projectionMultiplierDual, hv]
  have hs : (∑ i, (a i * max (alpha i - beta i) 0 - b i * max (beta i - alpha i) 0)) =
      (∑ i, (a i * alpha i - b i * beta i)) +
        ∑ i, (b i - a i) * min (alpha i) (beta i) := by
    rw [← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro i _
    rw [← (remove_common_multiplier _ _ (halpha i) (hbeta i)).1,
      ← (remove_common_multiplier _ _ (halpha i) (hbeta i)).2]
    ring
  rw [hs]
  ring

theorem projectionMultiplierDual_le_positiveParts (theta a b alpha beta : Fin d → ℝ)
    (hab : ∀ i, a i ≤ b i) (halpha : ∀ i, 0 ≤ alpha i) (hbeta : ∀ i, 0 ≤ beta i) :
    projectionMultiplierDual (m := m) theta a b alpha beta ≤
      projectionMultiplierDual (m := m) theta a b
        (fun i => max (alpha i - beta i) 0) (fun i => max (beta i - alpha i) 0) := by
  rw [projectionMultiplierDual_remove_common _ _ _ _ _ halpha hbeta]
  exact le_add_of_nonneg_right (Finset.sum_nonneg fun i _ =>
    mul_nonneg (sub_nonneg.mpr (hab i)) (le_min (halpha i) (hbeta i)))

theorem projectionMultiplierDual_positiveParts (theta a b v : Fin d → ℝ) :
    projectionMultiplierDual (m := m) theta a b
      (fun i => max (v i) 0) (fun i => max (-v i) 0) =
      logPartition (m := m) theta - projectionDual (m := m) theta a b v := by
  have hv : (fun i => max (v i) 0) - (fun i => max (-v i) 0) = v := by
    ext i
    exact positivePart_sub_negativePart (v i)
  simp only [projectionMultiplierDual, hv, projectionDual, projectionPenalty]
  have hs : (∑ i, (a i * max (v i) 0 - b i * max (-v i) 0)) =
      -(∑ i, (-a i * max (v i) 0 + b i * max (-v i) 0)) := by
    rw [← Finset.sum_neg_distrib]
    apply Finset.sum_congr rfl
    intro i _
    ring
  rw [hs]
  ring

/-- Supporting-hyperplane inequality for F, obtained from KL nonnegativity. -/
theorem logPartition_support (theta psi : Fin d → ℝ) (hmd : m ≤ d) :
    logPartition (m := m) theta + weightedMarginal (m := m) theta ⬝ᵥ (psi - theta) ≤
      logPartition (m := m) psi := by
  have h := finiteKL_weightedLaw_shift (weightedLaw (m := m) theta)
    (sum_weightedLaw theta hmd) theta (psi - theta) hmd
  have heq : theta + (psi - theta) = psi := by abel
  rw [heq, finiteKL_self] at h
  have hnonneg := finiteKL_nonneg (weightedLaw (m := m) theta) (weightedLaw (m := m) psi)
    (fun x => (weightedLaw_pos theta hmd x).le) (sum_weightedLaw theta hmd)
    (weightedLaw_pos psi hmd) (sum_weightedLaw psi hmd)
  change logPartition (m := m) theta + marginal (weightedLaw theta) ⬝ᵥ (psi - theta) ≤ _
  linarith

/-- Convexity is proved, rather than supplied as a property of the partition. -/
theorem logPartition_convex (hmd : m ≤ d) :
    ConvexOn ℝ Set.univ (logPartition (d := d) (m := m)) := by
  refine ⟨convex_univ, ?_⟩
  intro x _ y _ a b ha hb hab
  let z := a • x + b • y
  have hx := mul_le_mul_of_nonneg_left (logPartition_support (m := m) z x hmd) ha
  have hy := mul_le_mul_of_nonneg_left (logPartition_support (m := m) z y hmd) hb
  have hs : a * (weightedMarginal (m := m) z ⬝ᵥ (x - z)) +
      b * (weightedMarginal (m := m) z ⬝ᵥ (y - z)) = 0 := by
    simp only [dotProduct, Pi.sub_apply, Finset.mul_sum, ← Finset.sum_add_distrib]
    apply Finset.sum_eq_zero
    intro i _
    have hb' : b = 1 - a := by linarith
    dsimp [z]
    rw [hb']
    ring
  change logPartition (m := m) z ≤ a * logPartition (m := m) x + b * logPartition (m := m) y
  have hF : a * logPartition (m := m) z + b * logPartition (m := m) z =
      logPartition (m := m) z := by rw [← add_mul, hab, one_mul]
  nlinarith only [hx, hy, hs, hF]

end MsetsPaper.Upper
