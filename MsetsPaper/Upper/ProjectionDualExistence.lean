import MsetsPaper.Upper.ProjectionDualSubgradient
import MsetsPaper.Upper.ESPMoments
import MsetsPaper.Upper.ProjectionSlater
import Mathlib.Topology.Order.Compact
import Mathlib.Analysis.Normed.Group.Bounded

/-!
# Existence of a projection-dual minimizer

The manuscript-facing existence theorem uses general convex Slater duality,
with the concrete simplex, KL and strict-feasibility hypotheses verified.
The earlier direct coercivity proof is retained as a separate true result.
-/

noncomputable section
open scoped BigOperators
open Matrix

namespace MsetsPaper.Upper

variable {d m : ℕ}

theorem weightedMarginal_zero_eq (hmpos : 1 ≤ m) (hmtop : m ≤ d - 1) (i : Fin d) :
    weightedMarginal (m := m) (0 : Fin d → ℝ) i = (m : ℝ) / d := by
  exact projection_slater_uniform_marginal hmpos hmtop i

theorem continuous_logPartition (hmd : m ≤ d) :
    Continuous (logPartition (d := d) (m := m)) := by
  apply Continuous.log _ (fun theta => (partition_pos theta hmd).ne')
  unfold partition
  simp_rw [MsetsLower.actionLoss_eq_finset_sum]
  fun_prop

theorem continuous_projectionDual (theta a b : Fin d → ℝ) (hmd : m ≤ d) :
    Continuous (projectionDual (m := m) theta a b) := by
  apply Continuous.add
  · exact (continuous_logPartition hmd).comp (continuous_const.add continuous_id)
  · unfold projectionPenalty
    fun_prop

/-- The strict feasible uniform mean supplies a linear lower bound in every
coordinate direction. This is the ingredient making the sublevel set bounded. -/
theorem scalarProjectionPenalty_coercive (a b r eps x : ℝ)
    (hlo : eps ≤ r - a) (hhi : eps ≤ b - r) :
    eps * |x| ≤ r * x + scalarProjectionPenalty a b x := by
  by_cases hx : 0 ≤ x
  · rw [abs_of_nonneg hx, scalarProjectionPenalty_pos _ _ _ hx]
    nlinarith [mul_le_mul_of_nonneg_right hlo hx]
  · have hx' : x ≤ 0 := by linarith
    rw [abs_of_nonpos hx', scalarProjectionPenalty_neg _ _ _ hx']
    nlinarith [mul_le_mul_of_nonneg_right hhi (neg_nonneg.mpr hx')]

theorem projectionDual_coercive (theta a b : Fin d → ℝ)
    (hmpos : 1 ≤ m) (hmtop : m ≤ d - 1) (eps : ℝ)
    (hlo : ∀ i, eps ≤ (m : ℝ) / d - a i)
    (hhi : ∀ i, eps ≤ b i - (m : ℝ) / d) (v : Fin d → ℝ) :
    logPartition (m := m) (0 : Fin d → ℝ) + ((m : ℝ) / d) * (∑ i, theta i) +
      eps * (∑ i, |v i|) ≤ projectionDual (m := m) theta a b v := by
  have hF := logPartition_support (m := m) (0 : Fin d → ℝ) (theta + v) (by omega)
  simp only [sub_zero, dotProduct, weightedMarginal_zero_eq hmpos hmtop,
    Pi.add_apply, mul_add, Finset.sum_add_distrib, ← Finset.mul_sum] at hF
  have hc := Finset.sum_le_sum fun i (_ : i ∈ (Finset.univ : Finset (Fin d))) =>
    scalarProjectionPenalty_coercive (a i) (b i) ((m : ℝ) / d) eps (v i) (hlo i) (hhi i)
  simp only [Finset.sum_add_distrib, ← Finset.mul_sum] at hc
  change eps * (∑ i, |v i|) ≤ ((m : ℝ) / d) * (∑ i, v i) + projectionPenalty a b v at hc
  unfold projectionDual
  linarith

/-- Actual existence, using positive uniform slack and compact sublevels. No
minimizer, dual optimizer or coercivity conclusion is supplied as a premise. -/
theorem projectionDual_exists_of_uniform_slack (theta a b : Fin d → ℝ)
    (hmpos : 1 ≤ m) (hmtop : m ≤ d - 1) (eps : ℝ) (heps : 0 < eps)
    (hlo : ∀ i, eps ≤ (m : ℝ) / d - a i)
    (hhi : ∀ i, eps ≤ b i - (m : ℝ) / d) :
    ∃ v, ∀ u, projectionDual (m := m) theta a b v ≤ projectionDual (m := m) theta a b u := by
  apply (continuous_projectionDual theta a b (show m ≤ d by omega)).exists_forall_le_of_isBounded 0
  rw [isBounded_iff_forall_norm_le]
  let C := logPartition (m := m) (0 : Fin d → ℝ) + ((m : ℝ) / d) * (∑ i, theta i)
  let R := (projectionDual (m := m) theta a b 0 - C) / eps
  refine ⟨max R 0, ?_⟩
  intro v hv
  have hc := projectionDual_coercive theta a b hmpos hmtop eps hlo hhi v
  have hs : (∑ i, |v i|) ≤ R := by
    apply (le_div_iff₀ heps).mpr
    dsimp [C] at *
    change projectionDual (m := m) theta a b v ≤ projectionDual (m := m) theta a b 0 at hv
    nlinarith
  apply (pi_norm_le_iff_of_nonneg (le_max_right R 0)).mpr
  intro i
  have hi : |v i| ≤ ∑ j, |v j| :=
    Finset.single_le_sum (fun j _ => abs_nonneg (v j)) (Finset.mem_univ i)
  exact hi.trans (hs.trans (le_max_left R 0))

def projectionLower (d m : ℕ) (lam : ℝ) : Fin d → ℝ := fun _ => lam * ((m : ℝ) / d)
def projectionUpper (d m : ℕ) (lam : ℝ) : Fin d → ℝ := fun _ => 1 - lam * (1 - (m : ℝ) / d)

/-- The paper's numerical box constraints really satisfy strict uniform slack. -/
theorem projection_uniform_slack (hmpos : 1 ≤ m) (hmtop : m ≤ d - 1)
    (lam : ℝ) (hlam : 0 < lam) (hlamhalf : lam ≤ 1 / 2) :
    ∃ eps > 0, (∀ i, eps ≤ (m : ℝ) / d - projectionLower d m lam i) ∧
      (∀ i, eps ≤ projectionUpper d m lam i - (m : ℝ) / d) := by
  have hd : (0 : ℝ) < d := by exact_mod_cast (show 0 < d by omega)
  have hm : (0 : ℝ) < m := by exact_mod_cast (show 0 < m by omega)
  have hmd : (m : ℝ) < d := by exact_mod_cast (show m < d by omega)
  have hr : 0 < (m : ℝ) / d := div_pos hm hd
  have hr1 : (m : ℝ) / d < 1 := (div_lt_one hd).mpr hmd
  refine ⟨(1 - lam) * min ((m : ℝ) / d) (1 - (m : ℝ) / d), ?_, ?_, ?_⟩
  · exact mul_pos (by linarith) (lt_min hr (by linarith))
  · intro i
    have h := mul_le_mul_of_nonneg_left
      (min_le_left ((m : ℝ) / d) (1 - (m : ℝ) / d)) (show 0 ≤ 1 - lam by linarith)
    dsimp [projectionLower]
    nlinarith
  · intro i
    have h := mul_le_mul_of_nonneg_left
      (min_le_right ((m : ℝ) / d) (1 - (m : ℝ) / d)) (show 0 ≤ 1 - lam by linarith)
    dsimp [projectionUpper]
    nlinarith

/-- Existence for the exact lambda-dependent objective in Lemma L7. -/
theorem projectionDual_exists (theta : Fin d → ℝ) (hmpos : 1 ≤ m) (hmtop : m ≤ d - 1)
    (lam : ℝ) (hlam : 0 < lam) (hlamhalf : lam ≤ 1 / 2) :
    ∃ v, ∀ u,
      projectionDual (m := m) theta (projectionLower d m lam) (projectionUpper d m lam) v ≤
      projectionDual (m := m) theta (projectionLower d m lam) (projectionUpper d m lam) u := by
  obtain ⟨eps, heps, hlo, hhi⟩ := projection_uniform_slack hmpos hmtop lam hlam hlamhalf
  apply projectionDual_exists_of_strict_uniform theta _ _ hmpos hmtop
  · intro i
    linarith [hlo i]
  · intro i
    linarith [hhi i]

end MsetsPaper.Upper
