import MsetsPaper.Upper.ProjectionDualExistence
import Mathlib.Analysis.Calculus.LocalExtr.Basic
import Mathlib.Analysis.SpecialFunctions.Log.Deriv

/-!
# Identification of every dual minimizer with the KL projection

The first-order conditions below are derived from an actual global minimum.
They are not supplied as a KKT certificate hypothesis.
-/

noncomputable section
open scoped BigOperators Topology
open Matrix

namespace MsetsPaper.Upper

variable {d m : ℕ}

theorem actionLoss_add_smul (a : Action d m) (theta z : Fin d → ℝ) (t : ℝ) :
    MsetsLower.actionLoss a (theta + t • z) =
      MsetsLower.actionLoss a theta + t * MsetsLower.actionLoss a z := by
  simp only [MsetsLower.actionLoss_eq_finset_sum, Pi.add_apply, Pi.smul_apply,
    smul_eq_mul, Finset.sum_add_distrib, Finset.mul_sum]

theorem hasDerivAt_logPartition_line (theta z : Fin d → ℝ) (hmd : m ≤ d) (t : ℝ) :
    HasDerivAt (fun s : ℝ => logPartition (m := m) (theta + s • z))
      (weightedMarginal (m := m) (theta + t • z) ⬝ᵥ z) t := by
  have hterm (a : Action d m) : HasDerivAt
      (fun s : ℝ => Real.exp (MsetsLower.actionLoss a (theta + s • z)))
      (Real.exp (MsetsLower.actionLoss a (theta + t • z)) * MsetsLower.actionLoss a z) t := by
    simp_rw [actionLoss_add_smul]
    convert (((hasDerivAt_id t).mul_const (MsetsLower.actionLoss a z)).const_add
      (MsetsLower.actionLoss a theta)).exp using 1 <;> simp
  have hp : HasDerivAt (fun s : ℝ => partition (m := m) (theta + s • z))
      (∑ a : Action d m, Real.exp (MsetsLower.actionLoss a (theta + t • z)) * MsetsLower.actionLoss a z) t := by
    have hs := HasDerivAt.sum (u := (Finset.univ : Finset (Action d m))) (fun a _ => hterm a)
    have heq : (∑ a : Action d m, fun s : ℝ => Real.exp (MsetsLower.actionLoss a (theta + s • z))) =
        (fun s : ℝ => partition (m := m) (theta + s • z)) := by
      funext s
      simp [partition]
    rw [heq] at hs
    exact hs
  have hl := hp.log (partition_pos (theta + t • z) hmd).ne'
  convert hl using 1
  · rfl
  · change marginal (weightedLaw (m := m) (theta + t • z)) ⬝ᵥ z = _
    rw [← mean_actionLoss (weightedLaw (m := m) (theta + t • z)) z]
    simp only [finiteExpectation, weightedLaw, Finset.sum_div]
    apply Finset.sum_congr rfl
    intro a _
    ring

/-- A differentiable function minimized on `[-c,infinity)` has a nonnegative
derivative at zero, and the derivative vanishes if the constraint has slack.
The product form includes the boundary case `c = 0`. -/
theorem derivative_of_nonnegative_coordinate_minimum {f : ℝ → ℝ} {f' c : ℝ}
    (hc : 0 ≤ c) (hf : HasDerivAt f f' 0)
    (hmin : ∀ t, -c ≤ t → f 0 ≤ f t) : 0 ≤ f' ∧ c * f' = 0 := by
  have hm : IsMinOn f (Set.Ici (-c)) 0 := fun t ht => hmin t ht
  have hzero : (0 : ℝ) ∈ Set.Ici (-c) := by change -c ≤ 0; linarith
  have hcone1 : (1 : ℝ) ∈ posTangentConeAt (Set.Ici (-c)) 0 := by
    apply mem_posTangentConeAt_of_segment_subset
    exact (convex_Ici (-c)).segment_subset hzero (by change -c ≤ 0 + 1; linarith)
  have hcone2 : -c ∈ posTangentConeAt (Set.Ici (-c)) 0 := by
    apply mem_posTangentConeAt_of_segment_subset
    exact (convex_Ici (-c)).segment_subset hzero (by simp)
  have h1 := hm.localize.hasFDerivWithinAt_nonneg hf.hasDerivWithinAt hcone1
  have h2 := hm.localize.hasFDerivWithinAt_nonneg hf.hasDerivWithinAt hcone2
  change 0 ≤ (1 : ℝ) * f' at h1
  change 0 ≤ -c * f' at h2
  have h1' : 0 ≤ f' := by simpa using h1
  exact ⟨h1', le_antisymm (by nlinarith) (mul_nonneg hc h1')⟩

/-- The negative multiplier dual, up to the constant `F(theta)`. -/
def projectionSmoothObjective (theta a b alpha beta : Fin d → ℝ) : ℝ :=
  logPartition (m := m) (theta + (alpha - beta)) -
    ∑ i, (a i * alpha i - b i * beta i)

theorem projectionSmoothObjective_positiveParts (theta a b v : Fin d → ℝ) :
    projectionSmoothObjective (m := m) theta a b
      (fun i => max (v i) 0) (fun i => max (-v i) 0) =
      projectionDual (m := m) theta a b v := by
  have h := projectionMultiplierDual_positiveParts (m := m) theta a b v
  unfold projectionMultiplierDual at h
  unfold projectionSmoothObjective
  linarith

theorem projectionDual_le_smoothObjective (theta a b alpha beta : Fin d → ℝ)
    (hab : ∀ i, a i ≤ b i) (halpha : ∀ i, 0 ≤ alpha i) (hbeta : ∀ i, 0 ≤ beta i) :
    projectionDual (m := m) theta a b (alpha - beta) ≤
      projectionSmoothObjective (m := m) theta a b alpha beta := by
  have h := projectionMultiplierDual_le_positiveParts (m := m) theta a b alpha beta
    hab halpha hbeta
  have hp := projectionMultiplierDual_positiveParts (m := m) theta a b (alpha - beta)
  simp only [Pi.sub_apply, neg_sub] at hp
  rw [hp] at h
  unfold projectionMultiplierDual at h
  unfold projectionSmoothObjective
  linarith

/-- A minimizer of G really supplies a minimum of the smooth multiplier
objective on the nonnegative orthant. -/
theorem projectionSmoothObjective_minimum (theta a b v : Fin d → ℝ)
    (hab : ∀ i, a i ≤ b i)
    (hmin : ∀ u, projectionDual (m := m) theta a b v ≤ projectionDual (m := m) theta a b u)
    (alpha beta : Fin d → ℝ) (halpha : ∀ i, 0 ≤ alpha i) (hbeta : ∀ i, 0 ≤ beta i) :
    projectionSmoothObjective (m := m) theta a b
      (fun i => max (v i) 0) (fun i => max (-v i) 0) ≤
        projectionSmoothObjective (m := m) theta a b alpha beta := by
  rw [projectionSmoothObjective_positiveParts]
  exact (hmin (alpha - beta)).trans
    (projectionDual_le_smoothObjective theta a b alpha beta hab halpha hbeta)

theorem projectionSmoothObjective_alpha_line (theta a b alpha beta : Fin d → ℝ)
    (i : Fin d) (t : ℝ) :
    projectionSmoothObjective (m := m) theta a b (alpha + t • Pi.single i 1) beta =
      logPartition (m := m) ((theta + (alpha - beta)) + t • Pi.single i 1) -
        (∑ j, (a j * alpha j - b j * beta j)) - t * a i := by
  have hv : theta + (alpha + t • Pi.single i 1 - beta) =
      (theta + (alpha - beta)) + t • Pi.single i 1 := by abel
  unfold projectionSmoothObjective
  rw [hv]
  have hs : (∑ j, (a j * (alpha + t • Pi.single i (1 : ℝ) : Fin d → ℝ) j - b j * beta j)) =
      (∑ j, (a j * alpha j - b j * beta j)) + t * a i := by
    simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, mul_add]
    simp_rw [show ∀ j, a j * alpha j + a j * (t * (Pi.single i (1 : ℝ) : Fin d → ℝ) j) - b j * beta j =
      (a j * alpha j - b j * beta j) + t * (a j * (Pi.single i (1 : ℝ) : Fin d → ℝ) j) by intro j; ring]
    rw [Finset.sum_add_distrib, ← Finset.mul_sum]
    change _ + t * (a ⬝ᵥ Pi.single i 1) = _
    rw [dotProduct_single, mul_one]
  rw [hs]
  ring

theorem projectionSmoothObjective_beta_line (theta a b alpha beta : Fin d → ℝ)
    (i : Fin d) (t : ℝ) :
    projectionSmoothObjective (m := m) theta a b alpha (beta + t • Pi.single i 1) =
      logPartition (m := m) ((theta + (alpha - beta)) + t • Pi.single i (-1)) -
        (∑ j, (a j * alpha j - b j * beta j)) + t * b i := by
  have hv : theta + (alpha - (beta + t • Pi.single i 1)) =
      (theta + (alpha - beta)) + t • Pi.single i (-1) := by
    ext j
    by_cases hij : j = i
    · subst j; simp; ring
    · simp [Pi.single_eq_of_ne hij]
  unfold projectionSmoothObjective
  rw [hv]
  have hs : (∑ j, (a j * alpha j - b j * (beta + t • Pi.single i (1 : ℝ) : Fin d → ℝ) j)) =
      (∑ j, (a j * alpha j - b j * beta j)) - t * b i := by
    simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, mul_add]
    simp_rw [show ∀ j, a j * alpha j - (b j * beta j + b j * (t * (Pi.single i (1 : ℝ) : Fin d → ℝ) j)) =
      (a j * alpha j - b j * beta j) - t * (b j * (Pi.single i (1 : ℝ) : Fin d → ℝ) j) by intro j; ring]
    rw [Finset.sum_sub_distrib, ← Finset.mul_sum]
    change _ - t * (b ⬝ᵥ Pi.single i 1) = _
    rw [dotProduct_single, mul_one]
  rw [hs]
  ring

theorem hasDerivAt_projectionSmoothObjective_alpha (theta a b alpha beta : Fin d → ℝ)
    (hmd : m ≤ d) (i : Fin d) :
    HasDerivAt (fun t : ℝ => projectionSmoothObjective (m := m) theta a b
      (alpha + t • Pi.single i 1) beta)
      (weightedMarginal (m := m) (theta + (alpha - beta)) i - a i) 0 := by
  simp_rw [projectionSmoothObjective_alpha_line]
  simpa only [zero_smul, add_zero, dotProduct_single, mul_one, one_mul, Pi.sub_apply,
    id_eq] using!
    ((hasDerivAt_logPartition_line (theta + (alpha - beta)) (Pi.single i 1) hmd 0).sub_const
    (∑ j, (a j * alpha j - b j * beta j))).fun_sub
      ((hasDerivAt_id (0 : ℝ)).mul_const (a i))

theorem hasDerivAt_projectionSmoothObjective_beta (theta a b alpha beta : Fin d → ℝ)
    (hmd : m ≤ d) (i : Fin d) :
    HasDerivAt (fun t : ℝ => projectionSmoothObjective (m := m) theta a b
      alpha (beta + t • Pi.single i 1))
      (b i - weightedMarginal (m := m) (theta + (alpha - beta)) i) 0 := by
  simp_rw [projectionSmoothObjective_beta_line]
  simpa only [zero_smul, add_zero, dotProduct_single, mul_neg_one, one_mul, Pi.add_apply,
    id_eq, sub_eq_add_neg, add_comm] using!
    ((hasDerivAt_logPartition_line (theta + (alpha - beta)) (Pi.single i (-1)) hmd 0).sub_const
    (∑ j, (a j * alpha j - b j * beta j))).fun_add
      ((hasDerivAt_id (0 : ℝ)).mul_const (b i))

theorem nonnegative_add_single (x : Fin d → ℝ) (hx : ∀ j, 0 ≤ x j)
    (i : Fin d) (t : ℝ) (ht : -x i ≤ t) :
    ∀ j, 0 ≤ (x + t • Pi.single i (1 : ℝ) : Fin d → ℝ) j := by
  intro j
  by_cases hij : j = i
  · subst j; simp only [Pi.add_apply, Pi.smul_apply, Pi.single_eq_same, smul_eq_mul,
      mul_one]; linarith
  · simpa [Pi.single_eq_of_ne hij] using hx j

/-- Feasibility and complementarity are consequences of minimality, with no
KKT/existence oracle. These are also the boundary products used in Lemma L8. -/
theorem projectionDual_minimum_conditions (theta a b v : Fin d → ℝ) (hmd : m ≤ d)
    (hab : ∀ i, a i ≤ b i)
    (hmin : ∀ u, projectionDual (m := m) theta a b v ≤ projectionDual (m := m) theta a b u)
    (i : Fin d) :
    a i ≤ weightedMarginal (m := m) (theta + v) i ∧
    weightedMarginal (m := m) (theta + v) i ≤ b i ∧
    max (v i) 0 * (weightedMarginal (m := m) (theta + v) i - a i) = 0 ∧
    max (-v i) 0 * (b i - weightedMarginal (m := m) (theta + v) i) = 0 := by
  let alpha : Fin d → ℝ := fun j => max (v j) 0
  let beta : Fin d → ℝ := fun j => max (-v j) 0
  have ha : ∀ j, 0 ≤ alpha j := fun j => le_max_right _ _
  have hb : ∀ j, 0 ≤ beta j := fun j => le_max_right _ _
  have hv : alpha - beta = v := by ext j; exact positivePart_sub_negativePart (v j)
  have hA := derivative_of_nonnegative_coordinate_minimum (ha i)
    (hasDerivAt_projectionSmoothObjective_alpha theta a b alpha beta hmd i)
    (fun t ht => by
      simpa only [zero_smul, add_zero] using
        projectionSmoothObjective_minimum theta a b v hab hmin
          (alpha + t • Pi.single i 1) beta (nonnegative_add_single alpha ha i t ht) hb)
  have hB := derivative_of_nonnegative_coordinate_minimum (hb i)
    (hasDerivAt_projectionSmoothObjective_beta theta a b alpha beta hmd i)
    (fun t ht => by
      simpa only [zero_smul, add_zero] using
        projectionSmoothObjective_minimum theta a b v hab hmin
          alpha (beta + t • Pi.single i 1) ha (nonnegative_add_single beta hb i t ht))
  rw [hv] at hA hB
  exact ⟨sub_nonneg.mp hA.1, sub_nonneg.mp hB.1, hA.2, hB.2⟩

theorem projectionDual_minimum_marginal_dot (theta a b v : Fin d → ℝ) (hmd : m ≤ d)
    (hab : ∀ i, a i ≤ b i)
    (hmin : ∀ u, projectionDual (m := m) theta a b v ≤ projectionDual (m := m) theta a b u)
    (q : Action d m → ℝ) (hqbox : ∀ i, a i ≤ marginal q i ∧ marginal q i ≤ b i) :
    weightedMarginal (m := m) (theta + v) ⬝ᵥ v ≤ marginal q ⬝ᵥ v := by
  apply Finset.sum_le_sum
  intro i _
  obtain ⟨_, _, hA, hB⟩ := projectionDual_minimum_conditions theta a b v hmd hab hmin i
  have hparts := positivePart_sub_negativePart (v i)
  have hqA := mul_nonneg (le_max_right (v i) 0) (sub_nonneg.mpr (hqbox i).1)
  have hqB := mul_nonneg (le_max_right (-v i) 0) (sub_nonneg.mpr (hqbox i).2)
  calc
    weightedMarginal (m := m) (theta + v) i * v i =
        weightedMarginal (m := m) (theta + v) i * (max (v i) 0 - max (-v i) 0) := by rw [hparts]
    _ ≤ marginal q i * (max (v i) 0 - max (-v i) 0) := by nlinarith only [hA, hB, hqA, hqB]
    _ = marginal q i * v i := by rw [hparts]

/-- Every global minimizer gives a feasible normalized positive law, and that
law is a genuine global KL minimizer over every feasible probability vector. -/
theorem projectionDual_minimum_is_KL_projection (theta a b v : Fin d → ℝ)
    (hmd : m ≤ d) (hab : ∀ i, a i ≤ b i)
    (hmin : ∀ u, projectionDual (m := m) theta a b v ≤ projectionDual (m := m) theta a b u) :
    (∀ i, a i ≤ weightedMarginal (m := m) (theta + v) i ∧
      weightedMarginal (m := m) (theta + v) i ≤ b i) ∧
    (∀ q : Action d m → ℝ, (∀ x, 0 ≤ q x) → (∑ x, q x) = 1 →
      (∀ i, a i ≤ marginal q i ∧ marginal q i ≤ b i) →
      finiteKL (weightedLaw (m := m) (theta + v)) (weightedLaw theta) ≤
        finiteKL q (weightedLaw theta)) := by
  constructor
  · intro i
    have h := projectionDual_minimum_conditions theta a b v hmd hab hmin i
    exact ⟨h.1, h.2.1⟩
  · intro q hq hqsum hqbox
    have hp := finiteKL_weightedLaw_shift (weightedLaw (m := m) (theta + v))
      (sum_weightedLaw (theta + v) hmd) theta v hmd
    rw [finiteKL_self] at hp
    have hqshift := finiteKL_weightedLaw_shift q hqsum theta v hmd
    have hqKL := finiteKL_nonneg q (weightedLaw (m := m) (theta + v)) hq hqsum
      (weightedLaw_pos (theta + v) hmd) (sum_weightedLaw (theta + v) hmd)
    have hdot := projectionDual_minimum_marginal_dot theta a b v hmd hab hmin q hqbox
    change marginal (weightedLaw (m := m) (theta + v)) ⬝ᵥ v ≤ marginal q ⬝ᵥ v at hdot
    linarith

end MsetsPaper.Upper
