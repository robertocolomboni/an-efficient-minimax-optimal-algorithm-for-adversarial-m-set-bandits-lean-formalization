import MsetsPaper.Upper.ProjectionDualCapstone

/-!
# Definitive manuscript: projection dual (L7)

Source: `paper/main.tex`, `lem:projection-dual`.
The declarations expose the simplex and the smoothing polytope explicitly.
Weak duality, zero duality gap and primal optimality are connected below;
the underlying capstone supplies the primal-optimality proof. Existence uses the
general finite convex Slater theorem proved by geometric separation, after
verifying compactness, continuity, convexity and strict uniform feasibility.
-/

noncomputable section
open scoped BigOperators
open Matrix MsetsPaper.Upper

namespace MsetsPaper.Alignment.Implementation

variable {d m : ℕ}

def ProbabilityVector (q : Action d m → ℝ) : Prop :=
  (∀ x, 0 ≤ q x) ∧ (∑ x, q x) = 1

def SmoothingPolytope (lam : ℝ) (q : Action d m → ℝ) : Prop :=
  ProbabilityVector q ∧ ∀ i,
    projectionLower d m lam i ≤ marginal q i ∧
      marginal q i ≤ projectionUpper d m lam i

theorem weightedLaw_probability (theta : Fin d → ℝ) (hmd : m ≤ d) :
    ProbabilityVector (weightedLaw (m := m) theta) :=
  ⟨fun x => (weightedLaw_pos theta hmd x).le, sum_weightedLaw theta hmd⟩

/-- The strict feasible uniform law used for Slater's hypothesis in the text. -/
theorem uniform_strict_feasibility (hm : 1 ≤ m) (hmtop : m ≤ d - 1)
    (lam : ℝ) (hlam : 0 < lam) (hlamhalf : lam ≤ 1 / 2) :
    ProbabilityVector (weightedLaw (m := m) (0 : Fin d → ℝ)) ∧
    (∀ x, 0 < weightedLaw (m := m) (0 : Fin d → ℝ) x) ∧
    (∀ i, projectionLower d m lam i <
      weightedMarginal (m := m) (0 : Fin d → ℝ) i ∧
      weightedMarginal (m := m) (0 : Fin d → ℝ) i < projectionUpper d m lam i) := by
  obtain ⟨eps, heps, hlo, hhi⟩ := projection_uniform_slack hm hmtop lam hlam hlamhalf
  refine ⟨weightedLaw_probability 0 (by omega), weightedLaw_pos 0 (by omega), ?_⟩
  intro i
  rw [weightedMarginal_zero_eq hm hmtop]
  constructor <;> linarith [hlo i, hhi i]

/-- Weak duality for every feasible probability vector, including zero masses. -/
theorem projection_weak_duality (theta a b alpha beta : Fin d → ℝ)
    (hmd : m ≤ d) (halpha : ∀ i, 0 ≤ alpha i) (hbeta : ∀ i, 0 ≤ beta i)
    (q : Action d m → ℝ) (hq : ProbabilityVector q)
    (hqbox : ∀ i, a i ≤ marginal q i ∧ marginal q i ≤ b i) :
    projectionMultiplierDual (m := m) theta a b alpha beta ≤
      finiteKL q (weightedLaw theta) := by
  have hdual := projectionMultiplierDual_le_lagrangian q hq.1 hq.2
    theta a b alpha beta hmd
  have hterms : (∑ i, (alpha i * (a i - marginal q i) +
      beta i * (marginal q i - b i))) ≤ 0 := by
    apply Finset.sum_nonpos
    intro i _
    exact add_nonpos
      (mul_nonpos_of_nonneg_of_nonpos (halpha i) (sub_nonpos.mpr (hqbox i).1))
      (mul_nonpos_of_nonneg_of_nonpos (hbeta i) (sub_nonpos.mpr (hqbox i).2))
  unfold projectionLagrangian at hdual
  linarith

/-- A minimizer yields feasibility, complementary slackness and zero duality
gap. This verifies the concrete KKT/strong-duality conclusions locally. -/
theorem projection_minimum_kkt (theta a b v : Fin d → ℝ)
    (hmd : m ≤ d) (hab : ∀ i, a i ≤ b i)
    (hmin : ∀ u, projectionDual (m := m) theta a b v ≤ projectionDual (m := m) theta a b u) :
    (∀ i, a i ≤ weightedMarginal (m := m) (theta + v) i ∧
      weightedMarginal (m := m) (theta + v) i ≤ b i) ∧
    (∀ i, max (v i) 0 * (weightedMarginal (m := m) (theta + v) i - a i) = 0 ∧
      max (-v i) 0 * (b i - weightedMarginal (m := m) (theta + v) i) = 0) ∧
    finiteKL (weightedLaw (m := m) (theta + v)) (weightedLaw theta) =
      projectionMultiplierDual (m := m) theta a b
        (fun i => max (v i) 0) (fun i => max (-v i) 0) := by
  have hconditions := projectionDual_minimum_conditions theta a b v hmd hab hmin
  refine ⟨fun i => ⟨(hconditions i).1, (hconditions i).2.1⟩,
    fun i => (hconditions i).2.2, ?_⟩
  let alpha : Fin d → ℝ := fun i => max (v i) 0
  let beta : Fin d → ℝ := fun i => max (-v i) 0
  have hshift : alpha - beta = v := funext fun i => positivePart_sub_negativePart (v i)
  have hlag := projectionLagrangian_at_weightedLaw theta a b alpha beta hmd
  rw [hshift] at hlag
  have hterms : (∑ i, (alpha i * (a i - weightedMarginal (m := m) (theta + v) i) +
      beta i * (weightedMarginal (m := m) (theta + v) i - b i))) = 0 := by
    apply Finset.sum_eq_zero
    intro i _
    have ha := (hconditions i).2.2.1
    have hb := (hconditions i).2.2.2
    dsimp only [alpha, beta]
    nlinarith
  unfold projectionLagrangian at hlag
  change finiteKL (weightedLaw (m := m) (theta + v)) (weightedLaw theta) +
      (∑ i, (alpha i * (a i - weightedMarginal (m := m) (theta + v) i) +
        beta i * (weightedMarginal (m := m) (theta + v) i - b i))) = _ at hlag
  simpa only [hterms, add_zero] using hlag

/-- The primal optimizer and an optimal multiplier pair attain the same value;
both comparisons are over all admissible competitors. -/
theorem projection_primal_dual_optimality (theta a b v : Fin d → ℝ)
    (hmd : m ≤ d) (hab : ∀ i, a i ≤ b i)
    (hmin : ∀ u, projectionDual (m := m) theta a b v ≤ projectionDual (m := m) theta a b u) :
    (∀ q : Action d m → ℝ, ProbabilityVector q →
      (∀ i, a i ≤ marginal q i ∧ marginal q i ≤ b i) →
      finiteKL (weightedLaw (m := m) (theta + v)) (weightedLaw theta) ≤
        finiteKL q (weightedLaw theta)) ∧
    (∀ alpha beta : Fin d → ℝ, (∀ i, 0 ≤ alpha i) → (∀ i, 0 ≤ beta i) →
      projectionMultiplierDual (m := m) theta a b alpha beta ≤
        projectionMultiplierDual (m := m) theta a b
          (fun i => max (v i) 0) (fun i => max (-v i) 0)) := by
  obtain ⟨hbox, _, hgap⟩ := projection_minimum_kkt theta a b v hmd hab hmin
  constructor
  · intro q hq hqbox
    rw [hgap]
    exact projection_weak_duality theta a b _ _ hmd
      (fun _ => le_max_right _ _) (fun _ => le_max_right _ _) q hq hqbox
  · intro alpha beta halpha hbeta
    rw [← hgap]
    exact projection_weak_duality theta a b alpha beta hmd halpha hbeta
      (weightedLaw (theta + v)) (weightedLaw_probability _ hmd) hbox

/-- Paper-facing L7. The norm on `Fin d → ℝ` is the infinity norm. -/
theorem projection_dual (theta : Fin d → ℝ)
    (hm : 1 ≤ m) (hmtop : m ≤ d - 1) (lam : ℝ)
    (hlam : 0 < lam) (hlamhalf : lam ≤ 1 / 2) :
    let a := projectionLower d m lam
    let b := projectionUpper d m lam
    ConvexOn ℝ Set.univ (projectionDual (m := m) theta a b) ∧
    (∃ v, ∀ u, projectionDual (m := m) theta a b v ≤ projectionDual (m := m) theta a b u) ∧
    (∀ v, (∀ u, projectionDual (m := m) theta a b v ≤ projectionDual (m := m) theta a b u) →
      SmoothingPolytope lam (weightedLaw (m := m) (theta + v)) ∧
      (∀ q : Action d m → ℝ, SmoothingPolytope lam q →
        finiteKL (weightedLaw (m := m) (theta + v)) (weightedLaw theta) ≤
          finiteKL q (weightedLaw theta))) ∧
    (∀ u v, projectionDual (m := m) theta a b v +
      projectionSubgradient (m := m) theta a b v ⬝ᵥ (u - v) ≤ projectionDual (m := m) theta a b u) ∧
    (∀ v, ‖projectionSubgradient (m := m) theta a b v‖ ≤ 1) := by
  obtain ⟨ha, hb, hab⟩ := projection_box_bounds hm hmtop lam hlam hlamhalf
  have hmd : m ≤ d := by omega
  refine ⟨projectionDual_convex theta _ _ hmd hab,
    projectionDual_exists theta hm hmtop lam hlam hlamhalf, ?_,
    (fun u v => projectionDual_subgradient theta _ _ u v hmd hab),
    (fun v => projectionSubgradient_norm_le_one theta _ _ v hm hmtop ha hb)⟩
  intro v hmin
  have hkkt := projection_minimum_kkt theta _ _ v hmd hab hmin
  have hopt := projection_primal_dual_optimality theta _ _ v hmd hab hmin
  exact ⟨⟨weightedLaw_probability _ hmd, hkkt.1⟩, fun q hq => hopt.1 q hq.1 hq.2⟩

end MsetsPaper.Alignment.Implementation
