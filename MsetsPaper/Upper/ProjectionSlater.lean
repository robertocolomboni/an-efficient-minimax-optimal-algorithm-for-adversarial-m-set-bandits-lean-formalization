import MsetsPaper.Upper.FiniteSlater
import MsetsPaper.Upper.ProjectionDualSubgradient
import Mathlib.Analysis.Convex.StdSimplex

/-! # Applying general Slater duality to the finite KL projection

The simplex is compact and convex; KL is continuous and convex there, including
zero masses. Marginal constraints are affine, and the uniform law is strictly
feasible. General Slater gives attained nonnegative multipliers, which the
already-proved Lagrangian identities turn into a minimizer of G.
-/

namespace MsetsPaper.Upper

open Set Matrix MsetsLower MsetsLower.History
open scoped BigOperators

noncomputable section

theorem continuous_finiteKL_reference {A : Type*} [Fintype A]
    (p : A → ℝ) (hp : ∀ x, 0 < p x) : Continuous (fun q : A → ℝ => finiteKL q p) := by
  have heq : (fun q : A → ℝ => finiteKL q p) =
      (fun q => ∑ x, (q x * Real.log (q x) - q x * Real.log (p x))) := by
    funext q
    rw [finiteKL_eq_sum_mul_log_sub_log q p hp]
    apply Finset.sum_congr rfl
    intro x _
    ring
  rw [heq]
  apply continuous_finset_sum
  intro x _
  exact (Real.continuous_mul_log.comp (continuous_apply x)).sub
    ((continuous_apply x).mul continuous_const)

theorem convexOn_finiteKL_simplex {A : Type*} [Fintype A]
    (p : A → ℝ) (hp : ∀ x, 0 < p x) :
    ConvexOn ℝ (stdSimplex ℝ A) (fun q => finiteKL q p) := by
  refine ⟨convex_stdSimplex ℝ A, ?_⟩
  intro q hq r hr a b ha hb hab
  simp_rw [finiteKL_eq_sum_mul_log_sub_log _ p hp]
  simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
  rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
  apply Finset.sum_le_sum
  intro x _
  have h := Real.convexOn_mul_log.2 (hq.1 x) (hr.1 x) ha hb hab
  change (a * q x + b * r x) * Real.log (a * q x + b * r x) ≤
    a * (q x * Real.log (q x)) + b * (r x * Real.log (r x)) at h
  nlinarith

variable {d m : ℕ}

theorem marginal_affine_combination (q r : Action d m → ℝ) (a b : ℝ) (i : Fin d) :
    marginal (a • q + b • r) i = a * marginal q i + b * marginal r i := by
  unfold marginal
  simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, add_mul, Finset.sum_add_distrib,
    mul_assoc, ← Finset.mul_sum]

theorem continuous_marginal_coordinate (i : Fin d) :
    Continuous (fun q : Action d m → ℝ => marginal q i) := by
  unfold marginal
  fun_prop

/-- Two affine inequalities for each marginal, encoded as a finite sum type. -/
def projectionConstraint (a b : Fin d → ℝ) : (Fin d ⊕ Fin d) → (Action d m → ℝ) → ℝ
  | Sum.inl i, q => a i - marginal q i
  | Sum.inr i, q => marginal q i - b i

theorem projectionConstraint_convex (a b : Fin d → ℝ) (j : Fin d ⊕ Fin d) :
    ConvexOn ℝ (stdSimplex ℝ (Action d m)) (projectionConstraint (m := m) a b j) := by
  refine ⟨convex_stdSimplex ℝ _, ?_⟩
  intro q _ r _ u v hu hv huv
  cases j with
  | inl i =>
    change a i - marginal (u • q + v • r) i ≤
      u * (a i - marginal q i) + v * (a i - marginal r i)
    rw [marginal_affine_combination]
    have h := congrArg (fun z : ℝ => z * a i) huv
    nlinarith only [h]
  | inr i =>
    change marginal (u • q + v • r) i - b i ≤
      u * (marginal q i - b i) + v * (marginal r i - b i)
    rw [marginal_affine_combination]
    have h := congrArg (fun z : ℝ => z * b i) huv
    nlinarith only [h]

theorem projectionConstraint_continuous (a b : Fin d → ℝ) (j : Fin d ⊕ Fin d) :
    Continuous (projectionConstraint (m := m) a b j) := by
  cases j with
  | inl i => exact continuous_const.sub (continuous_marginal_coordinate i)
  | inr i => exact (continuous_marginal_coordinate i).sub continuous_const

theorem projection_slater_uniform_marginal
    (hmpos : 1 ≤ m) (hmtop : m ≤ d - 1) (i : Fin d) :
    weightedMarginal (m := m) (0 : Fin d → ℝ) i = (m : ℝ) / d := by
  classical
  have hconst (j : Fin d) : weightedMarginal (m := m) (0 : Fin d → ℝ) j =
      weightedMarginal (m := m) (0 : Fin d → ℝ) i := by
    -- Swapping two items permutes all m-sets and preserves uniform weights.
    let e : Action d m ≃ Action d m :=
      (Equiv.finsetCongr (Equiv.swap i j)).subtypeEquiv (by
        intro a
        simp [Equiv.finsetCongr_apply])
    change (∑ a : Action d m, weightedLaw (0 : Fin d → ℝ) a * selectedIndicator j a) =
      ∑ a : Action d m, weightedLaw (0 : Fin d → ℝ) a * selectedIndicator i a
    rw [← e.sum_comp (fun a ↦ weightedLaw (0 : Fin d → ℝ) a * selectedIndicator j a)]
    apply Finset.sum_congr rfl
    intro a _
    simp [e, Equiv.subtypeEquiv, Equiv.finsetCongr_apply,
      selectedIndicator, weightedLaw, actionLoss]
  have hs := sum_weightedMarginal (m := m) (0 : Fin d → ℝ) (show m ≤ d by omega)
  simp_rw [hconst] at hs
  simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul] at hs
  have hd : (d : ℝ) ≠ 0 := by exact_mod_cast (show d ≠ 0 by omega)
  apply (eq_div_iff hd).mpr
  nlinarith

/-- Attainment of the actual multiplier dual via the general Slater theorem.
All compactness, convexity, continuity and strict-feasibility obligations are
proved for the concrete primal; no multiplier is an input certificate. -/
theorem projectionMultiplierDual_attains_via_slater (theta a b : Fin d → ℝ)
    (hmpos : 1 ≤ m) (hmtop : m ≤ d - 1)
    (hlo : ∀ i, a i < (m : ℝ) / d) (hhi : ∀ i, (m : ℝ) / d < b i) :
    ∃ alpha beta : Fin d → ℝ, (∀ i, 0 ≤ alpha i) ∧ (∀ i, 0 ≤ beta i) ∧
      ∀ alpha' beta' : Fin d → ℝ, (∀ i, 0 ≤ alpha' i) → (∀ i, 0 ≤ beta' i) →
        projectionMultiplierDual (m := m) theta a b alpha' beta' ≤
          projectionMultiplierDual (m := m) theta a b alpha beta := by
  classical
  have hmd : m ≤ d := by omega
  let q₀ := weightedLaw (m := m) (0 : Fin d → ℝ)
  have hq₀ : q₀ ∈ stdSimplex ℝ (Action d m) :=
    ⟨fun x => (weightedLaw_pos _ hmd x).le, sum_weightedLaw _ hmd⟩
  have hstrict (j : Fin d ⊕ Fin d) : projectionConstraint a b j q₀ < 0 := by
    cases j with
    | inl i =>
      change a i - weightedMarginal (m := m) 0 i < 0
      rw [projection_slater_uniform_marginal hmpos hmtop]
      exact sub_neg.mpr (hlo i)
    | inr i =>
      change weightedMarginal (m := m) 0 i - b i < 0
      rw [projection_slater_uniform_marginal hmpos hmtop]
      exact sub_neg.mpr (hhi i)
  obtain ⟨qstar, hqstar, hfeasible, lam, hlam, hlag, _hslack⟩ :=
    FiniteSlater.multipliers_on_compact
      (stdSimplex ℝ (Action d m)) (convex_stdSimplex ℝ _) (isCompact_stdSimplex ℝ _)
      (fun q => finiteKL q (weightedLaw theta))
      (convexOn_finiteKL_simplex _ (weightedLaw_pos theta hmd))
      (continuous_finiteKL_reference _ (weightedLaw_pos theta hmd)).continuousOn
      (projectionConstraint (m := m) a b) (projectionConstraint_convex a b)
      (projectionConstraint_continuous a b) q₀ hq₀ hstrict
  let alpha : Fin d → ℝ := fun i => lam (Sum.inl i)
  let beta : Fin d → ℝ := fun i => lam (Sum.inr i)
  have halpha (i) : 0 ≤ alpha i := hlam _
  have hbeta (i) : 0 ≤ beta i := hlam _
  have hsum (q : Action d m → ℝ) :
      (∑ j, lam j * projectionConstraint a b j q) =
        ∑ i, (alpha i * (a i - marginal q i) + beta i * (marginal q i - b i)) := by
    rw [Fintype.sum_sum_type, ← Finset.sum_add_distrib]
    rfl
  have hstrong : finiteKL qstar (weightedLaw theta) ≤
      projectionMultiplierDual (m := m) theta a b alpha beta := by
    have h := hlag (weightedLaw (theta + (alpha - beta)))
      ⟨fun x => (weightedLaw_pos _ hmd x).le, sum_weightedLaw _ hmd⟩
    rw [hsum] at h
    change _ ≤ projectionLagrangian theta a b alpha beta
      (weightedLaw (theta + (alpha - beta))) at h
    rwa [projectionLagrangian_at_weightedLaw _ _ _ _ _ hmd] at h
  refine ⟨alpha, beta, halpha, hbeta, ?_⟩
  intro alpha' beta' ha' hb'
  apply (projectionMultiplierDual_le_lagrangian qstar hqstar.1 hqstar.2
    theta a b alpha' beta' hmd).trans
  apply le_trans _ hstrong
  change finiteKL qstar (weightedLaw theta) + _ ≤ finiteKL qstar (weightedLaw theta)
  apply add_le_of_nonpos_right
  apply Finset.sum_nonpos
  intro i _
  exact add_nonpos
    (mul_nonpos_of_nonneg_of_nonpos (ha' i) (hfeasible (Sum.inl i)))
    (mul_nonpos_of_nonneg_of_nonpos (hb' i) (hfeasible (Sum.inr i)))

theorem projectionDual_exists_of_strict_uniform (theta a b : Fin d → ℝ)
    (hmpos : 1 ≤ m) (hmtop : m ≤ d - 1)
    (hlo : ∀ i, a i < (m : ℝ) / d) (hhi : ∀ i, (m : ℝ) / d < b i) :
    ∃ v, ∀ u, projectionDual (m := m) theta a b v ≤ projectionDual (m := m) theta a b u := by
  obtain ⟨alpha, beta, ha, hb, hmax⟩ :=
    projectionMultiplierDual_attains_via_slater theta a b hmpos hmtop hlo hhi
  refine ⟨alpha - beta, ?_⟩
  intro u
  have h := (hmax (fun i => max (u i) 0) (fun i => max (-u i) 0)
    (fun i => le_max_right _ _) (fun i => le_max_right _ _)).trans
    (projectionMultiplierDual_le_positiveParts theta a b alpha beta
      (fun i => (hlo i).le.trans (hhi i).le) ha hb)
  have hparts := projectionMultiplierDual_positiveParts (m := m) theta a b (alpha - beta)
  simp only [Pi.sub_apply, neg_sub] at hparts
  rw [projectionMultiplierDual_positiveParts, hparts] at h
  linarith

end
end MsetsPaper.Upper
