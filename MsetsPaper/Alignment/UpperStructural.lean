import MsetsPaper.Upper.BoundedIncrements

/-!
# Structural interfaces for the definitive manuscript

Source: `paper/main.tex`, structural lemmas L1--L3.
These statements expose the paper's distribution and marginal-set hypotheses.
They do not replace the underlying proofs or assume the spectral estimate.
-/

noncomputable section

open Matrix MsetsLower MsetsLower.History MsetsPaper.Upper
open scoped BigOperators

namespace MsetsPaper.Alignment

variable {d m : ℕ}

/-- Exactly the positive exponential family in the paper's definition of a
weighted m-set distribution, expressed as a property of the law itself. -/
def IsWeightedMSetLaw (p : Action d m → ℝ) : Prop :=
  ∃ theta : Fin d → ℝ, p = weightedLaw theta

/-- The coordinate inequalities in P_lambda. Normalization and positivity
follow separately from `IsWeightedMSetLaw` in the structural lemmas. -/
def InPaperMarginalSet (p : Action d m → ℝ) (lam : ℝ) : Prop :=
  ∀ i, lam * ((m : ℝ) / d) ≤ marginal p i ∧
    marginal p i ≤ 1 - lam * (1 - (m : ℝ) / d)

/-- `lem:linear-majorant-final`, with the actual law p as the argument. -/
theorem upper_linear_majorant (p : Action d m → ℝ)
    (hweighted : IsWeightedMSetLaw p)
    (hmpos : 1 ≤ m) (hmtop : m ≤ d - 1)
    {lam : ℝ} (hlam0 : 0 < lam) (_hlam1 : lam < 1)
    (hbox : InPaperMarginalSet p lam) :
    (∀ a : Action d m,
      (fun i ↦ selectedIndicator i a) ⬝ᵥ
        ((secondMoment p)⁻¹ *ᵥ (fun i ↦ selectedIndicator i a)) ≤
          phi (marginal p) (fun i ↦ selectedIndicator i a)) ∧
    (∀ a : Action d m, 4 * phi (marginal p) (fun i ↦ selectedIndicator i a) =
      ∑ i, correction (m : ℝ) (marginal p) i * selectedIndicator i a) ∧
    (∑ a : Action d m, p a * phi (marginal p) (fun i ↦ selectedIndicator i a)) =
      (d : ℝ) + 1 ∧
    (∀ a : Action d m,
      0 ≤ phi (marginal p) (fun i ↦ selectedIndicator i a) ∧
      phi (marginal p) (fun i ↦ selectedIndicator i a) ≤ 1 + 2 * d / lam) := by
  obtain ⟨theta, rfl⟩ := hweighted
  obtain ⟨hlev, haff, hmean, hrange⟩ := linear_majorant theta hmpos hmtop hlam0
    (fun i ↦ (hbox i).1) (fun i ↦ (hbox i).2)
  exact ⟨hlev, fun a ↦ (haff a).symm, hmean, hrange⟩

/-- `lem:inverse-covariance-identity`. The matrix denoted by Sigma^+ is the
proved, uniquely characterized Moore--Penrose inverse, not a supplied oracle. -/
theorem upper_inverse_covariance_identity (p : Action d m → ℝ)
    (hweighted : IsWeightedMSetLaw p)
    (hmpos : 1 ≤ m) (hmtop : m ≤ d - 1) :
    (secondMoment p).PosDef ∧
    (∀ y : Fin d → ℝ, (∑ i, y i = 0) →
      y ⬝ᵥ ((secondMoment p)⁻¹ *ᵥ y) = y ⬝ᵥ (covariancePseudoInverse p *ᵥ y)) ∧
    (∀ a : Action d m,
      (fun i ↦ selectedIndicator i a) ⬝ᵥ
        ((secondMoment p)⁻¹ *ᵥ (fun i ↦ selectedIndicator i a)) =
      1 + ((fun i ↦ selectedIndicator i a) - marginal p) ⬝ᵥ
        (covariancePseudoInverse p *ᵥ ((fun i ↦ selectedIndicator i a) - marginal p))) := by
  obtain ⟨theta, rfl⟩ := hweighted
  exact inverse_covariance_identity theta hmpos hmtop

/-- `lem:bounded-increments` is conditional on the CURRENT distribution being
in P_(lambda/2), exactly as in the definitive manuscript. It neither assumes
nor establishes the global algorithmic invariant. -/
theorem upper_bounded_increments (theta ell : Fin d → ℝ)
    (hmpos : 1 ≤ m) (hmtop : m ≤ d - 1)
    {eta lam : ℝ} (heta : 0 < eta) (hsmall : eta ≤ 1 / 64)
    (hlam : lam = 128 * eta * d) (_hlamcap : lam ≤ 1 / 2)
    (hloss : ∀ a : Action d m, |actionLoss a ell| ≤ 1)
    (hbox : InPaperMarginalSet (weightedLaw (m := m) theta) (lam / 2))
    (sampled comparator : Action d m) :
    eta * |surrogate theta ell eta sampled comparator| ≤ 1 / 4 := by
  subst lam
  exact bounded_increments theta ell hmpos hmtop heta hsmall hloss
    (fun i ↦ (hbox i).1) (fun i ↦ (hbox i).2) sampled comparator

end MsetsPaper.Alignment
