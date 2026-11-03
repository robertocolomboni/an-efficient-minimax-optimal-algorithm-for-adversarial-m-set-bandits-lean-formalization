import CoefficientOne.Sampling.OneSidedCoupling
import CoefficientOne.Sampling.InteriorSampler

/-! # The manuscript's local bound in marginal coordinates -/

open scoped Topology
open MeasureTheory Filter

namespace CoefficientOne.Sampling
noncomputable section

variable {n k : ℕ} [NeZero n]

theorem interior_local_coupling (hk : k ≤ n)
    (x : ℝ → interiorHypersimplex (Fin n) k) (a : Fin n → ℝ)
    (hθ : HasDerivAt (fun t => (parameterOfMarginal k (x t).val).val) a 0) :
    ∀ ε > (0 : ℝ), ∀ᶠ t in 𝓝[≠] (0 : ℝ),
      expectedOutputDistance (seedMeasure n) (interiorSampler k (x 0)) (interiorSampler k (x t)) / |t| ≤
        2 * samplerVariation (marginalWeights k (x 0).val) k a + ε :=
  parameter_local_coupling k hk (fun t => (parameterOfMarginal k (x t).val).val) a hθ

theorem interior_local_coupling_of_hasDerivAt (hkpos : 1 ≤ k) (hktop : k < n)
    (x : ℝ → interiorHypersimplex (Fin n) k) (v : Fin n → ℝ)
    (hx : HasDerivAt (fun t => (x t).val) v 0) :
    ∀ ε > (0 : ℝ), ∀ᶠ t in 𝓝[≠] (0 : ℝ),
      expectedOutputDistance (seedMeasure n) (interiorSampler k (x 0)) (interiorSampler k (x t)) / |t| ≤
        2 * samplerVariation (marginalWeights k (x 0).val) k
          (deriv (fun t => (parameterOfMarginal k (x t).val).val) 0) + ε := by
  have hp := (parameterOfMarginal_hasFDerivAt (ι := Fin n) hkpos (by simpa using hktop)
    (x 0).val (x 0).property).comp_hasDerivAt 0 hx
  have hd := (parameterSpace (Fin n)).subtypeL.hasFDerivAt.comp_hasDerivAt 0 hp
  exact interior_local_coupling hktop.le x _ hd.differentiableAt.hasDerivAt

theorem interior_local_coupling_within (hk : k ≤ n)
    (x : ℝ → interiorHypersimplex (Fin n) k) (a : Fin n → ℝ) (s : Set ℝ)
    (hθ : HasDerivWithinAt (fun t => (parameterOfMarginal k (x t).val).val) a s 0) :
    ∀ ε > (0 : ℝ), ∀ᶠ t in 𝓝[s \ {0}] (0 : ℝ),
      expectedOutputDistance (seedMeasure n) (interiorSampler k (x 0)) (interiorSampler k (x t)) / |t| ≤
        2 * samplerVariation (marginalWeights k (x 0).val) k a + ε :=
  parameter_local_coupling_within k hk (fun t => (parameterOfMarginal k (x t).val).val) a s hθ

theorem interior_local_coupling_of_hasDerivWithinAt (hkpos : 1 ≤ k) (hktop : k < n)
    (x : ℝ → interiorHypersimplex (Fin n) k) (v : Fin n → ℝ) (s : Set ℝ)
    (hx : HasDerivWithinAt (fun t => (x t).val) v s 0) :
    ∃ a : Fin n → ℝ,
      HasDerivWithinAt (fun t => (parameterOfMarginal k (x t).val).val) a s 0 ∧
      ∀ ε > (0 : ℝ), ∀ᶠ t in 𝓝[s \ {0}] (0 : ℝ),
        expectedOutputDistance (seedMeasure n) (interiorSampler k (x 0)) (interiorSampler k (x t)) / |t| ≤
          2 * samplerVariation (marginalWeights k (x 0).val) k a + ε := by
  have hp := (parameterOfMarginal_hasFDerivAt (ι := Fin n) hkpos (by simpa using hktop)
    (x 0).val (x 0).property).comp_hasDerivWithinAt 0 hx
  have hd := (parameterSpace (Fin n)).subtypeL.hasFDerivAt.comp_hasDerivWithinAt 0 hp
  exact ⟨_, hd, interior_local_coupling_within hktop.le x _ s hd⟩

end
end CoefficientOne.Sampling
