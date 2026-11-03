import CoefficientOne.Sampling.StoppedVariation
import CoefficientOne.Sampling.HistoryConditionalVariance
import CoefficientOne.Sampling.InteriorSampler

/-! # The variation lemma in the marginal parametrization of Appendix E.2 -/
open scoped BigOperators
open EffectiveResistance Matrix MeasureTheory
namespace CoefficientOne.Sampling
noncomputable section
variable {n k : ℕ} [NeZero n]

def interiorVariation (k : ℕ) (x : interiorHypersimplex (Fin n) k) (a : Fin n → ℝ) : ℝ :=
  samplerVariation (marginalWeights k x.val) k a

theorem interiorVariation_eq_stopped (hkpos : 1 ≤ k) (hktop : k < n)
    (x : interiorHypersimplex (Fin n) k) (a : Fin n → ℝ) :
    interiorVariation k x a = ∫ ω,
      ∑ ℓ ∈ Finset.range (samplerTerminalTime (marginalWeights k x.val) k hktop.le ω),
        variationContribution (marginalWeights k x.val) k ℓ a ω ∂seedMeasure n :=
  samplerVariation_eq_stopped _ (marginalWeights_pos k x.val) k hktop.le a

theorem interiorVariation_bound (hkpos : 1 ≤ k) (hktop : k < n)
    (x : interiorHypersimplex (Fin n) k) (a : Fin n → ℝ) :
    interiorVariation k x a ≤
      2 * (externalFieldCovarianceNetwork (marginalWeights k x.val) (marginalWeights_pos k x.val)
        k hkpos (by simpa using (show k ≤ n - 1 by omega))).edgeVariation a ∧
    2 * (externalFieldCovarianceNetwork (marginalWeights k x.val) (marginalWeights_pos k x.val)
        k hkpos (by simpa using (show k ≤ n - 1 by omega))).edgeVariation a ≤
      3 * l1Norm (lawCovariance (maximumEntropyLaw (interiorInputToClosed x)) *ᵥ a) := by
  rw [maximumEntropyLaw_eq_marginalWeights hkpos (by simpa using hktop), externalFieldLaw_covariance]
  exact samplerVariation_bound _ (marginalWeights_pos k x.val) k hkpos (by omega) a

theorem interiorVariation_le_three_l1 (hkpos : 1 ≤ k) (hktop : k < n)
    (x : interiorHypersimplex (Fin n) k) (a : Fin n → ℝ) :
    interiorVariation k x a ≤
      3 * l1Norm (lawCovariance (maximumEntropyLaw (interiorInputToClosed x)) *ᵥ a) :=
  (interiorVariation_bound hkpos hktop x a).1.trans (interiorVariation_bound hkpos hktop x a).2

end
end CoefficientOne.Sampling
