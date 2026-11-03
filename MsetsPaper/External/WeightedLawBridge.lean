import MsetsPaper.Upper.WeightedLaw
import MsetsPaper.Upper.InverseCovariance
import CoefficientOne.CovarianceBridge

/-!
# Identifying the two concrete fixed-cardinality laws

The spectral library uses positive multiplicative weights, whereas the m-set
algorithm uses exponential parameters. Their sample spaces are the same subtype
of finite sets. The following identities identify the actual probability masses,
marginals, covariance matrices, and coordinate variances at `w i = exp (theta i)`.
-/

noncomputable section

open Matrix MsetsPaper.Upper
open scoped BigOperators

namespace MsetsPaper.External

variable {d m : ℕ}

/-- The exponential m-set law is exactly the spectral library's external-field law. -/
theorem weightedLaw_eq_subsetProbability (theta : Fin d → ℝ) (a : Action d m) :
    weightedLaw theta a =
      EffectiveResistance.subsetProbability (fun i => Real.exp (theta i)) m a := by
  simpa only [EffectiveResistance.subsetProbability,
    EffectiveResistance.elementarySum, EffectiveResistance.subsetWeight] using
    weightedLaw_product_form theta a

/-- Both libraries take the same inclusion expectation under the same law. -/
theorem weightedMarginal_eq_inclusionMean (theta : Fin d → ℝ) (i : Fin d) :
    weightedMarginal (m := m) theta i =
      EffectiveResistance.inclusionMean (fun j => Real.exp (theta j)) m i := by
  simp only [weightedMarginal, marginal, EffectiveResistance.inclusionMean,
    EffectiveResistance.expectation, weightedLaw_eq_subsetProbability,
    MsetsLower.History.selectedIndicator, EffectiveResistance.indicator]

/-- The uncentered-moment definition equals the spectral centered expectation. -/
theorem covariance_weightedLaw_eq (theta : Fin d → ℝ) (hmd : m ≤ d) :
    covariance (weightedLaw (m := m) theta) =
      EffectiveResistance.covarianceMatrix (fun i => Real.exp (theta i)) m := by
  ext i j
  rw [covariance_eq_centered_secondMoment _ (sum_weightedLaw theta hmd) i j]
  simp only [EffectiveResistance.covarianceMatrix, EffectiveResistance.expectation,
    ← weightedLaw_eq_subsetProbability, ← weightedMarginal_eq_inclusionMean,
    weightedMarginal, MsetsLower.History.selectedIndicator,
    EffectiveResistance.indicator, mul_assoc]

/-- The spectral coordinate variance is the Bernoulli variance used in m-set. -/
theorem covarianceVariance_exp_eq (theta : Fin d → ℝ) (hmd : m ≤ d) (i : Fin d) :
    CoefficientOne.covarianceVariance (fun j => Real.exp (theta j)) m i =
      weightedMarginal (m := m) theta i * (1 - weightedMarginal (m := m) theta i) := by
  unfold CoefficientOne.covarianceVariance
  rw [EffectiveResistance.covariance_diagonal _ (fun j => Real.exp_pos (theta j))
    (by simpa using hmd), ← weightedMarginal_eq_inclusionMean]

end MsetsPaper.External
