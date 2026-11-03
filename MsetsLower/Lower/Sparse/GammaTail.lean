import MsetsLower.Lower.Sparse.ExtendedFixing
import MsetsLower.Lower.Sparse.FinalProbability

/-!
# From the mean of `Gamma` to a fixed sparse regret tail

This module is the final mean-to-tail interface for the sparse construction.
Its sole probabilistic premise is the concrete lower bound for the integral
of the already defined `sparseGamma` under the genuine centered full-table
joint law.
-/

set_option linter.style.header false

namespace MsetsLower.Lower.Sparse

open MsetsLower MeasureTheory ProbabilityTheory
open MsetsLower.Lower
open scoped ENNReal ProbabilityTheory

noncomputable section

/-- A concrete mean lower bound for the observable `Gamma` yields a fixed
deterministic sparse adversary with the manuscript's `2^-10` tail
probability.  Measurability, integrability, the pathwise upper bound, and the
event-to-regret implication are all discharged by existing concrete
certificates. -/
theorem lower_sparse_gammaTail_fixed
    {n n' k r B T : Nat} (P : Policy n k) (hk : 1 <= k)
    (hkn' : k <= n') (hT : 0 < T)
    (eta : Real) (heta0 : 0 <= eta) (heta : eta <= (1 : Real) / 16)
    (q c0 : Nat) (hn' : n' <= n) (hprod : n' = k * r) (hr : 0 < r)
    (sigma : Equiv.Perm (Fin n'))
    (hmean : sparseA / 4 * (k : Real) * (T : Real) <=
      ∫ z, sparseGamma hk eta heta0 heta q c0 hn' hprod hr sigma T z
        ∂sparseJointLaw (sparseHiddenTableMeasure B n)
          (sparseCenteredPolicy P)
          (sparseHiddenTableParameterFamily hk eta heta0 heta
            n' q c0 B) T) :
    HasRegretLowerTail (hkn'.trans hn') P T
      (sparseA * eta * (T : Real) / 8) (1 / (2 : Real) ^ 10) := by
  let mu := sparseJointLaw (sparseHiddenTableMeasure B n)
    (sparseCenteredPolicy P)
    (sparseHiddenTableParameterFamily hk eta heta0 heta n' q c0 B) T
  let Gamma : SparseHiddenTable B n × History n k T -> Real :=
    sparseGamma (B := B) hk eta heta0 heta q c0 hn'
      hprod hr sigma T
  letI : IsProbabilityMeasure mu := by
    dsimp [mu, sparseJointLaw]
    infer_instance
  obtain ⟨_hgroups, hGammaMeasurable, hGammaIntegrable,
      hGammaUpper, _hfixedBridge⟩ :=
    sparseGamma_joint_certificate (B := B) (T := T)
      hk eta heta0 heta q c0 hn' hprod hr sigma (sparseCenteredPolicy P)
  have hkR : 0 < (k : Real) := by exact_mod_cast hk
  have hTR : 0 < (T : Real) := by exact_mod_cast hT
  have hprobability : 1 / (2 : Real) ^ 10 <=
      mu.real {z | sparseA / 8 * (k : Real) * (T : Real) <= Gamma z} := by
    apply sparse_positive_event_probability_two_neg_ten
      mu Gamma hGammaMeasurable hGammaIntegrable hkR hTR
    · simpa [mu, Gamma] using hmean
    · simpa [mu, Gamma] using hGammaUpper
  apply lower_sparse_fixed_tail_of_centeredGamma_event
    P hk hkn' eta heta0 heta q c0 hn' hprod hr sigma
      (1 / (2 : Real) ^ 10)
  simpa [mu, Gamma, sparseCenteredGammaEvent] using hprobability

/-- Larger-horizon form of `lower_sparse_gammaTail_fixed`.  The centered
experiment, `Gamma`, and its mean are all evaluated at the active horizon
`T0`; the concrete fixed table is retained as a zero-suffix adversary through
the requested horizon `T`. -/
theorem lower_sparse_gammaTail_fixed_at_larger_horizon
    {n n' k r B T0 T : Nat} (P : Policy n k) (hk : 1 <= k)
    (hkn' : k <= n') (hT0pos : 0 < T0) (hT0T : T0 <= T)
    (eta : Real) (heta0 : 0 <= eta) (heta : eta <= (1 : Real) / 16)
    (q c0 : Nat) (hn' : n' <= n) (hprod : n' = k * r) (hr : 0 < r)
    (sigma : Equiv.Perm (Fin n'))
    (hmean : sparseA / 4 * (k : Real) * (T0 : Real) <=
      ∫ z, sparseGamma hk eta heta0 heta q c0 hn' hprod hr sigma T0 z
        ∂sparseJointLaw (sparseHiddenTableMeasure B n)
          (sparseCenteredPolicy P)
          (sparseHiddenTableParameterFamily hk eta heta0 heta
            n' q c0 B) T0) :
    HasRegretLowerTail (hkn'.trans hn') P T
      (sparseA * eta * (T0 : Real) / 8) (1 / (2 : Real) ^ 10) := by
  let mu := sparseJointLaw (sparseHiddenTableMeasure B n)
    (sparseCenteredPolicy P)
    (sparseHiddenTableParameterFamily hk eta heta0 heta n' q c0 B) T0
  let Gamma : SparseHiddenTable B n × History n k T0 -> Real :=
    sparseGamma (B := B) hk eta heta0 heta q c0 hn'
      hprod hr sigma T0
  letI : IsProbabilityMeasure mu := by
    dsimp [mu, sparseJointLaw]
    infer_instance
  obtain ⟨_hgroups, hGammaMeasurable, hGammaIntegrable,
      hGammaUpper, _hfixedBridge⟩ :=
    sparseGamma_joint_certificate (B := B) (T := T0)
      hk eta heta0 heta q c0 hn' hprod hr sigma (sparseCenteredPolicy P)
  have hkR : 0 < (k : Real) := by exact_mod_cast hk
  have hT0R : 0 < (T0 : Real) := by exact_mod_cast hT0pos
  have hprobability : 1 / (2 : Real) ^ 10 <=
      mu.real
        {z | sparseA / 8 * (k : Real) * (T0 : Real) <= Gamma z} := by
    apply sparse_positive_event_probability_two_neg_ten
      mu Gamma hGammaMeasurable hGammaIntegrable hkR hT0R
    · simpa [mu, Gamma] using hmean
    · simpa [mu, Gamma] using hGammaUpper
  apply lower_sparse_fixed_tail_at_larger_horizon_of_centeredGamma_event
    P hk hkn' eta heta0 heta q c0 hn' hprod hr sigma hT0T
      (1 / (2 : Real) ^ 10)
  simpa [mu, Gamma, sparseCenteredGammaEvent] using hprobability

#print axioms lower_sparse_gammaTail_fixed
#print axioms lower_sparse_gammaTail_fixed_at_larger_horizon

end

end MsetsLower.Lower.Sparse
