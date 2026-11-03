import MsetsLower.Lower.Sparse.ConcreteDrift
import MsetsLower.Lower.Sparse.ConcreteMixture
import MsetsLower.Lower.Sparse.GammaMean
import MsetsLower.Lower.Sparse.ScoreBiasExpectation

set_option linter.style.header false

/-!
# The concrete mean of the sparse score statistic

This module packages the five estimates in the manuscript's displayed
lower bound for the mean of `Gamma`: changed-law maxima, positive drift,
score bias, average total variation, and the exact expansion of `Gamma`.
-/

namespace MsetsLower.Lower.Sparse

open MsetsLower MeasureTheory ProbabilityTheory
open MsetsLower.Lower
open scoped BigOperators ENNReal ProbabilityTheory

noncomputable section

/-- Expected base-law coordinate score for the concrete sparse parameters. -/
def sparseConcreteCoordinateScoreMean
    {n k T : Nat} (hk : 1 <= k)
    (hr : 2 ^ 32 <= sparseRatio n k)
    (hT : 64 * (n : Real) * (k : Real) * actionCountLog n k <= T)
    (P : Policy n k) (j : Fin (sparseSignalCount n k)) : Real :=
  ∫ z,
    sparseObservableCoordinateScore
      ((sparseConcreteHiddenTableParameterFamily hk hr hT).at z.1)
      (sparseSignalCount_le n k) (sparseQ n k T) (sparseC0 n k T)
      (sparseHiddenTableU z.1) j (sparseT0 n k T) z.2
    ∂sparseConcreteJointLaw hk hr hT P

/-- Expected coordinate score under the literal full-table coordinate change. -/
def sparseConcreteChangedCoordinateScoreMean
    {n k T : Nat} (hk : 1 <= k)
    (hr : 2 ^ 32 <= sparseRatio n k)
    (hT : 64 * (n : Real) * (k : Real) * actionCountLog n k <= T)
    (P : Policy n k) (j : Fin (sparseSignalCount n k)) : Real :=
  ∫ z,
    sparseObservableCoordinateScore
      ((sparseConcreteHiddenTableParameterFamily hk hr hT).at z.1)
      (sparseSignalCount_le n k) (sparseQ n k T) (sparseC0 n k T)
      (sparseHiddenTableU z.1) j (sparseT0 n k T) z.2
    ∂Measure.map
      (sparseHiddenTableCoordinateJointMap sparseA (by norm_num [sparseA])
        (sparseSignalCoordinate (sparseSignalCount_le n k) j))
      (sparseConcreteJointLaw hk hr hT P)

/-- Expected learner score for the concrete sparse parameters. -/
def sparseConcreteLearnerScoreMean
    {n k T : Nat} (hk : 1 <= k)
    (hr : 2 ^ 32 <= sparseRatio n k)
    (hT : 64 * (n : Real) * (k : Real) * actionCountLog n k <= T)
    (P : Policy n k) : Real :=
  ∫ z,
    sparseObservableLearnerScore
      ((sparseConcreteHiddenTableParameterFamily hk hr hT).at z.1)
      (sparseSignalCount n k) (sparseQ n k T) (sparseC0 n k T)
      (sparseHiddenTableU z.1) (sparseT0 n k T) z.2
    ∂sparseConcreteJointLaw hk hr hT P

/-- Expected maximum score in one group of the concrete equipartition. -/
def sparseConcreteGroupScoreMean
    {n k T : Nat} (hk : 1 <= k)
    (hr : 2 ^ 32 <= sparseRatio n k)
    (hT : 64 * (n : Real) * (k : Real) * actionCountLog n k <= T)
    (P : Policy n k)
    (sigma : Equiv.Perm (Fin (sparseSignalCount n k))) (g : Fin k) : Real :=
  ∫ z,
    sparseObservableGroupMax
      (rfl : sparseSignalCount n k = k * sparseRatio n k)
      (lt_of_lt_of_le (by norm_num) hr) sigma
      ((sparseConcreteHiddenTableParameterFamily hk hr hT).at z.1)
      (sparseSignalCount_le n k) (sparseQ n k T) (sparseC0 n k T)
      (sparseHiddenTableU z.1) g (sparseT0 n k T) z.2
    ∂sparseConcreteJointLaw hk hr hT P

/-- Mean of the already-defined observable `Gamma` in the concrete experiment. -/
def sparseConcreteGammaMean
    {n k T : Nat} (hk : 1 <= k)
    (hr : 2 ^ 32 <= sparseRatio n k)
    (hT : 64 * (n : Real) * (k : Real) * actionCountLog n k <= T)
    (P : Policy n k)
    (sigma : Equiv.Perm (Fin (sparseSignalCount n k))) : Real :=
  ∫ z,
    sparseGamma hk (sparseEta n k T) (sparseEta_nonneg n k T)
      ((sparseEta_bounds hk hr hT).1.trans
        (sparseEta_bounds hk hr hT).2.le)
      (sparseQ n k T) (sparseC0 n k T)
      (sparseSignalCount_le n k)
      (rfl : sparseSignalCount n k = k * sparseRatio n k)
      (lt_of_lt_of_le (by norm_num) hr) sigma (sparseT0 n k T) z
    ∂sparseConcreteJointLaw hk hr hT P

/- Assembly of the concrete `Gamma` mean once the full-table score-bias
estimate is available.  Every other premise of the manuscript's displayed
mean computation is discharged here from the actual changed laws. -/
set_option maxHeartbeats 10000000 in
-- Expanding the dependent finite partition and the concrete joint-law aliases is costly.
theorem lower_sparse_concreteGammaMean_of_scoreBias
    {n k T : Nat} (hk : 1 <= k)
    (hr : 2 ^ 32 <= sparseRatio n k)
    (hT : 64 * (n : Real) * (k : Real) * actionCountLog n k <= T)
    (P : Policy n k)
    (hbias :
      -(48 * Real.sqrt sparseRho * (k : Real) *
          (sparseT0 n k T : Real)) <=
        (sparseRatio n k : Real)⁻¹ *
            ∑ j : Fin (sparseSignalCount n k),
              sparseConcreteCoordinateScoreMean hk hr hT
                (sparseCenteredPolicy P) j -
          sparseConcreteLearnerScoreMean hk hr hT
            (sparseCenteredPolicy P)) :
    ∃ sigma : Equiv.Perm (Fin (sparseSignalCount n k)),
      sparseA / 4 * (k : Real) * (sparseT0 n k T : Real) <=
        sparseConcreteGammaMean hk hr hT (sparseCenteredPolicy P) sigma := by
  classical
  let eta := sparseEta n k T
  let q := sparseQ n k T
  let c0 := sparseC0 n k T
  let n' := sparseSignalCount n k
  let r := sparseRatio n k
  let B := sparseBlockCount n k
  let T0 := sparseT0 n k T
  let P0 := sparseCenteredPolicy P
  letI : IsProbabilityMeasure (sparseConcreteJointLaw hk hr hT P0) := by
    dsimp [sparseConcreteJointLaw, sparseJointLaw]
    infer_instance
  letI : IsFiniteMeasure (sparseConcreteJointLaw hk hr hT P0) :=
    inferInstance
  have hrpos : 0 < r := by
    dsimp [r]
    exact lt_of_lt_of_le (by norm_num) hr
  have hellpos : 0 < sparseEll n k T := by
    have hc := sparseC0_ge hk hr hT
    have hcpos : 0 < sparseC0 n k T :=
      lt_of_lt_of_le (by positivity : 0 < 256 * k ^ 2) hc
    simpa [sparseC0] using hcpos
  obtain ⟨sigma, _hcard, htv⟩ :=
    exists_sparseConcrete_goodPartition_average_totalVariationDistance_le
      hk hr hT P0
  refine ⟨sigma, ?_⟩
  apply sparse_changed_group_mean_combination hk
    (rfl : sparseSignalCount n k = k * sparseRatio n k) sigma
    (fun j => sparseConcreteChangedCoordinateScoreMean hk hr hT P0 j)
    (fun j => sparseConcreteCoordinateScoreMean hk hr hT P0 j)
    (fun g => sparseConcreteGroupScoreMean hk hr hT P0 sigma g)
    (fun g => sparseConcreteGroupMixtureTV hk hr hT P0 sigma g)
    (sparseConcreteLearnerScoreMean hk hr hT P0)
    (sparseConcreteGammaMean hk hr hT P0 sigma)
  · intro g
    let G := sparsePartitionGroup
      (rfl : sparseSignalCount n k = k * sparseRatio n k) sigma g
    have hG : G.Nonempty := by
      have hcard : G.card = sparseRatio n k :=
        card_sparsePartitionGroup (rfl : sparseSignalCount n k = k * sparseRatio n k) sigma g
      exact Finset.card_pos.mp (hcard.symm ▸ hrpos)
    letI : Nonempty (↥G) := Finset.nonempty_coe_sort.mpr hG
    let Qg := sparseConcreteGroupMixtureMeasure hk hr hT P0 sigma g
    letI : IsProbabilityMeasure Qg := by
      dsimp [Qg]
      exact sparseConcreteGroupMixtureMeasure_isProbability
        hk hr hT P0 sigma g
    letI : IsFiniteMeasure Qg := inferInstance
    have hQg : Qg = MsetsLower.Probability.averageMeasure
        (fun j : ↥G =>
          Measure.map
            (sparseHiddenTableCoordinateJointMap sparseA
              (by norm_num [sparseA])
              (sparseSignalCoordinate (sparseSignalCount_le n k) j.1))
            (sparseConcreteJointLaw hk hr hT P0)) := by
      dsimp [Qg]
      rw [sparseConcreteGroupMixtureMeasure_eq_average_map]
      simp only [sparseConcreteGroupAverageMap]
      rfl
    letI : IsProbabilityMeasure
        (sparseJointLaw (sparseHiddenTableMeasure (sparseBlockCount n k) n)
          (sparseCenteredPolicy P)
          (sparseHiddenTableParameterFamily hk (sparseEta n k T)
            (sparseEta_nonneg n k T)
            ((sparseEta_bounds hk hr hT).1.trans
              (sparseEta_bounds hk hr hT).2.le)
            (sparseSignalCount n k) (sparseQ n k T) (sparseC0 n k T)
            (sparseBlockCount n k))
          (sparseT0 n k T)) := by
      dsimp [sparseJointLaw]
      infer_instance
    letI : IsFiniteMeasure
        (sparseJointLaw (sparseHiddenTableMeasure (sparseBlockCount n k) n)
          (sparseCenteredPolicy P)
          (sparseHiddenTableParameterFamily hk (sparseEta n k T)
            (sparseEta_nonneg n k T)
            ((sparseEta_bounds hk hr hT).1.trans
              (sparseEta_bounds hk hr hT).2.le)
            (sparseSignalCount n k) (sparseQ n k T) (sparseC0 n k T)
            (sparseBlockCount n k))
          (sparseT0 n k T)) := inferInstance
    have hg := integral_sparseObservableGroupMax_lower
      hk (sparseEta n k T) (sparseEta_nonneg n k T)
      ((sparseEta_bounds hk hr hT).1.trans
        (sparseEta_bounds hk hr hT).2.le)
      (sparseQ n k T) (sparseC0 n k T)
      (sparseSignalCount_le n k)
      (rfl : sparseSignalCount n k = k * sparseRatio n k)
      hrpos sigma P g Qg hQg
    simpa [sparseConcreteChangedCoordinateScoreMean,
      sparseConcreteGroupScoreMean, sparseConcreteGroupMixtureTV,
      sparseConcreteJointLaw, sparseConcreteHiddenTableParameterFamily,
      Qg, P0] using hg
  · simpa [sparseConcreteChangedCoordinateScoreMean,
      sparseConcreteCoordinateScoreMean, sparseConcreteJointLaw,
      sparseConcreteHiddenTableParameterFamily] using
        (lower_positive_drift_concreteFullTable P hk
          (sparseEta n k T) (sparseEta_nonneg n k T)
          ((sparseEta_bounds hk hr hT).1.trans
            (sparseEta_bounds hk hr hT).2.le)
          (sparseSignalCount_le n k) hrpos hr hellpos
          (rfl : sparseSignalCount n k = k * sparseRatio n k)
          (rfl : sparseQ n k T = sparseRatio n k * sparseEll n k T)
          (rfl : sparseC0 n k T = 8 * sparseEll n k T)
          (by simp [sparseT0, Nat.mul_comm]))
  · simpa [P0] using hbias
  · simpa [P0] using htv
  · have hgamma := integral_sparseGamma_eq_groupSum_sub_learner
      (B := sparseBlockCount n k) (T := sparseT0 n k T)
      hk (sparseEta n k T) (sparseEta_nonneg n k T)
      ((sparseEta_bounds hk hr hT).1.trans
        (sparseEta_bounds hk hr hT).2.le)
      (sparseQ n k T) (sparseC0 n k T)
      (sparseSignalCount_le n k)
      (rfl : sparseSignalCount n k = k * sparseRatio n k)
      hrpos sigma P0
    simpa [sparseConcreteGammaMean, sparseConcreteGroupScoreMean,
      sparseConcreteLearnerScoreMean, sparseConcreteJointLaw,
      sparseConcreteHiddenTableParameterFamily, P0] using hgamma.ge

#print axioms lower_sparse_concreteGammaMean_of_scoreBias

/-- The manuscript's concrete lower bound for the mean of `Gamma`, with the
full-table score-bias estimate discharged from the genuine joint law. -/
theorem lower_sparse_concreteGammaMean
    {n k T : Nat} (hk : 1 <= k)
    (hr : 2 ^ 32 <= sparseRatio n k)
    (hT : 64 * (n : Real) * (k : Real) * actionCountLog n k <= T)
    (P : Policy n k) :
    ∃ sigma : Equiv.Perm (Fin (sparseSignalCount n k)),
      sparseA / 4 * (k : Real) * (sparseT0 n k T : Real) <=
        sparseConcreteGammaMean hk hr hT (sparseCenteredPolicy P) sigma := by
  have hkposNat : 0 < k := lt_of_lt_of_le Nat.zero_lt_one hk
  have hkpos : 0 < (k : Real) := by exact_mod_cast hkposNat
  have hrone : 1 <= sparseRatio n k :=
    (by norm_num : 1 <= 2 ^ 32).trans hr
  have hrpos : 0 < sparseRatio n k := lt_of_lt_of_le Nat.zero_lt_one hrone
  have hcNat := sparseC0_ge hk hr hT
  have hcposNat : 0 < sparseC0 n k T :=
    lt_of_lt_of_le (by positivity : 0 < 256 * k ^ 2) hcNat
  have hcpos : 0 < (sparseC0 n k T : Real) := by exact_mod_cast hcposNat
  have hellpos : 0 < sparseEll n k T := by
    simpa [sparseC0] using hcposNat
  have hq : 0 < sparseQ n k T := by
    exact Nat.mul_pos hrpos hellpos
  have hquot : 0 <= sparseRho / (sparseC0 n k T : Real) :=
    div_nonneg sparseRho_pos.le hcpos.le
  have hrhoeq :
      sparseRho = sparseEta n k T ^ 2 * (sparseC0 n k T : Real) /
        (k : Real) ^ 2 := by
    rw [sparseEta, mul_pow, Real.sq_sqrt hquot]
    field_simp [ne_of_gt hkpos, ne_of_gt hcpos]
  have hcount :
      sparseBlockCount n k * sparseSignalCount n k * sparseC0 n k T =
        8 * k * sparseT0 n k T := by
    simp only [sparseSignalCount, sparseC0, sparseQ, sparseT0]
    ring
  have hbias := lower_score_bias_fullTable
    (B := sparseBlockCount n k) (n' := sparseSignalCount n k)
    (r := sparseRatio n k) (q := sparseQ n k T)
    (c0 := sparseC0 n k T) (T0 := sparseT0 n k T)
    (sparseCenteredPolicy P) hk
    (sparseEta n k T) (sparseEta_nonneg n k T)
    ((sparseEta_bounds hk hr hT).1.trans
      (sparseEta_bounds hk hr hT).2.le)
    hq (sparseSignalCount_le n k) hrone sparseRho_pos.le hrhoeq
    (by simp [sparseT0, Nat.mul_comm])
    (rfl : sparseSignalCount n k = k * sparseRatio n k) hcount
  apply lower_sparse_concreteGammaMean_of_scoreBias hk hr hT P
  simpa [sparseConcreteCoordinateScoreMean, sparseConcreteLearnerScoreMean,
    sparseConcreteJointLaw, sparseConcreteHiddenTableParameterFamily] using hbias

#print axioms lower_sparse_concreteGammaMean

end

end MsetsLower.Lower.Sparse
