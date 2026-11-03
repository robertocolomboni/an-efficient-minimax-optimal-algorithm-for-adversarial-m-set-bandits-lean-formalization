import CoefficientOne.Sampling.ExponentialFamily

/-!
# Differential identities for the finite log partition function

All derivatives are computed from the actual finite sum defining the law.
-/

open scoped BigOperators Topology
open EffectiveResistance

namespace CoefficientOne.Sampling
noncomputable section

variable {ι : Type*} [Fintype ι] [DecidableEq ι] {k : ℕ}

def subsetStatistic (S : Finset ι) : (ι → ℝ) →L[ℝ] ℝ :=
  ∑ i ∈ S, ContinuousLinearMap.proj i

@[simp] theorem subsetStatistic_apply (S : Finset ι) (θ : ι → ℝ) :
    subsetStatistic S θ = ∑ i ∈ S, θ i := by simp [subsetStatistic]

def partitionFunction (k : ℕ) (θ : ι → ℝ) : ℝ :=
  ∑ S : RankSubset ι k, Real.exp (subsetStatistic S.val θ)

def logPartition (k : ℕ) (θ : ι → ℝ) : ℝ := Real.log (partitionFunction k θ)

def partitionDerivative (k : ℕ) (θ : ι → ℝ) : (ι → ℝ) →L[ℝ] ℝ :=
  ∑ S : RankSubset ι k, Real.exp (subsetStatistic S.val θ) • subsetStatistic S.val

theorem partitionFunction_eq_elementarySum (θ : ι → ℝ) :
    partitionFunction k θ = elementarySum (fun i => Real.exp (θ i)) k := by
  simp [partitionFunction, elementarySum, subsetWeight_exp]

theorem partitionFunction_pos (hk : k ≤ Fintype.card ι) (θ : ι → ℝ) :
    0 < partitionFunction k θ := by
  rw [partitionFunction_eq_elementarySum]
  exact elementarySum_pos _ (fun i => Real.exp_pos (θ i)) hk

theorem partitionFunction_hasFDerivAt (θ : ι → ℝ) :
    HasFDerivAt (partitionFunction k) (partitionDerivative k θ) θ := by
  unfold partitionFunction partitionDerivative
  apply HasFDerivAt.fun_sum
  intro S _
  exact (subsetStatistic S.val).hasFDerivAt.exp

theorem partitionFunction_contDiff : ContDiff ℝ ⊤ (partitionFunction (ι := ι) k) := by
  unfold partitionFunction
  fun_prop

theorem logPartition_contDiff (hk : k ≤ Fintype.card ι) :
    ContDiff ℝ ⊤ (logPartition (ι := ι) k) := by
  exact partitionFunction_contDiff.log (fun θ => (partitionFunction_pos hk θ).ne')

theorem logPartition_hasFDerivAt (hk : k ≤ Fintype.card ι) (θ : ι → ℝ) :
    HasFDerivAt (logPartition k)
      ((partitionFunction k θ)⁻¹ • partitionDerivative k θ) θ :=
  (partitionFunction_hasFDerivAt θ).log (partitionFunction_pos hk θ).ne'

def exponentialMean (k : ℕ) (θ : ι → ℝ) : ι → ℝ :=
  inclusionMean (fun i => Real.exp (θ i)) k

theorem exponentialMean_contDiff (hk : k ≤ Fintype.card ι) :
    ContDiff ℝ ⊤ (exponentialMean (ι := ι) k) := by
  unfold exponentialMean inclusionMean expectation subsetProbability
  simp_rw [← partitionFunction_eq_elementarySum, subsetWeight_exp]
  apply contDiff_pi.2
  intro i
  apply ContDiff.sum
  intro S _
  apply ContDiff.mul _ contDiff_const
  convert ((subsetStatistic S.val).contDiff.exp).div partitionFunction_contDiff
    (fun θ => (partitionFunction_pos hk θ).ne') using 1 <;>
    first | rfl | (ext θ; simp)

theorem subsetStatistic_eq_indicator (S : Finset ι) (u : ι → ℝ) :
    subsetStatistic S u = ∑ i, indicator i S * u i := by
  simp [indicator]

@[simp] theorem partitionDerivative_apply (θ u : ι → ℝ) :
    partitionDerivative k θ u = ∑ S : RankSubset ι k,
      Real.exp (subsetStatistic S.val θ) * subsetStatistic S.val u := by
  simp [partitionDerivative]

theorem exponentialMean_dot (θ u : ι → ℝ) :
    ∑ i, exponentialMean k θ i * u i = ∑ S : RankSubset ι k,
      subsetProbability (fun i => Real.exp (θ i)) k S * subsetStatistic S.val u := by
  simp only [exponentialMean, inclusionMean, expectation, Finset.sum_mul]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro S _
  rw [subsetStatistic_eq_indicator, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i _
  ring

theorem logPartition_derivative_apply (θ u : ι → ℝ) :
    ((partitionFunction k θ)⁻¹ • partitionDerivative k θ) u =
      ∑ i, exponentialMean k θ i * u i := by
  rw [ContinuousLinearMap.smul_apply, smul_eq_mul, partitionDerivative_apply,
    exponentialMean_dot, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro S _
  rw [subsetProbability, ← partitionFunction_eq_elementarySum, subsetWeight_exp,
    ← subsetStatistic_apply]
  ring

def meanLinear (k : ℕ) (θ : ι → ℝ) : (ι → ℝ) →L[ℝ] ℝ :=
  ∑ i, exponentialMean k θ i • ContinuousLinearMap.proj i

@[simp] theorem meanLinear_apply (θ u : ι → ℝ) :
    meanLinear k θ u = ∑ i, exponentialMean k θ i * u i := by simp [meanLinear]

theorem logPartition_gradient (hk : k ≤ Fintype.card ι) (θ : ι → ℝ) :
    HasFDerivAt (logPartition k) (meanLinear k θ) θ := by
  convert logPartition_hasFDerivAt hk θ using 1
  ext u
  simpa only [meanLinear_apply] using (logPartition_derivative_apply (k := k) θ u).symm

def probabilityDerivative (k : ℕ) (θ : ι → ℝ) (S : RankSubset ι k) :
    (ι → ℝ) →L[ℝ] ℝ :=
  subsetProbability (fun i => Real.exp (θ i)) k S • (subsetStatistic S.val - meanLinear k θ)

theorem subsetProbability_exp_hasFDerivAt (hk : k ≤ Fintype.card ι)
    (θ : ι → ℝ) (S : RankSubset ι k) :
    HasFDerivAt (fun t : ι → ℝ => subsetProbability (fun i => Real.exp (t i)) k S)
      (probabilityDerivative k θ S) θ := by
  have hf := (subsetStatistic S.val).hasFDerivAt.exp (x := θ)
  have hg := (hasDerivAt_inv (partitionFunction_pos hk θ).ne').comp_hasFDerivAt θ
    (partitionFunction_hasFDerivAt θ)
  have hd := hf.mul hg
  convert hd using 1 <;> try rfl
  · ext t
    simp [subsetProbability, subsetWeight_exp, partitionFunction_eq_elementarySum,
      div_eq_mul_inv]
  · ext u
    simp only [probabilityDerivative, ContinuousLinearMap.smul_apply,
      ContinuousLinearMap.sub_apply, smul_eq_mul, ContinuousLinearMap.add_apply]
    rw [meanLinear_apply, ← logPartition_derivative_apply]
    simp only [ContinuousLinearMap.smul_apply, smul_eq_mul]
    rw [subsetProbability, ← partitionFunction_eq_elementarySum, subsetWeight_exp,
      ← subsetStatistic_apply]
    simp only [Function.comp_apply, inv_pow]
    ring

def meanDerivative (k : ℕ) (θ : ι → ℝ) : (ι → ℝ) →L[ℝ] (ι → ℝ) :=
  ContinuousLinearMap.pi fun i =>
    ∑ S : RankSubset ι k, indicator i S.val • probabilityDerivative k θ S

theorem exponentialMean_hasFDerivAt (hk : k ≤ Fintype.card ι) (θ : ι → ℝ) :
    HasFDerivAt (exponentialMean k) (meanDerivative k θ) θ := by
  apply hasFDerivAt_pi.2
  intro i
  have hh := HasFDerivAt.fun_sum (u := Finset.univ)
    (fun S _ => (subsetProbability_exp_hasFDerivAt hk θ S).const_smul (indicator i S.val))
  convert hh using 1
  ext t
  simp [exponentialMean, inclusionMean, expectation, mul_comm]

theorem covariance_eq_secondMoment_sub (w : ι → ℝ) (hw : ∀ i, 0 < w i)
    (hk : k ≤ Fintype.card ι) (i j : ι) :
    covarianceMatrix w k i j =
      (∑ S : RankSubset ι k, subsetProbability w k S * indicator i S.val * indicator j S.val) -
        inclusionMean w k i * inclusionMean w k j := by
  unfold covarianceMatrix expectation
  calc
    (∑ S : RankSubset ι k, subsetProbability w k S *
        ((indicator i S.val - inclusionMean w k i) *
          (indicator j S.val - inclusionMean w k j))) =
        ∑ S : RankSubset ι k,
          (subsetProbability w k S * indicator i S.val * indicator j S.val -
          inclusionMean w k j * (subsetProbability w k S * indicator i S.val) -
          inclusionMean w k i * (subsetProbability w k S * indicator j S.val) +
          (inclusionMean w k i * inclusionMean w k j) * subsetProbability w k S) := by
      apply Finset.sum_congr rfl
      intro S _
      ring
    _ = _ := by
      simp only [Finset.sum_add_distrib, Finset.sum_sub_distrib, ← Finset.mul_sum,
        sum_subsetProbability w hw hk, mul_one]
      change _ - inclusionMean w k j * inclusionMean w k i -
        inclusionMean w k i * inclusionMean w k j +
        inclusionMean w k i * inclusionMean w k j = _
      ring

@[simp] theorem subsetStatistic_single (S : Finset ι) (i : ι) :
    subsetStatistic S (Pi.single i 1) = indicator i S := by
  classical
  simp [subsetStatistic, indicator, Pi.single_apply, eq_comm]

@[simp] theorem meanLinear_single (θ : ι → ℝ) (i : ι) :
    meanLinear k θ (Pi.single i 1) = exponentialMean k θ i := by
  simp [meanLinear, Pi.single_apply]

theorem meanDerivative_single (hk : k ≤ Fintype.card ι) (θ : ι → ℝ) (i j : ι) :
    meanDerivative k θ (Pi.single j 1) i = covarianceMatrix (fun l => Real.exp (θ l)) k i j := by
  simp only [meanDerivative, ContinuousLinearMap.pi_apply, ContinuousLinearMap.sum_apply,
    smul_apply, smul_eq_mul, probabilityDerivative, sub_apply,
    subsetStatistic_single, meanLinear_single]
  rw [covariance_eq_secondMoment_sub _ (fun l => Real.exp_pos (θ l)) hk]
  calc
    (∑ S : RankSubset ι k, indicator i S.val *
        (subsetProbability (fun l => Real.exp (θ l)) k S *
          (indicator j S.val - exponentialMean k θ j))) =
      (∑ S : RankSubset ι k,
        subsetProbability (fun l => Real.exp (θ l)) k S * indicator i S.val * indicator j S.val) -
      exponentialMean k θ j * (∑ S : RankSubset ι k,
        subsetProbability (fun l => Real.exp (θ l)) k S * indicator i S.val) := by
      rw [Finset.mul_sum, ← Finset.sum_sub_distrib]
      apply Finset.sum_congr rfl
      intro S _
      ring
    _ = _ := by
      change _ - exponentialMean k θ j * exponentialMean k θ i = _
      unfold exponentialMean
      ring

/-- The Jacobian of the marginal map is the actual covariance matrix. -/
theorem meanDerivative_apply (hk : k ≤ Fintype.card ι) (θ u : ι → ℝ) (i : ι) :
    meanDerivative k θ u i = (covarianceMatrix (fun l => Real.exp (θ l)) k).mulVec u i := by
  have hh := linearFunctional_eq_coordinate_sum
    ((ContinuousLinearMap.proj i).comp (meanDerivative k θ)).toLinearMap u
  change meanDerivative k θ u i = ∑ j, u j * meanDerivative k θ (Pi.single j 1) i at hh
  rw [hh]
  simp_rw [meanDerivative_single hk θ]
  simp [Matrix.mulVec, dotProduct, mul_comm]

theorem exponentialMean_fderiv_eq_covariance (hk : k ≤ Fintype.card ι) (θ u : ι → ℝ) :
    fderiv ℝ (exponentialMean k) θ u = (covarianceMatrix (fun l => Real.exp (θ l)) k).mulVec u := by
  rw [(exponentialMean_hasFDerivAt hk θ).fderiv]
  funext i
  exact meanDerivative_apply hk θ u i

end
end CoefficientOne.Sampling
