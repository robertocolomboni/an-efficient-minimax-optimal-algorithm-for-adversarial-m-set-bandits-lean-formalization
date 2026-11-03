import CoefficientOne.Sampling.RestrictedLawRecursion
import CoefficientOne.Sampling.VarianceDrop
import CoefficientOne.Sampling.Coarea

/-! # The covariance and variance of the actual residual law

The law on ambient subsets is transported to the fixed-rank law on the
remaining subtype. No covariance formula or conditional law is assumed.
-/

open scoped BigOperators
open EffectiveResistance Matrix MeasureTheory

namespace CoefficientOne.Sampling
noncomputable section

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

def liftResidualSubset (R : Finset ι) (S : Finset R) : Finset ι :=
  S.map (Function.Embedding.subtype (fun i => i ∈ R))

theorem liftResidualSubset_univ (R : Finset ι) :
    liftResidualSubset R Finset.univ = R := by
  ext i
  simp [liftResidualSubset]

def restrictedSum (w : ι → ℝ) (R : Finset ι) (r : ℕ) (f : Finset ι → ℝ) : ℝ :=
  ∑ S, restrictedMass w R r S * f S

theorem restrictedSum_eq_subtype (w : ι → ℝ)
    (R : Finset ι) (r : ℕ) (f : Finset ι → ℝ) :
    restrictedSum w R r f =
      expectation (fun i : R => w i.val) r (fun S => f (liftResidualSubset R S.val)) := by
  have hsum : restrictedSum w R r f =
      ∑ S ∈ R.powersetCard r, subsetWeight w S / restrictedElementary w R r * f S := by
    simp only [restrictedSum, restrictedMass, ite_mul, zero_mul,
      Finset.sum_ite_mem, Finset.univ_inter]
  rw [hsum]
  have hR := liftResidualSubset_univ R
  unfold liftResidualSubset at hR
  have hp : R.powersetCard r = ((Finset.univ : Finset R).powersetCard r).map
      (Finset.mapEmbedding (Function.Embedding.subtype (fun i => i ∈ R))).toEmbedding := by
    rw [← Finset.powersetCard_map, hR]
  rw [hp, Finset.sum_map]
  rw [restrictedElementary_eq_elementarySum_subtype]
  unfold expectation subsetProbability
  change (∑ S ∈ (Finset.univ : Finset R).powersetCard r,
    subsetWeight w (liftResidualSubset R S) / elementarySum (fun i : R => w i.val) r *
      f (liftResidualSubset R S)) = _
  have hwmap (S : Finset R) : subsetWeight w (liftResidualSubset R S) =
      subsetWeight (fun i : R => w i.val) S := by
    simp [subsetWeight, liftResidualSubset]
  simp_rw [hwmap]
  apply Finset.sum_subtype
  intro S
  simp only [Finset.mem_powersetCard, Finset.subset_univ, true_and]

theorem restrictedExpectation_eq_subtype (w : ι → ℝ) (hw : ∀ i, 0 < w i)
    (R : Finset ι) (r : ℕ) (hr : r ≤ R.card) (f : Finset ι → ℝ) :
    lawExpectation (restrictedLaw w hw R r hr) f =
      expectation (fun i : R => w i.val) r (fun S => f (liftResidualSubset R S.val)) :=
  restrictedSum_eq_subtype w R r f

@[simp] theorem indicator_liftResidualSubset (R : Finset ι) (S : Finset R) (i : R) :
    indicator i.val (liftResidualSubset R S) = indicator i S := by
  simp [indicator, liftResidualSubset]

theorem liftResidualSubset_subset (R : Finset ι) (S : Finset R) :
    liftResidualSubset R S ⊆ R := by
  intro i hi
  obtain ⟨j, _, rfl⟩ := Finset.mem_map.mp hi
  exact j.property

theorem restrictedSum_congr (w : ι → ℝ) (R : Finset ι) (r : ℕ)
    (f g : Finset ι → ℝ) (hfg : ∀ S ∈ R.powersetCard r, f S = g S) :
    restrictedSum w R r f = restrictedSum w R r g := by
  apply Finset.sum_congr rfl
  intro S _
  by_cases hS : S ∈ R.powersetCard r
  · rw [hfg S hS]
  · simp [restrictedMass, hS]

def residualMean (w : ι → ℝ) (R : Finset ι) (r : ℕ) (i : ι) : ℝ :=
  restrictedSum w R r (fun S => indicator i S)

def residualCovariance (w : ι → ℝ) (R : Finset ι) (r : ℕ) : Matrix ι ι ℝ :=
  fun i j => restrictedSum w R r (fun S =>
    (indicator i S - residualMean w R r i) * (indicator j S - residualMean w R r j))

theorem residualMean_subtype (w : ι → ℝ) (R : Finset ι) (r : ℕ) (i : R) :
    residualMean w R r i.val = inclusionMean (fun j : R => w j.val) r i := by
  rw [residualMean, restrictedSum_eq_subtype]
  simp only [indicator_liftResidualSubset, inclusionMean]

theorem residualCovariance_subtype (w : ι → ℝ) (R : Finset ι) (r : ℕ) (i j : R) :
    residualCovariance w R r i.val j.val = covarianceMatrix (fun j : R => w j.val) r i j := by
  rw [residualCovariance, restrictedSum_eq_subtype]
  simp only [indicator_liftResidualSubset, residualMean_subtype, covarianceMatrix]

theorem residualMean_notMem (w : ι → ℝ) (R : Finset ι) (r : ℕ) (i : ι) (hi : i ∉ R) :
    residualMean w R r i = 0 := by
  unfold residualMean
  have he : restrictedSum w R r (fun S => indicator i S) = restrictedSum w R r (fun _ => 0) := by
    apply restrictedSum_congr
    intro S hS
    have hn : i ∉ S := fun h => hi ((Finset.mem_powersetCard.mp hS).1 h)
    simp [indicator, hn]
  rw [he]
  simp [restrictedSum]

theorem residualCovariance_notMem_left (w : ι → ℝ) (R : Finset ι) (r : ℕ)
    (i j : ι) (hi : i ∉ R) : residualCovariance w R r i j = 0 := by
  unfold residualCovariance
  rw [residualMean_notMem w R r i hi]
  have he : restrictedSum w R r (fun S =>
      (indicator i S - 0) * (indicator j S - residualMean w R r j)) =
      restrictedSum w R r (fun _ => 0) := by
    apply restrictedSum_congr
    intro S hS
    have hn : i ∉ S := fun h => hi ((Finset.mem_powersetCard.mp hS).1 h)
    simp [indicator, hn]
  rw [he]
  simp [restrictedSum]

theorem residualCovariance_comm (w : ι → ℝ) (R : Finset ι) (r : ℕ) (i j : ι) :
    residualCovariance w R r i j = residualCovariance w R r j i := by
  unfold residualCovariance
  simp only [mul_comm]

theorem residualCovariance_notMem_right (w : ι → ℝ) (R : Finset ι) (r : ℕ)
    (i j : ι) (hj : j ∉ R) : residualCovariance w R r i j = 0 := by
  rw [residualCovariance_comm]
  exact residualCovariance_notMem_left w R r j i hj

@[simp] theorem restrictedSum_zero (w : ι → ℝ) (R : Finset ι) (f : Finset ι → ℝ) :
    restrictedSum w R 0 f = f ∅ := by
  simp [restrictedSum, restrictedMass_zero, ite_mul]

@[simp] theorem restrictedSum_full (w : ι → ℝ) (hw : ∀ i, 0 < w i)
    (R : Finset ι) (f : Finset ι → ℝ) : restrictedSum w R R.card f = f R := by
  simp [restrictedSum, restrictedMass_full w hw, ite_mul]

@[simp] theorem residualCovariance_zero (w : ι → ℝ) (R : Finset ι) :
    residualCovariance w R 0 = 0 := by
  ext i j
  simp only [residualCovariance, residualMean, restrictedSum_zero, sub_self, mul_zero,
    Matrix.zero_apply]

@[simp] theorem residualCovariance_full (w : ι → ℝ) (hw : ∀ i, 0 < w i) (R : Finset ι) :
    residualCovariance w R R.card = 0 := by
  ext i j
  simp only [residualCovariance, residualMean, restrictedSum_full w hw, sub_self, mul_zero,
    Matrix.zero_apply]

theorem residualCovariance_of_card_lt (w : ι → ℝ) (R : Finset ι) (r : ℕ) (hr : R.card < r) :
    residualCovariance w R r = 0 := by
  ext i j
  simp [residualCovariance, restrictedSum, restrictedMass, Finset.powersetCard_eq_empty.mpr hr]

def subsetLinearStatistic (a : ι → ℝ) (S : Finset ι) : ℝ :=
  ∑ i ∈ S, a i

theorem subsetLinearStatistic_eq_indicator (a : ι → ℝ) (S : Finset ι) :
    subsetLinearStatistic a S = ∑ i, a i * indicator i S := by
  simp [subsetLinearStatistic, indicator]

theorem subsetLinearStatistic_lift (R : Finset ι) (a : ι → ℝ) (S : Finset R) :
    subsetLinearStatistic a (liftResidualSubset R S) =
      subsetLinearStatistic (fun i : R => a i.val) S := by
  simp [subsetLinearStatistic, liftResidualSubset]

def residualVariance (w : ι → ℝ) (hw : ∀ i, 0 < w i)
    (R : Finset ι) (r : ℕ) (hr : r ≤ R.card) (a : ι → ℝ) : ℝ :=
  lawVariance (restrictedLaw w hw R r hr) (subsetLinearStatistic a)

theorem residualVariance_eq_subtype (w : ι → ℝ) (hw : ∀ i, 0 < w i)
    (R : Finset ι) (r : ℕ) (hr : r ≤ R.card) (a : ι → ℝ) :
    residualVariance w hw R r hr a =
      quadraticForm (covarianceMatrix (fun i : R => w i.val) r) (fun i : R => a i.val) := by
  unfold residualVariance lawVariance
  rw [restrictedExpectation_eq_subtype, restrictedExpectation_eq_subtype]
  change (expectation (fun i : R => w i.val) r (fun S =>
    (subsetLinearStatistic a (liftResidualSubset R S.val) -
      expectation (fun i : R => w i.val) r
        (fun T => subsetLinearStatistic a (liftResidualSubset R T.val))) ^ 2)) = _
  simp_rw [subsetLinearStatistic_lift, subsetLinearStatistic_eq_indicator]
  exact lawVariance_linearStatistic
    (externalFieldLaw (fun i : R => w i.val) (fun i => hw i.val) (by simpa using hr))
    (fun i : R => a i.val)

theorem residualVariance_nonneg (w : ι → ℝ) (hw : ∀ i, 0 < w i)
    (R : Finset ι) (r : ℕ) (hr : r ≤ R.card) (a : ι → ℝ) :
    0 ≤ residualVariance w hw R r hr a := by
  apply Finset.sum_nonneg
  intro S _
  exact mul_nonneg (law_nonneg _ _) (sq_nonneg _)

end
end CoefficientOne.Sampling
