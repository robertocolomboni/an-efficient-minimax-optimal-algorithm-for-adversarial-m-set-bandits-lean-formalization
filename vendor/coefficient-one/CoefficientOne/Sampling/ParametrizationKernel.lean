import CoefficientOne.Sampling.LogPartition
import CoefficientOne.ExchangeRatio

/-!
# The covariance kernel from full support and subset exchanges

This is the variance-zero argument in the parametrization lemma. It does not
deduce nondegeneracy from the stronger covariance comparison theorem.
-/

open scoped BigOperators Topology
open EffectiveResistance

namespace CoefficientOne.Sampling
noncomputable section

variable {ι : Type*} [Fintype ι] [DecidableEq ι] {k : ℕ}

theorem exists_exchange_background (hkpos : 1 ≤ k) (hktop : k < Fintype.card ι)
    (i j : ι) (hij : i ≠ j) :
    ∃ T : Finset ι, i ∉ T ∧ j ∉ T ∧ T.card + 1 = k := by
  let A := ((Finset.univ : Finset ι).erase i).erase j
  have hj : j ∈ (Finset.univ : Finset ι).erase i := by simp [hij, hij.symm]
  have hcard : A.card = Fintype.card ι - 2 := by
    simp [A, Finset.card_erase_of_mem hj, Finset.card_erase_of_mem (Finset.mem_univ i)]
    omega
  have hfit : k - 1 ≤ A.card := by rw [hcard]; omega
  obtain ⟨T, hTA, hT⟩ := Finset.exists_subset_card_eq hfit
  refine ⟨T, ?_, ?_, by omega⟩
  · intro hi
    have := hTA hi
    simpa [A] using this
  · intro hjT
    have := hTA hjT
    simpa [A] using this

theorem constant_subsetStatistic_implies_constant
    (hkpos : 1 ≤ k) (hktop : k < Fintype.card ι) (u : ι → ℝ) (c : ℝ)
    (hu : ∀ S : RankSubset ι k, subsetStatistic S.val u = c) :
    ∀ i j, u i = u j := by
  intro i j
  by_cases hij : i = j
  · rw [hij]
  obtain ⟨T, hi, hj, hT⟩ := exists_exchange_background hkpos hktop i j hij
  have hleft := hu (exchangeInsert k T hT i hi)
  have hright := hu (exchangeInsert k T hT j hj)
  simp only [subsetStatistic_apply, exchangeInsert, Finset.sum_insert hi] at hleft
  simp only [subsetStatistic_apply, exchangeInsert, Finset.sum_insert hj] at hright
  linarith

theorem centeredStatistic_exp (θ u : ι → ℝ) (S : RankSubset ι k) :
    centeredLinearStatistic (fun i => Real.exp (θ i)) k u S =
      subsetStatistic S.val u - ∑ i, exponentialMean k θ i * u i := by
  rw [subsetStatistic_eq_indicator]
  simp only [centeredLinearStatistic, centeredIndicator, mul_sub, Finset.sum_sub_distrib,
    exponentialMean]
  congr 1 <;> apply Finset.sum_congr rfl <;> intro i _ <;> ring

theorem covariance_quadratic_pos_of_nonconstant
    (hkpos : 1 ≤ k) (hktop : k < Fintype.card ι) (θ u : ι → ℝ)
    (hu : ¬ ∀ i j, u i = u j) :
    0 < quadraticForm (covarianceMatrix (fun i => Real.exp (θ i)) k) u := by
  by_contra hnot
  have hqzero : quadraticForm (covarianceMatrix (fun i => Real.exp (θ i)) k) u = 0 :=
    le_antisymm (le_of_not_gt hnot)
      (covariance_quadratic_nonnegative _ (fun i => Real.exp_pos (θ i)) hktop.le u)
  rw [quadraticForm_covariance, expectation] at hqzero
  have hall : ∀ S : RankSubset ι k,
      centeredLinearStatistic (fun i => Real.exp (θ i)) k u S = 0 := by
    intro S
    have hterm : subsetProbability (fun i => Real.exp (θ i)) k S *
        centeredLinearStatistic (fun i => Real.exp (θ i)) k u S ^ 2 = 0 :=
      (Finset.sum_eq_zero_iff_of_nonneg (fun T _ =>
        mul_nonneg (subsetProbability_pos _ (fun i => Real.exp_pos (θ i)) hktop.le T).le
          (sq_nonneg _))).mp hqzero S (Finset.mem_univ S)
    have hs := (mul_eq_zero.mp hterm).resolve_left
      (subsetProbability_pos _ (fun i => Real.exp_pos (θ i)) hktop.le S).ne'
    exact sq_eq_zero_iff.mp hs
  apply hu
  apply constant_subsetStatistic_implies_constant hkpos hktop u
    (∑ i, exponentialMean k θ i * u i)
  intro S
  have h := hall S
  rw [centeredStatistic_exp] at h
  linarith

theorem zeroSum_constant_eq_zero (u : ι → ℝ) (hsum : ∑ i, u i = 0)
    (hc : ∀ i j, u i = u j) : u = 0 := by
  funext i
  have hni : (Fintype.card ι : ℝ) ≠ 0 := by
    haveI : Nonempty ι := ⟨i⟩
    exact_mod_cast Fintype.card_ne_zero
  have hsum' : (Fintype.card ι : ℝ) * u i = 0 := by
    calc
      (Fintype.card ι : ℝ) * u i = ∑ j : ι, u i := by simp
      _ = ∑ j : ι, u j := Finset.sum_congr rfl (fun j _ => hc i j)
      _ = 0 := hsum
  exact (mul_eq_zero.mp hsum').resolve_left hni

theorem covariance_quadratic_pos_zeroSum
    (hkpos : 1 ≤ k) (hktop : k < Fintype.card ι) (θ u : ι → ℝ)
    (hsum : ∑ i, u i = 0) (hu : u ≠ 0) :
    0 < quadraticForm (covarianceMatrix (fun i => Real.exp (θ i)) k) u := by
  apply covariance_quadratic_pos_of_nonconstant hkpos hktop θ u
  intro hc
  exact hu (zeroSum_constant_eq_zero u hsum hc)

theorem covariance_mulVec_eq_zero_iff_constant
    (hkpos : 1 ≤ k) (hktop : k < Fintype.card ι) (θ u : ι → ℝ) :
    (covarianceMatrix (fun i => Real.exp (θ i)) k).mulVec u = 0 ↔ ∀ i j, u i = u j := by
  constructor
  · intro hzero
    by_contra hnc
    have hh := covariance_quadratic_pos_of_nonconstant hkpos hktop θ u hnc
    simp [quadraticForm, hzero] at hh
  · intro hc
    funext i
    change ∑ j, covarianceMatrix (fun l => Real.exp (θ l)) k i j * u j = 0
    calc
      (∑ j, covarianceMatrix (fun l => Real.exp (θ l)) k i j * u j) =
          (∑ j, covarianceMatrix (fun l => Real.exp (θ l)) k i j) * u i := by
        rw [Finset.sum_mul]
        apply Finset.sum_congr rfl
        intro j _
        rw [hc j i]
      _ = 0 := by rw [covariance_rowSum_zero _ (fun l => Real.exp_pos (θ l)) hktop.le i, zero_mul]

end
end CoefficientOne.Sampling
