import CoefficientOne.CovarianceBridge
import CoefficientOne.ElementaryBridge

/-!
# The actual uniform fixed-rank law

The weights are all one. Permuting the finite sample space proves equality of
marginals and of distinct off-diagonal covariance entries. The fixed-rank sum
and the zero row sums then give the formulas in Appendix E.3, at every rank.
-/

open scoped BigOperators
open Matrix EffectiveResistance

namespace CoefficientOne
noncomputable section

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

def uniformRankSubsetEquiv (e : Equiv.Perm ι) (m : ℕ) :
    RankSubset ι m ≃ RankSubset ι m :=
  e.finsetCongr.subtypeEquiv (by intro S; simp)

omit [DecidableEq ι] in
theorem uniform_expectation_permutation (e : Equiv.Perm ι) (m : ℕ)
    (f : RankSubset ι m → ℝ) :
    expectation (fun _ : ι => 1) m (fun S => f (uniformRankSubsetEquiv e m S)) =
      expectation (fun _ : ι => 1) m f := by
  unfold expectation
  simpa [subsetProbability, subsetWeight] using
    (uniformRankSubsetEquiv e m).sum_comp
      (fun S => (1 / elementarySum (fun _ : ι => 1) m) * f S)

theorem uniform_indicator_permutation (e : Equiv.Perm ι) (m : ℕ)
    (S : RankSubset ι m) (i : ι) :
    indicator (e i) (uniformRankSubsetEquiv e m S).1 = indicator i S.1 := by
  simp [uniformRankSubsetEquiv, Equiv.subtypeEquiv, indicator]

theorem uniform_inclusionMean_permutation (e : Equiv.Perm ι) (m : ℕ) (i : ι) :
    inclusionMean (fun _ : ι => 1) m (e i) =
      inclusionMean (fun _ : ι => 1) m i := by
  unfold inclusionMean
  rw [← uniform_expectation_permutation e m]
  congr 1
  funext S
  exact uniform_indicator_permutation e m S i

theorem uniform_covariance_permutation (e : Equiv.Perm ι) (m : ℕ) (i j : ι) :
    covarianceMatrix (fun _ : ι => 1) m (e i) (e j) =
      covarianceMatrix (fun _ : ι => 1) m i j := by
  unfold covarianceMatrix
  rw [uniform_inclusionMean_permutation, uniform_inclusionMean_permutation]
  rw [← uniform_expectation_permutation e m]
  congr 1
  funext S
  simp only [uniform_indicator_permutation]

def uniformWeights (n : ℕ) : Fin n → ℝ := fun _ => 1

theorem uniformWeights_pos (n : ℕ) : ∀ i, 0 < uniformWeights n i := by
  intro i
  exact zero_lt_one

theorem uniform_subsetProbability {n : ℕ} (m : ℕ) (S : RankSubset (Fin n) m) :
    subsetProbability (uniformWeights n) m S = 1 / (n.choose m : ℝ) := by
  simp [subsetProbability, subsetWeight, uniformWeights,
    elementarySum_eq_powersetCard, Finset.card_powersetCard]

theorem uniform_inclusionMean {n : ℕ} (hn : 0 < n) (m : ℕ) (hm : m ≤ n)
    (i : Fin n) : inclusionMean (uniformWeights n) m i = (m : ℝ) / n := by
  have heq (j : Fin n) : inclusionMean (uniformWeights n) m j =
      inclusionMean (uniformWeights n) m i := by
    change inclusionMean (fun _ : Fin n => 1) m j = inclusionMean (fun _ => 1) m i
    simpa only [Equiv.swap_apply_left] using
      uniform_inclusionMean_permutation (Equiv.swap i j) m i
  have hs := sum_inclusionMean (uniformWeights n) (uniformWeights_pos n)
    (by simpa using hm)
  simp_rw [heq] at hs
  simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul] at hs
  apply (eq_div_iff (by exact_mod_cast hn.ne' : (n : ℝ) ≠ 0)).mpr
  linarith

def uniformVariance (n m : ℕ) : ℝ := ((m : ℝ) / n) * (1 - (m : ℝ) / n)

theorem uniform_covariance_diagonal {n : ℕ} (hn : 0 < n) (m : ℕ) (hm : m ≤ n)
    (i : Fin n) : covarianceMatrix (uniformWeights n) m i i = uniformVariance n m := by
  rw [covariance_diagonal _ (uniformWeights_pos n) (by simpa using hm),
    uniform_inclusionMean hn m hm]
  rfl

theorem uniform_covariance_offDiagonal {n : ℕ} (hn : 2 ≤ n) (m : ℕ) (hm : m ≤ n)
    (i j : Fin n) (hij : i ≠ j) :
    covarianceMatrix (uniformWeights n) m i j = -uniformVariance n m / ((n : ℝ) - 1) := by
  classical
  have heq (k : Fin n) (hki : k ≠ i) :
      covarianceMatrix (uniformWeights n) m i k = covarianceMatrix (uniformWeights n) m i j := by
    change covarianceMatrix (fun _ : Fin n => 1) m i k =
      covarianceMatrix (fun _ => 1) m i j
    simpa only [Equiv.swap_apply_of_ne_of_ne hij (Ne.symm hki), Equiv.swap_apply_left] using
      uniform_covariance_permutation (Equiv.swap j k) m i j
  have hs := covariance_rowSum_zero (uniformWeights n) (uniformWeights_pos n)
    (by simpa using hm) i
  rw [← Finset.sum_erase_add _ _ (Finset.mem_univ i)] at hs
  have hsum : (∑ k ∈ (Finset.univ : Finset (Fin n)).erase i,
      covarianceMatrix (uniformWeights n) m i k) =
      ((n - 1 : ℕ) : ℝ) * covarianceMatrix (uniformWeights n) m i j := by
    calc
      _ = ∑ _k ∈ (Finset.univ : Finset (Fin n)).erase i,
          covarianceMatrix (uniformWeights n) m i j := by
        apply Finset.sum_congr rfl
        intro k hk
        exact heq k (Finset.mem_erase.mp hk).1
      _ = _ := by simp
  rw [hsum, uniform_covariance_diagonal (by omega) m hm] at hs
  have hc : ((n - 1 : ℕ) : ℝ) = (n : ℝ) - 1 := by
    exact_mod_cast Nat.cast_sub (by omega : 1 ≤ n)
  rw [hc] at hs
  have hn1 : (n : ℝ) - 1 ≠ 0 := by
    have : (2 : ℝ) ≤ n := by exact_mod_cast hn
    linarith
  apply (eq_div_iff hn1).mpr
  linarith

theorem uniform_covariance_matrix {n : ℕ} (hn : 2 ≤ n) (m : ℕ) (hm : m ≤ n) :
    covarianceMatrix (uniformWeights n) m =
      ((n : ℝ) * uniformVariance n m / ((n : ℝ) - 1)) •
        (1 - ((n : ℝ)⁻¹) • Matrix.vecMulVec (fun _ => 1) (fun _ => 1)) := by
  have hn0 : (n : ℝ) ≠ 0 := by exact_mod_cast (show n ≠ 0 by omega)
  have hn1 : (n : ℝ) - 1 ≠ 0 := by
    have : (2 : ℝ) ≤ n := by exact_mod_cast hn
    linarith
  ext i j
  by_cases hij : i = j
  · subst j
    rw [uniform_covariance_diagonal (by omega) m hm]
    simp only [Matrix.smul_apply, Matrix.sub_apply, Matrix.one_apply_eq,
      Matrix.vecMulVec_apply, smul_eq_mul, mul_one]
    field_simp
  · rw [uniform_covariance_offDiagonal hn m hm i j hij]
    simp only [Matrix.smul_apply, Matrix.sub_apply, Matrix.one_apply_ne hij,
      Matrix.vecMulVec_apply, smul_eq_mul, mul_one]
    field_simp
    ring

theorem uniformVariance_pos {n m : ℕ} (hmpos : 1 ≤ m) (hmtop : m ≤ n - 1) :
    0 < uniformVariance n m := by
  have hn : (0 : ℝ) < n := by exact_mod_cast (show 0 < n by omega)
  have hm : (0 : ℝ) < m := by exact_mod_cast (show 0 < m by omega)
  have hmn : (m : ℝ) < n := by exact_mod_cast (show m < n by omega)
  exact mul_pos (div_pos hm hn) (sub_pos.mpr ((div_lt_one hn).mpr hmn))

end
end CoefficientOne
