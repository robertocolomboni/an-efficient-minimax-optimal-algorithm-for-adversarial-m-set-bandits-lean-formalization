import EffectiveResistance.FiniteLaw
import EffectiveResistance.MatrixOrder
import Mathlib.LinearAlgebra.Matrix.Symmetric
import Mathlib.Tactic.Ring

/-!
# Elementary covariance identities for the fixed-rank law
-/

open scoped BigOperators
open Matrix

namespace EffectiveResistance

noncomputable section

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

def centeredIndicator (w : ι → ℝ) (m : ℕ) (i : ι)
    (S : RankSubset ι m) : ℝ :=
  indicator i S.1 - inclusionMean w m i

def centeredLinearStatistic (w : ι → ℝ) (m : ℕ)
    (a : ι → ℝ) (S : RankSubset ι m) : ℝ :=
  ∑ i, a i * centeredIndicator w m i S

theorem subsetProbability_pos
    (w : ι → ℝ) (hw : ∀ i, 0 < w i)
    (hm : m ≤ Fintype.card ι) (S : RankSubset ι m) :
    0 < subsetProbability w m S := by
  rw [subsetProbability]
  exact div_pos (Finset.prod_pos fun i _ => hw i) (elementarySum_pos w hw hm)

theorem expectation_nonnegative
    (w : ι → ℝ) (hw : ∀ i, 0 < w i)
    (hm : m ≤ Fintype.card ι)
    {f : RankSubset ι m → ℝ} (hf : ∀ S, 0 ≤ f S) :
    0 ≤ expectation w m f := by
  rw [expectation]
  exact Finset.sum_nonneg fun S _ =>
    mul_nonneg (subsetProbability_pos w hw hm S).le (hf S)

theorem covariance_apply (w : ι → ℝ) (m : ℕ) (i j : ι) :
    covarianceMatrix w m i j =
      expectation w m fun S =>
        centeredIndicator w m i S * centeredIndicator w m j S :=
  rfl

theorem covariance_comm (w : ι → ℝ) (m : ℕ) (i j : ι) :
    covarianceMatrix w m i j = covarianceMatrix w m j i := by
  rw [covariance_apply, covariance_apply]
  unfold expectation
  apply Finset.sum_congr rfl
  intro S _
  ring

theorem covariance_isSymm (w : ι → ℝ) (m : ℕ) :
    Matrix.IsSymm (covarianceMatrix w m) := by
  apply Matrix.IsSymm.ext
  intro i j
  exact covariance_comm w m j i

theorem quadraticForm_covariance
    (w : ι → ℝ) (m : ℕ) (a : ι → ℝ) :
    quadraticForm (covarianceMatrix w m) a =
      expectation w m fun S => (centeredLinearStatistic w m a S) ^ 2 := by
  calc
    quadraticForm (covarianceMatrix w m) a =
        ∑ i, ∑ j, a i * a j *
          expectation w m (fun S =>
            centeredIndicator w m i S * centeredIndicator w m j S) := by
      simp only [quadraticForm, Matrix.mulVec, dotProduct, Finset.mul_sum,
        covariance_apply]
      apply Finset.sum_congr rfl
      intro i _
      apply Finset.sum_congr rfl
      intro j _
      ring
    _ = ∑ S : RankSubset ι m, subsetProbability w m S *
        (∑ i, ∑ j, a i * a j *
          (centeredIndicator w m i S * centeredIndicator w m j S)) := by
      unfold expectation
      calc
        (∑ i, ∑ j, a i * a j *
            ∑ S : RankSubset ι m, subsetProbability w m S *
              (centeredIndicator w m i S * centeredIndicator w m j S)) =
            ∑ i, ∑ j, ∑ S : RankSubset ι m,
              subsetProbability w m S *
                ((a i * centeredIndicator w m i S) *
                 (a j * centeredIndicator w m j S)) := by
              apply Finset.sum_congr rfl
              intro i _
              apply Finset.sum_congr rfl
              intro j _
              rw [Finset.mul_sum]
              apply Finset.sum_congr rfl
              intro S _
              ring
        _ = ∑ i, ∑ S : RankSubset ι m, ∑ j,
              subsetProbability w m S *
                ((a i * centeredIndicator w m i S) *
                 (a j * centeredIndicator w m j S)) := by
              apply Finset.sum_congr rfl
              intro i _
              rw [Finset.sum_comm]
        _ = ∑ S : RankSubset ι m, ∑ i, ∑ j,
              subsetProbability w m S *
                ((a i * centeredIndicator w m i S) *
                 (a j * centeredIndicator w m j S)) := by
              rw [Finset.sum_comm]
        _ = ∑ S : RankSubset ι m, subsetProbability w m S *
            (∑ i, ∑ j, a i * a j *
              (centeredIndicator w m i S * centeredIndicator w m j S)) := by
              apply Finset.sum_congr rfl
              intro S _
              rw [Finset.mul_sum]
              apply Finset.sum_congr rfl
              intro i _
              rw [Finset.mul_sum]
              apply Finset.sum_congr rfl
              intro j _
              ring
    _ = expectation w m fun S => (centeredLinearStatistic w m a S) ^ 2 := by
      unfold expectation
      apply Finset.sum_congr rfl
      intro S _
      congr 1
      unfold centeredLinearStatistic
      simp only
      rw [pow_two, Finset.sum_mul]
      apply Finset.sum_congr rfl
      intro i _
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro j _
      ring

theorem covariance_quadratic_nonnegative
    (w : ι → ℝ) (hw : ∀ i, 0 < w i)
    (hm : m ≤ Fintype.card ι) (a : ι → ℝ) :
    0 ≤ quadraticForm (covarianceMatrix w m) a := by
  rw [quadraticForm_covariance]
  exact expectation_nonnegative w hw hm fun S => sq_nonneg _

theorem indicator_sq (i : ι) (S : Finset ι) :
    indicator i S ^ 2 = indicator i S := by
  by_cases hi : i ∈ S <;> simp [indicator, hi]

theorem indicator_mul_self (i : ι) (S : Finset ι) :
    indicator i S * indicator i S = indicator i S := by
  by_cases hi : i ∈ S <;> simp [indicator, hi]

theorem covariance_diagonal
    (w : ι → ℝ) (hw : ∀ i, 0 < w i)
    (hm : m ≤ Fintype.card ι) (i : ι) :
    covarianceMatrix w m i i =
      inclusionMean w m i * (1 - inclusionMean w m i) := by
  rw [covariance_apply]
  unfold centeredIndicator
  unfold expectation
  have hnorm := sum_subsetProbability w hw hm
  have hmean :
      ∑ S : RankSubset ι m,
        subsetProbability w m S * indicator i S.1 = inclusionMean w m i := by
    rfl
  have hpoint (S : RankSubset ι m) :
      subsetProbability w m S *
          ((indicator i S.1 - inclusionMean w m i) *
           (indicator i S.1 - inclusionMean w m i)) =
        subsetProbability w m S * indicator i S.1 -
          2 * inclusionMean w m i *
            (subsetProbability w m S * indicator i S.1) +
          (inclusionMean w m i) ^ 2 * subsetProbability w m S := by
    calc
      _ = subsetProbability w m S *
          (indicator i S.1 * indicator i S.1 -
            2 * inclusionMean w m i * indicator i S.1 +
            (inclusionMean w m i) ^ 2) := by ring
      _ = _ := by
        rw [indicator_mul_self]
        ring
  calc
    (∑ S : RankSubset ι m, subsetProbability w m S *
      ((indicator i S.1 - inclusionMean w m i) *
       (indicator i S.1 - inclusionMean w m i))) =
        (∑ S : RankSubset ι m,
          subsetProbability w m S * indicator i S.1) -
        2 * inclusionMean w m i *
          (∑ S : RankSubset ι m,
            subsetProbability w m S * indicator i S.1) +
          (inclusionMean w m i) ^ 2 *
          (∑ S : RankSubset ι m, subsetProbability w m S) := by
      simp_rw [hpoint, Finset.sum_add_distrib, Finset.sum_sub_distrib,
        Finset.mul_sum]
    _ = inclusionMean w m i * (1 - inclusionMean w m i) := by
      rw [hmean, hnorm]
      ring

theorem sum_centeredIndicator
    (w : ι → ℝ) (hw : ∀ i, 0 < w i)
    (hm : m ≤ Fintype.card ι) (S : RankSubset ι m) :
    ∑ i, centeredIndicator w m i S = 0 := by
  change (∑ i, (indicator i S.1 - inclusionMean w m i)) = 0
  rw [Finset.sum_sub_distrib, sum_indicator S,
    sum_inclusionMean w hw hm]
  ring

theorem covariance_rowSum_zero
    (w : ι → ℝ) (hw : ∀ i, 0 < w i)
    (hm : m ≤ Fintype.card ι) (i : ι) :
    ∑ j, covarianceMatrix w m i j = 0 := by
  simp_rw [covariance_apply]
  unfold expectation
  rw [Finset.sum_comm]
  apply Finset.sum_eq_zero
  intro S _
  simp only
  rw [← Finset.mul_sum]
  rw [← Finset.mul_sum]
  rw [sum_centeredIndicator w hw hm S]
  ring

end

end EffectiveResistance
