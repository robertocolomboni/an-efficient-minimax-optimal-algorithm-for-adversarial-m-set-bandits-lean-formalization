import EffectiveResistance.Covariance
import EffectiveResistance.PairTable

/-!
# The endpoint four-cell table of the fixed-rank law
-/

open scoped BigOperators

namespace EffectiveResistance

noncomputable section

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

def pairCell11 (w : ι → ℝ) (m : ℕ) (i j : ι) : ℝ :=
  expectation w m fun S => indicator i S.1 * indicator j S.1

def pairCell10 (w : ι → ℝ) (m : ℕ) (i j : ι) : ℝ :=
  expectation w m fun S => indicator i S.1 * (1 - indicator j S.1)

def pairCell01 (w : ι → ℝ) (m : ℕ) (i j : ι) : ℝ :=
  expectation w m fun S => (1 - indicator i S.1) * indicator j S.1

def pairCell00 (w : ι → ℝ) (m : ℕ) (i j : ι) : ℝ :=
  expectation w m fun S => (1 - indicator i S.1) * (1 - indicator j S.1)

theorem indicator_nonnegative (i : ι) (S : Finset ι) :
    0 ≤ indicator i S := by
  by_cases hi : i ∈ S <;> simp [indicator, hi]

theorem indicator_le_one (i : ι) (S : Finset ι) :
    indicator i S ≤ 1 := by
  by_cases hi : i ∈ S <;> simp [indicator, hi]

theorem pairCell11_nonnegative
    (w : ι → ℝ) (hw : ∀ k, 0 < w k) (hm : m ≤ Fintype.card ι)
    (i j : ι) : 0 ≤ pairCell11 w m i j := by
  exact expectation_nonnegative w hw hm fun S =>
    mul_nonneg (indicator_nonnegative i S.1) (indicator_nonnegative j S.1)

theorem pairCell10_nonnegative
    (w : ι → ℝ) (hw : ∀ k, 0 < w k) (hm : m ≤ Fintype.card ι)
    (i j : ι) : 0 ≤ pairCell10 w m i j := by
  exact expectation_nonnegative w hw hm fun S =>
    mul_nonneg (indicator_nonnegative i S.1)
      (sub_nonneg.mpr (indicator_le_one j S.1))

theorem pairCell01_nonnegative
    (w : ι → ℝ) (hw : ∀ k, 0 < w k) (hm : m ≤ Fintype.card ι)
    (i j : ι) : 0 ≤ pairCell01 w m i j := by
  exact expectation_nonnegative w hw hm fun S =>
    mul_nonneg (sub_nonneg.mpr (indicator_le_one i S.1))
      (indicator_nonnegative j S.1)

theorem pairCell00_nonnegative
    (w : ι → ℝ) (hw : ∀ k, 0 < w k) (hm : m ≤ Fintype.card ι)
    (i j : ι) : 0 ≤ pairCell00 w m i j := by
  exact expectation_nonnegative w hw hm fun S =>
    mul_nonneg (sub_nonneg.mpr (indicator_le_one i S.1))
      (sub_nonneg.mpr (indicator_le_one j S.1))

theorem pairCells_total
    (w : ι → ℝ) (hw : ∀ k, 0 < w k) (hm : m ≤ Fintype.card ι)
    (i j : ι) :
    pairCell11 w m i j + pairCell10 w m i j +
      pairCell01 w m i j + pairCell00 w m i j = 1 := by
  simp only [pairCell11, pairCell10, pairCell01, pairCell00, expectation]
  rw [← Finset.sum_add_distrib, ← Finset.sum_add_distrib,
    ← Finset.sum_add_distrib]
  calc
    _ = ∑ S : RankSubset ι m, subsetProbability w m S := by
      apply Finset.sum_congr rfl
      intro S _
      ring
    _ = 1 := sum_subsetProbability w hw hm

/-- The two-coordinate probability table induced by the external-field law. -/
def externalFieldPairTable
    (w : ι → ℝ) (hw : ∀ k, 0 < w k) (hm : m ≤ Fintype.card ι)
    (i j : ι) : PairTable where
  p11 := pairCell11 w m i j
  p10 := pairCell10 w m i j
  p01 := pairCell01 w m i j
  p00 := pairCell00 w m i j
  nonneg11 := pairCell11_nonnegative w hw hm i j
  nonneg10 := pairCell10_nonnegative w hw hm i j
  nonneg01 := pairCell01_nonnegative w hw hm i j
  nonneg00 := pairCell00_nonnegative w hw hm i j
  total := pairCells_total w hw hm i j

theorem pairCell11_add_pairCell10
    (w : ι → ℝ) (m : ℕ) (i j : ι) :
    pairCell11 w m i j + pairCell10 w m i j = inclusionMean w m i := by
  simp only [pairCell11, pairCell10, inclusionMean, expectation]
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro S _
  ring

theorem pairCell11_add_pairCell01
    (w : ι → ℝ) (m : ℕ) (i j : ι) :
    pairCell11 w m i j + pairCell01 w m i j = inclusionMean w m j := by
  simp only [pairCell11, pairCell01, inclusionMean, expectation]
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro S _
  ring

theorem covariance_eq_pairCell11_sub_means
    (w : ι → ℝ) (hw : ∀ k, 0 < w k) (hm : m ≤ Fintype.card ι)
    (i j : ι) :
    covarianceMatrix w m i j = pairCell11 w m i j -
      inclusionMean w m i * inclusionMean w m j := by
  rw [covariance_apply]
  simp only [centeredIndicator, expectation, pairCell11]
  have hnorm := sum_subsetProbability w hw hm
  have hmeani :
      ∑ S : RankSubset ι m,
        subsetProbability w m S * indicator i S.1 = inclusionMean w m i := rfl
  have hmeanj :
      ∑ S : RankSubset ι m,
        subsetProbability w m S * indicator j S.1 = inclusionMean w m j := rfl
  calc
    (∑ S : RankSubset ι m, subsetProbability w m S *
      ((indicator i S.1 - inclusionMean w m i) *
       (indicator j S.1 - inclusionMean w m j))) =
        (∑ S : RankSubset ι m, subsetProbability w m S *
          (indicator i S.1 * indicator j S.1)) -
        inclusionMean w m j *
          (∑ S : RankSubset ι m, subsetProbability w m S * indicator i S.1) -
        inclusionMean w m i *
          (∑ S : RankSubset ι m, subsetProbability w m S * indicator j S.1) +
        (inclusionMean w m i * inclusionMean w m j) *
          (∑ S : RankSubset ι m, subsetProbability w m S) := by
      calc
        _ = ∑ S : RankSubset ι m,
            (subsetProbability w m S * (indicator i S.1 * indicator j S.1) -
             inclusionMean w m j *
               (subsetProbability w m S * indicator i S.1) -
             inclusionMean w m i *
               (subsetProbability w m S * indicator j S.1) +
             (inclusionMean w m i * inclusionMean w m j) *
               subsetProbability w m S) := by
          apply Finset.sum_congr rfl
          intro S _
          ring
        _ = _ := by
          rw [Finset.sum_add_distrib, Finset.sum_sub_distrib,
            Finset.sum_sub_distrib, ← Finset.mul_sum, ← Finset.mul_sum,
            ← Finset.mul_sum]
    _ = (∑ S : RankSubset ι m, subsetProbability w m S *
          (indicator i S.1 * indicator j S.1)) -
        inclusionMean w m i * inclusionMean w m j := by
      rw [hmeani, hmeanj, hnorm]
      ring

theorem externalFieldPairTable_means
    (w : ι → ℝ) (hw : ∀ k, 0 < w k) (hm : m ≤ Fintype.card ι)
    (i j : ι) :
    (externalFieldPairTable w hw hm i j).μi = inclusionMean w m i ∧
      (externalFieldPairTable w hw hm i j).μj = inclusionMean w m j := by
  constructor
  · exact pairCell11_add_pairCell10 w m i j
  · exact pairCell11_add_pairCell01 w m i j

/-- For the induced four-cell table, its determinant defect is exactly the
negative off-diagonal covariance. -/
theorem externalFieldPairTable_omega_eq_neg_covariance
    (w : ι → ℝ) (hw : ∀ k, 0 < w k) (hm : m ≤ Fintype.card ι)
    (i j : ι) :
    (externalFieldPairTable w hw hm i j).ω = -covarianceMatrix w m i j := by
  let P := externalFieldPairTable w hw hm i j
  have hμ := externalFieldPairTable_means w hw hm i j
  have hcov := covariance_eq_pairCell11_sub_means w hw hm i j
  have htotal := P.total
  simp only [PairTable.ω, P, externalFieldPairTable] at hμ htotal ⊢
  rw [hcov]
  rcases hμ with ⟨hμi, hμj⟩
  simp only [PairTable.μi, PairTable.μj, externalFieldPairTable] at hμi hμj
  rw [← hμi, ← hμj]
  have hp00 : pairCell00 w m i j =
      1 - pairCell11 w m i j - pairCell10 w m i j - pairCell01 w m i j := by
    linarith [htotal]
  rw [hp00]
  ring

end

end EffectiveResistance
