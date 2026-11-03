import EffectiveResistance.AdjacentCurvature
import EffectiveResistance.Covariance
import EffectiveResistance.OccupancyCounting

/-!
# Adjacent-rank curvature for external-field laws

This file instantiates the abstract covariance/Cauchy--Schwarz argument with
the occupancy likelihood-ratio identity proved by explicit counting.
-/

open scoped BigOperators

namespace EffectiveResistance

noncomputable section

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

def rankPairProbability (w : ι → ℝ) (r : ℕ)
    (P : RankSubset ι r × RankSubset ι r) : ℝ :=
  subsetProbability w r P.1 * subsetProbability w r P.2

def rankLinearStatistic (a : ι → ℝ) (S : Finset ι) : ℝ :=
  ∑ i, a i * indicator i S

def rankPairOccupancy (P : RankSubset ι r × RankSubset ι r) (i : ι) : ℝ :=
  indicator i P.1.1 + indicator i P.2.1

def rankCurvature (w : ι → ℝ) (q : ℕ) (i : ι) : ℝ :=
  inclusionMean w q i - 2 * inclusionMean w (q + 1) i +
    inclusionMean w (q + 2) i

theorem finiteExpectation_rankPair
    (w : ι → ℝ) (r : ℕ)
    (G : RankSubset ι r → RankSubset ι r → ℝ) :
    finiteExpectation (rankPairProbability w r)
        (fun P => G P.1 P.2) =
      rankPairExpectation w r r G := by
  unfold finiteExpectation rankPairProbability rankPairExpectation
  rw [Fintype.sum_prod_type]

theorem finiteExpectation_rankPair_general
    (w : ι → ℝ) (r s : ℕ)
    (G : RankSubset ι r → RankSubset ι s → ℝ) :
    finiteExpectation
        (fun P : RankSubset ι r × RankSubset ι s =>
          subsetProbability w r P.1 * subsetProbability w s P.2)
        (fun P => G P.1 P.2) =
      rankPairExpectation w r s G := by
  unfold finiteExpectation rankPairExpectation
  rw [Fintype.sum_prod_type]

theorem rankPairProbability_nonnegative
    (w : ι → ℝ) (hw : ∀ i, 0 < w i) (r : ℕ)
    (hr : r ≤ Fintype.card ι) :
    ∀ P, 0 ≤ rankPairProbability w r P := by
  intro P
  exact mul_nonneg
    (subsetProbability_pos w hw hr P.1).le
    (subsetProbability_pos w hw hr P.2).le

theorem rankPairProbability_sum
    (w : ι → ℝ) (hw : ∀ i, 0 < w i) (r : ℕ)
    (hr : r ≤ Fintype.card ι) :
    ∑ P, rankPairProbability w r P = 1 := by
  unfold rankPairProbability
  rw [Fintype.sum_prod_type]
  calc
    (∑ A, ∑ B, subsetProbability w r A * subsetProbability w r B) =
        ∑ A, subsetProbability w r A *
          (∑ B, subsetProbability w r B) := by
      apply Finset.sum_congr rfl
      intro A _
      rw [Finset.mul_sum]
    _ = (∑ A, subsetProbability w r A) *
        (∑ B, subsetProbability w r B) := by rw [Finset.sum_mul]
    _ = 1 := by rw [sum_subsetProbability w hw hr]; norm_num

theorem rankPairExpectation_additive
    (w : ι → ℝ) (hw : ∀ i, 0 < w i) (r s : ℕ)
    (hr : r ≤ Fintype.card ι) (hs : s ≤ Fintype.card ι)
    (f : RankSubset ι r → ℝ) (g : RankSubset ι s → ℝ) :
    rankPairExpectation w r s (fun A B => f A + g B) =
      expectation w r f + expectation w s g := by
  rw [← finiteExpectation_rankPair_general]
  exact finiteExpectation_independent_sum
    (sum_subsetProbability w hw hr) (sum_subsetProbability w hw hs) f g

theorem expectation_rankLinearStatistic
    (w : ι → ℝ) (r : ℕ) (a : ι → ℝ) :
    expectation w r (fun S => rankLinearStatistic a S.1) =
      ∑ i, a i * inclusionMean w r i := by
  unfold expectation rankLinearStatistic inclusionMean
  calc
    (∑ S : RankSubset ι r,
      subsetProbability w r S * ∑ i, a i * indicator i S.1) =
        ∑ S : RankSubset ι r, ∑ i,
          subsetProbability w r S * (a i * indicator i S.1) := by
      apply Finset.sum_congr rfl
      intro S _
      rw [Finset.mul_sum]
    _ = ∑ i, ∑ S : RankSubset ι r,
          subsetProbability w r S * (a i * indicator i S.1) := by
      rw [Finset.sum_comm]
    _ = ∑ i, a i *
          (∑ S : RankSubset ι r,
            subsetProbability w r S * indicator i S.1) := by
      apply Finset.sum_congr rfl
      intro i _
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro S _
      ring

theorem centeredLinearStatistic_eq
    (w : ι → ℝ) (r : ℕ) (a : ι → ℝ) (S : RankSubset ι r) :
    centeredLinearStatistic w r a S =
      rankLinearStatistic a S.1 - ∑ i, a i * inclusionMean w r i := by
  unfold centeredLinearStatistic centeredIndicator rankLinearStatistic
  calc
    (∑ i, a i * (indicator i S.1 - inclusionMean w r i)) =
        ∑ i, (a i * indicator i S.1 - a i * inclusionMean w r i) := by
      apply Finset.sum_congr rfl
      intro i _
      ring
    _ = _ := by rw [Finset.sum_sub_distrib]

theorem finiteVariance_rankLinearStatistic
    (w : ι → ℝ) (r : ℕ) (a : ι → ℝ) :
    finiteVariance (subsetProbability w r)
        (fun S => rankLinearStatistic a S.1) =
      quadraticForm (covarianceMatrix w r) a := by
  rw [quadraticForm_covariance]
  unfold finiteVariance finiteExpectation expectation
  apply Finset.sum_congr rfl
  intro S _
  congr 1
  have hmean :
      (∑ T : RankSubset ι r,
        subsetProbability w r T * rankLinearStatistic a T.1) =
        ∑ i, a i * inclusionMean w r i := by
    simpa [expectation] using expectation_rankLinearStatistic w r a
  rw [hmean]
  change
    (rankLinearStatistic a S.1 - ∑ i, a i * inclusionMean w r i) ^ 2 =
      centeredLinearStatistic w r a S ^ 2
  rw [centeredLinearStatistic_eq]

theorem expectation_rankLinear_residual_decomposition
    (w : ι → ℝ) (hw : ∀ i, 0 < w i) (r : ℕ)
    (hr : r ≤ Fintype.card ι) (a : ι → ℝ) (c : ℝ) :
    expectation w r (fun S => (c - rankLinearStatistic a S.1) ^ 2) =
      quadraticForm (covarianceMatrix w r) a +
        (c - ∑ i, a i * inclusionMean w r i) ^ 2 := by
  calc
    expectation w r (fun S => (c - rankLinearStatistic a S.1) ^ 2) =
      finiteExpectation (subsetProbability w r)
        (fun S => (c - rankLinearStatistic a S.1) ^ 2) := rfl
    _ = finiteVariance (subsetProbability w r)
          (fun S => rankLinearStatistic a S.1) +
        (c - finiteExpectation (subsetProbability w r)
          (fun S => rankLinearStatistic a S.1)) ^ 2 :=
      finiteExpectation_sq_residual (sum_subsetProbability w hw hr) _ c
    _ = quadraticForm (covarianceMatrix w r) a +
        (c - ∑ i, a i * inclusionMean w r i) ^ 2 := by
      rw [finiteVariance_rankLinearStatistic]
      change quadraticForm (covarianceMatrix w r) a +
          (c - expectation w r (fun S => rankLinearStatistic a S.1)) ^ 2 = _
      rw [expectation_rankLinearStatistic]

theorem linear_rankPairOccupancy
    (a : ι → ℝ) (P : RankSubset ι r × RankSubset ι r) :
    (∑ i, a i * rankPairOccupancy P i) =
      rankLinearStatistic a P.1.1 + rankLinearStatistic a P.2.1 := by
  unfold rankPairOccupancy rankLinearStatistic
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro i _
  ring

theorem occupancy_cast (A B : Finset ι) (i : ι) :
    (occupancy A B i : ℝ) = indicator i A + indicator i B := by
  by_cases hiA : i ∈ A <;> by_cases hiB : i ∈ B <;>
    simp [occupancy, indicator, hiA, hiB] <;> norm_num

theorem linearOccupancy_eq_rankLinear
    (a : ι → ℝ) (A B : Finset ι) :
    (∑ i, a i * (occupancy A B i : ℝ)) =
      rankLinearStatistic a A + rankLinearStatistic a B := by
  simp_rw [occupancy_cast]
  unfold rankLinearStatistic
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro i _
  ring

theorem rankPairExpectation_linearOccupancy
    (w : ι → ℝ) (hw : ∀ i, 0 < w i) (r s : ℕ)
    (hr : r ≤ Fintype.card ι) (hs : s ≤ Fintype.card ι)
    (a : ι → ℝ) :
    rankPairExpectation w r s
        (fun A B => ∑ i, a i * (occupancy A.1 B.1 i : ℝ)) =
      (∑ i, a i * inclusionMean w r i) +
        ∑ i, a i * inclusionMean w s i := by
  calc
    rankPairExpectation w r s
        (fun A B => ∑ i, a i * (occupancy A.1 B.1 i : ℝ)) =
      rankPairExpectation w r s
        (fun A B => rankLinearStatistic a A.1 + rankLinearStatistic a B.1) := by
          unfold rankPairExpectation
          apply Finset.sum_congr rfl
          intro A _
          apply Finset.sum_congr rfl
          intro B _
          change
            subsetProbability w r A * subsetProbability w s B *
                (∑ i, a i * (occupancy A.1 B.1 i : ℝ)) =
              subsetProbability w r A * subsetProbability w s B *
                (rankLinearStatistic a A.1 + rankLinearStatistic a B.1)
          rw [linearOccupancy_eq_rankLinear]
    _ = expectation w r (fun A => rankLinearStatistic a A.1) +
        expectation w s (fun B => rankLinearStatistic a B.1) :=
      rankPairExpectation_additive w hw r s hr hs _ _
    _ = _ := by
      rw [expectation_rankLinearStatistic, expectation_rankLinearStatistic]

theorem expected_occupancyTilt
    (w : ι → ℝ) (hw : ∀ i, 0 < w i) (q : ℕ)
    (hq : q + 2 ≤ Fintype.card ι) :
    finiteExpectation (rankPairProbability w (q + 1))
        (fun P => occupancyTilt P.1.1 P.2.1) = adjacentTheta w q := by
  have hq0 : q ≤ Fintype.card ι := by omega
  have h := occupancy_likelihood_ratio w hw q hq (fun _ => 1)
  rw [rankPairExpectation_one w hw q (q + 2) hq0 hq, mul_one] at h
  calc
    finiteExpectation (rankPairProbability w (q + 1))
        (fun P => occupancyTilt P.1.1 P.2.1) =
      rankPairExpectation w (q + 1) (q + 1)
        (fun A B => occupancyTilt A.1 B.1) :=
      by
        simpa using
          (finiteExpectation_rankPair w (q + 1)
            (fun A B => occupancyTilt A.1 B.1))
    _ = adjacentTheta w q := by simpa using h

theorem adjacentTheta_pos
    (w : ι → ℝ) (hw : ∀ i, 0 < w i) (q : ℕ)
    (hq : q + 2 ≤ Fintype.card ι) :
    0 < adjacentTheta w q := by
  have hq0 : q ≤ Fintype.card ι := by omega
  have hq1 : q + 1 ≤ Fintype.card ι := by omega
  unfold adjacentTheta
  exact div_pos
    (mul_pos (elementarySum_pos w hw hq0) (elementarySum_pos w hw hq))
    (sq_pos_of_pos (elementarySum_pos w hw hq1))

theorem adjacentTheta_lt_one
    (w : ι → ℝ) (hw : ∀ i, 0 < w i) (q : ℕ)
    (hq : q + 2 ≤ Fintype.card ι) :
    adjacentTheta w q < 1 := by
  have hq1 : q + 1 ≤ Fintype.card ι := by omega
  have hnorm := rankPairProbability_sum w hw (q + 1) hq1
  have htheta := expected_occupancyTilt w hw q hq
  obtain ⟨S, -, hS⟩ := Finset.exists_subset_card_eq hq1
  let A : RankSubset ι (q + 1) := ⟨S, hS⟩
  let P : RankSubset ι (q + 1) × RankSubset ι (q + 1) := (A, A)
  have hgap : 0 < finiteExpectation (rankPairProbability w (q + 1))
      (fun Q => 1 - occupancyTilt Q.1.1 Q.2.1) := by
    unfold finiteExpectation
    refine Finset.sum_pos' (fun Q _ => ?_) ⟨P, Finset.mem_univ P, ?_⟩
    · simpa [rankPairProbability] using (mul_pos
        (mul_pos (subsetProbability_pos w hw hq1 Q.1)
          (subsetProbability_pos w hw hq1 Q.2))
        (sub_pos.mpr (occupancyTilt_lt_one Q.1.1 Q.2.1))).le
    · simpa [rankPairProbability] using (mul_pos
        (mul_pos (subsetProbability_pos w hw hq1 P.1)
          (subsetProbability_pos w hw hq1 P.2))
        (sub_pos.mpr (occupancyTilt_lt_one P.1.1 P.2.1)))
  have hgap_eq :
      finiteExpectation (rankPairProbability w (q + 1))
          (fun Q => 1 - occupancyTilt Q.1.1 Q.2.1) =
        1 - finiteExpectation (rankPairProbability w (q + 1))
          (fun Q => occupancyTilt Q.1.1 Q.2.1) := by
    unfold finiteExpectation
    calc
      (∑ Q, rankPairProbability w (q + 1) Q *
          (1 - occupancyTilt Q.1.1 Q.2.1)) =
        (∑ Q, rankPairProbability w (q + 1) Q) -
          ∑ Q, rankPairProbability w (q + 1) Q *
            occupancyTilt Q.1.1 Q.2.1 := by
              rw [← Finset.sum_sub_distrib]
              apply Finset.sum_congr rfl
              intro Q _
              ring
      _ = _ := by rw [hnorm]
  rw [hgap_eq, htheta] at hgap
  linarith

theorem rankPairOccupancy_variance
    (w : ι → ℝ) (hw : ∀ i, 0 < w i) (r : ℕ)
    (hr : r ≤ Fintype.card ι) (a : ι → ℝ) :
    finiteVariance (rankPairProbability w r)
        (fun P => ∑ i, a i * rankPairOccupancy P i) =
      2 * quadraticForm (covarianceMatrix w r) a := by
  have hnorm := sum_subsetProbability w hw hr
  calc
    finiteVariance (rankPairProbability w r)
        (fun P => ∑ i, a i * rankPairOccupancy P i) =
      finiteVariance
        (fun P : RankSubset ι r × RankSubset ι r =>
          subsetProbability w r P.1 * subsetProbability w r P.2)
        (fun P => rankLinearStatistic a P.1.1 + rankLinearStatistic a P.2.1) := by
          congr 1
          funext P
          exact linear_rankPairOccupancy a P
    _ = 2 * finiteVariance (subsetProbability w r)
        (fun S => rankLinearStatistic a S.1) :=
      finiteVariance_iid_sum hnorm
        (fun S : RankSubset ι r => rankLinearStatistic a S.1)
    _ = 2 * quadraticForm (covarianceMatrix w r) a := by
      rw [finiteVariance_rankLinearStatistic]

theorem adjacent_occupancy_mean_difference
    (w : ι → ℝ) (hw : ∀ i, 0 < w i) (q : ℕ)
    (hq : q + 2 ≤ Fintype.card ι) (a : ι → ℝ) :
    rankPairExpectation w q (q + 2)
        (fun A B => ∑ i, a i * (occupancy A.1 B.1 i : ℝ)) -
      rankPairExpectation w (q + 1) (q + 1)
        (fun A B => ∑ i, a i * (occupancy A.1 B.1 i : ℝ)) =
      ∑ i, a i * rankCurvature w q i := by
  have hq0 : q ≤ Fintype.card ι := by omega
  have hq1 : q + 1 ≤ Fintype.card ι := by omega
  rw [rankPairExpectation_linearOccupancy w hw q (q + 2) hq0 hq a,
    rankPairExpectation_linearOccupancy w hw (q + 1) (q + 1) hq1 hq1 a]
  calc
    ((∑ i, a i * inclusionMean w q i) +
          ∑ i, a i * inclusionMean w (q + 2) i) -
        ((∑ i, a i * inclusionMean w (q + 1) i) +
          ∑ i, a i * inclusionMean w (q + 1) i) =
      (∑ i, (a i * inclusionMean w q i +
          a i * inclusionMean w (q + 2) i)) -
        ∑ i, (a i * inclusionMean w (q + 1) i +
          a i * inclusionMean w (q + 1) i) := by
            rw [Finset.sum_add_distrib, Finset.sum_add_distrib]
    _ = ∑ i, (
        (a i * inclusionMean w q i + a i * inclusionMean w (q + 2) i) -
          (a i * inclusionMean w (q + 1) i +
            a i * inclusionMean w (q + 1) i)) := by
              rw [Finset.sum_sub_distrib]
    _ = ∑ i, a i * rankCurvature w q i := by
      apply Finset.sum_congr rfl
      intro i _
      unfold rankCurvature
      ring

theorem linear_rankPairOccupancy_eq_linearOccupancy
    (a : ι → ℝ) (P : RankSubset ι r × RankSubset ι r) :
    (∑ i, a i * rankPairOccupancy P i) =
      ∑ i, a i * (occupancy P.1.1 P.2.1 i : ℝ) := by
  rw [linear_rankPairOccupancy, linearOccupancy_eq_rankLinear]

theorem finiteExpectation_rankPairOccupancy
    (w : ι → ℝ) (r : ℕ) (a : ι → ℝ) :
    finiteExpectation (rankPairProbability w r)
        (fun P => ∑ i, a i * rankPairOccupancy P i) =
      rankPairExpectation w r r
        (fun A B => ∑ i, a i * (occupancy A.1 B.1 i : ℝ)) := by
  calc
    finiteExpectation (rankPairProbability w r)
        (fun P => ∑ i, a i * rankPairOccupancy P i) =
      finiteExpectation (rankPairProbability w r)
        (fun P => ∑ i, a i * (occupancy P.1.1 P.2.1 i : ℝ)) := by
          congr 1
          funext P
          exact linear_rankPairOccupancy_eq_linearOccupancy a P
    _ = _ := by
      simpa using
        (finiteExpectation_rankPair w r
          (fun A B => ∑ i, a i * (occupancy A.1 B.1 i : ℝ)))

theorem rankCurvature_as_tilt_covariance
    (w : ι → ℝ) (hw : ∀ i, 0 < w i) (q : ℕ)
    (hq : q + 2 ≤ Fintype.card ι) (a : ι → ℝ) :
    (∑ i, a i * rankCurvature w q i) =
      finiteCovariance (rankPairProbability w (q + 1))
        (fun P => ∑ i, a i * rankPairOccupancy P i)
        (fun P => occupancyTilt P.1.1 P.2.1) /
          adjacentTheta w q := by
  let F : RankSubset ι (q + 1) × RankSubset ι (q + 1) → ℝ :=
    fun P => ∑ i, a i * rankPairOccupancy P i
  let φ : RankSubset ι (q + 1) × RankSubset ι (q + 1) → ℝ :=
    fun P => occupancyTilt P.1.1 P.2.1
  let EP : ℝ := rankPairExpectation w (q + 1) (q + 1)
    (fun A B => ∑ i, a i * (occupancy A.1 B.1 i : ℝ))
  let EQ : ℝ := rankPairExpectation w q (q + 2)
    (fun A B => ∑ i, a i * (occupancy A.1 B.1 i : ℝ))
  have hq1 : q + 1 ≤ Fintype.card ι := by omega
  have hnorm := rankPairProbability_sum w hw (q + 1) hq1
  have htheta := expected_occupancyTilt w hw q hq
  have hthetaPos := adjacentTheta_pos w hw q hq
  have hthetaNe : adjacentTheta w q ≠ 0 := ne_of_gt hthetaPos
  have hEF : finiteExpectation (rankPairProbability w (q + 1)) F = EP := by
    dsimp only [F, EP]
    exact finiteExpectation_rankPairOccupancy w (q + 1) a
  have hEφ : finiteExpectation (rankPairProbability w (q + 1)) φ =
      adjacentTheta w q := by
    dsimp only [φ]
    exact htheta
  have hEFφ :
      finiteExpectation (rankPairProbability w (q + 1))
          (fun P => F P * φ P) = adjacentTheta w q * EQ := by
    have hlr := occupancy_likelihood_ratio w hw q hq
      (fun O => ∑ i, a i * (O i : ℝ))
    calc
      finiteExpectation (rankPairProbability w (q + 1))
          (fun P => F P * φ P) =
        rankPairExpectation w (q + 1) (q + 1)
          (fun A B => occupancyTilt A.1 B.1 *
            (∑ i, a i * (occupancy A.1 B.1 i : ℝ))) := by
              rw [← finiteExpectation_rankPair]
              congr 1
              funext P
              dsimp only [F, φ]
              rw [linear_rankPairOccupancy_eq_linearOccupancy]
              ring
      _ = adjacentTheta w q * EQ := by
        simpa only [EQ] using hlr
  have hdiff : EQ - EP = ∑ i, a i * rankCurvature w q i := by
    dsimp only [EQ, EP]
    exact adjacent_occupancy_mean_difference w hw q hq a
  rw [finiteCovariance_expansion hnorm]
  change (∑ i, a i * rankCurvature w q i) =
    (finiteExpectation (rankPairProbability w (q + 1))
        (fun P => F P * φ P) -
      finiteExpectation (rankPairProbability w (q + 1)) F *
        finiteExpectation (rankPairProbability w (q + 1)) φ) /
      adjacentTheta w q
  rw [hEFφ, hEF, hEφ]
  field_simp [hthetaNe]
  linarith

/-- The adjacent-rank curvature inequality for the external-field law.  This
is the paper's finite-dimensional three-rank estimate in variational form. -/
theorem externalField_adjacent_rank_curvature
    (w : ι → ℝ) (hw : ∀ i, 0 < w i) (q : ℕ)
    (hq : q + 2 ≤ Fintype.card ι) :
    ∀ a : ι → ℝ,
      (∑ i, a i * rankCurvature w q i) ^ 2 ≤
        (2 * (1 - adjacentTheta w q) / adjacentTheta w q) *
          quadraticForm (covarianceMatrix w (q + 1)) a := by
  have hq1 : q + 1 ≤ Fintype.card ι := by omega
  exact adjacent_rank_curvature_of_occupancy_identity
    (p := rankPairProbability w (q + 1))
    (hp := rankPairProbability_nonnegative w hw (q + 1) hq1)
    (hnorm := rankPairProbability_sum w hw (q + 1) hq1)
    (φ := fun P => occupancyTilt P.1.1 P.2.1)
    (hφ0 := fun P => occupancyTilt_nonnegative P.1.1 P.2.1)
    (hφ1 := fun P => occupancyTilt_le_one P.1.1 P.2.1)
    (θ := adjacentTheta w q)
    (hθ := expected_occupancyTilt w hw q hq)
    (hθpos := adjacentTheta_pos w hw q hq)
    (O := rankPairOccupancy)
    (κ := rankCurvature w q)
    (rankVariance := fun a =>
      quadraticForm (covarianceMatrix w (q + 1)) a)
    (hrank_nonneg := fun a =>
      covariance_quadratic_nonnegative w hw hq1 a)
    (hOvar := rankPairOccupancy_variance w hw (q + 1) hq1)
    (hkappa := rankCurvature_as_tilt_covariance w hw q hq)

end

end EffectiveResistance
