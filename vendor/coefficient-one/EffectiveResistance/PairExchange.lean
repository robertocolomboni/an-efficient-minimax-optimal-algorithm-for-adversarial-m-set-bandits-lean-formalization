import EffectiveResistance.PairCellFormulas
import EffectiveResistance.ThreeSliceRegression

/-!
# Pair-exchange decomposition

The two middle endpoint states have the same background law.  This file
formalizes the resulting orthogonal decomposition of the endpoint-difference
regression loss.
-/

open scoped BigOperators

namespace EffectiveResistance

noncomputable section

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- Split a finite sum into two distinguished coordinates and their
complement. -/
theorem sum_eq_pair_add_complement (i j : ι) (hij : i ≠ j) (f : ι → ℝ) :
    (∑ k, f k) = f i + f j + ∑ k : PairComplement i j, f k.1 := by
  have hj : j ∈ Finset.univ.erase i := by
    exact Finset.mem_erase.mpr ⟨hij.symm, Finset.mem_univ j⟩
  have hmem : ∀ k : ι, k ∈ (Finset.univ.erase i).erase j ↔
      k ≠ i ∧ k ≠ j := by
    intro k
    simp only [Finset.mem_erase, Finset.mem_univ, and_true]
    exact and_comm
  have hsub := Finset.sum_subtype
    (p := fun k : ι => k ≠ i ∧ k ≠ j)
    (F := inferInstanceAs (Fintype (PairComplement i j)))
    ((Finset.univ.erase i).erase j) hmem f
  calc
    (∑ k, f k) = (∑ k ∈ Finset.univ.erase i, f k) + f i := by
      rw [Finset.sum_erase_add _ _ (Finset.mem_univ i)]
    _ = (∑ k ∈ (Finset.univ.erase i).erase j, f k) + f j + f i := by
      rw [Finset.sum_erase_add _ _ hj]
    _ = f i + f j + ∑ k : PairComplement i j, f k.1 := by
      rw [hsub]
      ring
variable {i j : ι} {q : ℕ}

theorem rankLinearStatistic_liftPair11
    (a : PairComplement i j → ℝ) (hij : i ≠ j)
    (A : RankSubset (PairComplement i j) q) :
    (∑ k : PairComplement i j,
      a k * indicator k.1 (liftPair11 i j hij A).1) =
      rankLinearStatistic a A.1 := by
  unfold rankLinearStatistic
  apply Finset.sum_congr rfl
  intro k _
  congr 1
  simp [indicator, liftPair11, mem_liftPairBackground, k.2]

theorem rankLinearStatistic_liftPair10
    (a : PairComplement i j → ℝ)
    (A : RankSubset (PairComplement i j) (q + 1)) :
    (∑ k : PairComplement i j,
      a k * indicator k.1 (liftPair10 i j A).1) =
      rankLinearStatistic a A.1 := by
  unfold rankLinearStatistic
  apply Finset.sum_congr rfl
  intro k _
  congr 1
  simp [indicator, liftPair10, mem_liftPairBackground, k.2]

theorem rankLinearStatistic_liftPair01
    (a : PairComplement i j → ℝ)
    (A : RankSubset (PairComplement i j) (q + 1)) :
    (∑ k : PairComplement i j,
      a k * indicator k.1 (liftPair01 i j A).1) =
      rankLinearStatistic a A.1 := by
  unfold rankLinearStatistic
  apply Finset.sum_congr rfl
  intro k _
  congr 1
  simp [indicator, liftPair01, mem_liftPairBackground, k.2]

theorem rankLinearStatistic_liftPair00
    (a : PairComplement i j → ℝ)
    (A : RankSubset (PairComplement i j) (q + 2)) :
    (∑ k : PairComplement i j,
      a k * indicator k.1 (liftPair00 i j A).1) =
      rankLinearStatistic a A.1 := by
  unfold rankLinearStatistic
  apply Finset.sum_congr rfl
  intro k _
  congr 1
  simp [indicator, liftPair00, mem_liftPairBackground, k.2]

def pairBackgroundLinearMean (w : ι → ℝ) (m : ℕ) (i j : ι)
    (a : PairComplement i j → ℝ) : ℝ :=
  ∑ k : PairComplement i j, a k * inclusionMean w m k.1

theorem centeredBackground_of_indicator_sum
    (w : ι → ℝ) (m : ℕ) (i j : ι)
    (a : PairComplement i j → ℝ) (S : Finset ι) (A : Finset (PairComplement i j))
    (h : (∑ k : PairComplement i j, a k * indicator k.1 S) =
      rankLinearStatistic a A) :
    (∑ k : PairComplement i j,
      a k * (indicator k.1 S - inclusionMean w m k.1)) =
      rankLinearStatistic a A - pairBackgroundLinearMean w m i j a := by
  unfold pairBackgroundLinearMean
  calc
    (∑ k : PairComplement i j,
        a k * (indicator k.1 S - inclusionMean w m k.1)) =
      ∑ k : PairComplement i j,
        (a k * indicator k.1 S - a k * inclusionMean w m k.1) := by
          apply Finset.sum_congr rfl
          intro k _
          ring
    _ = (∑ k : PairComplement i j, a k * indicator k.1 S) -
        ∑ k : PairComplement i j, a k * inclusionMean w m k.1 := by
          rw [Finset.sum_sub_distrib]
    _ = _ := by rw [h]

@[simp] theorem centeredBackground_liftPair11
    (w : ι → ℝ) (m : ℕ) (a : PairComplement i j → ℝ)
    (hij : i ≠ j) (A : RankSubset (PairComplement i j) q) :
    (∑ k : PairComplement i j,
      a k * (indicator k.1 (liftPair11 i j hij A).1 - inclusionMean w m k.1)) =
      rankLinearStatistic a A.1 - pairBackgroundLinearMean w m i j a :=
  centeredBackground_of_indicator_sum w m i j a _ _
    (rankLinearStatistic_liftPair11 a hij A)

@[simp] theorem centeredBackground_liftPair10
    (w : ι → ℝ) (m : ℕ) (a : PairComplement i j → ℝ)
    (A : RankSubset (PairComplement i j) (q + 1)) :
    (∑ k : PairComplement i j,
      a k * (indicator k.1 (liftPair10 i j A).1 - inclusionMean w m k.1)) =
      rankLinearStatistic a A.1 - pairBackgroundLinearMean w m i j a :=
  centeredBackground_of_indicator_sum w m i j a _ _
    (rankLinearStatistic_liftPair10 a A)

@[simp] theorem centeredBackground_liftPair01
    (w : ι → ℝ) (m : ℕ) (a : PairComplement i j → ℝ)
    (A : RankSubset (PairComplement i j) (q + 1)) :
    (∑ k : PairComplement i j,
      a k * (indicator k.1 (liftPair01 i j A).1 - inclusionMean w m k.1)) =
      rankLinearStatistic a A.1 - pairBackgroundLinearMean w m i j a :=
  centeredBackground_of_indicator_sum w m i j a _ _
    (rankLinearStatistic_liftPair01 a A)

@[simp] theorem centeredBackground_liftPair00
    (w : ι → ℝ) (m : ℕ) (a : PairComplement i j → ℝ)
    (A : RankSubset (PairComplement i j) (q + 2)) :
    (∑ k : PairComplement i j,
      a k * (indicator k.1 (liftPair00 i j A).1 - inclusionMean w m k.1)) =
      rankLinearStatistic a A.1 - pairBackgroundLinearMean w m i j a :=
  centeredBackground_of_indicator_sum w m i j a _ _
    (rankLinearStatistic_liftPair00 a A)

namespace PairTable

variable (P : PairTable)

def pairRegressionLoss (w : ι → ℝ) (m : ℕ) (i j : ι)
    (a : PairComplement i j → ℝ) : ℝ :=
  expectation w m fun S =>
    ((indicator i S.1 - indicator j S.1) - P.δ -
      ∑ k : PairComplement i j,
        a k * (indicator k.1 S.1 - inclusionMean w m k.1)) ^ 2

end PairTable

theorem externalFieldPairTable_delta_eq_mean_sub
    (w : ι → ℝ) (hw : ∀ k, 0 < w k) (m : ℕ)
    (hm : m ≤ Fintype.card ι) (i j : ι) :
    (externalFieldPairTable w hw hm i j).δ =
      inclusionMean w m i - inclusionMean w m j := by
  have hμ := externalFieldPairTable_means w hw hm i j
  simp only [PairTable.δ, PairTable.μi, PairTable.μj] at hμ ⊢
  linarith [hμ.1, hμ.2]

/-- Every centered linear statistic whose endpoint coefficients differ by
two is an endpoint-difference regression residual. -/
theorem centeredLinearStatistic_eq_pairRegressionResidual
    (w : ι → ℝ) (hw : ∀ k, 0 < w k) (m : ℕ)
    (hm : m ≤ Fintype.card ι) (i j : ι) (hij : i ≠ j)
    (c : ι → ℝ) (hc : c i - c j = 2) (S : RankSubset ι m) :
    centeredLinearStatistic w m c S =
      (indicator i S.1 - indicator j S.1) -
        (externalFieldPairTable w hw hm i j).δ -
        ∑ k : PairComplement i j,
          (1 - (c k.1 - c j)) *
            (indicator k.1 S.1 - inclusionMean w m k.1) := by
  let P := externalFieldPairTable w hw hm i j
  let y : ι → ℝ := fun k => centeredIndicator w m k S
  have hδ : P.δ = inclusionMean w m i - inclusionMean w m j :=
    externalFieldPairTable_delta_eq_mean_sub w hw m hm i j
  have hsum : ∑ k, y k = 0 := by
    simpa only [y] using sum_centeredIndicator w hw hm S
  have hsumSplit := sum_eq_pair_add_complement i j hij y
  have hbackground :
      (∑ k : PairComplement i j, y k.1) = -y i - y j := by
    linarith [hsum, hsumSplit]
  have hcoefficient : c i = c j + 2 := by
    linarith [hc]
  have hweightedSplit := sum_eq_pair_add_complement i j hij
    (fun k => c k * y k)
  have hregressor :
      (∑ k : PairComplement i j,
          (1 - (c k.1 - c j)) * y k.1) =
        (∑ k : PairComplement i j, y k.1) -
          (∑ k : PairComplement i j, c k.1 * y k.1) +
          c j * (∑ k : PairComplement i j, y k.1) := by
    calc
      (∑ k : PairComplement i j,
          (1 - (c k.1 - c j)) * y k.1) =
          ∑ k : PairComplement i j,
            ((y k.1 - c k.1 * y k.1) + c j * y k.1) := by
              apply Finset.sum_congr rfl
              intro k _
              ring
      _ = (∑ k : PairComplement i j, y k.1) -
          (∑ k : PairComplement i j, c k.1 * y k.1) +
          c j * (∑ k : PairComplement i j, y k.1) := by
            rw [Finset.sum_add_distrib, Finset.sum_sub_distrib,
              ← Finset.mul_sum]
  have hendpoint :
      (indicator i S.1 - indicator j S.1) - P.δ = y i - y j := by
    rw [hδ]
    simp only [y, centeredIndicator]
    ring
  change (∑ k, c k * y k) =
    (indicator i S.1 - indicator j S.1) - P.δ -
      ∑ k : PairComplement i j,
        (1 - (c k.1 - c j)) * y k.1
  calc
    (∑ k, c k * y k) =
        c i * y i + c j * y j +
          ∑ k : PairComplement i j, c k.1 * y k.1 := hweightedSplit
    _ = (y i - y j) -
        ∑ k : PairComplement i j,
          (1 - (c k.1 - c j)) * y k.1 := by
            rw [hregressor, hbackground, hcoefficient]
            ring
    _ = (indicator i S.1 - indicator j S.1) - P.δ -
        ∑ k : PairComplement i j,
          (1 - (c k.1 - c j)) * y k.1 := by
            rw [hendpoint]

theorem externalFieldPairTable_vi_eq_covariance_diagonal
    (w : ι → ℝ) (hw : ∀ k, 0 < w k) (m : ℕ)
    (hm : m ≤ Fintype.card ι) (i j : ι) :
    (externalFieldPairTable w hw hm i j).vi = covarianceMatrix w m i i := by
  rw [covariance_diagonal w hw hm i]
  simp only [PairTable.vi]
  rw [(externalFieldPairTable_means w hw hm i j).1]

theorem externalFieldPairTable_vj_eq_covariance_diagonal
    (w : ι → ℝ) (hw : ∀ k, 0 < w k) (m : ℕ)
    (hm : m ≤ Fintype.card ι) (i j : ι) :
    (externalFieldPairTable w hw hm i j).vj = covarianceMatrix w m j j := by
  rw [covariance_diagonal w hw hm j]
  simp only [PairTable.vj]
  rw [(externalFieldPairTable_means w hw hm i j).2]

/-- The pair-regression objective is the covariance quadratic form after the
fixed-rank gauge has normalized the endpoint coefficient difference to two. -/
theorem pairRegressionLoss_eq_quadraticForm_covariance
    (w : ι → ℝ) (hw : ∀ k, 0 < w k) (m : ℕ)
    (hm : m ≤ Fintype.card ι) (i j : ι) (hij : i ≠ j)
    (c : ι → ℝ) (hc : c i - c j = 2) :
    (externalFieldPairTable w hw hm i j).pairRegressionLoss w m i j
        (fun k => 1 - (c k.1 - c j)) =
      quadraticForm (covarianceMatrix w m) c := by
  rw [quadraticForm_covariance]
  unfold PairTable.pairRegressionLoss expectation
  apply Finset.sum_congr rfl
  intro S _
  congr 1
  exact congrArg (fun x : ℝ => x ^ 2)
    (centeredLinearStatistic_eq_pairRegressionResidual
      w hw m hm i j hij c hc S).symm

/-- The scalar cancellation behind pair exchange, integrated against an
arbitrary normalized finite weight. -/
theorem weighted_pair_exchange_sum
    {K : Type*} [Fintype K]
    (p : K → ℝ) (hp : ∑ x, p x = 1) (U : K → ℝ)
    {p10 p01 s : ℝ} (hs : s = p10 + p01) (hspos : 0 < s) :
    p10 * (∑ x, p x * (U x + 2 * p01 / s) ^ 2) +
      p01 * (∑ x, p x * (U x - 2 * p10 / s) ^ 2) =
      4 * p10 * p01 / s + s * (∑ x, p x * U x ^ 2) := by
  rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
  calc
    (∑ x, (p10 * (p x * (U x + 2 * p01 / s) ^ 2) +
        p01 * (p x * (U x - 2 * p10 / s) ^ 2))) =
      ∑ x, p x * (4 * p10 * p01 / s + s * U x ^ 2) := by
        apply Finset.sum_congr rfl
        intro x _
        field_simp [ne_of_gt hspos]
        rw [hs]
        ring
    _ = 4 * p10 * p01 / s + s * (∑ x, p x * U x ^ 2) := by
      calc
        (∑ x, p x * (4 * p10 * p01 / s + s * U x ^ 2)) =
            ∑ x, (p x * (4 * p10 * p01 / s) +
              s * (p x * U x ^ 2)) := by
              apply Finset.sum_congr rfl
              intro x _
              ring
        _ = (∑ x, p x * (4 * p10 * p01 / s)) +
              ∑ x, s * (p x * U x ^ 2) := by
                rw [Finset.sum_add_distrib]
        _ = (∑ x, p x) * (4 * p10 * p01 / s) +
              s * (∑ x, p x * U x ^ 2) := by
                rw [Finset.sum_mul, Finset.mul_sum]
        _ = _ := by rw [hp, one_mul]

namespace PairTable

/-- Exact pair-exchange decomposition for the finite external-field law. -/
theorem externalField_pairExchange_loss_decomposition
    (P : PairTable) (w : ι → ℝ) (hw : ∀ k, 0 < w k)
    (i j : ι) (hij : i ≠ j) (q : ℕ)
    (hm : q + 2 ≤ Fintype.card ι)
    (hq : q + 2 ≤ Fintype.card (PairComplement i j))
    (hP : P = externalFieldPairTable w hw hm i j)
    (a : PairComplement i j → ℝ) :
    P.pairRegressionLoss w (q + 2) i j a =
      4 * P.p10 * P.p01 / P.s +
        P.scaledThreeSliceLoss (pairRestrictedWeight w i j) q
          (P.δ / P.s)
          (P.δ - pairBackgroundLinearMean w (q + 2) i j a) a := by
  subst P
  let P := externalFieldPairTable w hw hm i j
  let z := pairRestrictedWeight w i j
  let M := pairBackgroundLinearMean w (q + 2) i j a
  change P.pairRegressionLoss w (q + 2) i j a =
    4 * P.p10 * P.p01 / P.s +
      P.scaledThreeSliceLoss z q (P.δ / P.s) (P.δ - M) a
  have hcells := pairCells_pos_of_background_rank w hw i j hij q hq
  have hspos : 0 < P.s := by
    apply P.s_pos
    exact hcells.2.1
  have hq1 : q + 1 ≤ Fintype.card (PairComplement i j) := by omega
  have hnorm :
      ∑ A : RankSubset (PairComplement i j) (q + 1),
        subsetProbability z (q + 1) A = 1 :=
    sum_subsetProbability z (fun k => hw k.1) hq1
  unfold pairRegressionLoss
  rw [expectation_pairDecomposition w hw i j hij q hq]
  change
    P.p11 * _ + P.p10 * _ + P.p01 * _ + P.p00 * _ = _
  simp only [centeredBackground_liftPair11, centeredBackground_liftPair10,
    centeredBackground_liftPair01, centeredBackground_liftPair00]
  simp [indicator, right_not_mem_liftPair10 i j hij,
    left_not_mem_liftPair01 i j hij]
  change
    P.p11 * expectation z q
        (fun A => (-P.δ - (rankLinearStatistic a A.1 - M)) ^ 2) +
      P.p10 * expectation z (q + 1)
        (fun A => (1 - P.δ - (rankLinearStatistic a A.1 - M)) ^ 2) +
      P.p01 * expectation z (q + 1)
        (fun A => (-1 - P.δ - (rankLinearStatistic a A.1 - M)) ^ 2) +
      P.p00 * expectation z (q + 2)
        (fun A => (-P.δ - (rankLinearStatistic a A.1 - M)) ^ 2) =
      4 * P.p10 * P.p01 / P.s +
        P.scaledThreeSliceLoss z q (P.δ / P.s) (P.δ - M) a
  let U : RankSubset (PairComplement i j) (q + 1) → ℝ :=
    fun A => P.δ / P.s - (P.δ - M) - rankLinearStatistic a A.1
  have hplus (A : RankSubset (PairComplement i j) (q + 1)) :
      1 - P.δ - (rankLinearStatistic a A.1 - M) =
        U A + 2 * P.p01 / P.s := by
    dsimp only [U]
    field_simp [ne_of_gt hspos]
    simp only [PairTable.δ, PairTable.s]
    ring
  have hminus (A : RankSubset (PairComplement i j) (q + 1)) :
      -1 - P.δ - (rankLinearStatistic a A.1 - M) =
        U A - 2 * P.p10 / P.s := by
    dsimp only [U]
    field_simp [ne_of_gt hspos]
    simp only [PairTable.δ, PairTable.s]
    ring
  have hmiddle :
      P.p10 * expectation z (q + 1)
          (fun A => (1 - P.δ - (rankLinearStatistic a A.1 - M)) ^ 2) +
        P.p01 * expectation z (q + 1)
          (fun A => (-1 - P.δ - (rankLinearStatistic a A.1 - M)) ^ 2) =
        4 * P.p10 * P.p01 / P.s +
          P.s * expectation z (q + 1) (fun A => U A ^ 2) := by
    have hx := weighted_pair_exchange_sum
      (p := fun A : RankSubset (PairComplement i j) (q + 1) =>
        subsetProbability z (q + 1) A)
      hnorm U (show P.s = P.p10 + P.p01 from rfl) hspos
    unfold expectation
    simpa only [hplus, hminus] using hx
  have houter (t : ℕ) :
      expectation z t
          (fun A => (-P.δ - (rankLinearStatistic a A.1 - M)) ^ 2) =
        expectation z t
          (fun A => (0 - (P.δ - M) - rankLinearStatistic a A.1) ^ 2) := by
    unfold expectation
    apply Finset.sum_congr rfl
    intro A _
    congr 1
    ring
  rw [houter q, houter (q + 2)]
  unfold scaledThreeSliceLoss
  change _ = 4 * P.p10 * P.p01 / P.s +
    (P.p11 * expectation z q
        (fun A => (0 - (P.δ - M) - rankLinearStatistic a A.1) ^ 2) +
      P.s * expectation z (q + 1) (fun A => U A ^ 2) +
      P.p00 * expectation z (q + 2)
        (fun A => (0 - (P.δ - M) - rankLinearStatistic a A.1) ^ 2))
  linarith [hmiddle]

/-- Interior-rank lower bound for every endpoint-difference regression
coefficient.  This is the analytic heart of the resistance theorem. -/
theorem externalField_pairRegressionLoss_lower_bound
    (P : PairTable) (w : ι → ℝ) (hw : ∀ k, 0 < w k)
    (i j : ι) (hij : i ≠ j) (q : ℕ)
    (hm : q + 2 ≤ Fintype.card ι)
    (hq : q + 2 ≤ Fintype.card (PairComplement i j))
    (hP : P = externalFieldPairTable w hw hm i j)
    (a : PairComplement i j → ℝ) :
    4 * P.vi * P.vj / (P.vi + P.vj) ≤
      P.pairRegressionLoss w (q + 2) i j a := by
  subst P
  let P := externalFieldPairTable w hw hm i j
  let z := pairRestrictedWeight w i j
  let M := pairBackgroundLinearMean w (q + 2) i j a
  change 4 * P.vi * P.vj / (P.vi + P.vj) ≤
    P.pairRegressionLoss w (q + 2) i j a
  have hcells := pairCells_pos_of_background_rank w hw i j hij q hq
  have h11 : 0 < P.p11 := hcells.1
  have h10 : 0 < P.p10 := hcells.2.1
  have h01 : 0 < P.p01 := hcells.2.2.1
  have h00 : 0 < P.p00 := hcells.2.2.2
  have hs : 0 < P.s := P.s_pos h10
  have hvi : 0 < P.vi := P.vi_pos h11 h10 h01
  have hvj : 0 < P.vj := P.vj_pos h11 h10 h01
  have hvsum : 0 < P.vi + P.vj := add_pos hvi hvj
  have hωpos : 0 < P.ω := by
    change 0 < pairCell10 w (q + 2) i j * pairCell01 w (q + 2) i j -
      pairCell11 w (q + 2) i j * pairCell00 w (q + 2) i j
    exact pairCell_omega_pos w hw i j hij q hq
  have htheta : adjacentTheta z q =
      P.p11 * P.p00 / (P.p10 * P.p01) := by
    exact adjacentTheta_eq_pairCell_ratio w hw i j hij q hq
  have hslice := P.externalField_scaledThreeSliceLoss_bound
    z (fun k => hw k.1) q hq h11 h10 h01 h00 hωpos.le htheta
    (P.δ / P.s) (P.δ - M) a
  have hslice' :
      4 * P.p11 * P.p00 * P.δ ^ 2 /
          (P.s * (P.vi + P.vj)) ≤
        P.scaledThreeSliceLoss z q (P.δ / P.s) (P.δ - M) a := by
    convert hslice using 1
    field_simp [ne_of_gt hs, ne_of_gt hvsum]
  have hpair := P.harmonic_conductance_bound hωpos.le
  have hfraction :
      4 * P.vi * P.vj / (P.vi + P.vj) ≤
        4 * P.p10 * P.p01 / P.s +
          4 * P.p11 * P.p00 * P.δ ^ 2 /
            (P.s * (P.vi + P.vj)) := by
    have hscaled := mul_le_mul_of_nonneg_left hpair
      (show 0 ≤ 4 / (P.s * (P.vi + P.vj)) by positivity)
    calc
      4 * P.vi * P.vj / (P.vi + P.vj) =
          (4 / (P.s * (P.vi + P.vj))) * (P.s * P.vi * P.vj) := by
            field_simp [ne_of_gt hs, ne_of_gt hvsum]
            <;> ring
      _ ≤ (4 / (P.s * (P.vi + P.vj))) *
          (P.p10 * P.p01 * (P.vi + P.vj) +
            P.p11 * P.p00 * P.δ ^ 2) := hscaled
      _ = 4 * P.p10 * P.p01 / P.s +
          4 * P.p11 * P.p00 * P.δ ^ 2 /
            (P.s * (P.vi + P.vj)) := by
              field_simp [ne_of_gt hs, ne_of_gt hvsum]
              <;> ring
  rw [P.externalField_pairExchange_loss_decomposition
    w hw i j hij q hm hq rfl a]
  exact hfraction.trans (by
    simpa only [z, M, add_comm, add_left_comm, add_assoc] using
      add_le_add_left hslice' (4 * P.p10 * P.p01 / P.s))

end PairTable

/-- Interior-rank covariance-energy form of the main analytic estimate. -/
theorem externalField_covariance_energy_lower_bound
    (w : ι → ℝ) (hw : ∀ k, 0 < w k)
    (i j : ι) (hij : i ≠ j) (q : ℕ)
    (hm : q + 2 ≤ Fintype.card ι)
    (hq : q + 2 ≤ Fintype.card (PairComplement i j))
    (c : ι → ℝ) (hc : c i - c j = 2) :
    4 * covarianceMatrix w (q + 2) i i *
          covarianceMatrix w (q + 2) j j /
        (covarianceMatrix w (q + 2) i i +
          covarianceMatrix w (q + 2) j j) ≤
      quadraticForm (covarianceMatrix w (q + 2)) c := by
  let P := externalFieldPairTable w hw hm i j
  let a : PairComplement i j → ℝ := fun k => 1 - (c k.1 - c j)
  have hlower := P.externalField_pairRegressionLoss_lower_bound
    w hw i j hij q hm hq rfl a
  have hloss := pairRegressionLoss_eq_quadraticForm_covariance
    w hw (q + 2) hm i j hij c hc
  have hvi := externalFieldPairTable_vi_eq_covariance_diagonal
    w hw (q + 2) hm i j
  have hvj := externalFieldPairTable_vj_eq_covariance_diagonal
    w hw (q + 2) hm i j
  rw [← hvi, ← hvj]
  change 4 * P.vi * P.vj / (P.vi + P.vj) ≤
    quadraticForm (covarianceMatrix w (q + 2)) c
  rw [← hloss]
  exact hlower

end

end EffectiveResistance
