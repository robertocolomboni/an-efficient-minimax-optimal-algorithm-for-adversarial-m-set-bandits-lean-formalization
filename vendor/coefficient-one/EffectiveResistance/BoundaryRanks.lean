import EffectiveResistance.MainTheorem

/-!
# Boundary ranks

The rank-one law is categorical.  The top rank is obtained from it by
particle--hole complementation.
-/

open scoped BigOperators
open Matrix

namespace EffectiveResistance

noncomputable section

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

theorem inclusionMean_nonnegative
    (w : ι → ℝ) (hw : ∀ k, 0 < w k) (m : ℕ)
    (hm : m ≤ Fintype.card ι) (i : ι) :
    0 ≤ inclusionMean w m i := by
  unfold inclusionMean
  exact expectation_nonnegative w hw hm fun S => indicator_nonnegative i S.1

theorem inclusionMean_rankOne_pos
    (w : ι → ℝ) (hw : ∀ k, 0 < w k)
    (i : ι) : 0 < inclusionMean w 1 i := by
  have hm : 1 ≤ Fintype.card ι := by
    exact Fintype.card_pos_iff.mpr ⟨i⟩
  let S : RankSubset ι 1 := ⟨{i}, Finset.card_singleton i⟩
  unfold inclusionMean expectation
  refine Finset.sum_pos' (fun T _ =>
    mul_nonneg (subsetProbability_pos w hw hm T).le
      (indicator_nonnegative i T.1)) ?_
  refine ⟨S, Finset.mem_univ S, ?_⟩
  have hprob := subsetProbability_pos w hw hm S
  have hind : indicator i S.1 = 1 := by
    simp [S, indicator]
  change 0 < subsetProbability w 1 S * indicator i S.1
  rw [hind]
  simpa using hprob

theorem pairCell11_rankOne_eq_zero
    (w : ι → ℝ) (i j : ι) (hij : i ≠ j) :
    pairCell11 w 1 i j = 0 := by
  unfold pairCell11 expectation
  apply Finset.sum_eq_zero
  intro S _
  have hind : indicator i S.1 * indicator j S.1 = 0 := by
    by_cases hi : i ∈ S.1
    · by_cases hj : j ∈ S.1
      · have hlt : 1 < S.1.card :=
          Finset.one_lt_card.mpr ⟨i, hi, j, hj, hij⟩
        omega
      · simp [indicator, hi, hj]
    · simp [indicator, hi]
  change subsetProbability w 1 S *
    (indicator i S.1 * indicator j S.1) = 0
  rw [hind]
  ring

/-- Covariance matrix of the categorical rank-one law. -/
theorem covarianceMatrix_rankOne
    (w : ι → ℝ) (hw : ∀ k, 0 < w k)
    (hm : 1 ≤ Fintype.card ι) :
    covarianceMatrix w 1 =
      Matrix.diagonal (inclusionMean w 1) -
        Matrix.vecMulVec (inclusionMean w 1) (inclusionMean w 1) := by
  ext i j
  by_cases hij : i = j
  · subst j
    rw [covariance_diagonal w hw hm i]
    simp [Matrix.vecMulVec]
    ring
  · rw [covariance_eq_pairCell11_sub_means w hw hm i j,
      pairCell11_rankOne_eq_zero w i j hij]
    simp [Matrix.vecMulVec, hij]

/-- Explicit solution of the categorical endpoint demand equation. -/
def rankOnePairPotential (μ : ι → ℝ) (i j : ι) : ι → ℝ :=
  fun k => if k = i then 1 / μ i else if k = j then -(1 / μ j) else 0

theorem rankOnePairPotential_weighted_sum
    (μ : ι → ℝ) (i j : ι) (hij : i ≠ j)
    (hμi : 0 < μ i) (hμj : 0 < μ j) :
    ∑ k, μ k * rankOnePairPotential μ i j k = 0 := by
  unfold rankOnePairPotential
  calc
    (∑ k, μ k *
        (if k = i then 1 / μ i else if k = j then -(1 / μ j) else 0)) =
        (∑ k, if k = i then μ k * (1 / μ i) else 0) +
          ∑ k, if k = j then μ k * (-(1 / μ j)) else 0 := by
            rw [← Finset.sum_add_distrib]
            apply Finset.sum_congr rfl
            intro k _
            by_cases hki : k = i
            · subst k
              simp [hij]
            · by_cases hkj : k = j
              · subst k
                simp [hki]
              · simp [hki, hkj]
    _ = μ i * (1 / μ i) + μ j * (-(1 / μ j)) := by simp
    _ = 0 := by
      field_simp [ne_of_gt hμi, ne_of_gt hμj]
      norm_num

theorem covarianceMatrix_rankOne_solve_pairDemand
    (w : ι → ℝ) (hw : ∀ k, 0 < w k)
    (i j : ι) (hij : i ≠ j) :
    covarianceMatrix w 1 *ᵥ
        rankOnePairPotential (inclusionMean w 1) i j =
      pairDemand i j := by
  let μ := inclusionMean w 1
  have hμi : 0 < μ i := inclusionMean_rankOne_pos w hw i
  have hμj : 0 < μ j := inclusionMean_rankOne_pos w hw j
  have hm : 1 ≤ Fintype.card ι := Fintype.card_pos_iff.mpr ⟨i⟩
  have hweighted := rankOnePairPotential_weighted_sum μ i j hij hμi hμj
  rw [covarianceMatrix_rankOne w hw hm]
  funext k
  rw [Matrix.sub_mulVec]
  change (Matrix.diagonal μ *ᵥ rankOnePairPotential μ i j) k -
      (Matrix.vecMulVec μ μ *ᵥ rankOnePairPotential μ i j) k =
        pairDemand i j k
  rw [Matrix.mulVec_diagonal]
  simp only [Matrix.mulVec, dotProduct, Matrix.vecMulVec_apply]
  have hfactor :
      (∑ x, μ k * μ x * rankOnePairPotential μ i j x) =
        μ k * (∑ x, μ x * rankOnePairPotential μ i j x) := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro x _
    ring
  rw [hfactor]
  rw [hweighted]
  by_cases hki : k = i
  · subst k
    simp [rankOnePairPotential, pairDemand, hij, ne_of_gt hμi]
  · by_cases hkj : k = j
    · subst k
      simp [rankOnePairPotential, pairDemand, hki, hij,
        ne_of_gt hμj]
    · simp [rankOnePairPotential, pairDemand, hki, hkj]

/-- The endpoint resistance bound at rank one. -/
theorem externalField_effectiveResistance_bound_rankOne
    (w : ι → ℝ) (hw : ∀ k, 0 < w k)
    (N : ConductanceNetwork ι) (G : GreenKernel N)
    (i j : ι) (hij : i ≠ j)
    (hL : N.laplacian = covarianceMatrix w 1) :
    G.effectiveResistance i j ≤
      1 / covarianceMatrix w 1 i i + 1 / covarianceMatrix w 1 j j := by
  let μ := inclusionMean w 1
  have hm : 1 ≤ Fintype.card ι := Fintype.card_pos_iff.mpr ⟨i⟩
  have hμi : 0 < μ i := inclusionMean_rankOne_pos w hw i
  have hμj : 0 < μ j := inclusionMean_rankOne_pos w hw j
  have hsum : ∑ k, μ k = 1 := by
    simpa [μ] using sum_inclusionMean w hw hm
  have hsplit := sum_eq_pair_add_complement i j hij μ
  have hbackground : 0 ≤ ∑ k : PairComplement i j, μ k.1 :=
    Finset.sum_nonneg fun k _ => inclusionMean_nonnegative w hw 1 hm k.1
  have hpair : μ i + μ j ≤ 1 := by
    linarith [hsum, hsplit, hbackground]
  have hμi_lt : μ i < 1 := by linarith [hμj]
  have hμj_lt : μ j < 1 := by linarith [hμi]
  have hvi : 0 < covarianceMatrix w 1 i i := by
    rw [covariance_diagonal w hw hm i]
    exact mul_pos hμi (sub_pos.mpr hμi_lt)
  have hvj : 0 < covarianceMatrix w 1 j j := by
    rw [covariance_diagonal w hw hm j]
    exact mul_pos hμj (sub_pos.mpr hμj_lt)
  let x := rankOnePairPotential μ i j
  have hx : N.laplacian *ᵥ x = pairDemand i j := by
    rw [hL]
    exact covarianceMatrix_rankOne_solve_pairDemand w hw i j hij
  have hR := G.effectiveResistance_eq_solution_drop hij x hx
  have hxdrop : x i - x j = 1 / μ i + 1 / μ j := by
    simp [x, rankOnePairPotential, hij, Ne.symm hij]
  rw [hxdrop] at hR
  have hvi_le : covarianceMatrix w 1 i i ≤ μ i := by
    rw [covariance_diagonal w hw hm i]
    nlinarith [sq_nonneg (μ i)]
  have hvj_le : covarianceMatrix w 1 j j ≤ μ j := by
    rw [covariance_diagonal w hw hm j]
    nlinarith [sq_nonneg (μ j)]
  have hreci := one_div_le_one_div_of_le hvi hvi_le
  have hrecj := one_div_le_one_div_of_le hvj hvj_le
  rw [hR]
  linarith

theorem pairCell00_topRank_eq_zero
    (w : ι → ℝ) (i j : ι) (hij : i ≠ j) :
    pairCell00 w (Fintype.card ι - 1) i j = 0 := by
  unfold pairCell00 expectation
  apply Finset.sum_eq_zero
  intro S _
  have hind : (1 - indicator i S.1) * (1 - indicator j S.1) = 0 := by
    by_cases hi : i ∈ S.1
    · simp [indicator, hi]
    · by_cases hj : j ∈ S.1
      · simp [indicator, hj]
      · exfalso
        let T := insert i (insert j S.1)
        have hcardT : T.card = S.1.card + 2 := by
          simp [T, hi, hj, hij, Ne.symm hij]
        have hle : T.card ≤ Fintype.card ι := Finset.card_le_univ T
        rw [S.property] at hcardT
        omega
  change subsetProbability w (Fintype.card ι - 1) S *
    ((1 - indicator i S.1) * (1 - indicator j S.1)) = 0
  rw [hind]
  ring

theorem covariance_eq_pairCell00_sub_exclusion_means
    (w : ι → ℝ) (hw : ∀ k, 0 < w k) (m : ℕ)
    (hm : m ≤ Fintype.card ι) (i j : ι) :
    covarianceMatrix w m i j = pairCell00 w m i j -
      (1 - inclusionMean w m i) * (1 - inclusionMean w m j) := by
  have hcov := covariance_eq_pairCell11_sub_means w hw hm i j
  have htotal := pairCells_total w hw hm i j
  have hmeani := pairCell11_add_pairCell10 w m i j
  have hmeanj := pairCell11_add_pairCell01 w m i j
  have hcell : pairCell00 w m i j =
      1 - inclusionMean w m i - inclusionMean w m j +
        pairCell11 w m i j := by
    linarith [htotal, hmeani, hmeanj]
  rw [hcov, hcell]
  ring

/-- Covariance matrix at top rank, expressed through the probabilities of
the unique excluded coordinate. -/
theorem covarianceMatrix_topRank
    (w : ι → ℝ) (hw : ∀ k, 0 < w k)
    (hm : Fintype.card ι - 1 ≤ Fintype.card ι) :
    covarianceMatrix w (Fintype.card ι - 1) =
      Matrix.diagonal (fun k => 1 - inclusionMean w (Fintype.card ι - 1) k) -
        Matrix.vecMulVec
          (fun k => 1 - inclusionMean w (Fintype.card ι - 1) k)
          (fun k => 1 - inclusionMean w (Fintype.card ι - 1) k) := by
  let ν : ι → ℝ := fun k => 1 - inclusionMean w (Fintype.card ι - 1) k
  ext i j
  by_cases hij : i = j
  · subst j
    rw [covariance_diagonal w hw hm i]
    rw [Matrix.sub_apply, Matrix.diagonal_apply_eq,
      Matrix.vecMulVec_apply]
    ring
  · rw [covariance_eq_pairCell00_sub_exclusion_means w hw
        (Fintype.card ι - 1) hm i j,
      pairCell00_topRank_eq_zero w i j hij]
    rw [Matrix.sub_apply, Matrix.diagonal_apply_ne _ hij,
      Matrix.vecMulVec_apply]

theorem exclusionMean_topRank_pos
    (w : ι → ℝ) (hw : ∀ k, 0 < w k) (i : ι) :
    0 < 1 - inclusionMean w (Fintype.card ι - 1) i := by
  have hm : Fintype.card ι - 1 ≤ Fintype.card ι := Nat.sub_le _ _
  let S : RankSubset ι (Fintype.card ι - 1) :=
    ⟨Finset.univ.erase i, by simp⟩
  have hexpect :
      1 - inclusionMean w (Fintype.card ι - 1) i =
        expectation w (Fintype.card ι - 1)
          (fun T => 1 - indicator i T.1) := by
    unfold inclusionMean expectation
    have hnorm := sum_subsetProbability w hw hm
    calc
      1 - (∑ T, subsetProbability w (Fintype.card ι - 1) T *
          indicator i T.1) =
          (∑ T, subsetProbability w (Fintype.card ι - 1) T) -
            ∑ T, subsetProbability w (Fintype.card ι - 1) T *
              indicator i T.1 := by rw [hnorm]
      _ = ∑ T, subsetProbability w (Fintype.card ι - 1) T *
          (1 - indicator i T.1) := by
            rw [← Finset.sum_sub_distrib]
            apply Finset.sum_congr rfl
            intro T _
            ring
  rw [hexpect]
  unfold expectation
  refine Finset.sum_pos' (fun T _ =>
    mul_nonneg (subsetProbability_pos w hw hm T).le
      (sub_nonneg.mpr (indicator_le_one i T.1))) ?_
  refine ⟨S, Finset.mem_univ S, ?_⟩
  have hprob := subsetProbability_pos w hw hm S
  have hind : indicator i S.1 = 0 := by
    simp [S, indicator]
  change 0 < subsetProbability w (Fintype.card ι - 1) S *
    (1 - indicator i S.1)
  rw [hind]
  simpa using hprob

theorem inclusionMean_topRank_pos_of_ne
    (w : ι → ℝ) (hw : ∀ k, 0 < w k)
    (i j : ι) (hij : i ≠ j) :
    0 < inclusionMean w (Fintype.card ι - 1) i := by
  have hm : Fintype.card ι - 1 ≤ Fintype.card ι := Nat.sub_le _ _
  let S : RankSubset ι (Fintype.card ι - 1) :=
    ⟨Finset.univ.erase j, by simp⟩
  unfold inclusionMean expectation
  refine Finset.sum_pos' (fun T _ =>
    mul_nonneg (subsetProbability_pos w hw hm T).le
      (indicator_nonnegative i T.1)) ?_
  refine ⟨S, Finset.mem_univ S, ?_⟩
  have hprob := subsetProbability_pos w hw hm S
  have hind : indicator i S.1 = 1 := by
    simp [S, indicator, hij]
  change 0 < subsetProbability w (Fintype.card ι - 1) S * indicator i S.1
  rw [hind]
  simpa using hprob

theorem covarianceMatrix_topRank_solve_pairDemand
    (w : ι → ℝ) (hw : ∀ k, 0 < w k)
    (i j : ι) (hij : i ≠ j) :
    covarianceMatrix w (Fintype.card ι - 1) *ᵥ
        rankOnePairPotential
          (fun k => 1 - inclusionMean w (Fintype.card ι - 1) k) i j =
      pairDemand i j := by
  let ν : ι → ℝ := fun k => 1 - inclusionMean w (Fintype.card ι - 1) k
  have hνi : 0 < ν i := exclusionMean_topRank_pos w hw i
  have hνj : 0 < ν j := exclusionMean_topRank_pos w hw j
  have hweighted := rankOnePairPotential_weighted_sum ν i j hij hνi hνj
  have hm : Fintype.card ι - 1 ≤ Fintype.card ι := Nat.sub_le _ _
  rw [covarianceMatrix_topRank w hw hm]
  funext k
  rw [Matrix.sub_mulVec]
  change (Matrix.diagonal ν *ᵥ rankOnePairPotential ν i j) k -
      (Matrix.vecMulVec ν ν *ᵥ rankOnePairPotential ν i j) k =
        pairDemand i j k
  rw [Matrix.mulVec_diagonal]
  simp only [Matrix.mulVec, dotProduct, Matrix.vecMulVec_apply]
  have hfactor :
      (∑ x, ν k * ν x * rankOnePairPotential ν i j x) =
        ν k * (∑ x, ν x * rankOnePairPotential ν i j x) := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro x _
    ring
  rw [hfactor, hweighted]
  by_cases hki : k = i
  · subst k
    simp [rankOnePairPotential, pairDemand, hij, ne_of_gt hνi]
  · by_cases hkj : k = j
    · subst k
      simp [rankOnePairPotential, pairDemand, hki, ne_of_gt hνj]
    · simp [rankOnePairPotential, pairDemand, hki, hkj]

/-- The endpoint resistance bound at rank `card ι - 1`. -/
theorem externalField_effectiveResistance_bound_topRank
    (w : ι → ℝ) (hw : ∀ k, 0 < w k)
    (N : ConductanceNetwork ι) (G : GreenKernel N)
    (i j : ι) (hij : i ≠ j)
    (hL : N.laplacian = covarianceMatrix w (Fintype.card ι - 1)) :
    G.effectiveResistance i j ≤
      1 / covarianceMatrix w (Fintype.card ι - 1) i i +
        1 / covarianceMatrix w (Fintype.card ι - 1) j j := by
  let m := Fintype.card ι - 1
  let ν : ι → ℝ := fun k => 1 - inclusionMean w m k
  have hm : m ≤ Fintype.card ι := Nat.sub_le _ _
  have hνi : 0 < ν i := exclusionMean_topRank_pos w hw i
  have hνj : 0 < ν j := exclusionMean_topRank_pos w hw j
  have hμi : 0 < inclusionMean w m i :=
    inclusionMean_topRank_pos_of_ne w hw i j hij
  have hμj : 0 < inclusionMean w m j :=
    inclusionMean_topRank_pos_of_ne w hw j i (Ne.symm hij)
  have hνi_lt : ν i < 1 := by
    dsimp [ν]
    linarith
  have hνj_lt : ν j < 1 := by
    dsimp [ν]
    linarith
  have hvi : 0 < covarianceMatrix w m i i := by
    rw [covariance_diagonal w hw hm i]
    exact mul_pos hμi hνi
  have hvj : 0 < covarianceMatrix w m j j := by
    rw [covariance_diagonal w hw hm j]
    exact mul_pos hμj hνj
  let x := rankOnePairPotential ν i j
  have hx : N.laplacian *ᵥ x = pairDemand i j := by
    rw [hL]
    exact covarianceMatrix_topRank_solve_pairDemand w hw i j hij
  have hR := G.effectiveResistance_eq_solution_drop hij x hx
  have hxdrop : x i - x j = 1 / ν i + 1 / ν j := by
    simp [x, rankOnePairPotential, hij, Ne.symm hij]
  rw [hxdrop] at hR
  have hvi_le : covarianceMatrix w m i i ≤ ν i := by
    rw [covariance_diagonal w hw hm i]
    dsimp [ν]
    nlinarith [sq_nonneg (1 - inclusionMean w m i)]
  have hvj_le : covarianceMatrix w m j j ≤ ν j := by
    rw [covariance_diagonal w hw hm j]
    dsimp [ν]
    nlinarith [sq_nonneg (1 - inclusionMean w m j)]
  have hreci := one_div_le_one_div_of_le hvi hvi_le
  have hrecj := one_div_le_one_div_of_le hvj hvj_le
  change G.effectiveResistance i j ≤
    1 / covarianceMatrix w m i i + 1 / covarianceMatrix w m j j
  rw [hR]
  linarith

end

end EffectiveResistance
