import EffectiveResistance.PairCells
import EffectiveResistance.PairDecomposition
import EffectiveResistance.ExternalFieldCurvature

/-!
# Explicit endpoint-cell formulas

This file evaluates the four endpoint probabilities of a rank-`q+2`
external-field law through elementary symmetric sums on the complement of
the two endpoints.
-/

open scoped BigOperators

namespace EffectiveResistance

noncomputable section

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

theorem pairCell11_eq_elementarySums
    (w : ι → ℝ) (i j : ι) (hij : i ≠ j) (q : ℕ) :
    pairCell11 w (q + 2) i j =
      w i * w j * elementarySum (pairRestrictedWeight w i j) q /
        elementarySum w (q + 2) := by
  unfold pairCell11 expectation subsetProbability
  rw [sum_rankSubset_pairDecomposition i j hij q]
  simp [indicator, subsetWeight_liftPair11, subsetWeight_liftPair10,
    subsetWeight_liftPair01, subsetWeight_liftPair00,
    elementarySum, hij, Finset.mul_sum, Finset.sum_div]

theorem pairCell10_eq_elementarySums
    (w : ι → ℝ) (i j : ι) (hij : i ≠ j) (q : ℕ) :
    pairCell10 w (q + 2) i j =
      w i * elementarySum (pairRestrictedWeight w i j) (q + 1) /
        elementarySum w (q + 2) := by
  unfold pairCell10 expectation subsetProbability
  rw [sum_rankSubset_pairDecomposition i j hij q]
  simp [indicator, subsetWeight_liftPair11, subsetWeight_liftPair10,
    subsetWeight_liftPair01, subsetWeight_liftPair00,
    elementarySum, hij, Finset.mul_sum, Finset.sum_div]

theorem pairCell01_eq_elementarySums
    (w : ι → ℝ) (i j : ι) (hij : i ≠ j) (q : ℕ) :
    pairCell01 w (q + 2) i j =
      w j * elementarySum (pairRestrictedWeight w i j) (q + 1) /
        elementarySum w (q + 2) := by
  unfold pairCell01 expectation subsetProbability
  rw [sum_rankSubset_pairDecomposition i j hij q]
  simp [indicator, subsetWeight_liftPair11, subsetWeight_liftPair10,
    subsetWeight_liftPair01, subsetWeight_liftPair00,
    elementarySum, hij, Finset.mul_sum, Finset.sum_div]

theorem pairCell00_eq_elementarySums
    (w : ι → ℝ) (i j : ι) (hij : i ≠ j) (q : ℕ) :
    pairCell00 w (q + 2) i j =
      elementarySum (pairRestrictedWeight w i j) (q + 2) /
        elementarySum w (q + 2) := by
  unfold pairCell00 expectation subsetProbability
  rw [sum_rankSubset_pairDecomposition i j hij q]
  simp [indicator, subsetWeight_liftPair11, subsetWeight_liftPair10,
    subsetWeight_liftPair01, subsetWeight_liftPair00,
    elementarySum, hij, Finset.sum_div]

theorem pairCells_pos_of_background_rank
    (w : ι → ℝ) (hw : ∀ k, 0 < w k)
    (i j : ι) (hij : i ≠ j) (q : ℕ)
    (hq : q + 2 ≤ Fintype.card (PairComplement i j)) :
    0 < pairCell11 w (q + 2) i j ∧
      0 < pairCell10 w (q + 2) i j ∧
      0 < pairCell01 w (q + 2) i j ∧
      0 < pairCell00 w (q + 2) i j := by
  let z := pairRestrictedWeight w i j
  have hwz : ∀ k, 0 < z k := fun k => hw k.1
  have hq0 : q ≤ Fintype.card (PairComplement i j) := by omega
  have hq1 : q + 1 ≤ Fintype.card (PairComplement i j) := by omega
  have hfull : q + 2 ≤ Fintype.card ι :=
    hq.trans (Fintype.card_subtype_le (fun k : ι => k ≠ i ∧ k ≠ j))
  have hE0 := elementarySum_pos z hwz hq0
  have hE1 := elementarySum_pos z hwz hq1
  have hE2 := elementarySum_pos z hwz hq
  have hZ := elementarySum_pos w hw hfull
  constructor
  · rw [pairCell11_eq_elementarySums w i j hij q]
    change 0 < w i * w j * elementarySum z q / elementarySum w (q + 2)
    exact div_pos (mul_pos (mul_pos (hw i) (hw j)) hE0) hZ
  constructor
  · rw [pairCell10_eq_elementarySums w i j hij q]
    change 0 < w i * elementarySum z (q + 1) / elementarySum w (q + 2)
    exact div_pos (mul_pos (hw i) hE1) hZ
  constructor
  · rw [pairCell01_eq_elementarySums w i j hij q]
    change 0 < w j * elementarySum z (q + 1) / elementarySum w (q + 2)
    exact div_pos (mul_pos (hw j) hE1) hZ
  · rw [pairCell00_eq_elementarySums w i j hij q]
    change 0 < elementarySum z (q + 2) / elementarySum w (q + 2)
    positivity

theorem adjacentTheta_eq_pairCell_ratio
    (w : ι → ℝ) (hw : ∀ k, 0 < w k)
    (i j : ι) (hij : i ≠ j) (q : ℕ)
    (hq : q + 2 ≤ Fintype.card (PairComplement i j)) :
    adjacentTheta (pairRestrictedWeight w i j) q =
      pairCell11 w (q + 2) i j * pairCell00 w (q + 2) i j /
        (pairCell10 w (q + 2) i j * pairCell01 w (q + 2) i j) := by
  let z := pairRestrictedWeight w i j
  have hwz : ∀ k, 0 < z k := fun k => hw k.1
  have hq0 : q ≤ Fintype.card (PairComplement i j) := by omega
  have hq1 : q + 1 ≤ Fintype.card (PairComplement i j) := by omega
  have hfull : q + 2 ≤ Fintype.card ι :=
    hq.trans (Fintype.card_subtype_le (fun k : ι => k ≠ i ∧ k ≠ j))
  have hE0 : elementarySum z q ≠ 0 :=
    ne_of_gt (elementarySum_pos z hwz hq0)
  have hE1 : elementarySum z (q + 1) ≠ 0 :=
    ne_of_gt (elementarySum_pos z hwz hq1)
  have hE2 : elementarySum z (q + 2) ≠ 0 :=
    ne_of_gt (elementarySum_pos z hwz hq)
  have hZ : elementarySum w (q + 2) ≠ 0 :=
    ne_of_gt (elementarySum_pos w hw hfull)
  rw [pairCell11_eq_elementarySums w i j hij q,
    pairCell10_eq_elementarySums w i j hij q,
    pairCell01_eq_elementarySums w i j hij q,
    pairCell00_eq_elementarySums w i j hij q]
  unfold adjacentTheta
  change elementarySum z q * elementarySum z (q + 2) /
      elementarySum z (q + 1) ^ 2 =
    ((w i * w j * elementarySum z q / elementarySum w (q + 2)) *
      (elementarySum z (q + 2) / elementarySum w (q + 2))) /
      ((w i * elementarySum z (q + 1) / elementarySum w (q + 2)) *
        (w j * elementarySum z (q + 1) / elementarySum w (q + 2)))
  field_simp [hE0, hE1, hE2, hZ, ne_of_gt (hw i), ne_of_gt (hw j)]

theorem pairCell_omega_pos
    (w : ι → ℝ) (hw : ∀ k, 0 < w k)
    (i j : ι) (hij : i ≠ j) (q : ℕ)
    (hq : q + 2 ≤ Fintype.card (PairComplement i j)) :
    0 < pairCell10 w (q + 2) i j * pairCell01 w (q + 2) i j -
      pairCell11 w (q + 2) i j * pairCell00 w (q + 2) i j := by
  have hpos := pairCells_pos_of_background_rank w hw i j hij q hq
  have hden : 0 < pairCell10 w (q + 2) i j * pairCell01 w (q + 2) i j :=
    mul_pos hpos.2.1 hpos.2.2.1
  have htheta := adjacentTheta_lt_one
    (pairRestrictedWeight w i j) (fun k => hw k.1) q hq
  rw [adjacentTheta_eq_pairCell_ratio w hw i j hij q hq] at htheta
  exact sub_pos.mpr ((div_lt_one hden).mp htheta)

/-- Disintegration of the full rank-`q+2` expectation into the four endpoint
cells.  The `10` and `01` cells use the same rank-`q+1` background law. -/
theorem expectation_pairDecomposition
    (w : ι → ℝ) (hw : ∀ k, 0 < w k)
    (i j : ι) (hij : i ≠ j) (q : ℕ)
    (hq : q + 2 ≤ Fintype.card (PairComplement i j))
    (F : RankSubset ι (q + 2) → ℝ) :
    expectation w (q + 2) F =
      pairCell11 w (q + 2) i j *
        expectation (pairRestrictedWeight w i j) q
          (fun A => F (liftPair11 i j hij A)) +
      pairCell10 w (q + 2) i j *
        expectation (pairRestrictedWeight w i j) (q + 1)
          (fun A => F (liftPair10 i j A)) +
      pairCell01 w (q + 2) i j *
        expectation (pairRestrictedWeight w i j) (q + 1)
          (fun A => F (liftPair01 i j A)) +
      pairCell00 w (q + 2) i j *
        expectation (pairRestrictedWeight w i j) (q + 2)
          (fun A => F (liftPair00 i j A)) := by
  let z := pairRestrictedWeight w i j
  have hwz : ∀ k, 0 < z k := fun k => hw k.1
  have hq0 : q ≤ Fintype.card (PairComplement i j) := by omega
  have hq1 : q + 1 ≤ Fintype.card (PairComplement i j) := by omega
  have hfull : q + 2 ≤ Fintype.card ι :=
    hq.trans (Fintype.card_subtype_le (fun k : ι => k ≠ i ∧ k ≠ j))
  have hE0 : elementarySum z q ≠ 0 :=
    ne_of_gt (elementarySum_pos z hwz hq0)
  have hE1 : elementarySum z (q + 1) ≠ 0 :=
    ne_of_gt (elementarySum_pos z hwz hq1)
  have hE2 : elementarySum z (q + 2) ≠ 0 :=
    ne_of_gt (elementarySum_pos z hwz hq)
  have hZ : elementarySum w (q + 2) ≠ 0 :=
    ne_of_gt (elementarySum_pos w hw hfull)
  change expectation w (q + 2) F =
      pairCell11 w (q + 2) i j *
        expectation z q (fun A => F (liftPair11 i j hij A)) +
      pairCell10 w (q + 2) i j *
        expectation z (q + 1) (fun A => F (liftPair10 i j A)) +
      pairCell01 w (q + 2) i j *
        expectation z (q + 1) (fun A => F (liftPair01 i j A)) +
      pairCell00 w (q + 2) i j *
        expectation z (q + 2) (fun A => F (liftPair00 i j A))
  have h11 :
      (∑ A : RankSubset (PairComplement i j) q,
        subsetProbability w (q + 2) (liftPair11 i j hij A) *
          F (liftPair11 i j hij A)) =
        pairCell11 w (q + 2) i j *
          expectation z q (fun A => F (liftPair11 i j hij A)) := by
    rw [pairCell11_eq_elementarySums w i j hij q]
    unfold expectation subsetProbability
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro A _
    rw [subsetWeight_liftPair11]
    change (w i * w j * subsetWeight z A.1 / elementarySum w (q + 2)) * _ = _
    field_simp [hE0, hZ]
    ring
  have h10 :
      (∑ A : RankSubset (PairComplement i j) (q + 1),
        subsetProbability w (q + 2) (liftPair10 i j A) *
          F (liftPair10 i j A)) =
        pairCell10 w (q + 2) i j *
          expectation z (q + 1) (fun A => F (liftPair10 i j A)) := by
    rw [pairCell10_eq_elementarySums w i j hij q]
    unfold expectation subsetProbability
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro A _
    rw [subsetWeight_liftPair10]
    change (w i * subsetWeight z A.1 / elementarySum w (q + 2)) * _ = _
    field_simp [hE1, hZ]
    ring
  have h01 :
      (∑ A : RankSubset (PairComplement i j) (q + 1),
        subsetProbability w (q + 2) (liftPair01 i j A) *
          F (liftPair01 i j A)) =
        pairCell01 w (q + 2) i j *
          expectation z (q + 1) (fun A => F (liftPair01 i j A)) := by
    rw [pairCell01_eq_elementarySums w i j hij q]
    unfold expectation subsetProbability
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro A _
    rw [subsetWeight_liftPair01]
    change (w j * subsetWeight z A.1 / elementarySum w (q + 2)) * _ = _
    field_simp [hE1, hZ]
    ring
  have h00 :
      (∑ A : RankSubset (PairComplement i j) (q + 2),
        subsetProbability w (q + 2) (liftPair00 i j A) *
          F (liftPair00 i j A)) =
        pairCell00 w (q + 2) i j *
          expectation z (q + 2) (fun A => F (liftPair00 i j A)) := by
    rw [pairCell00_eq_elementarySums w i j hij q]
    unfold expectation subsetProbability
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro A _
    rw [subsetWeight_liftPair00]
    change (subsetWeight z A.1 / elementarySum w (q + 2)) *
        F (liftPair00 i j A) =
      (elementarySum z (q + 2) / elementarySum w (q + 2)) *
        ((subsetWeight z A.1 / elementarySum z (q + 2)) *
          F (liftPair00 i j A))
    field_simp [hE2, hZ]
  unfold expectation
  rw [sum_rankSubset_pairDecomposition i j hij q, h11, h10, h01, h00]
  rfl

end

end EffectiveResistance
