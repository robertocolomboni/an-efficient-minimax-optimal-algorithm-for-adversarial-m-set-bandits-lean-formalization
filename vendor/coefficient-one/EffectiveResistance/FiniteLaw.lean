import Mathlib.Algebra.BigOperators.Field
import Mathlib.Data.Fintype.Card
import Mathlib.Data.Matrix.Basic
import Mathlib.Data.Real.Basic

/-!
# Fixed-rank external-field laws

This file gives a finite-sum model of the probability law used in the paper.
Using a finite sample space keeps the algebraic proof of the resistance
theorem independent of measure-theoretic integration.
-/

open scoped BigOperators

namespace EffectiveResistance

noncomputable section

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- The finite sample space of subsets of `ι` having cardinality `m`. -/
abbrev RankSubset (ι : Type*) [Fintype ι] (m : ℕ) :=
  {S : Finset ι // S.card = m}

/-- The multiplicative external-field weight of a subset. -/
def subsetWeight (w : ι → ℝ) (S : Finset ι) : ℝ :=
  ∏ i ∈ S, w i

/-- The `m`th elementary symmetric sum, written directly as a finite sum. -/
def elementarySum (w : ι → ℝ) (m : ℕ) : ℝ :=
  ∑ S : RankSubset ι m, subsetWeight w S.1

/-- Probability mass of a rank-`m` subset under the external field `w`. -/
def subsetProbability (w : ι → ℝ) (m : ℕ) (S : RankSubset ι m) : ℝ :=
  subsetWeight w S.1 / elementarySum w m

/-- Expectation under the rank-`m` external-field law. -/
def expectation (w : ι → ℝ) (m : ℕ) (f : RankSubset ι m → ℝ) : ℝ :=
  ∑ S : RankSubset ι m, subsetProbability w m S * f S

/-- Coordinate indicator of a subset. -/
def indicator (i : ι) (S : Finset ι) : ℝ :=
  if i ∈ S then 1 else 0

/-- Inclusion marginal of coordinate `i`. -/
def inclusionMean (w : ι → ℝ) (m : ℕ) (i : ι) : ℝ :=
  expectation w m fun S => indicator i S.1

/-- Covariance matrix of the indicator vector. -/
def covarianceMatrix (w : ι → ℝ) (m : ℕ) : Matrix ι ι ℝ :=
  fun i j => expectation w m fun S =>
    (indicator i S.1 - inclusionMean w m i) *
      (indicator j S.1 - inclusionMean w m j)

theorem sum_indicator (S : RankSubset ι m) :
    ∑ i : ι, indicator i S.1 = m := by
  classical
  simp [indicator, S.property]

theorem elementarySum_pos
    (w : ι → ℝ) (hw : ∀ i, 0 < w i)
    (hm : m ≤ Fintype.card ι) :
    0 < elementarySum w m := by
  classical
  obtain ⟨S, _, hS⟩ := Finset.exists_subset_card_eq hm
  have hterm : 0 < subsetWeight w S := by
    exact Finset.prod_pos fun i _ => hw i
  let T : RankSubset ι m := ⟨S, hS⟩
  refine Finset.sum_pos' (fun U _ => le_of_lt ?_) ?_
  · exact Finset.prod_pos fun i _ => hw i
  · exact ⟨T, Finset.mem_univ T, hterm⟩

theorem sum_subsetProbability
    (w : ι → ℝ) (hw : ∀ i, 0 < w i)
    (hm : m ≤ Fintype.card ι) :
    ∑ S : RankSubset ι m, subsetProbability w m S = 1 := by
  classical
  have hZ : elementarySum w m ≠ 0 := ne_of_gt (elementarySum_pos w hw hm)
  simp only [subsetProbability]
  rw [← Finset.sum_div]
  exact div_self hZ

theorem expectation_const
    (w : ι → ℝ) (hw : ∀ i, 0 < w i)
    (hm : m ≤ Fintype.card ι) (c : ℝ) :
    expectation w m (fun _ => c) = c := by
  classical
  simp [expectation, ← Finset.sum_mul, sum_subsetProbability w hw hm]

theorem sum_inclusionMean
    (w : ι → ℝ) (hw : ∀ i, 0 < w i)
    (hm : m ≤ Fintype.card ι) :
    ∑ i : ι, inclusionMean w m i = m := by
  classical
  simp only [inclusionMean, expectation]
  rw [Finset.sum_comm]
  calc
    ∑ S : RankSubset ι m,
        ∑ i : ι, subsetProbability w m S * indicator i S.1 =
        ∑ S : RankSubset ι m, subsetProbability w m S * m := by
          apply Finset.sum_congr rfl
          intro S _
          rw [← Finset.mul_sum, sum_indicator S]
    _ = m := by
      rw [← Finset.sum_mul, sum_subsetProbability w hw hm]
      simp

end

end EffectiveResistance
