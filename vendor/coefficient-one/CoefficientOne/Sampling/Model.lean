import EffectiveResistance.Covariance
import EffectiveResistance.PairTransport
import Mathlib.Analysis.Convex.StdSimplex
import Mathlib.Data.Finset.SymmDiff

/-!
# Concrete finite-law model for Appendix E.2

These definitions retain the fixed-rank sample space and indicators of the
existing covariance theorem.  All probability laws below are normalized
nonnegative mass functions, rather than an abstract law with assumed properties.
-/

open scoped BigOperators
open EffectiveResistance

namespace CoefficientOne.Sampling

noncomputable section

/-- The closed, exact-cardinality hypersimplex. -/
def hypersimplex (ι : Type*) [Fintype ι] (k : ℕ) : Set (ι → ℝ) :=
  {x | (∀ i, 0 ≤ x i ∧ x i ≤ 1) ∧ ∑ i, x i = (k : ℝ)}

/-- The coordinate description of the relative interior for `0 < k < card ι`. -/
def interiorHypersimplex (ι : Type*) [Fintype ι] (k : ℕ) : Set (ι → ℝ) :=
  {x | (∀ i, 0 < x i ∧ x i < 1) ∧ ∑ i, x i = (k : ℝ)}

/-- The at-most-cardinality hypersimplex. -/
def atMostHypersimplex (ι : Type*) [Fintype ι] (k : ℕ) : Set (ι → ℝ) :=
  {x | (∀ i, 0 ≤ x i ∧ x i ≤ 1) ∧ ∑ i, x i ≤ (k : ℝ)}

/-- A finite probability law represented by its real masses. -/
abbrev FiniteLaw (α : Type*) [Fintype α] :=
  {p : α → ℝ // p ∈ stdSimplex ℝ α}

variable {α : Type*} [Fintype α]

theorem law_nonneg (p : FiniteLaw α) (a : α) : 0 ≤ p.val a :=
  p.property.1 a

theorem law_sum (p : FiniteLaw α) : ∑ a, p.val a = 1 :=
  p.property.2

theorem law_le_one (p : FiniteLaw α) (a : α) : p.val a ≤ 1 :=
  (mem_Icc_of_mem_stdSimplex p.property a).2

/-- Expectation under a normalized finite real mass function. -/
def lawExpectation (p : FiniteLaw α) (f : α → ℝ) : ℝ :=
  ∑ a, p.val a * f a

theorem lawExpectation_const (p : FiniteLaw α) (c : ℝ) :
    lawExpectation p (fun _ => c) = c := by
  simp [lawExpectation, ← Finset.sum_mul, law_sum]

variable {ι : Type*} [Fintype ι] [DecidableEq ι] {k : ℕ}

/-- Inclusion marginals of an arbitrary finite fixed-rank law. -/
def lawMean (p : FiniteLaw (RankSubset ι k)) (i : ι) : ℝ :=
  lawExpectation p fun S => indicator i S.val

/-- The covariance of the actual indicator vector under an arbitrary law. -/
def lawCovariance (p : FiniteLaw (RankSubset ι k)) : Matrix ι ι ℝ :=
  fun i j => lawExpectation p fun S =>
    (indicator i S.val - lawMean p i) * (indicator j S.val - lawMean p j)

/-- The metric on outputs used in E.2, with values in the reals. -/
def outputDistance (S T : Finset ι) : ℝ := (symmDiff S T).card

/-- Explicit one-norm; the default norm on a function space is not used here. -/
abbrev vectorL1 (x : ι → ℝ) : ℝ := EffectiveResistance.l1Norm x

theorem interiorHypersimplex_subset :
    interiorHypersimplex ι k ⊆ hypersimplex ι k := by
  intro x hx
  exact ⟨fun i => ⟨(hx.1 i).1.le, (hx.1 i).2.le⟩, hx.2⟩

theorem lawMean_nonneg (p : FiniteLaw (RankSubset ι k)) (i : ι) :
    0 ≤ lawMean p i := by
  apply Finset.sum_nonneg
  intro S _
  exact mul_nonneg (law_nonneg p S) (by dsimp [indicator]; split_ifs <;> norm_num)

theorem lawMean_le_one (p : FiniteLaw (RankSubset ι k)) (i : ι) :
    lawMean p i ≤ 1 := by
  calc
    lawMean p i ≤ ∑ S, p.val S := by
      apply Finset.sum_le_sum
      intro S _
      exact mul_le_of_le_one_right (law_nonneg p S)
        (by dsimp [indicator]; split_ifs <;> norm_num)
    _ = 1 := law_sum p

theorem sum_lawMean (p : FiniteLaw (RankSubset ι k)) :
    ∑ i, lawMean p i = (k : ℝ) := by
  simp only [lawMean, lawExpectation]
  rw [Finset.sum_comm]
  simp_rw [← Finset.mul_sum, sum_indicator]
  rw [← Finset.sum_mul, law_sum, one_mul]

theorem lawMean_mem_hypersimplex (p : FiniteLaw (RankSubset ι k)) :
    lawMean p ∈ hypersimplex ι k :=
  ⟨fun i => ⟨lawMean_nonneg p i, lawMean_le_one p i⟩, sum_lawMean p⟩

end
end CoefficientOne.Sampling
