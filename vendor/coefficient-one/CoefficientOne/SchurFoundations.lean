import AlgebraicCombinatorics.SymmetricFunctions.LittlewoodRichardson

/-!
# Concrete Schur positivity and the one-column Yamanouchi reduction

These statements use the finite tableau sum from
facebookresearch/algebraic-combinatorics, commit
b6022318e986a0c20764569208ba8ebbe1c04dbf; see THIRD_PARTY.md.

The positivity proof follows the manuscript's tableau argument (Macdonald,
Symmetric Functions and Hall Polynomials, 2nd ed., I.(5.12)). The last theorem is
the one-column reduction used in `VerticalPieri` to derive the vertical Pieri
identity from the Littlewood–Richardson rule.
-/

noncomputable section

open Finset BigOperators AlgebraicCombinatorics

namespace CoefficientOne

variable {N : ℕ}

/-- The concrete, tableau-defined Schur polynomial evaluated at real letters. -/
def schurValue (lam : Fin N → ℕ) (a : Fin N → ℝ) : ℝ :=
  MvPolynomial.eval a (AlgebraicCombinatorics.schurPoly lam)

theorem eval_xPow (alpha : Fin N → ℕ) (a : Fin N → ℝ) :
    MvPolynomial.eval a (xPow alpha : MvPolynomial (Fin N) ℝ) =
      ∏ i, a i ^ alpha i := by
  simp [xPow, AlgebraicCombinatorics.SymmetricFunctions.monomialExp]

/-- Each tableau has nonnegative weight on a nonnegative alphabet. -/
theorem schurValue_nonneg (lam : Fin N → ℕ) (a : Fin N → ℝ)
    (ha : ∀ i, 0 ≤ a i) : 0 ≤ schurValue lam a := by
  unfold schurValue AlgebraicCombinatorics.schurPoly skewSchurPoly
  rw [map_sum]
  apply Finset.sum_nonneg
  intro T _
  rw [eval_xPow]
  exact Finset.prod_nonneg fun i _ => pow_nonneg (ha i) _

/-- The tableau putting the row index in each cell has strictly positive weight.
Trailing zero rows allow the empty partition and N = 0 as well. -/
theorem schurValue_pos (lam : Fin N → ℕ) (a : Fin N → ℝ)
    (ha : ∀ i, 0 < a i) : 0 < schurValue lam a := by
  unfold schurValue AlgebraicCombinatorics.schurPoly skewSchurPoly
  rw [map_sum]
  apply Finset.sum_pos
  · intro T _
    rw [eval_xPow]
    exact Finset.prod_pos fun i _ => pow_pos (ha i) _
  · exact ⟨⟨minimalisticTableau lam, minimalisticTableau_semistandard lam⟩,
      Finset.mem_univ _⟩

/-- On a one-column shape, the only nontrivial Yamanouchi test is the full
content test. This supplies the partition condition in vertical Pieri. -/
theorem isYamanouchi_singleColumn_iff (lam nu : Fin N → ℕ)
    (hlam : ∀ i, lam i ≤ 1) (hnu : AlgebraicCombinatorics.IsNPartition nu)
    (T : Tableau lam 0) :
    IsYamanouchi nu T ↔
      IsSemistandard T ∧ AlgebraicCombinatorics.IsNPartition (nu + contentTableau T) := by
  constructor
  · intro h
    exact ⟨h.isSemistandard, h.isNPartition_add_content⟩
  · rintro ⟨hT, hcontent⟩
    refine ⟨hT, ?_⟩
    intro j hj
    by_cases h1 : j = 1
    · subst j
      simpa only [contentColGeq_one_eq_contentTableau] using hcontent
    · have hlarge : ∀ i, lam i < j := by
        intro i
        have hi := hlam i
        omega
      rw [contentColGeq_eq_zero_of_large T j hlarge, add_zero]
      exact hnu

end CoefficientOne
