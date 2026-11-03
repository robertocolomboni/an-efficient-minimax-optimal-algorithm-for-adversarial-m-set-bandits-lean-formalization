import CoefficientOne.JacobiTrudi
import CoefficientOne.SchurFoundations
import CoefficientOne.ElementaryBridge

/-!
# Vertical Pieri from the proved Littlewood–Richardson rule

The proof reuses the explicit subset/column-tableau bijection behind
`JacobiTrudi.esymm_eq_schurPoly_column`. To reindex its weights, we apply the
linear operator sending `x^alpha` to `s_(mu+alpha)` when `mu+alpha` is a
partition, and to zero otherwise. For a column, the partition condition is
exactly the Yamanouchi condition; hence the proved LR rule identifies its image
with the required product. On the elementary-polynomial side each monomial is
the indicator of a subset, yielding the finite-subset Pieri sum.

Mathematical references: Macdonald, Symmetric Functions and Hall Polynomials,
2nd ed., Chapter I, (5.17) (vertical Pieri). The imported LR theorem has a proved
sign-reversing-involution proof; its provenance is recorded in THIRD_PARTY.md.
No admitted upstream Pieri declaration is imported or assumed.
-/

open scoped BigOperators
open Finset MvPolynomial AlgebraicCombinatorics

namespace CoefficientOne

noncomputable section

variable {N : ℕ}
variable {R : Type*} [CommRing R]

/-- The exponent tuple of the squarefree monomial indexed by a subset. -/
def subsetIndicator (S : Finset (Fin N)) : Fin N → ℕ :=
  fun i => if i ∈ S then 1 else 0

/-- The summand of vertical Pieri, zero when the enlarged tuple is not a partition. -/
def verticalPieriTerm (mu alpha : Fin N → ℕ) : MvPolynomial (Fin N) R := by
  classical
  exact if AlgebraicCombinatorics.IsNPartition (mu + alpha)
    then AlgebraicCombinatorics.schurPoly (mu + alpha) else 0

/-- Linear reindexing of monomial weights; its action is fully specified on
the standard monomial basis. -/
def verticalPieriOperator (mu : Fin N → ℕ) :
    MvPolynomial (Fin N) R →ₗ[R] MvPolynomial (Fin N) R :=
  (MvPolynomial.basisMonomials (Fin N) R).constr R
    (fun d => verticalPieriTerm mu (fun i => d i))

theorem verticalPieriOperator_xPow (mu alpha : Fin N → ℕ) :
    verticalPieriOperator (R := R) mu (xPow alpha) = verticalPieriTerm mu alpha := by
  rw [verticalPieriOperator, xPow_eq_monomialExp,
    AlgebraicCombinatorics.SymmetricFunctions.monomialExp_eq_monomial]
  change ((MvPolynomial.basisMonomials (Fin N) R).constr R
    (fun d => verticalPieriTerm mu (fun i => d i)))
      ((MvPolynomial.basisMonomials (Fin N) R) (Finsupp.equivFunOnFinite.symm alpha)) = _
  rw [Module.Basis.constr_basis]
  congr 1

/-- Squarefree products have the subset indicator as their exact exponent tuple. -/
theorem xPow_subsetIndicator (S : Finset (Fin N)) :
    (xPow (subsetIndicator S) : MvPolynomial (Fin N) R) = ∏ i ∈ S, MvPolynomial.X i := by
  unfold xPow AlgebraicCombinatorics.SymmetricFunctions.monomialExp subsetIndicator
  calc
    _ = ∏ i : Fin N, if i ∈ S then (MvPolynomial.X i : MvPolynomial (Fin N) R) else 1 := by
      apply Finset.prod_congr rfl
      intro i hi
      by_cases hmem : i ∈ S <;> simp [hmem]
    _ = _ := Fintype.prod_ite_mem S _

/-- Applying the operator to the elementary polynomial gives the subset sum. -/
theorem verticalPieriOperator_esymm (mu : Fin N → ℕ) (k : ℕ) :
    verticalPieriOperator (R := R) mu (MvPolynomial.esymm (Fin N) R k) =
      ∑ S ∈ (Finset.univ : Finset (Fin N)).powersetCard k,
        verticalPieriTerm mu (subsetIndicator S) := by
  unfold MvPolynomial.esymm
  rw [map_sum]
  apply Finset.sum_congr rfl
  intro S hS
  rw [← xPow_subsetIndicator S, verticalPieriOperator_xPow]

/-- Filtering the semistandard column tableaux by partition content is
exactly summing over Yamanouchi column tableaux. -/
theorem verticalPieriTerm_sum_eq_yamanouchi
    (lam mu : Fin N → ℕ) (hlam : ∀ i, lam i ≤ 1)
    (hmu : AlgebraicCombinatorics.IsNPartition mu) :
    (∑ T : {T : Tableau lam 0 // IsSemistandard T},
      verticalPieriTerm (R := R) mu (contentTableau T.val)) =
        ∑ T : {T : Tableau lam 0 // IsYamanouchi mu T},
          (AlgebraicCombinatorics.schurPoly (mu + contentTableau T.val) :
            MvPolynomial (Fin N) R) := by
  classical
  let semis : Finset (Tableau lam 0) := Finset.univ.filter IsSemistandard
  have hsemis (T : Tableau lam 0) : T ∈ semis ↔ IsSemistandard T := by
    simp [semis]
  rw [← Finset.sum_subtype semis hsemis
    (fun T => verticalPieriTerm (R := R) mu (contentTableau T))]
  unfold verticalPieriTerm
  rw [← Finset.sum_filter]
  apply Finset.sum_subtype
  intro T
  simp only [Finset.mem_filter, hsemis]
  exact (isYamanouchi_singleColumn_iff lam mu hlam hmu T).symm

/-- The column's image under the operator is the product specified by LR. -/
theorem verticalPieriOperator_column [IsDomain R]
    (mu : Fin N → ℕ) (hmu : AlgebraicCombinatorics.IsNPartition mu)
    (k : ℕ) (hk : k ≤ N) :
    verticalPieriOperator (R := R) mu
        (AlgebraicCombinatorics.schurPoly
          (SymmetricFunctions.NPartition.colPartition N k hk).parts) =
      (AlgebraicCombinatorics.schurPoly mu : MvPolynomial (Fin N) R) *
        AlgebraicCombinatorics.schurPoly
          (SymmetricFunctions.NPartition.colPartition N k hk).parts := by
  let lam := (SymmetricFunctions.NPartition.colPartition N k hk).parts
  have hlam : AlgebraicCombinatorics.IsNPartition lam :=
    (SymmetricFunctions.NPartition.colPartition N k hk).weaklyDecreasing
  have hcol : ∀ i, lam i ≤ 1 := by
    intro i
    dsimp [lam, SymmetricFunctions.NPartition.colPartition]
    split_ifs <;> omega
  rw [schurPoly_mul_expansion mu lam hmu hlam]
  change verticalPieriOperator (R := R) mu
    (∑ T : {T : Tableau lam 0 // IsSemistandard T}, xPow (contentTableau T.val)) = _
  rw [map_sum]
  simp_rw [verticalPieriOperator_xPow]
  exact verticalPieriTerm_sum_eq_yamanouchi lam mu hcol hmu

/-- Vertical Pieri, with each vertical strip represented by its set of rows.
Every coefficient and multiplicity is accounted for by the proved column
bijection and the exact Yamanouchi filter. -/
theorem verticalPieri [IsDomain R]
    (mu : Fin N → ℕ) (hmu : AlgebraicCombinatorics.IsNPartition mu)
    (k : ℕ) (hk : k ≤ N) :
    MvPolynomial.esymm (Fin N) R k * AlgebraicCombinatorics.schurPoly mu =
      ∑ S ∈ (Finset.univ : Finset (Fin N)).powersetCard k,
        verticalPieriTerm (R := R) mu (subsetIndicator S) := by
  calc
    _ = verticalPieriOperator (R := R) mu (MvPolynomial.esymm (Fin N) R k) := by
      rw [JacobiTrudi.esymm_eq_schurPoly_column k hk,
        verticalPieriOperator_column mu hmu k hk]
      exact mul_comm _ _
    _ = _ := verticalPieriOperator_esymm mu k

/-- If the proposed strip exceeds the alphabet size, both sides are zero. -/
theorem verticalPieri_all [IsDomain R]
    (mu : Fin N → ℕ) (hmu : AlgebraicCombinatorics.IsNPartition mu) (k : ℕ) :
    MvPolynomial.esymm (Fin N) R k * AlgebraicCombinatorics.schurPoly mu =
      ∑ S ∈ (Finset.univ : Finset (Fin N)).powersetCard k,
        verticalPieriTerm (R := R) mu (subsetIndicator S) := by
  by_cases hk : k ≤ N
  · exact verticalPieri mu hmu k hk
  · have hempty : (Finset.univ : Finset (Fin N)).powersetCard k = ∅ := by
      apply Finset.powersetCard_eq_empty.mpr
      simp only [Finset.card_univ, Fintype.card_fin]
      omega
    simp [MvPolynomial.esymm, hempty]

attribute [local instance] Classical.propDecidable

/-- The explicit finite-subset formula, including strips larger than the alphabet. -/
theorem verticalPieri_explicit [IsDomain R]
    (mu : Fin N → ℕ) (hmu : AlgebraicCombinatorics.IsNPartition mu) (k : ℕ) :
    MvPolynomial.esymm (Fin N) R k * AlgebraicCombinatorics.schurPoly mu =
      ∑ S ∈ (Finset.univ : Finset (Fin N)).powersetCard k,
        if AlgebraicCombinatorics.IsNPartition (mu + subsetIndicator S)
        then (AlgebraicCombinatorics.schurPoly (mu + subsetIndicator S) :
          MvPolynomial (Fin N) R) else 0 := by
  exact verticalPieri_all mu hmu k

/-- Evaluated vertical Pieri, using the exact elementary sums of the finite law. -/
theorem verticalPieri_value
    (mu : Fin N → ℕ) (hmu : AlgebraicCombinatorics.IsNPartition mu)
    (k : ℕ) (a : Fin N → ℝ) :
    EffectiveResistance.elementarySum a k * schurValue mu a =
      ∑ S ∈ (Finset.univ : Finset (Fin N)).powersetCard k,
        if AlgebraicCombinatorics.IsNPartition (mu + subsetIndicator S)
        then schurValue (mu + subsetIndicator S) a else 0 := by
  have h := congrArg (MvPolynomial.eval a) (verticalPieri_explicit (R := ℝ) mu hmu k)
  simpa [map_mul, map_sum, schurValue, eval_esymm_eq_elementarySum, apply_ite] using h
end

end CoefficientOne
