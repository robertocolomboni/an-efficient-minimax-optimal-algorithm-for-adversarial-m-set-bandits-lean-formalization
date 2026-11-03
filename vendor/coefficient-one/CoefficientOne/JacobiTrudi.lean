import AlgebraicCombinatorics.SymmetricFunctions.PieriJacobiTrudi
import CoefficientOne.SchurFoundations

/-!
# Jacobi–Trudi for the same concrete Schur polynomials used in the scalar proof

The imported Jacobi–Trudi theorem is proved through LGV in the selected upstream
sources; it contains no assumed Pieri or dual Jacobi–Trudi declaration. This file
constructs the missing equivalence with the tableau sum used in
`AlgebraicCombinatorics.schurPoly`. A row offset k corresponds to absolute column
mu_i + k + 1. Both inverse maps and preservation of tableau weights are proved.

Mathematical reference: Macdonald, 2nd edition, Chapter I, (3.4), (5.12).
Source provenance and compatibility changes are recorded in THIRD_PARTY.md.
-/

noncomputable section

open Finset BigOperators
open SymmetricFunctions (SkewPartition SkewSSYT)

namespace CoefficientOne.JacobiTrudi

variable {N : ℕ}

abbrev RowCell (s : SkewPartition N) :=
  (i : Fin N) × Fin (s.outer.parts i - s.inner.parts i)

abbrev LRCell (s : SkewPartition N) :=
  {c : Fin N × ℕ //
    c ∈ AlgebraicCombinatorics.skewYoungDiagram s.outer.parts s.inner.parts}

abbrev LRTableau (s : SkewPartition N) :=
  AlgebraicCombinatorics.Tableau s.outer.parts s.inner.parts

abbrev LRSemistandard (s : SkewPartition N) :=
  {T : LRTableau s // AlgebraicCombinatorics.IsSemistandard T}

/-- The column shift between dependent row offsets and absolute cell coordinates. -/
def cellEquiv (s : SkewPartition N) : RowCell s ≃ LRCell s where
  toFun c := ⟨(c.1, s.inner.parts c.1 + c.2.val + 1), by
    have hc := c.2.isLt
    have hs := s.contained c.1
    change s.inner.parts c.1 < s.inner.parts c.1 + c.2.val + 1 ∧
      s.inner.parts c.1 + c.2.val + 1 ≤ s.outer.parts c.1
    constructor <;> omega⟩
  invFun c := ⟨c.val.1, ⟨c.val.2 - s.inner.parts c.val.1 - 1, by
    have hc := c.property
    change s.inner.parts c.val.1 < c.val.2 ∧ c.val.2 ≤ s.outer.parts c.val.1 at hc
    omega⟩⟩
  left_inv c := by
    rcases c with ⟨i, j⟩
    apply Sigma.ext
    · rfl
    apply heq_of_eq
    apply Fin.ext
    dsimp
    omega
  right_inv c := by
    apply Subtype.ext
    apply Prod.ext
    · rfl
    have hc := c.property
    change s.inner.parts c.val.1 < c.val.2 ∧ c.val.2 ≤ s.outer.parts c.val.1 at hc
    dsimp
    omega

def toLR {s : SkewPartition N} (T : SkewSSYT s) : LRTableau s :=
  fun c => T.entries ((cellEquiv s).symm c).1 ((cellEquiv s).symm c).2

theorem toLR_semistandard {s : SkewPartition N} (T : SkewSSYT s) :
    AlgebraicCombinatorics.IsSemistandard (toLR T) := by
  constructor
  · rintro ⟨⟨i, j⟩, hc⟩ ⟨⟨i', j'⟩, hc'⟩ hrow hcol
    change i = i' at hrow
    subst i'
    apply T.rowWeak
    change j - s.inner.parts i - 1 ≤ j' - s.inner.parts i - 1
    exact Nat.sub_le_sub_right (Nat.sub_le_sub_right (le_of_lt hcol) _) _
  · intro c d hcol hrow
    apply T.colStrict_nonadjacent c.val.1 d.val.1 hrow
    have hc := c.property
    have hd := d.property
    change s.inner.parts c.val.1 < c.val.2 ∧ c.val.2 ≤ s.outer.parts c.val.1 at hc
    change s.inner.parts d.val.1 < d.val.2 ∧ d.val.2 ≤ s.outer.parts d.val.1 at hd
    dsimp [cellEquiv]
    omega

def fromLR {s : SkewPartition N} (T : LRSemistandard s) : SkewSSYT s where
  entries i k := T.val (cellEquiv s ⟨i, k⟩)
  rowWeak i j k hjk := by
    rcases lt_or_eq_of_le hjk with hlt | heq
    · apply T.property.1 (cellEquiv s ⟨i, j⟩) (cellEquiv s ⟨i, k⟩) rfl
      change s.inner.parts i + j.val + 1 < s.inner.parts i + k.val + 1
      exact Nat.add_lt_add_right (Nat.add_lt_add_left hlt _) _
    · subst k
      exact le_refl _
  colStrict i hi k hcol hk' := by
    apply T.property.2
    · dsimp [cellEquiv]
      omega
    · change i.val < i.val + 1
      omega

/-- The two semistandard tableau types are equivalent, not just equinumerous. -/
def tableauEquiv (s : SkewPartition N) : SkewSSYT s ≃ LRSemistandard s where
  toFun T := ⟨toLR T, toLR_semistandard T⟩
  invFun T := fromLR T
  left_inv T := by
    apply SkewSSYT.eq_of_entries_eq
    funext i k
    change (fun c : RowCell s => T.entries c.1 c.2)
      ((cellEquiv s).symm (cellEquiv s ⟨i, k⟩)) = _
    rw [Equiv.symm_apply_apply]
  right_inv T := by
    apply Subtype.ext
    funext c
    change T.val (cellEquiv s ((cellEquiv s).symm c)) = T.val c
    rw [Equiv.apply_symm_apply]

variable {R : Type*} [CommRing R]

/-- Counting the entries of each value and grouping the factors give the same weight. -/
theorem xPow_content_eq_prod {lam mu : Fin N → ℕ}
    (T : AlgebraicCombinatorics.Tableau lam mu) :
    (AlgebraicCombinatorics.xPow (AlgebraicCombinatorics.contentTableau T) :
        MvPolynomial (Fin N) R) = ∏ c, MvPolynomial.X (T c) := by
  unfold AlgebraicCombinatorics.xPow AlgebraicCombinatorics.SymmetricFunctions.monomialExp
  simp only [AlgebraicCombinatorics.contentTableau_eq_card]
  have h := Finset.prod_fiberwise' Finset.univ T (MvPolynomial.X (R := R))
  simp only [Finset.prod_const] at h
  convert h using 1
  apply Finset.prod_congr rfl
  intro i hi
  congr 1
  apply congrArg Finset.card
  ext c
  simp only [Finset.mem_filter, Finset.mem_univ, true_and]

theorem weight_preserved {s : SkewPartition N} (T : SkewSSYT s) :
    (AlgebraicCombinatorics.xPow
      (AlgebraicCombinatorics.contentTableau (toLR T)) : MvPolynomial (Fin N) R) =
      T.toMonomial := by
  rw [xPow_content_eq_prod]
  have h := Fintype.prod_equiv (cellEquiv s)
    (fun c : RowCell s => (MvPolynomial.X (T.entries c.1 c.2) : MvPolynomial (Fin N) R))
    (fun c : LRCell s => MvPolynomial.X (toLR T c)) (by
      intro c
      exact congrArg (fun q : RowCell s =>
        (MvPolynomial.X (T.entries q.1 q.2) : MvPolynomial (Fin N) R))
        ((cellEquiv s).symm_apply_apply c).symm)
  rw [← h, Fintype.prod_sigma]
  rfl

theorem skewSchur_eq_LR (s : SkewPartition N) :
    (SymmetricFunctions.skewSchur s : MvPolynomial (Fin N) R) =
      AlgebraicCombinatorics.skewSchurPoly s.outer.parts s.inner.parts := by
  have hall : SymmetricFunctions.skewSSYTFinset s = Finset.univ := by
    ext T
    simp only [Finset.mem_univ, iff_true]
    exact SymmetricFunctions.skewSSYTFinset_mem s T
  unfold SymmetricFunctions.skewSchur AlgebraicCombinatorics.skewSchurPoly
  rw [hall]
  apply Fintype.sum_equiv (tableauEquiv s)
  intro T
  exact (weight_preserved T).symm

/-- Ordinary Jacobi–Trudi, for the concrete LR tableau definition of skew Schur. -/
theorem skewSchurPoly_eq_det (lam mu : Fin N → ℕ)
    (hlam : AlgebraicCombinatorics.IsNPartition lam)
    (hmu : AlgebraicCombinatorics.IsNPartition mu)
    (hcontained : ∀ i, mu i ≤ lam i) :
    (AlgebraicCombinatorics.skewSchurPoly lam mu : MvPolynomial (Fin N) R) =
      (SymmetricFunctions.jacobiTrudiMatrixH (R := R) lam mu).det := by
  rw [← skewSchur_eq_LR ⟨⟨lam, hlam⟩, ⟨mu, hmu⟩, hcontained⟩]
  exact SymmetricFunctions.jacobiTrudi_h lam mu hlam hmu hcontained

/-- Non-skew Jacobi–Trudi for the same Schur polynomial used everywhere else. -/
theorem schurPoly_eq_det (lam : Fin N → ℕ)
    (hlam : AlgebraicCombinatorics.IsNPartition lam) :
    (AlgebraicCombinatorics.schurPoly lam : MvPolynomial (Fin N) R) =
      (SymmetricFunctions.jacobiTrudiMatrixH (R := R) lam 0).det := by
  exact skewSchurPoly_eq_det lam 0 hlam
    (fun _ _ _ => le_refl 0) (fun _ => Nat.zero_le _)


/-- The non-skew upstream tableau sum agrees with the LR tableau sum. -/
theorem schur_eq_LR (lam : SymmetricFunctions.NPartition N) :
    (SymmetricFunctions.schur lam : MvPolynomial (Fin N) R) =
      AlgebraicCombinatorics.schurPoly lam.parts := by
  rw [SymmetricFunctions.schur_eq_skewSchur_zero, skewSchur_eq_LR]
  rfl

/-- The elementary symmetric polynomial is the concrete Schur polynomial of a column.
The source proof uses the explicit sorted-subset/column-tableau bijection. -/
theorem esymm_eq_schurPoly_column (r : ℕ) (hr : r ≤ N) :
    MvPolynomial.esymm (Fin N) R r =
      AlgebraicCombinatorics.schurPoly
        (SymmetricFunctions.NPartition.colPartition N r hr).parts := by
  rw [SymmetricFunctions.esymm_eq_schur_colPartition r hr, schur_eq_LR]

/-- Evaluating Jacobi–Trudi gives the real determinant used in the manuscript. -/
theorem schurValue_eq_det (lam : Fin N → ℕ)
    (hlam : AlgebraicCombinatorics.IsNPartition lam) (a : Fin N → ℝ) :
    CoefficientOne.schurValue lam a =
      Matrix.det (fun i j : Fin N => MvPolynomial.eval a
        (SymmetricFunctions.hsymmExt (R := ℝ)
          ((lam i : ℤ) - (i.val : ℤ) + (j.val : ℤ)))) := by
  unfold CoefficientOne.schurValue
  rw [schurPoly_eq_det lam hlam, RingHom.map_det]
  rfl

end CoefficientOne.JacobiTrudi
