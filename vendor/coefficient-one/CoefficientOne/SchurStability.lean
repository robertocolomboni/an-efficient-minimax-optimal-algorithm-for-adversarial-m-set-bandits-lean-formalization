import CoefficientOne.SignedLoad
import CoefficientOne.JacobiTrudi

/-!
# Specialization of Schur values after padding an alphabet with zero letters

This module keeps every row of the large shape. A shape with a nonzero row
beyond the small alphabet size has value zero; it is never silently truncated.
The proof uses the concrete tableau sum and its column-strictness property.
The argument corresponds to Step 1 and equation `eq:load` in `paper/main.tex`; the
specialization argument is proved here from the imported concrete definitions
`AlgebraicCombinatorics.skewSchurPoly` and `IsSemistandard`.
The only imported tableau facts used are the proved `tableau_entry_ge_row`
and `CoefficientOne.JacobiTrudi.xPow_content_eq_prod`; no stability theorem
is assumed.
-/

noncomputable section

namespace CoefficientOne.SchurStability

open Finset AlgebraicCombinatorics

variable {N M K : ℕ}

/-- Extend an alphabet by actual zero letters. -/
def paddedAlphabet {R : Type*} [Zero R] (a : Fin N → R) (i : Fin M) : R :=
  if hi : i.val < N then a ⟨i.val, hi⟩ else 0

theorem paddedAlphabet_castLE {R : Type*} [Zero R] (h : N ≤ M) (a : Fin N → R)
    (i : Fin N) : paddedAlphabet a (Fin.castLE h i) = a i := by
  simp [paddedAlphabet, i.isLt]

theorem paddedAlphabet_of_ge {R : Type*} [Zero R] (a : Fin N → R) (i : Fin M)
    (hi : N ≤ i.val) : paddedAlphabet a i = 0 := by
  simp [paddedAlphabet, show ¬i.val < N by omega]

theorem paddedAlphabet_self {R : Type*} [Zero R] (a : Fin N → R) :
    paddedAlphabet (M := N) a = a := by
  funext i
  simp [paddedAlphabet, i.isLt]

theorem paddedAlphabet_trans {R : Type*} [Zero R] (a : Fin N → R) (hNM : N ≤ M) :
    paddedAlphabet (M := K) (paddedAlphabet (M := M) a) = paddedAlphabet (M := K) a := by
  funext i
  unfold paddedAlphabet
  split_ifs <;> simp_all <;> omega

theorem sum_paddedAlphabet {R A : Type*} [Zero R] [AddCommMonoid A]
    (hNM : N ≤ M) (a : Fin N → R) (f : R → A) (hf : f 0 = 0) :
    (∑ i : Fin M, f (paddedAlphabet a i)) = ∑ i : Fin N, f (a i) := by
  have hfilter : (∑ i : Fin M, f (paddedAlphabet a i)) =
      ∑ i ∈ univ.filter (fun i : Fin M => i.val < N), f (paddedAlphabet a i) := by
    rw [Finset.sum_filter]
    apply Finset.sum_congr rfl
    intro i hi
    by_cases h : i.val < N
    · simp [h]
    · simp [h, paddedAlphabet_of_ge a i (by omega), hf]
  rw [hfilter]
  symm
  refine Finset.sum_bij (fun i _ => Fin.castLE hNM i) ?_ ?_ ?_ ?_
  · intro i hi
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Fin.val_castLE]
    exact i.isLt
  · intro i hi j hj hij
    exact Fin.ext (congrArg (fun z : Fin M => z.val) hij)
  · intro i hi
    have hiN := (Finset.mem_filter.mp hi).2
    refine ⟨⟨i.val, hiN⟩, Finset.mem_univ _, ?_⟩
    exact Fin.ext rfl
  · intro i hi
    rw [paddedAlphabet_castLE]

theorem powerSum_paddedAlphabet {R : Type*} [CommRing R] (hNM : N ≤ M)
    (a : Fin N → R) (t : ℕ) (ht : 0 < t) :
    AlternantIdentities.powerSum (paddedAlphabet (M := M) a) t =
      AlternantIdentities.powerSum a t := by
  apply sum_paddedAlphabet hNM a (fun z => z ^ t)
  exact zero_pow (Nat.ne_of_gt ht)

theorem contentTableau_pos_at_cell {lam : Fin M → ℕ} (T : Tableau lam 0)
    (c : {c : Fin M × ℕ // c ∈ skewYoungDiagram lam 0}) :
    0 < contentTableau T (T c) := by
  rw [contentTableau_eq_card]
  apply Finset.card_pos.mpr
  exact ⟨c, by simp⟩

theorem eval_tableau_eq_zero_of_large_entry (a : Fin N → ℝ) {lam : Fin M → ℕ}
    (T : Tableau lam 0) (c : {c : Fin M × ℕ // c ∈ skewYoungDiagram lam 0})
    (hc : N ≤ (T c).val) :
    MvPolynomial.eval (paddedAlphabet a) (xPow (contentTableau T) : MvPolynomial (Fin M) ℝ) = 0 := by
  rw [CoefficientOne.eval_xPow]
  apply Finset.prod_eq_zero (Finset.mem_univ (T c))
  rw [paddedAlphabet_of_ge a (T c) hc]
  exact zero_pow (Nat.ne_of_gt (contentTableau_pos_at_cell T c))

/-- A column reaching past the available letters forces a zero tableau weight. -/
theorem schurValue_padded_eq_zero_of_long_shape (a : Fin N → ℝ) (lam : Fin M → ℕ)
    (hlam : AlgebraicCombinatorics.IsNPartition lam) (r : Fin M)
    (hr : N ≤ r.val) (hlr : 0 < lam r) :
    CoefficientOne.schurValue lam (paddedAlphabet a) = 0 := by
  let c : {c : Fin M × ℕ // c ∈ skewYoungDiagram lam 0} := ⟨(r, 1), by
    change 0 < 1 ∧ 1 ≤ lam r
    omega⟩
  unfold CoefficientOne.schurValue AlgebraicCombinatorics.schurPoly skewSchurPoly
  rw [map_sum]
  apply Finset.sum_eq_zero
  intro T hT
  apply eval_tableau_eq_zero_of_large_entry a T.val c
  have hrow := tableau_entry_ge_row hlam T.val T.property c
  have hval : r.val ≤ (T.val c).val := hrow
  omega


def restrictShape (h : N ≤ M) (lam : Fin M → ℕ) (i : Fin N) : ℕ :=
  lam (Fin.castLE h i)

abbrev ShapeCell (lam : Fin M → ℕ) :=
  {c : Fin M × ℕ // c ∈ skewYoungDiagram lam 0}

abbrev SSYT (lam : Fin M → ℕ) := {T : Tableau lam 0 // IsSemistandard T}

abbrev BoundedSSYT (N : ℕ) (lam : Fin M → ℕ) :=
  {T : SSYT lam // ∀ c, (T.val c).val < N}

theorem cell_row_lt (lam : Fin M → ℕ) (hzero : ∀ i : Fin M, N ≤ i.val → lam i = 0)
    (c : ShapeCell lam) : c.val.1.val < N := by
  have hc := c.property
  change 0 < c.val.2 ∧ c.val.2 ≤ lam c.val.1 at hc
  by_contra h
  have heq := hzero c.val.1 (by omega)
  omega

def cellEquiv (h : N ≤ M) (lam : Fin M → ℕ)
    (hzero : ∀ i : Fin M, N ≤ i.val → lam i = 0) :
    ShapeCell (restrictShape h lam) ≃ ShapeCell lam where
  toFun c := ⟨(Fin.castLE h c.val.1, c.val.2), c.property⟩
  invFun c := ⟨(⟨c.val.1.val, cell_row_lt lam hzero c⟩, c.val.2), by
    have hc := c.property
    change 0 < c.val.2 ∧ c.val.2 ≤ lam c.val.1 at hc
    change 0 < c.val.2 ∧ c.val.2 ≤ lam _
    have heq : Fin.castLE h (⟨c.val.1.val, cell_row_lt lam hzero c⟩ : Fin N) = c.val.1 := Fin.ext rfl
    simpa only [heq] using hc⟩
  left_inv c := by ext <;> rfl
  right_inv c := by ext <;> rfl

def liftTableau (h : N ≤ M) (lam : Fin M → ℕ)
    (hzero : ∀ i : Fin M, N ≤ i.val → lam i = 0)
    (T : Tableau (restrictShape h lam) 0) : Tableau lam 0 :=
  fun c => Fin.castLE h (T ((cellEquiv h lam hzero).symm c))

theorem liftTableau_semistandard (h : N ≤ M) (lam : Fin M → ℕ)
    (hzero : ∀ i : Fin M, N ≤ i.val → lam i = 0)
    (T : Tableau (restrictShape h lam) 0) (hT : IsSemistandard T) :
    IsSemistandard (liftTableau h lam hzero T) := by
  constructor
  · intro c d hrow hcol
    apply hT.1 ((cellEquiv h lam hzero).symm c) ((cellEquiv h lam hzero).symm d)
    · exact Fin.ext (congrArg (fun i : Fin M => i.val) hrow)
    · exact hcol
  · intro c d hcol hrow
    apply hT.2 ((cellEquiv h lam hzero).symm c) ((cellEquiv h lam hzero).symm d)
    · exact hcol
    · exact hrow

def restrictTableau (h : N ≤ M) (lam : Fin M → ℕ)
    (hzero : ∀ i : Fin M, N ≤ i.val → lam i = 0)
    (T : BoundedSSYT N lam) : Tableau (restrictShape h lam) 0 :=
  fun c => ⟨(T.val.val (cellEquiv h lam hzero c)).val, T.property _⟩

theorem restrictTableau_semistandard (h : N ≤ M) (lam : Fin M → ℕ)
    (hzero : ∀ i : Fin M, N ≤ i.val → lam i = 0) (T : BoundedSSYT N lam) :
    IsSemistandard (restrictTableau h lam hzero T) := by
  constructor
  · intro c d hrow hcol
    apply T.val.property.1 (cellEquiv h lam hzero c) (cellEquiv h lam hzero d)
    · exact congrArg (Fin.castLE h) hrow
    · exact hcol
  · intro c d hcol hrow
    apply T.val.property.2 (cellEquiv h lam hzero c) (cellEquiv h lam hzero d)
    · exact hcol
    · exact hrow

def tableauEquiv (h : N ≤ M) (lam : Fin M → ℕ)
    (hzero : ∀ i : Fin M, N ≤ i.val → lam i = 0) :
    SSYT (restrictShape h lam) ≃ BoundedSSYT N lam where
  toFun T := ⟨⟨liftTableau h lam hzero T.val,
    liftTableau_semistandard h lam hzero T.val T.property⟩, fun c =>
      (T.val ((cellEquiv h lam hzero).symm c)).isLt⟩
  invFun T := ⟨restrictTableau h lam hzero T, restrictTableau_semistandard h lam hzero T⟩
  left_inv T := by
    apply Subtype.ext
    funext c
    apply Fin.ext
    change (T.val ((cellEquiv h lam hzero).symm (cellEquiv h lam hzero c))).val = _
    rw [Equiv.symm_apply_apply]
  right_inv T := by
    apply Subtype.ext
    apply Subtype.ext
    funext c
    apply Fin.ext
    change (T.val.val (cellEquiv h lam hzero ((cellEquiv h lam hzero).symm c))).val = _
    rw [Equiv.apply_symm_apply]

theorem eval_liftTableau (h : N ≤ M) (lam : Fin M → ℕ)
    (hzero : ∀ i : Fin M, N ≤ i.val → lam i = 0)
    (T : Tableau (restrictShape h lam) 0) (a : Fin N → ℝ) :
    MvPolynomial.eval (paddedAlphabet a)
      (xPow (contentTableau (liftTableau h lam hzero T)) : MvPolynomial (Fin M) ℝ) =
    MvPolynomial.eval a (xPow (contentTableau T) : MvPolynomial (Fin N) ℝ) := by
  rw [JacobiTrudi.xPow_content_eq_prod, JacobiTrudi.xPow_content_eq_prod,
    map_prod, map_prod]
  simp only [MvPolynomial.eval_X, liftTableau, paddedAlphabet_castLE]
  symm
  exact Fintype.prod_equiv (cellEquiv h lam hzero) _ _ (by
    intro c
    rw [Equiv.symm_apply_apply])

theorem schurValue_padded_eq_restrict (h : N ≤ M) (a : Fin N → ℝ) (lam : Fin M → ℕ)
    (hzero : ∀ i : Fin M, N ≤ i.val → lam i = 0) :
    CoefficientOne.schurValue lam (paddedAlphabet a) =
      CoefficientOne.schurValue (restrictShape h lam) a := by
  classical
  unfold CoefficientOne.schurValue schurPoly skewSchurPoly
  rw [map_sum, map_sum]
  let f : SSYT lam → ℝ := fun T => MvPolynomial.eval (paddedAlphabet a)
    (xPow (contentTableau T.val))
  have hsum : (∑ T : SSYT lam, f T) = ∑ T : BoundedSSYT N lam, f T.val := by
    apply Finset.sum_congr_set {T : SSYT lam | ∀ c, (T.val c).val < N} f
      (fun T => f T.val)
    · intro T hT
      rfl
    · intro T hT
      change ¬ ∀ c, (T.val c).val < N at hT
      obtain ⟨c, hc⟩ := not_forall.mp hT
      exact eval_tableau_eq_zero_of_large_entry a T.val c (by omega)
  change (∑ T : SSYT lam, f T) = _
  rw [hsum]
  symm
  apply Fintype.sum_equiv (tableauEquiv h lam hzero)
  intro T
  exact (eval_liftTableau h lam hzero T.val a).symm



/-- Schur value of a complete sequence of row lengths on an N-letter alphabet.
The zero case keeps the usual convention for a shape with more than N rows. -/
def globalSchurValue (lam : ℕ → ℕ) (a : Fin N → ℝ) : ℝ := by
  classical
  exact if ∀ i, N ≤ i → lam i = 0 then
    CoefficientOne.schurValue (fun i : Fin N => lam i.val) a else 0

theorem globalSchurValue_eq_of_fits (lam : ℕ → ℕ) (a : Fin N → ℝ)
    (hfit : ∀ i, N ≤ i → lam i = 0) :
    globalSchurValue lam a = CoefficientOne.schurValue (fun i : Fin N => lam i.val) a := by
  unfold globalSchurValue
  rw [if_pos hfit]

theorem globalSchurValue_eq_zero_of_long (lam : ℕ → ℕ) (a : Fin N → ℝ)
    (r : ℕ) (hr : N ≤ r) (hlr : 0 < lam r) : globalSchurValue lam a = 0 := by
  have h : ¬ ∀ i, N ≤ i → lam i = 0 := by
    intro h
    have hh := h r hr
    omega
  simp [globalSchurValue, h]

/-- Padding is an actual tableau specialization, including the overlong case. -/
theorem schurValue_padded_eq_global (h : N ≤ M) (a : Fin N → ℝ) (lam : ℕ → ℕ)
    (hlam : Antitone lam) (hM : ∀ i, M ≤ i → lam i = 0) :
    CoefficientOne.schurValue (fun i : Fin M => lam i.val) (paddedAlphabet a) =
      globalSchurValue lam a := by
  classical
  by_cases hfit : ∀ i, N ≤ i → lam i = 0
  · rw [globalSchurValue_eq_of_fits lam a hfit,
      schurValue_padded_eq_restrict h a _ (fun i hi => hfit i.val hi)]
    rfl
  · obtain ⟨r, hr⟩ := not_forall.mp hfit
    have hrN : N ≤ r := by by_contra hn; exact hr (by omega)
    have hlr : 0 < lam r := by by_contra hn; exact hr (fun _ => by omega)
    have hrM : r < M := by
      by_contra hn
      have hh := hM r (by omega)
      omega
    rw [globalSchurValue_eq_zero_of_long lam a r hrN hlr]
    exact schurValue_padded_eq_zero_of_long_shape a _
      (fun i j hij => hlam hij) ⟨r, hrM⟩ hrN hlr

theorem globalSchurValue_padded (h : N ≤ M) (a : Fin N → ℝ) (lam : ℕ → ℕ)
    (hlam : Antitone lam) :
    globalSchurValue lam (paddedAlphabet (M := M) a) = globalSchurValue lam a := by
  classical
  by_cases hM : ∀ i, M ≤ i → lam i = 0
  · rw [globalSchurValue_eq_of_fits lam _ hM,
      schurValue_padded_eq_global h a lam hlam hM]
  · obtain ⟨r, hr⟩ := not_forall.mp hM
    have hrM : M ≤ r := by by_contra hn; exact hr (by omega)
    have hlr : 0 < lam r := by by_contra hn; exact hr (fun _ => by omega)
    rw [globalSchurValue_eq_zero_of_long lam _ r hrM hlr,
      globalSchurValue_eq_zero_of_long lam _ r (h.trans hrM) hlr]

open AlternantCancellation AlternantIdentities SignedLoad

def initialPartition (k j : ℤ) (r : ℕ) : ℕ := (initialPart k j (r + 1)).toNat
def pPartition (k j : ℤ) (r : ℕ) : ℕ := (pPart k j (r + 1)).toNat
def qPartition (k j : ℤ) (r : ℕ) : ℕ := (qPart k j (r + 1)).toNat
def zPartition (k j : ℤ) (r : ℕ) : ℕ := (zPart k j (r + 1)).toNat

theorem initialPartition_antitone (k j : ℤ) (hj : 0 ≤ j) :
    Antitone (initialPartition k j) := by
  intro r s hrs
  unfold initialPartition initialPart
  split_ifs <;> omega

theorem pPartition_antitone (k j : ℤ) (hj : 0 ≤ j) :
    Antitone (pPartition k j) := by
  intro r s hrs
  unfold pPartition pPart
  split_ifs <;> omega

theorem qPartition_antitone (k j : ℤ) (hj : 0 ≤ j) :
    Antitone (qPartition k j) := by
  intro r s hrs
  unfold qPartition qPart
  split_ifs <;> omega

theorem zPartition_antitone (k j : ℤ) (hj : 0 ≤ j) :
    Antitone (zPartition k j) := by
  intro r s hrs
  unfold zPartition zPart
  split_ifs <;> omega

theorem initialPartition_zero (k j : ℤ) (hj : 0 ≤ j) (hM : k ≤ (M : ℤ))
    (r : ℕ) (hr : M ≤ r) : initialPartition k j r = 0 := by
  unfold initialPartition initialPart
  split_ifs <;> omega

theorem pPartition_zero (k j : ℤ) (hj : 0 ≤ j) (hjk : j ≤ k)
    (hM : 2 * k + 3 ≤ (M : ℤ)) (r : ℕ) (hr : M ≤ r) : pPartition k j r = 0 := by
  unfold pPartition pPart
  split_ifs <;> omega

theorem qPartition_zero (k j : ℤ) (hj : 0 ≤ j) (hjk : j ≤ k)
    (hM : 2 * k + 3 ≤ (M : ℤ)) (r : ℕ) (hr : M ≤ r) : qPartition k j r = 0 := by
  unfold qPartition qPart
  split_ifs <;> omega

theorem zPartition_zero (k j : ℤ) (hj : 0 ≤ j) (hjk : j ≤ k - 1)
    (hM : 2 * k + 3 ≤ (M : ℤ)) (r : ℕ) (hr : M ≤ r) : zPartition k j r = 0 := by
  unfold zPartition zPart
  split_ifs <;> omega

theorem initialShape_padded_eq_global (h : N ≤ M) (a : Fin N → ℝ) (k j : ℤ)
    (hj : 0 ≤ j) (hM : k ≤ (M : ℤ)) :
    CoefficientOne.schurValue (initialShape k j) (paddedAlphabet (M := M) a) =
      globalSchurValue (initialPartition k j) a := by
  exact schurValue_padded_eq_global h a (initialPartition k j)
    (initialPartition_antitone k j hj) (initialPartition_zero k j hj hM)

theorem pShape_padded_eq_global (h : N ≤ M) (a : Fin N → ℝ) (k j : ℤ)
    (hj : 0 ≤ j) (hjk : j ≤ k) (hM : 2 * k + 3 ≤ (M : ℤ)) :
    CoefficientOne.schurValue (pShape k j) (paddedAlphabet (M := M) a) =
      globalSchurValue (pPartition k j) a := by
  exact schurValue_padded_eq_global h a (pPartition k j)
    (pPartition_antitone k j hj) (pPartition_zero k j hj hjk hM)

theorem qShape_padded_eq_global (h : N ≤ M) (a : Fin N → ℝ) (k j : ℤ)
    (hj : 0 ≤ j) (hjk : j ≤ k) (hM : 2 * k + 3 ≤ (M : ℤ)) :
    CoefficientOne.schurValue (qShape k j) (paddedAlphabet (M := M) a) =
      globalSchurValue (qPartition k j) a := by
  exact schurValue_padded_eq_global h a (qPartition k j)
    (qPartition_antitone k j hj) (qPartition_zero k j hj hjk hM)

theorem zShape_padded_eq_global (h : N ≤ M) (a : Fin N → ℝ) (k j : ℤ)
    (hj : 0 ≤ j) (hjk : j ≤ k - 1) (hM : 2 * k + 3 ≤ (M : ℤ)) :
    CoefficientOne.schurValue (zShape k j) (paddedAlphabet (M := M) a) =
      globalSchurValue (zPartition k j) a := by
  exact schurValue_padded_eq_global h a (zPartition k j)
    (zPartition_antitone k j hj) (zPartition_zero k j hj hjk hM)

/-- The manuscript's signed-load identity on an arbitrary finite real alphabet.
All displayed partitions retain all their rows. -/
theorem signed_load_value_arbitrary (a : Fin N → ℝ) (k : ℤ) (hk : 0 ≤ k) :
    (∑ j ∈ Icc 0 k, (-1 : ℝ) ^ j.toNat * powerSum a (j + 2).toNat *
        globalSchurValue (initialPartition k j) a) =
      (∑ j ∈ Icc 0 k,
        (globalSchurValue (pPartition k j) a - globalSchurValue (qPartition k j) a)) -
      ∑ j ∈ Icc 0 (k - 1), globalSchurValue (zPartition k j) a := by
  let M := N + 2 * k.toNat + 3
  have hNM : N ≤ M := by omega
  have hM : 2 * k + 3 ≤ (M : ℤ) := by dsimp [M]; omega
  have hMk : k ≤ (M : ℤ) := by omega
  have h := SignedLoad.signed_load_value (paddedAlphabet (M := M) a) k hk hM
  have hleft : (∑ j ∈ Icc 0 k, (-1 : ℝ) ^ j.toNat *
      powerSum (paddedAlphabet (M := M) a) (j + 2).toNat *
      CoefficientOne.schurValue (initialShape k j) (paddedAlphabet (M := M) a)) =
      ∑ j ∈ Icc 0 k, (-1 : ℝ) ^ j.toNat * powerSum a (j + 2).toNat *
        globalSchurValue (initialPartition k j) a := by
    apply Finset.sum_congr rfl
    intro j hj
    have hj0 := (Finset.mem_Icc.mp hj).1
    rw [powerSum_paddedAlphabet hNM a _ (by omega),
      initialShape_padded_eq_global hNM a k j hj0 hMk]
  have hpq : (∑ j ∈ Icc 0 k,
      (CoefficientOne.schurValue (pShape k j) (paddedAlphabet (M := M) a) -
        CoefficientOne.schurValue (qShape k j) (paddedAlphabet (M := M) a))) =
      ∑ j ∈ Icc 0 k, (globalSchurValue (pPartition k j) a -
        globalSchurValue (qPartition k j) a) := by
    apply Finset.sum_congr rfl
    intro j hj
    obtain ⟨hj0, hjk⟩ := Finset.mem_Icc.mp hj
    rw [pShape_padded_eq_global hNM a k j hj0 hjk hM,
      qShape_padded_eq_global hNM a k j hj0 hjk hM]
  have hz : (∑ j ∈ Icc 0 (k - 1),
      CoefficientOne.schurValue (zShape k j) (paddedAlphabet (M := M) a)) =
      ∑ j ∈ Icc 0 (k - 1), globalSchurValue (zPartition k j) a := by
    apply Finset.sum_congr rfl
    intro j hj
    obtain ⟨hj0, hjk⟩ := Finset.mem_Icc.mp hj
    rw [zShape_padded_eq_global hNM a k j hj0 hjk hM]
  rw [hleft, hpq, hz] at h
  exact h



theorem paddedAlphabet_nonneg (a : Fin N → ℝ) (ha : ∀ i, 0 ≤ a i) :
    ∀ i : Fin M, 0 ≤ paddedAlphabet a i := by
  intro i
  unfold paddedAlphabet
  split_ifs with hi
  · exact ha _
  · exact le_rfl

theorem globalSchurValue_nonneg (lam : ℕ → ℕ) (a : Fin N → ℝ)
    (ha : ∀ i, 0 ≤ a i) : 0 ≤ globalSchurValue lam a := by
  unfold globalSchurValue
  split_ifs
  · exact CoefficientOne.schurValue_nonneg _ a ha
  · exact le_rfl

theorem globalSchurValue_pos_of_fits (lam : ℕ → ℕ) (a : Fin N → ℝ)
    (ha : ∀ i, 0 < a i) (hfit : ∀ i, N ≤ i → lam i = 0) :
    0 < globalSchurValue lam a := by
  rw [globalSchurValue_eq_of_fits lam a hfit]
  exact CoefficientOne.schurValue_pos _ a ha

theorem globalSchurValue_pos_iff (lam : ℕ → ℕ) (a : Fin N → ℝ)
    (ha : ∀ i, 0 < a i) :
    0 < globalSchurValue lam a ↔ ∀ i, N ≤ i → lam i = 0 := by
  classical
  constructor
  · intro h
    by_contra hfit
    have hz : globalSchurValue lam a = 0 := by
      unfold globalSchurValue
      rw [if_neg hfit]
    rw [hz] at h
    exact lt_irrefl 0 h
  · exact globalSchurValue_pos_of_fits lam a ha


end CoefficientOne.SchurStability

end
