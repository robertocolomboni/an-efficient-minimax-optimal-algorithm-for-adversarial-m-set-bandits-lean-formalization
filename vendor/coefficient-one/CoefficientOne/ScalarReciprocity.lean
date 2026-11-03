import CoefficientOne.ScalarLoad

/-!
# Reciprocity of the scalar expressions

Rectangle reciprocity is a specialization of the proved complement lemma.
Alphabet deletion is handled by a permutation followed by actual zero-padding,
so the complement formula is used on precisely the remaining positive letters.
-/

noncomputable section

namespace CoefficientOne.ScalarReciprocity

open Finset RectangleDeterminants RectangleComplement SchurStability ScalarLoad

variable {N : ℕ}

theorem complement_rectangleShape (q k : ℕ) (hk : k ≤ N) :
    complementShape q (rectangleShape N q (N - k)) = rectangleShape N q k := by
  funext i
  have hi := i.isLt
  simp only [complementShape, rectangleShape, reverseRows_apply, Fin.val_rev]
  change q - (if N - (i.val + 1) < N - k then q else 0) =
    (if i.val < k then q else 0)
  split_ifs <;> omega

theorem rectangleSchur_reciprocity (a : Fin N → ℝ) (ha : ∀ i, 0 < a i)
    (q k : ℕ) (hk : k ≤ N) :
    rectangleSchur a q k =
      (∏ i, a i) ^ q * rectangleSchur (fun i => (a i)⁻¹) q (N - k) := by
  have hbound : ∀ i, rectangleShape N q (N - k) i ≤ q := by
    intro i
    unfold rectangleShape
    split_ifs <;> omega
  have h := schurValue_complement a ha q (rectangleShape N q (N - k))
    (rectangleShape_isPartition N q (N - k)) hbound
  rw [complement_rectangleShape q k hk] at h
  exact h.symm

theorem elementary_reciprocity (a : Fin N → ℝ) (ha : ∀ i, 0 < a i)
    (k : ℕ) (hk : k ≤ N) :
    elementaryInt a k = (∏ i, a i) * elementaryInt (fun i => (a i)⁻¹) (N - k) := by
  rw [← rectangleSchur_width_one a k hk, rectangleSchur_reciprocity a ha 1 k hk,
    rectangleSchur_width_one _ (N - k) (Nat.sub_le _ _), pow_one]
  rw [Nat.cast_sub hk]

theorem completeInt_comp_perm (a : Fin N → ℝ) (e : Equiv.Perm (Fin N)) (d : ℤ) :
    completeInt (a ∘ e) d = completeInt a d := by
  unfold completeInt
  rw [← MvPolynomial.eval_rename]
  rw [SymmetricFunctions.hsymmExt_isSymmetric d e]

theorem schurValue_comp_perm (lam : Fin N → ℕ)
    (hlam : AlgebraicCombinatorics.IsNPartition lam)
    (a : Fin N → ℝ) (e : Equiv.Perm (Fin N)) :
    schurValue lam (a ∘ e) = schurValue lam a := by
  rw [JacobiTrudi.schurValue_eq_det lam hlam, JacobiTrudi.schurValue_eq_det lam hlam]
  apply congrArg Matrix.det
  ext i j
  exact completeInt_comp_perm a e _

theorem globalSchurValue_comp_perm (lam : ℕ → ℕ) (hlam : Antitone lam)
    (a : Fin N → ℝ) (e : Equiv.Perm (Fin N)) :
    globalSchurValue lam (a ∘ e) = globalSchurValue lam a := by
  unfold globalSchurValue
  split_ifs
  · apply schurValue_comp_perm
    intro i j hij
    exact hlam hij
  · rfl

/-- Move the removed coordinate to the last position, then retain the others. -/
def deletedAlphabet (a : Fin (N + 1) → ℝ) (i : Fin (N + 1)) : Fin N → ℝ :=
  fun j => a ((Equiv.swap i (Fin.last N)) j.castSucc)

theorem deletedAlphabet_pos (a : Fin (N + 1) → ℝ) (ha : ∀ j, 0 < a j)
    (i : Fin (N + 1)) : ∀ j, 0 < deletedAlphabet a i j := fun j => ha _

theorem update_comp_swap_eq_padded (a : Fin (N + 1) → ℝ) (i : Fin (N + 1)) :
    Function.update a i 0 ∘ Equiv.swap i (Fin.last N) =
      paddedAlphabet (deletedAlphabet a i) := by
  funext j
  by_cases hj : j.val < N
  · have hne : Equiv.swap i (Fin.last N) j ≠ i := by
      intro heq
      have hh := congrArg (Equiv.swap i (Fin.last N)) heq
      have hlast : j = Fin.last N := by simpa using hh
      have hv := congrArg Fin.val hlast
      simp only [Fin.val_last] at hv
      omega
    simp only [Function.comp_apply, Function.update_of_ne hne,
      paddedAlphabet, dif_pos hj, deletedAlphabet]
    congr 2
  · have heq : j = Fin.last N := by apply Fin.ext; simp; omega
    subst j
    simp [Function.comp_apply, paddedAlphabet]

theorem globalSchurValue_update_eq_deleted (lam : ℕ → ℕ) (hlam : Antitone lam)
    (a : Fin (N + 1) → ℝ) (i : Fin (N + 1)) :
    globalSchurValue lam (Function.update a i 0) =
      globalSchurValue lam (deletedAlphabet a i) := by
  rw [← globalSchurValue_comp_perm lam hlam (Function.update a i 0)
    (Equiv.swap i (Fin.last N)), update_comp_swap_eq_padded]
  exact globalSchurValue_padded (Nat.le_succ N) (deletedAlphabet a i) lam hlam

theorem deletedAlphabet_inv (a : Fin (N + 1) → ℝ) (i : Fin (N + 1)) :
    deletedAlphabet (fun j => (a j)⁻¹) i = fun j => (deletedAlphabet a i j)⁻¹ := rfl

theorem deletedAlphabet_prod_mul (a : Fin (N + 1) → ℝ) (i : Fin (N + 1)) :
    (∏ j, deletedAlphabet a i j) * a i = ∏ j, a j := by
  have hp := (Equiv.prod_comp (Equiv.swap i (Fin.last N)) a)
  rw [Fin.prod_univ_castSucc] at hp
  simpa only [Equiv.swap_apply_right, deletedAlphabet] using hp

/-- The rectangular complement formula expressed with untruncated partitions. -/
theorem globalRectangle_reciprocity (a : Fin N → ℝ) (ha : ∀ i, 0 < a i)
    (q k : ℕ) (hk : k ≤ N) :
    globalSchurValue (rectanglePartition q k) a =
      (∏ i, a i) ^ q * globalSchurValue (rectanglePartition q (N - k))
        (fun i => (a i)⁻¹) := by
  rw [globalRectangle_eq_rectangleSchur a q k hk,
    globalRectangle_eq_rectangleSchur _ q (N - k) (Nat.sub_le _ _)]
  exact rectangleSchur_reciprocity a ha q k hk

/-- Reciprocity of the actual load. The alphabet has N+1 letters, so each
complement is taken in the N-letter alphabet left after deletion. -/
theorem load_reciprocity (a : Fin (N + 1) → ℝ) (ha : ∀ i, 0 < a i)
    (k : ℕ) (hk : k ≤ N) :
    load a k = (∏ i, a i) ^ 4 * load (fun i => (a i)⁻¹) (N - k) := by
  unfold load
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i _
  rw [globalSchurValue_update_eq_deleted _ (rectanglePartition_antitone 4 k),
    globalSchurValue_update_eq_deleted _ (rectanglePartition_antitone 4 (N - k)),
    globalRectangle_eq_rectangleSchur _ 4 k hk,
    globalRectangle_eq_rectangleSchur _ 4 (N - k) (Nat.sub_le _ _),
    rectangleSchur_reciprocity _ (deletedAlphabet_pos a ha i) 4 k hk,
    deletedAlphabet_inv]
  rw [← deletedAlphabet_prod_mul a i]
  have hi : a i ≠ 0 := ne_of_gt (ha i)
  field_simp

/-- The two scalar expressions in equation `eq:scalars`. -/
def scalarA (a : Fin N → ℝ) (k : ℕ) : ℝ :=
  globalSchurValue (rectanglePartition 2 k) a *
    globalSchurValue (rectanglePartition 3 (k + 1)) a -
      elementaryInt a (k + 1 : ℕ) * load a k

def scalarB (a : Fin N → ℝ) (k : ℕ) : ℝ :=
  globalSchurValue (rectanglePartition 3 k) a *
    globalSchurValue (rectanglePartition 2 (k + 1)) a -
      elementaryInt a k * load a k

/-- A_k(a) = product(a)^5 B_(N-k)(a^-1) on an (N+1)-letter alphabet. -/
theorem scalarA_reciprocity (a : Fin (N + 1) → ℝ) (ha : ∀ i, 0 < a i)
    (k : ℕ) (hk : k ≤ N) :
    scalarA a k = (∏ i, a i) ^ 5 * scalarB (fun i => (a i)⁻¹) (N - k) := by
  have h2 := globalRectangle_reciprocity a ha 2 k (by omega)
  have h3 := globalRectangle_reciprocity a ha 3 (k + 1) (by omega)
  have he := elementary_reciprocity a ha (k + 1) (by omega)
  rw [show N + 1 - k = (N - k) + 1 by omega] at h2
  rw [show N + 1 - (k + 1) = N - k by omega] at h3
  have heidx : ((N + 1 : ℕ) : ℤ) - ((k + 1 : ℕ) : ℤ) = ((N - k : ℕ) : ℤ) := by omega
  rw [heidx] at he
  unfold scalarA scalarB
  rw [h2, h3, he, load_reciprocity a ha k hk]
  ring

/-- The coefficient-one shape `(5^ell,1,1)` in the scalar lemma. -/
def distinguishedPartition (ell : ℕ) (r : ℕ) : ℕ :=
  if r < ell then 5 else if r < ell + 2 then 1 else 0

/-- Its complement, `(5^(k-1),4,4)`, used for the strict lower bound. -/
def strictPartition (k : ℕ) (r : ℕ) : ℕ :=
  if r < k - 1 then 5 else if r < k + 1 then 4 else 0

theorem distinguishedPartition_antitone (ell : ℕ) : Antitone (distinguishedPartition ell) := by
  intro r s hrs
  unfold distinguishedPartition
  split_ifs <;> omega

theorem strictPartition_antitone (k : ℕ) : Antitone (strictPartition k) := by
  intro r s hrs
  unfold strictPartition
  split_ifs <;> omega

theorem distinguished_complement (k : ℕ) (hk : k ≤ N) (hkpos : 1 ≤ k) :
    complementShape 5 (fun i : Fin (N + 1) => distinguishedPartition (N - k) i.val) =
      (fun i : Fin (N + 1) => strictPartition k i.val) := by
  funext i
  have hi := i.isLt
  simp only [complementShape, distinguishedPartition, strictPartition,
    reverseRows_apply, Fin.val_rev]
  change 5 - (if N + 1 - (i.val + 1) < N - k then 5
      else if N + 1 - (i.val + 1) < N - k + 2 then 1 else 0) =
    (if i.val < k - 1 then 5 else if i.val < k + 1 then 4 else 0)
  split_ifs <;> omega

/-- Exact identification of the retained positive Schur term after reciprocity. -/
theorem distinguished_reciprocity (a : Fin (N + 1) → ℝ) (ha : ∀ i, 0 < a i)
    (k : ℕ) (hk : k ≤ N) (hkpos : 1 ≤ k) :
    (∏ i, a i) ^ 5 * globalSchurValue (distinguishedPartition (N - k))
        (fun i => (a i)⁻¹) = globalSchurValue (strictPartition k) a := by
  have hfitD : ∀ r, N + 1 ≤ r → distinguishedPartition (N - k) r = 0 := by
    intro r hr
    unfold distinguishedPartition
    split_ifs <;> omega
  have hfitS : ∀ r, N + 1 ≤ r → strictPartition k r = 0 := by
    intro r hr
    unfold strictPartition
    split_ifs <;> omega
  rw [globalSchurValue_eq_of_fits _ _ hfitD, globalSchurValue_eq_of_fits _ _ hfitS]
  have hlam : AlgebraicCombinatorics.IsNPartition
      (fun i : Fin (N + 1) => distinguishedPartition (N - k) i.val) := by
    intro i j hij
    exact distinguishedPartition_antitone (N - k) hij
  have hbound : ∀ i : Fin (N + 1), distinguishedPartition (N - k) i.val ≤ 5 := by
    intro i
    unfold distinguishedPartition
    split_ifs <;> omega
  have h := schurValue_complement a ha 5 _ hlam hbound
  rw [distinguished_complement k hk hkpos] at h
  exact h

theorem strictSchurValue_pos (a : Fin (N + 1) → ℝ) (ha : ∀ i, 0 < a i)
    (k : ℕ) (hk : k ≤ N) : 0 < globalSchurValue (strictPartition k) a := by
  apply globalSchurValue_pos_of_fits _ a ha
  intro r hr
  unfold strictPartition
  split_ifs <;> omega

end CoefficientOne.ScalarReciprocity
