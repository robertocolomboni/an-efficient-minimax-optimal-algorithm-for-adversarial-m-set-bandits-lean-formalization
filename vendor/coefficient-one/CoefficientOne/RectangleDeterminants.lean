import CoefficientOne.JacobiTrudi
import CoefficientOne.ElementaryBridge
import CoefficientOne.DesnanotJacobi
import CoefficientOne.RectangleComplement

/-!
# Rectangular dual Jacobi–Trudi by condensation

The ordinary Jacobi–Trudi identity is imported with its LGV proof and its explicit
tableau bridge. For the rectangular dual identity required in the manuscript,
we give a separate proof: both determinants obey Desnanot–Jacobi condensation;
the column identity starts the induction, and positivity of the tableau sum
justifies cancellation. Empty and full-height rectangles are treated explicitly.
-/

noncomputable section

namespace CoefficientOne.RectangleDeterminants

open Finset Matrix

variable {R : Type*} [CommRing R] {N : ℕ}

/-- Toeplitz matrix with integer-indexed coefficients, including the zero-degree
and negative-degree conventions in the manuscript. -/
def toeplitz (f : ℤ → R) (z : ℤ) (d : ℕ) : Matrix (Fin d) (Fin d) R :=
  fun i j => f (z - (i.val : ℤ) + (j.val : ℤ))

theorem toeplitz_condensation (f : ℤ → R) (z : ℤ) (d : ℕ) :
    (toeplitz f z (d + 2)).det * (toeplitz f z d).det =
      (toeplitz f z (d + 1)).det ^ 2 -
        (toeplitz f (z - 1) (d + 1)).det *
          (toeplitz f (z + 1) (d + 1)).det := by
  have h11 : DesnanotJacobi.M11 (toeplitz f z (d + 2)) = toeplitz f z (d + 1) := by
    ext i j
    simp only [DesnanotJacobi.M11, toeplitz, submatrix_apply, Fin.succAbove_zero,
      Fin.val_succ, Nat.cast_add, Nat.cast_one]
    congr 1
    ring
  have hkk : DesnanotJacobi.Mkk (toeplitz f z (d + 2)) = toeplitz f z (d + 1) := by
    ext i j
    simp [DesnanotJacobi.Mkk, toeplitz]
  have h1k : DesnanotJacobi.M1k (toeplitz f z (d + 2)) =
      toeplitz f (z - 1) (d + 1) := by
    ext i j
    simp only [DesnanotJacobi.M1k, toeplitz, submatrix_apply, Fin.succAbove_zero,
      Fin.succAbove_last, Fin.val_succ, Fin.val_castSucc, Nat.cast_add, Nat.cast_one]
    congr 1
    ring
  have hk1 : DesnanotJacobi.Mk1 (toeplitz f z (d + 2)) =
      toeplitz f (z + 1) (d + 1) := by
    ext i j
    simp only [DesnanotJacobi.Mk1, toeplitz, submatrix_apply, Fin.succAbove_zero,
      Fin.succAbove_last, Fin.val_succ, Fin.val_castSucc, Nat.cast_add, Nat.cast_one]
    congr 1
    ring
  have hmid : DesnanotJacobi.M1k_1k (toeplitz f z (d + 2)) = toeplitz f z d := by
    ext i j
    simp only [DesnanotJacobi.M1k_1k, toeplitz, submatrix_apply, Function.comp_apply,
      Fin.succAbove_zero, Fin.succAbove_last, Fin.val_succ, Fin.val_castSucc,
      Nat.cast_add, Nat.cast_one]
    congr 1
    ring
  simpa only [h11, hkk, h1k, hk1, hmid, pow_two] using
    DesnanotJacobi.desnanot_jacobi (toeplitz f z (d + 2))

/-- Ordinary Jacobi–Trudi matrix after padding a rectangle with zero rows. -/
def paddedMatrix (f : ℤ → R) (q : ℤ) (k n : ℕ) : Matrix (Fin n) (Fin n) R :=
  fun i j => f ((if i.val < k then q else 0) - (i.val : ℤ) + (j.val : ℤ))

theorem paddedMatrix_det_succ (f : ℤ → R) (hf0 : f 0 = 1)
    (hfneg : ∀ z < 0, f z = 0) (q : ℤ) (k n : ℕ) (hkn : k ≤ n) :
    (paddedMatrix f q k (n + 1)).det = (paddedMatrix f q k n).det := by
  rw [Matrix.det_succ_row _ (Fin.last n), Finset.sum_eq_single (Fin.last n)]
  · have hsub : (paddedMatrix f q k (n + 1)).submatrix
        (Fin.last n).succAbove (Fin.last n).succAbove = paddedMatrix f q k n := by
      ext i j
      simp only [paddedMatrix, submatrix_apply, Fin.succAbove_last, Fin.val_castSucc]
    have hpow : (-1 : R) ^ (n + n) = 1 := by
      rw [← two_mul, pow_mul]
      simp
    simp only [Fin.val_last, paddedMatrix, not_lt.mpr hkn, if_false,
      zero_sub, neg_add_cancel, hf0, hpow, one_mul, hsub]
  · intro j _ hj
    have hjn : j.val < n := by
      have hne : j.val ≠ n := fun h => hj (Fin.ext h)
      omega
    have hz : (0 : ℤ) - n + j.val < 0 := by omega
    simp only [paddedMatrix, Fin.val_last, not_lt.mpr hkn, if_false, hfneg _ hz,
      mul_zero, zero_mul]
  · simp

theorem paddedMatrix_det (f : ℤ → R) (hf0 : f 0 = 1)
    (hfneg : ∀ z < 0, f z = 0) (q : ℤ) (k n : ℕ) (hkn : k ≤ n) :
    (paddedMatrix f q k n).det = (toeplitz f q k).det := by
  obtain ⟨t, rfl⟩ := Nat.exists_eq_add_of_le hkn
  induction t with
  | zero =>
      congr 1
      ext i j
      simp [paddedMatrix, toeplitz, i.isLt]
  | succ t ih =>
      rw [show k + (t + 1) = k + t + 1 by omega,
        paddedMatrix_det_succ f hf0 hfneg q k (k + t) (by omega)]
      exact ih (by omega)

theorem toeplitz_zero_det (f : ℤ → R) (hf0 : f 0 = 1)
    (hfneg : ∀ z < 0, f z = 0) (d : ℕ) : (toeplitz f 0 d).det = 1 := by
  have h := paddedMatrix_det f hf0 hfneg 0 0 d (Nat.zero_le _)
  have hm : paddedMatrix f 0 0 d = toeplitz f 0 d := by
    ext i j
    simp only [paddedMatrix, toeplitz, Nat.not_lt_zero, if_false]
  rw [hm] at h
  simpa using h

def rectangleShape (N q k : ℕ) : Fin N → ℕ :=
  fun i => if i.val < k then q else 0

def rectangleSchur (a : Fin N → ℝ) (q k : ℕ) : ℝ :=
  schurValue (rectangleShape N q k) a

theorem rectangleShape_isPartition (N q k : ℕ) :
    AlgebraicCombinatorics.IsNPartition (rectangleShape N q k) := by
  intro i j hij
  dsimp [rectangleShape]
  split_ifs <;> omega

def completeInt (a : Fin N → ℝ) (j : ℤ) : ℝ :=
  MvPolynomial.eval a (SymmetricFunctions.hsymmExt (R := ℝ) j)

theorem completeInt_zero (a : Fin N → ℝ) : completeInt a 0 = 1 := by
  simp [completeInt, SymmetricFunctions.hsymmExt]

theorem completeInt_of_neg (a : Fin N → ℝ) (j : ℤ) (hj : j < 0) :
    completeInt a j = 0 := by
  simp [completeInt, SymmetricFunctions.hsymmExt, not_le.mpr hj]

theorem rectangleSchur_eq_completeDet (a : Fin N → ℝ) (q k : ℕ) (hk : k ≤ N) :
    rectangleSchur a q k = (toeplitz (completeInt a) q k).det := by
  rw [rectangleSchur, JacobiTrudi.schurValue_eq_det _ (rectangleShape_isPartition N q k)]
  have hm : (fun i j : Fin N => MvPolynomial.eval a
      (SymmetricFunctions.hsymmExt (R := ℝ)
        ((rectangleShape N q k i : ℤ) - (i.val : ℤ) + (j.val : ℤ)))) =
      paddedMatrix (completeInt a) q k N := by
    ext i j
    simp only [rectangleShape, paddedMatrix, completeInt, Nat.cast_ite, Nat.cast_zero]
  rw [hm]
  exact paddedMatrix_det _ (completeInt_zero a) (completeInt_of_neg a) _ _ _ hk


/-- The dual determinant whose number of rows is the rectangle's width. -/
def elementaryDet (a : Fin N → ℝ) (q k : ℕ) : ℝ :=
  (toeplitz (elementaryInt a) k q).det

theorem rectangleSchur_pos (a : Fin N → ℝ) (ha : ∀ i, 0 < a i) (q k : ℕ) :
    0 < rectangleSchur a q k := schurValue_pos _ a ha

theorem rectangleSchur_width_zero (a : Fin N → ℝ) (k : ℕ) :
    rectangleSchur a 0 k = 1 := by
  have he : rectangleShape N 0 k = fun _ => 0 := by
    ext i
    simp [rectangleShape]
  rw [rectangleSchur, he, RectangleComplement.schurValue_const]
  simp

theorem rectangleSchur_height_zero (a : Fin N → ℝ) (q : ℕ) :
    rectangleSchur a q 0 = 1 := by
  have he : rectangleShape N q 0 = fun _ => 0 := by
    ext i
    simp [rectangleShape]
  rw [rectangleSchur, he, RectangleComplement.schurValue_const]
  simp

theorem rectangleSchur_height_full (a : Fin N → ℝ) (q : ℕ) :
    rectangleSchur a q N = (∏ i, a i) ^ q := by
  have he : rectangleShape N q N = fun _ => q := by
    ext i
    simp [rectangleShape, i.isLt]
  rw [rectangleSchur, he, RectangleComplement.schurValue_const]

theorem rectangleSchur_width_one (a : Fin N → ℝ) (k : ℕ) (hk : k ≤ N) :
    rectangleSchur a 1 k = elementaryInt a k := by
  rw [elementaryInt_nat, ← eval_esymm_eq_elementarySum,
    JacobiTrudi.esymm_eq_schurPoly_column k hk]
  rfl

theorem elementaryDet_width_zero (a : Fin N → ℝ) (k : ℕ) :
    elementaryDet a 0 k = 1 := by
  simp [elementaryDet]

theorem elementaryDet_width_one (a : Fin N → ℝ) (k : ℕ) :
    elementaryDet a 1 k = elementaryInt a k := by
  simp [elementaryDet, Matrix.det_unique, toeplitz]

theorem elementaryDet_height_zero (a : Fin N → ℝ) (q : ℕ) :
    elementaryDet a q 0 = 1 := by
  exact toeplitz_zero_det _ (elementaryInt_zero a) (elementaryInt_of_neg a) q

theorem elementaryInt_card (a : Fin N → ℝ) : elementaryInt a N = ∏ i, a i := by
  rw [elementaryInt_nat, elementarySum_eq_powersetCard]
  have hs := Finset.powersetCard_self (Finset.univ : Finset (Fin N))
  simp only [Finset.card_univ, Fintype.card_fin] at hs
  rw [hs]
  simp

theorem elementaryDet_height_full (a : Fin N → ℝ) (q : ℕ) :
    elementaryDet a q N = (∏ i, a i) ^ q := by
  have htri : (toeplitz (elementaryInt a) N q).BlockTriangular OrderDual.toDual := by
    intro i j hij
    apply elementaryInt_of_card_lt
    simp only [Fintype.card_fin]
    have hval : i.val < j.val := hij
    omega
  rw [elementaryDet, Matrix.det_of_lowerTriangular _ htri]
  simp [toeplitz, elementaryInt_card]

theorem elementaryDet_condensation (a : Fin N → ℝ) (q k : ℕ) :
    elementaryDet a (q + 2) (k + 1) * elementaryDet a q (k + 1) =
      elementaryDet a (q + 1) (k + 1) ^ 2 -
        elementaryDet a (q + 1) k * elementaryDet a (q + 1) (k + 2) := by
  simpa only [elementaryDet, Nat.cast_add, Nat.cast_one, Nat.cast_ofNat,
    add_sub_cancel_right, add_assoc, one_add_one_eq_two] using
    toeplitz_condensation (elementaryInt a) (k + 1) q

theorem rectangleSchur_condensation (a : Fin N → ℝ) (q k : ℕ) (hk : k + 2 ≤ N) :
    rectangleSchur a (q + 2) (k + 1) * rectangleSchur a q (k + 1) =
      rectangleSchur a (q + 1) (k + 1) ^ 2 -
        rectangleSchur a (q + 1) k * rectangleSchur a (q + 1) (k + 2) := by
  have h := toeplitz_condensation (completeInt a) (q + 1) k
  have hcast : (q : ℤ) + 1 + 1 = (q + 2 : ℕ) := by omega
  simp only [Nat.cast_add, Nat.cast_one, add_sub_cancel_right, hcast] at h
  rw [rectangleSchur_eq_completeDet a _ _ (by omega),
    rectangleSchur_eq_completeDet a _ _ (by omega),
    rectangleSchur_eq_completeDet a _ _ (by omega),
    rectangleSchur_eq_completeDet a _ _ (by omega),
    rectangleSchur_eq_completeDet a _ _ hk]
  simp only [Nat.cast_add, Nat.cast_one, Nat.cast_ofNat] at h ⊢
  nlinarith [h]

/-- Rectangular dual Jacobi–Trudi. The proof follows condensation and uses
strict positivity of the actual tableau sum at each cancellation. -/
theorem rectangleSchur_eq_elementaryDet (a : Fin N → ℝ) (ha : ∀ i, 0 < a i)
    (q k : ℕ) (hk : k ≤ N) : rectangleSchur a q k = elementaryDet a q k := by
  induction q using Nat.twoStepInduction generalizing k with
  | zero => rw [rectangleSchur_width_zero, elementaryDet_width_zero]
  | one => rw [rectangleSchur_width_one a k hk, elementaryDet_width_one]
  | more q ih0 ih1 =>
      by_cases hk0 : k = 0
      · subst k
        rw [rectangleSchur_height_zero, elementaryDet_height_zero]
      by_cases hkN : k = N
      · subst k
        rw [rectangleSchur_height_full, elementaryDet_height_full]
      obtain ⟨r, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hk0
      have hr : r + 2 ≤ N := by omega
      have hF := rectangleSchur_condensation a q r hr
      have hG := elementaryDet_condensation a q r
      rw [← ih0 (r + 1) (by omega), ← ih1 (r + 1) (by omega),
        ← ih1 r (by omega), ← ih1 (r + 2) hr] at hG
      exact mul_right_cancel₀ (ne_of_gt (rectangleSchur_pos a ha q (r + 1)))
        (hF.trans hG.symm)

theorem elementaryDet_pos (a : Fin N → ℝ) (ha : ∀ i, 0 < a i)
    (q k : ℕ) (hk : k ≤ N) : 0 < elementaryDet a q k := by
  rw [← rectangleSchur_eq_elementaryDet a ha q k hk]
  exact rectangleSchur_pos a ha q k

end CoefficientOne.RectangleDeterminants

