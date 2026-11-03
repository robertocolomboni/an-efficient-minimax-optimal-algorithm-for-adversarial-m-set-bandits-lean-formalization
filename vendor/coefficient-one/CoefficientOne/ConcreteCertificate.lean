import CoefficientOne.AlphabetDeterminants
import CoefficientOne.RestrictionBridge
import CoefficientOne.ScalarReciprocity
import CoefficientOne.MatrixCertificate

/-!
# The actual matrix certificate

This file constructs H, b, t and R from the alphabet, proves their concrete
diagonal/off-diagonal identities, and evaluates R on the alphabet vector.
The final row formula is the scalar A/B expression in the manuscript.
-/

noncomputable section

namespace CoefficientOne.ConcreteCertificate

open Finset Matrix AlphabetDeterminants RectangleDeterminants ElementaryDeletion
open ScalarReciprocity ScalarLoad

variable {N : ℕ}

def Hzeroed (a : Fin N → ℝ) (k : ℕ) : Matrix (Fin N) (Fin N) ℝ :=
  fun i l => if i = l then 0 else kernelK (zeroPair a i l) k

def b (a : Fin N → ℝ) (k : ℕ) : Fin N → ℝ :=
  fun i => kernelK (zeroLetter a i) k

def t (a : Fin N → ℝ) (k : ℕ) : Fin N → ℝ :=
  fun i => a i * rectangleSchur (zeroLetter a i) 3 k

def coefficient (a : Fin N → ℝ) (k : ℕ) : ℝ :=
  elementaryInt a (k + 1 : ℕ) / rectangleSchur a 3 (k + 1)

def R (a : Fin N → ℝ) (k : ℕ) : Matrix (Fin N) (Fin N) ℝ :=
  Matrix.vecMulVec (b a k) (b a k) - kernelK a k • Hzeroed a k -
    coefficient a k • Matrix.vecMulVec (t a k) (t a k)

theorem R_eq_certificate (a : Fin N → ℝ) (k : ℕ) :
    R a k = Matrix.vecMulVec (b a k) (b a k) - kernelK a k • Hzeroed a k -
      coefficient a k • Matrix.vecMulVec (t a k) (t a k) := rfl

theorem R_apply (a : Fin N → ℝ) (k : ℕ) (i l : Fin N) :
    R a k i l = b a k i * b a k l - kernelK a k * Hzeroed a k i l -
      coefficient a k * t a k i * t a k l := by
  simp [R, Matrix.vecMulVec_apply, Matrix.smul_apply, smul_eq_mul]
  ring

theorem kernelMatrix_eq_Hzeroed (a : Fin N → ℝ) (k : ℕ) :
    kernelMatrix a k = Hzeroed a k := by
  ext i l
  simp only [kernelMatrix, Hzeroed, RestrictionBridge.kernelK_pairRestricted_eq_zeroPair]

theorem Hzeroed_isSymm (a : Fin N → ℝ) (k : ℕ) : (Hzeroed a k).IsSymm := by
  change (Hzeroed a k).transpose = Hzeroed a k
  ext i l
  by_cases hil : i = l
  · subst l
    rfl
  · simp [Hzeroed, hil, Ne.symm hil, zeroPair_comm a i l hil]

theorem Hzeroed_isHermitian (a : Fin N → ℝ) (k : ℕ) : (Hzeroed a k).IsHermitian :=
  Matrix.isHermitian_iff_isSymm.mpr (Hzeroed_isSymm a k)

theorem R_isSymm (a : Fin N → ℝ) (k : ℕ) : (R a k).IsSymm := by
  change (R a k).transpose = R a k
  ext i l
  have hH := congr_fun (congr_fun (Hzeroed_isSymm a k) i) l
  change Hzeroed a k l i = Hzeroed a k i l at hH
  simp only [Matrix.transpose_apply, R_apply, hH]
  ring

theorem R_offDiagonal (a : Fin N → ℝ) (ha : ∀ j, 0 < a j)
    (k : ℕ) (hk : k + 1 ≤ N) (i l : Fin N) (hil : i ≠ l) :
    R a k i l =
      -(kernelK a k * elementaryInt a (k + 1 : ℕ) / rectangleSchur a 3 (k + 1)) *
        a i * a l * rectangleSchur (zeroPair a i l) 4 k := by
  rw [R_apply]
  simp only [b, t, coefficient, Hzeroed, if_neg hil]
  exact offDiagonal_identity a ha i l hil k hk

theorem R_diagonal (a : Fin N → ℝ) (ha : ∀ j, 0 < a j)
    (k : ℕ) (hk : k + 1 ≤ N) (i : Fin N) :
    R a k i i = (kernelK a k / rectangleSchur a 3 (k + 1)) *
      (kernelK (zeroLetter a i) k * rectangleSchur (zeroLetter a i) 3 (k + 1) +
        a i * rectangleSchur (zeroLetter a i) 3 k * kernelK (zeroLetter a i) (k + 1 : ℕ)) := by
  have hz : Hzeroed a k i i = 0 := by simp [Hzeroed]
  rw [R_apply, hz, mul_zero, sub_zero]
  simp only [b, t, coefficient]
  convert diagonal_identity a ha i k hk using 1 <;>
    simp only [Nat.cast_add, Nat.cast_one] <;> ring

theorem R_offDiagonal_nonpos (a : Fin N → ℝ) (ha : ∀ j, 0 < a j)
    (k : ℕ) (hk : k + 1 ≤ N) (i l : Fin N) (hil : i ≠ l) : R a k i l ≤ 0 := by
  rw [R_offDiagonal a ha k hk i l hil]
  have hK := kernelK_nonneg a (fun j => (ha j).le) k (by omega)
  have he : 0 ≤ elementaryInt a (k + 1 : ℕ) :=
    (elementaryInt_pos a ha _ (by omega) (by simp only [Fintype.card_fin]; omega)).le
  have hden := (rectangleSchur_pos a ha 3 (k + 1)).le
  have hfour : 0 ≤ rectangleSchur (zeroPair a i l) 4 k :=
    schurValue_nonneg _ _ (zeroPair_nonneg a (fun j => (ha j).le) i l)
  exact mul_nonpos_of_nonpos_of_nonneg
    (mul_nonpos_of_nonpos_of_nonneg
      (mul_nonpos_of_nonpos_of_nonneg (neg_nonpos.mpr (div_nonneg (mul_nonneg hK he) hden))
        (ha i).le) (ha l).le) hfour

theorem scalarA_eq_rectangles (a : Fin N → ℝ) (ha : ∀ j, 0 ≤ a j)
    (k : ℕ) (hk : k + 1 ≤ N) :
    scalarA a k = kernelK a k * rectangleSchur a 3 (k + 1) -
      elementaryInt a (k + 1 : ℕ) * load a k := by
  rw [scalarA, globalRectangle_eq_rectangleSchur a 2 k (by omega),
    globalRectangle_eq_rectangleSchur a 3 (k + 1) hk,
    ← kernelK_eq_rectangleSchur a ha k (by omega)]

theorem scalarB_eq_rectangles (a : Fin N → ℝ) (ha : ∀ j, 0 ≤ a j)
    (k : ℕ) (hk : k + 1 ≤ N) :
    scalarB a k = rectangleSchur a 3 k * kernelK a (k + 1 : ℕ) -
      elementaryInt a k * load a k := by
  rw [scalarB, globalRectangle_eq_rectangleSchur a 3 k (by omega),
    globalRectangle_eq_rectangleSchur a 2 (k + 1) hk,
    ← kernelK_eq_rectangleSchur a ha (k + 1) hk]

theorem load_zeroLetter_eq_sum (a : Fin N → ℝ) (i : Fin N) (k : ℕ) (hk : k ≤ N) :
    load (zeroLetter a i) k =
      ∑ l ∈ (Finset.univ : Finset (Fin N)).erase i,
        a l ^ 2 * rectangleSchur (zeroPair a i l) 4 k := by
  unfold load
  simp_rw [globalRectangle_eq_rectangleSchur _ 4 k hk]
  change (∑ l, zeroLetter a i l ^ 2 * rectangleSchur (zeroPair a i l) 4 k) = _
  calc
    _ = ∑ l ∈ (Finset.univ : Finset (Fin N)).erase i,
        zeroLetter a i l ^ 2 * rectangleSchur (zeroPair a i l) 4 k := by
      symm
      apply Finset.sum_subset (Finset.erase_subset i Finset.univ)
      intro l hl hnot
      have heq : l = i := by simpa only [Finset.mem_erase, hl, and_true, not_not] using hnot
      subst l
      simp [zeroLetter]
    _ = _ := by
      apply Finset.sum_congr rfl
      intro l hl
      have hli : l ≠ i := (Finset.mem_erase.mp hl).1
      simp [zeroLetter, Function.update, hli]

theorem R_offDiagonal_row_sum (a : Fin N → ℝ) (ha : ∀ j, 0 < a j)
    (k : ℕ) (hk : k + 1 ≤ N) (i : Fin N) :
    (∑ l ∈ (Finset.univ : Finset (Fin N)).erase i, R a k i l * a l) =
      -(kernelK a k * a i / rectangleSchur a 3 (k + 1)) *
        elementaryInt a (k + 1 : ℕ) * load (zeroLetter a i) k := by
  rw [load_zeroLetter_eq_sum a i k (by omega), Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro l hl
  rw [R_offDiagonal a ha k hk i l (Ne.symm (Finset.mem_erase.mp hl).1)]
  ring

theorem R_mulVec_eq_load (a : Fin N → ℝ) (ha : ∀ j, 0 < a j)
    (k : ℕ) (hk : k + 1 ≤ N) (i : Fin N) :
    (R a k *ᵥ a) i = (kernelK a k * a i / rectangleSchur a 3 (k + 1)) *
      (kernelK (zeroLetter a i) k * rectangleSchur (zeroLetter a i) 3 (k + 1) +
        a i * rectangleSchur (zeroLetter a i) 3 k * kernelK (zeroLetter a i) (k + 1 : ℕ) -
        elementaryInt a (k + 1 : ℕ) * load (zeroLetter a i) k) := by
  change (∑ l, R a k i l * a l) = _
  rw [← Finset.sum_erase_add _ _ (Finset.mem_univ i), R_offDiagonal_row_sum a ha k hk i,
    R_diagonal a ha k hk i]
  ring

/-- Equation R-positive-vector before applying the scalar positivity theorem. -/
theorem R_mulVec_eq_scalars (a : Fin N → ℝ) (ha : ∀ j, 0 < a j)
    (k : ℕ) (hk : k + 1 ≤ N) (i : Fin N) :
    (R a k *ᵥ a) i = (kernelK a k * a i / rectangleSchur a 3 (k + 1)) *
      (scalarA (zeroLetter a i) k + a i * scalarB (zeroLetter a i) k) := by
  rw [R_mulVec_eq_load a ha k hk i,
    scalarA_eq_rectangles _ (zeroLetter_nonneg a (fun j => (ha j).le) i) k hk,
    scalarB_eq_rectangles _ (zeroLetter_nonneg a (fun j => (ha j).le) i) k hk]
  have he := elementaryInt_one_deletion a i ((k + 1 : ℕ) : ℤ)
  have hkm : ((k + 1 : ℕ) : ℤ) - 1 = k := by omega
  rw [hkm] at he
  change elementaryInt a (k + 1 : ℕ) = elementaryInt (zeroLetter a i) (k + 1 : ℕ) +
    a i * elementaryInt (zeroLetter a i) k at he
  rw [he]
  ring


theorem kernelK_pos (a : Fin N → ℝ) (ha : ∀ j, 0 < a j)
    (k : ℕ) (hk : k ≤ N) : 0 < kernelK a k := by
  rw [kernelK_eq_rectangleSchur a (fun j => (ha j).le) k hk]
  exact rectangleSchur_pos a ha 2 k

theorem coefficient_pos (a : Fin N → ℝ) (ha : ∀ j, 0 < a j)
    (k : ℕ) (hk : k + 1 ≤ N) : 0 < coefficient a k := by
  exact div_pos
    (elementaryInt_pos a ha _ (by omega) (by simp only [Fintype.card_fin]; omega))
    (rectangleSchur_pos a ha 3 (k + 1))

theorem R_mulVec_pos_of_scalar_bounds (a : Fin N → ℝ) (ha : ∀ j, 0 < a j)
    (k : ℕ) (hk : k + 1 ≤ N)
    (hA : ∀ i, 0 < scalarA (zeroLetter a i) k)
    (hB : ∀ i, 0 ≤ scalarB (zeroLetter a i) k) (i : Fin N) :
    0 < (R a k *ᵥ a) i := by
  rw [R_mulVec_eq_scalars a ha k hk i]
  exact mul_pos
    (div_pos (mul_pos (kernelK_pos a ha k (by omega)) (ha i))
      (rectangleSchur_pos a ha 3 (k + 1)))
    (add_pos_of_pos_of_nonneg (hA i) (mul_nonneg (ha i).le (hB i)))

/-- Once the separately proved scalar inequalities are supplied, the concrete
certificate is positive definite by the manuscript's weighted sum of squares. -/
theorem R_posDef_of_scalar_bounds (a : Fin N → ℝ) (ha : ∀ j, 0 < a j)
    (k : ℕ) (hk : k + 1 ≤ N)
    (hA : ∀ i, 0 < scalarA (zeroLetter a i) k)
    (hB : ∀ i, 0 ≤ scalarB (zeroLetter a i) k) : (R a k).PosDef :=
  matrix_posDef_of_weighted_row_sums (R a k) a (R_isSymm a k) ha
    (R_offDiagonal_nonpos a ha k hk) (R_mulVec_pos_of_scalar_bounds a ha k hk hA hB)

theorem Hzeroed_negative_hyperplane_of_scalar_bounds (a : Fin N → ℝ)
    (ha : ∀ j, 0 < a j) (k : ℕ) (hk : k + 1 ≤ N)
    (hA : ∀ i, 0 < scalarA (zeroLetter a i) k)
    (hB : ∀ i, 0 ≤ scalarB (zeroLetter a i) k)
    (z : Fin N → ℝ) (hz : z ≠ 0) (hbz : b a k ⬝ᵥ z = 0) :
    z ⬝ᵥ (Hzeroed a k *ᵥ z) < 0 :=
  quadraticForm_neg_of_positive_certificate (Hzeroed a k) (R a k)
    (b a k) (t a k) (kernelK a k) (coefficient a k)
    (kernelK_pos a ha k (by omega)) (coefficient_pos a ha k hk).le
    (R_posDef_of_scalar_bounds a ha k hk hA hB) (R_eq_certificate a k) z hz hbz

end CoefficientOne.ConcreteCertificate

