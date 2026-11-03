import CoefficientOne.ElementaryDeletion

/-!
# Determinant identities on actual alphabets

The scalar identities are instantiated using the proved elementary deletion
formulas. For rectangular condensation we use Desnanot–Jacobi on the dual
Jacobi–Trudi matrix of size four. Multiplication by two unipotent bidiagonal
matrices performs the one-letter additions; every corner minor is checked.
This is the dual version of the complete-symmetric row/column operations in
the manuscript (Desnanot–Jacobi: Krattenthaler, Proposition 10, (2.16)).
-/

noncomputable section

namespace CoefficientOne.AlphabetDeterminants

open Finset Matrix RectangleDeterminants ElementaryDeletion

section CommRing

variable {R : Type*} [CommRing R]

def fourToeplitz (a b c d e f g : R) : Matrix (Fin 4) (Fin 4) R :=
  !![d, e, f, g; c, d, e, f; b, c, d, e; a, b, c, d]

def rectangleFour (a b c d e f g : R) : R := (fourToeplitz a b c d e f g).det

def upperBidiagonal (x : R) : Matrix (Fin 4) (Fin 4) R :=
  !![1, x, 0, 0; 0, 1, x, 0; 0, 0, 1, x; 0, 0, 0, 1]

theorem upperBidiagonal_det (x : R) : (upperBidiagonal x).det = 1 := by
  have hu : (upperBidiagonal x).BlockTriangular id := by
    intro i j hij
    fin_cases i <;> fin_cases j <;> simp_all [upperBidiagonal]
  rw [Matrix.det_of_upperTriangular hu]
  simp [upperBidiagonal, Fin.prod_univ_succ]

def transformedFour (a b c d e f g x y : R) : Matrix (Fin 4) (Fin 4) R :=
  upperBidiagonal x * fourToeplitz a b c d e f g * upperBidiagonal y

theorem transformedFour_det (a b c d e f g x y : R) :
    (transformedFour a b c d e f g x y).det = rectangleFour a b c d e f g := by
  simp [transformedFour, Matrix.det_mul, upperBidiagonal_det, rectangleFour]

theorem transformedFour_M11 (a b c d e f g x y : R) :
    (DesnanotJacobi.M11 (transformedFour a b c d e f g x y)).det =
      rectangleThree (b + y * a) (c + y * b) (d + y * c) (e + y * d) (f + y * e) := by
  simp [DesnanotJacobi.M11, transformedFour, fourToeplitz, upperBidiagonal,
    Matrix.det_fin_three, Matrix.mul_apply, Fin.sum_univ_succ, rectangleThree]
  ring

theorem transformedFour_Mkk (a b c d e f g x y : R) :
    (DesnanotJacobi.Mkk (transformedFour a b c d e f g x y)).det =
      rectangleThree (b + x * a) (c + x * b) (d + x * c) (e + x * d) (f + x * e) := by
  simp only [DesnanotJacobi.Mkk, Fin.succAbove_zero, Fin.succAbove_last]
  simp [transformedFour, fourToeplitz, upperBidiagonal,
    Matrix.det_fin_three, Matrix.mul_apply, Fin.sum_univ_succ, rectangleThree]
  ring

theorem transformedFour_M1k (a b c d e f g x y : R) :
    (DesnanotJacobi.M1k (transformedFour a b c d e f g x y)).det =
      rectangleThree a b c d e := by
  simp only [DesnanotJacobi.M1k, Fin.succAbove_zero, Fin.succAbove_last]
  simp [transformedFour, fourToeplitz, upperBidiagonal,
    Matrix.det_fin_three, Matrix.mul_apply, Fin.sum_univ_succ, rectangleThree]
  ring

theorem transformedFour_Mk1 (a b c d e f g x y : R) :
    (DesnanotJacobi.Mk1 (transformedFour a b c d e f g x y)).det =
      rectangleThree (c + (x + y) * b + x * y * a)
        (d + (x + y) * c + x * y * b) (e + (x + y) * d + x * y * c)
        (f + (x + y) * e + x * y * d) (g + (x + y) * f + x * y * e) := by
  simp only [DesnanotJacobi.Mk1, Fin.succAbove_zero, Fin.succAbove_last]
  simp [transformedFour, fourToeplitz, upperBidiagonal,
    Matrix.det_fin_three, Matrix.mul_apply, Fin.sum_univ_succ, rectangleThree]
  ring

theorem transformedFour_Mmid (a b c d e f g x y : R) :
    (DesnanotJacobi.M1k_1k (transformedFour a b c d e f g x y)).det =
      rectangleTwo (c + (x + y) * b + x * y * a)
        (d + (x + y) * c + x * y * b) (e + (x + y) * d + x * y * c) := by
  simp only [DesnanotJacobi.M1k_1k, Fin.succAbove_zero, Fin.succAbove_last]
  simp [transformedFour, fourToeplitz, upperBidiagonal,
    Matrix.det_fin_two, Matrix.mul_apply, Fin.sum_univ_succ, rectangleTwo]
  ring

/-- Dual-JT form of the manuscript's rectangular condensation identity.
The proof is Desnanot–Jacobi on a determinant-preserving transformation,
with all five minors identified above. -/
theorem rectangle_condensation_coefficients (a b c d e f g x y : R) :
    rectangleThree (b + x * a) (c + x * b) (d + x * c) (e + x * d) (f + x * e) *
        rectangleThree (b + y * a) (c + y * b) (d + y * c) (e + y * d) (f + y * e) -
      rectangleThree (c + (x + y) * b + x * y * a)
        (d + (x + y) * c + x * y * b) (e + (x + y) * d + x * y * c)
        (f + (x + y) * e + x * y * d) (g + (x + y) * f + x * y * e) *
        rectangleThree a b c d e =
      rectangleTwo (c + (x + y) * b + x * y * a)
        (d + (x + y) * c + x * y * b) (e + (x + y) * d + x * y * c) *
        rectangleFour a b c d e f g := by
  have h := DesnanotJacobi.desnanot_jacobi (transformedFour a b c d e f g x y)
  rw [transformedFour_det, transformedFour_M11, transformedFour_Mkk,
    transformedFour_M1k, transformedFour_Mk1, transformedFour_Mmid] at h
  linear_combination -h

end CommRing


section Alphabets

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

def zeroLetter (a : ι → ℝ) (i : ι) : ι → ℝ := Function.update a i 0

def zeroPair (a : ι → ℝ) (i l : ι) : ι → ℝ := zeroLetter (zeroLetter a i) l

theorem zeroPair_comm (a : ι → ℝ) (i l : ι) (hil : i ≠ l) :
    zeroPair a i l = zeroPair a l i := Function.update_comm hil 0 0 a

theorem zeroLetter_nonneg (a : ι → ℝ) (ha : ∀ j, 0 ≤ a j) (i : ι) :
    ∀ j, 0 ≤ zeroLetter a i j := by
  intro j
  by_cases hji : j = i
  · subst j
    simp [zeroLetter]
  · simpa [zeroLetter, Function.update, hji] using ha j

theorem zeroPair_nonneg (a : ι → ℝ) (ha : ∀ j, 0 ≤ a j) (i l : ι) :
    ∀ j, 0 ≤ zeroPair a i l j :=
  zeroLetter_nonneg _ (zeroLetter_nonneg a ha i) l

theorem elementaryInt_one_from_pair_left (a : ι → ℝ) (i l : ι)
    (hil : i ≠ l) (d : ℤ) :
    elementaryInt (zeroLetter a i) d = elementaryInt (zeroPair a i l) d +
      a l * elementaryInt (zeroPair a i l) (d - 1) := by
  have h := elementaryInt_one_deletion (Function.update a i 0) l d
  have he : Function.update a i 0 l = a l := by simp [Function.update, Ne.symm hil]
  rw [he] at h
  exact h

theorem elementaryInt_one_from_pair_right (a : ι → ℝ) (i l : ι)
    (hil : i ≠ l) (d : ℤ) :
    elementaryInt (zeroLetter a l) d = elementaryInt (zeroPair a i l) d +
      a i * elementaryInt (zeroPair a i l) (d - 1) := by
  rw [zeroPair_comm a i l hil]
  exact elementaryInt_one_from_pair_left a l i hil.symm d

theorem elementaryInt_from_zeroPair (a : ι → ℝ) (i l : ι)
    (hil : i ≠ l) (d : ℤ) :
    elementaryInt a d = elementaryInt (zeroPair a i l) d +
      (a i + a l) * elementaryInt (zeroPair a i l) (d - 1) +
      a i * a l * elementaryInt (zeroPair a i l) (d - 2) :=
  elementaryInt_two_deletions a i l hil d

def elementaryThree (a : ι → ℝ) (d : ℤ) : ℝ :=
  rectangleThree (elementaryInt a (d - 2)) (elementaryInt a (d - 1))
    (elementaryInt a d) (elementaryInt a (d + 1)) (elementaryInt a (d + 2))

def elementaryFour (a : ι → ℝ) (d : ℤ) : ℝ :=
  rectangleFour (elementaryInt a (d - 3)) (elementaryInt a (d - 2))
    (elementaryInt a (d - 1)) (elementaryInt a d) (elementaryInt a (d + 1))
    (elementaryInt a (d + 2)) (elementaryInt a (d + 3))


/-- The manuscript's elementary two-deletion identity on the actual coefficients. -/
theorem kernelK_two_deletions (a : ι → ℝ) (i l : ι) (hil : i ≠ l) (d : ℤ) :
    kernelK (zeroLetter a i) d * kernelK (zeroLetter a l) d -
      kernelK a d * kernelK (zeroPair a i l) d =
      a i * a l * elementaryInt a (d + 1) * elementaryThree (zeroPair a i l) (d - 1) := by
  let v := elementaryInt (zeroPair a i l)
  have hc := rectangleTwo_twoDeletion (v (d - 3)) (v (d - 2)) (v (d - 1))
    (v d) (v (d + 1)) (a l) (a i)
  dsimp only [v] at hc
  have hI := elementaryInt_one_from_pair_left a i l hil
  have hL := elementaryInt_one_from_pair_right a i l hil
  have hA := elementaryInt_from_zeroPair a i l hil
  simp only [kernelK_eq_rectangleTwo, elementaryThree, hI, hL, hA]
  convert hc using 1 <;> simp only [rectangleTwo, rectangleThree] <;> ring_nf

set_option maxHeartbeats 1000000 in
/-- Rectangular condensation on actual elementary coefficients, obtained from
the determinant-preserving four-by-four transformation above. -/
theorem rectangular_condensation (a : ι → ℝ) (i l : ι) (hil : i ≠ l) (d : ℤ) :
    elementaryThree (zeroLetter a i) d * elementaryThree (zeroLetter a l) d -
      elementaryThree a (d + 1) * elementaryThree (zeroPair a i l) (d - 1) =
      kernelK a d * elementaryFour (zeroPair a i l) d := by
  let v := elementaryInt (zeroPair a i l)
  have hc := rectangle_condensation_coefficients
    (v (d - 3)) (v (d - 2)) (v (d - 1)) (v d)
    (v (d + 1)) (v (d + 2)) (v (d + 3)) (a l) (a i)
  dsimp only [v] at hc
  have hI := elementaryInt_one_from_pair_left a i l hil
  have hL := elementaryInt_one_from_pair_right a i l hil
  have hA := elementaryInt_from_zeroPair a i l hil
  simp only [kernelK_eq_rectangleTwo, elementaryThree, elementaryFour, hI, hL, hA]
  convert hc using 1 <;> ring_nf

set_option maxHeartbeats 1000000 in
theorem adjacent_first (a : ι → ℝ) (i : ι) (d : ℤ) :
    kernelK a d * elementaryThree (zeroLetter a i) (d + 1) =
      kernelK (zeroLetter a i) d * elementaryThree a (d + 1) -
        a i * kernelK a (d + 1) * elementaryThree (zeroLetter a i) d := by
  let v := elementaryInt (zeroLetter a i)
  have hc := rectangle_adjacent_first (v (d - 2)) (v (d - 1)) (v d)
    (v (d + 1)) (v (d + 2)) (v (d + 3)) (a i)
  dsimp only [v] at hc
  have hA := elementaryInt_one_deletion a i
  change ∀ z, elementaryInt a z = elementaryInt (zeroLetter a i) z +
    a i * elementaryInt (zeroLetter a i) (z - 1) at hA
  simp only [kernelK_eq_rectangleTwo, elementaryThree, hA]
  convert hc using 1 <;> simp only [rectangleTwo, rectangleThree] <;> ring_nf

theorem adjacent_second (a : ι → ℝ) (i : ι) (d : ℤ) :
    kernelK (zeroLetter a i) d * kernelK a (d + 1) -
      kernelK a d * kernelK (zeroLetter a i) (d + 1) =
      a i * elementaryInt a (d + 1) * elementaryThree (zeroLetter a i) d := by
  let v := elementaryInt (zeroLetter a i)
  have hc := rectangle_adjacent_second (v (d - 2)) (v (d - 1)) (v d)
    (v (d + 1)) (v (d + 2)) (a i)
  dsimp only [v] at hc
  have hA := elementaryInt_one_deletion a i
  change ∀ z, elementaryInt a z = elementaryInt (zeroLetter a i) z +
    a i * elementaryInt (zeroLetter a i) (z - 1) at hA
  simp only [kernelK_eq_rectangleTwo, elementaryThree, hA]
  convert hc using 1 <;> simp only [rectangleTwo, rectangleThree] <;> ring_nf

theorem diagonal_numerator (a : ι → ℝ) (i : ι) (d : ℤ) :
    kernelK (zeroLetter a i) d ^ 2 * elementaryThree a (d + 1) -
      a i ^ 2 * elementaryInt a (d + 1) * elementaryThree (zeroLetter a i) d ^ 2 =
      kernelK a d * (kernelK (zeroLetter a i) d * elementaryThree (zeroLetter a i) (d + 1) +
        a i * elementaryThree (zeroLetter a i) d * kernelK (zeroLetter a i) (d + 1)) :=
  diagonal_numerator_of_adjacent _ _ _ _ _ _ _ _ _ (adjacent_first a i d) (adjacent_second a i d)

/-- The off-diagonal numerator before division by the positive three-square value. -/
theorem offDiagonal_numerator (a : ι → ℝ) (i l : ι) (hil : i ≠ l) (d : ℤ) :
    (kernelK (zeroLetter a i) d * kernelK (zeroLetter a l) d -
        kernelK a d * kernelK (zeroPair a i l) d) * elementaryThree a (d + 1) -
      elementaryInt a (d + 1) *
        (a i * elementaryThree (zeroLetter a i) d) *
        (a l * elementaryThree (zeroLetter a l) d) =
      -kernelK a d * elementaryInt a (d + 1) * a i * a l *
        elementaryFour (zeroPair a i l) d := by
  rw [kernelK_two_deletions a i l hil d]
  have hc := rectangular_condensation a i l hil d
  linear_combination -(a i * a l * elementaryInt a (d + 1)) * hc


/-- The four consecutive rows used in the manuscript's adjacent-minor proof. -/
def elementaryRow (a : ι → ℝ) (r : ℤ) (j : ℕ) : Fin 3 → ℝ :=
  fun c => elementaryInt a (r - (j : ℤ) + (c.val : ℤ))

theorem elementary_fourRows_alternating (a : ι → ℝ) (r : ℤ) (q : Fin 3) :
    elementaryRow a r 0 q * rowMinorThree (elementaryRow a r 1) (elementaryRow a r 2) (elementaryRow a r 3) -
      elementaryRow a r 1 q * rowMinorThree (elementaryRow a r 0) (elementaryRow a r 2) (elementaryRow a r 3) +
      elementaryRow a r 2 q * rowMinorThree (elementaryRow a r 0) (elementaryRow a r 1) (elementaryRow a r 3) -
      elementaryRow a r 3 q * rowMinorThree (elementaryRow a r 0) (elementaryRow a r 1) (elementaryRow a r 2) = 0 :=
  fourRows_alternating _ _ _ _ q

theorem elementary_adjacent_minors_first (a : ι → ℝ) (r : ℤ) :
    rowMinorTwo (elementaryRow a r 1) (elementaryRow a r 2) *
        rowMinorThree (elementaryRow a r 0) (elementaryRow a r 1) (elementaryRow a r 3) -
      rowMinorTwo (elementaryRow a r 0) (elementaryRow a r 1) *
        rowMinorThree (elementaryRow a r 1) (elementaryRow a r 2) (elementaryRow a r 3) =
      rowMinorTwo (elementaryRow a r 1) (elementaryRow a r 3) *
        rowMinorThree (elementaryRow a r 0) (elementaryRow a r 1) (elementaryRow a r 2) :=
  adjacent_minors_first _ _ _ _

theorem elementary_adjacent_minors_second (a : ι → ℝ) (r : ℤ) :
    rowMinorTwo (elementaryRow a r 1) (elementaryRow a r 2) *
        rowMinorThree (elementaryRow a r 0) (elementaryRow a r 2) (elementaryRow a r 3) -
      rowMinorTwo (elementaryRow a r 0) (elementaryRow a r 2) *
        rowMinorThree (elementaryRow a r 1) (elementaryRow a r 2) (elementaryRow a r 3) =
      rowMinorTwo (elementaryRow a r 2) (elementaryRow a r 3) *
        rowMinorThree (elementaryRow a r 0) (elementaryRow a r 1) (elementaryRow a r 2) :=
  adjacent_minors_second _ _ _ _

theorem elementaryRow_one_deletion (a : ι → ℝ) (i : ι) (r : ℤ) (j : ℕ) :
    elementaryRow a r j = fun c => elementaryRow (zeroLetter a i) r j c +
      a i * elementaryRow (zeroLetter a i) r (j + 1) c := by
  funext c
  unfold elementaryRow
  rw [elementaryInt_one_deletion a i]
  change elementaryInt (zeroLetter a i) (r - (j : ℤ) + (c.val : ℤ)) +
      a i * elementaryInt (zeroLetter a i) (r - (j : ℤ) + (c.val : ℤ) - 1) = _
  congr 2
  congr 1
  push_cast
  ring

theorem elementary_threeRows_oneLetter (a : ι → ℝ) (i : ι) (r : ℤ) :
    rowMinorThree (elementaryRow a r 0) (elementaryRow a r 1) (elementaryRow a r 2) =
      rowMinorThree (elementaryRow (zeroLetter a i) r 0) (elementaryRow (zeroLetter a i) r 1)
        (elementaryRow (zeroLetter a i) r 2) +
      a i * rowMinorThree (elementaryRow (zeroLetter a i) r 0) (elementaryRow (zeroLetter a i) r 1)
        (elementaryRow (zeroLetter a i) r 3) +
      a i ^ 2 * rowMinorThree (elementaryRow (zeroLetter a i) r 0) (elementaryRow (zeroLetter a i) r 2)
        (elementaryRow (zeroLetter a i) r 3) +
      a i ^ 3 * rowMinorThree (elementaryRow (zeroLetter a i) r 1) (elementaryRow (zeroLetter a i) r 2)
        (elementaryRow (zeroLetter a i) r 3) := by
  rw [elementaryRow_one_deletion a i r 0, elementaryRow_one_deletion a i r 1,
    elementaryRow_one_deletion a i r 2]
  exact rowMinorThree_oneLetter _ _ _ _ (a i)

end Alphabets



section FinAlphabet

variable {N : ℕ}

theorem elementaryThree_eq_elementaryDet (a : Fin N → ℝ) (k : ℕ) :
    elementaryThree a k = elementaryDet a 3 k := by
  have hm : toeplitz (elementaryInt a) k 3 =
      !![elementaryInt a k, elementaryInt a (k + 1), elementaryInt a (k + 2);
         elementaryInt a (k - 1), elementaryInt a k, elementaryInt a (k + 1);
         elementaryInt a (k - 2), elementaryInt a (k - 1), elementaryInt a k] := by
    ext i j
    fin_cases i <;> fin_cases j <;> simp [toeplitz] <;> congr 1 <;> omega
  rw [elementaryDet, hm, ← rectangleThree_eq_matrix_det]
  rfl

theorem elementaryFour_eq_elementaryDet (a : Fin N → ℝ) (k : ℕ) :
    elementaryFour a k = elementaryDet a 4 k := by
  have hm : toeplitz (elementaryInt a) k 4 =
      fourToeplitz (elementaryInt a (k - 3)) (elementaryInt a (k - 2))
        (elementaryInt a (k - 1)) (elementaryInt a k) (elementaryInt a (k + 1))
        (elementaryInt a (k + 2)) (elementaryInt a (k + 3)) := by
    ext i j
    fin_cases i <;> fin_cases j <;> simp [toeplitz, fourToeplitz] <;> congr 1 <;> omega
  rw [elementaryDet, hm]
  rfl

theorem elementaryThree_eq_rectangleSchur (a : Fin N → ℝ) (ha : ∀ i, 0 ≤ a i)
    (k : ℕ) (hk : k ≤ N) : elementaryThree a k = rectangleSchur a 3 k := by
  rw [elementaryThree_eq_elementaryDet,
    RectangleContinuity.rectangleSchur_eq_elementaryDet_of_nonneg a ha 3 k hk]

theorem elementaryFour_eq_rectangleSchur (a : Fin N → ℝ) (ha : ∀ i, 0 ≤ a i)
    (k : ℕ) (hk : k ≤ N) : elementaryFour a k = rectangleSchur a 4 k := by
  rw [elementaryFour_eq_elementaryDet,
    RectangleContinuity.rectangleSchur_eq_elementaryDet_of_nonneg a ha 4 k hk]


/-- The actual off-diagonal certificate identity, with the strictly positive
denominator justified by the tableau expansion. The integer parameter in the
manuscript is r=k+1. No relation between zeroed and shortened alphabets is assumed. -/
theorem offDiagonal_identity (a : Fin N → ℝ) (ha : ∀ j, 0 < a j)
    (i l : Fin N) (hil : i ≠ l) (k : ℕ) (hk : k + 1 ≤ N) :
    kernelK (zeroLetter a i) k * kernelK (zeroLetter a l) k -
      kernelK a k * kernelK (zeroPair a i l) k -
      (elementaryInt a (k + 1) / rectangleSchur a 3 (k + 1)) *
        (a i * rectangleSchur (zeroLetter a i) 3 k) *
        (a l * rectangleSchur (zeroLetter a l) 3 k) =
      -(kernelK a k * elementaryInt a (k + 1) / rectangleSchur a 3 (k + 1)) *
        a i * a l * rectangleSchur (zeroPair a i l) 4 k := by
  have ha0 : ∀ j, 0 ≤ a j := fun j => (ha j).le
  have hi0 := zeroLetter_nonneg a ha0 i
  have hl0 := zeroLetter_nonneg a ha0 l
  have hp0 := zeroPair_nonneg a ha0 i l
  have hnum := offDiagonal_numerator a i l hil (k : ℤ)
  have hkp : (k : ℤ) + 1 = ((k + 1 : ℕ) : ℤ) := by omega
  rw [hkp, elementaryThree_eq_rectangleSchur a ha0 (k + 1) hk,
    elementaryThree_eq_rectangleSchur _ hi0 k (by omega),
    elementaryThree_eq_rectangleSchur _ hl0 k (by omega),
    elementaryFour_eq_rectangleSchur _ hp0 k (by omega)] at hnum
  have hden : rectangleSchur a 3 (k + 1) ≠ 0 :=
    ne_of_gt (rectangleSchur_pos a ha 3 (k + 1))
  field_simp [hden]
  simp only [Nat.cast_add, Nat.cast_one] at hnum
  nlinarith [hnum]

/-- The actual diagonal numerator identity in tableau-Schur notation. -/
theorem diagonal_numerator_schur (a : Fin N → ℝ) (ha : ∀ j, 0 ≤ a j)
    (i : Fin N) (k : ℕ) (hk : k + 1 ≤ N) :
    kernelK (zeroLetter a i) k ^ 2 * rectangleSchur a 3 (k + 1) -
      a i ^ 2 * elementaryInt a (k + 1) * rectangleSchur (zeroLetter a i) 3 k ^ 2 =
      kernelK a k * (kernelK (zeroLetter a i) k * rectangleSchur (zeroLetter a i) 3 (k + 1) +
        a i * rectangleSchur (zeroLetter a i) 3 k * kernelK (zeroLetter a i) (k + 1)) := by
  have hi0 := zeroLetter_nonneg a ha i
  have hnum := diagonal_numerator a i (k : ℤ)
  have hkp : (k : ℤ) + 1 = ((k + 1 : ℕ) : ℤ) := by omega
  rw [hkp, elementaryThree_eq_rectangleSchur a ha (k + 1) hk,
    elementaryThree_eq_rectangleSchur _ hi0 k (by omega),
    elementaryThree_eq_rectangleSchur _ hi0 (k + 1) hk] at hnum
  exact hnum

theorem diagonal_identity (a : Fin N → ℝ) (ha : ∀ j, 0 < a j)
    (i : Fin N) (k : ℕ) (hk : k + 1 ≤ N) :
    kernelK (zeroLetter a i) k ^ 2 -
      (elementaryInt a (k + 1) / rectangleSchur a 3 (k + 1)) *
        (a i * rectangleSchur (zeroLetter a i) 3 k) ^ 2 =
      (kernelK a k / rectangleSchur a 3 (k + 1)) *
        (kernelK (zeroLetter a i) k * rectangleSchur (zeroLetter a i) 3 (k + 1) +
          a i * rectangleSchur (zeroLetter a i) 3 k * kernelK (zeroLetter a i) (k + 1)) := by
  have hnum := diagonal_numerator_schur a (fun j => (ha j).le) i k hk
  have hden : rectangleSchur a 3 (k + 1) ≠ 0 :=
    ne_of_gt (rectangleSchur_pos a ha 3 (k + 1))
  field_simp [hden]
  nlinarith [hnum]

end FinAlphabet


end CoefficientOne.AlphabetDeterminants

