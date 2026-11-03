import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
import Mathlib.Tactic.Ring
import Mathlib.Tactic.FinCases

/-!
# Universal determinant identities for the coefficient-one certificate

These polynomial identities hold over an arbitrary commutative ring.
They assume neither Schur positivity nor the matrix or covariance conclusion.
The two-square and three-square Toeplitz determinants are linked explicitly
to Matrix.det. Alphabet applications substitute consecutive elementary
coefficients for the scalar variables.
-/

namespace CoefficientOne

section CommRing

variable {R : Type*} [CommRing R]

/-- The polynomial expansion of a two-by-two determinant. -/
def detTwo (a b c d : R) : R := a * d - b * c

/-- The polynomial expansion of a three-by-three determinant. -/
def detThree (a b c d e f g h i : R) : R :=
  a * (e * i - f * h) - b * (d * i - f * g) + c * (d * h - e * g)

theorem detTwo_eq_matrix_det (a b c d : R) :
    detTwo a b c d = Matrix.det !![a, b; c, d] := by
  simp [detTwo]

theorem detThree_eq_matrix_det (a b c d e f g h i : R) :
    detThree a b c d e f g h i = Matrix.det !![a, b, c; d, e, f; g, h, i] := by
  simp [Matrix.det_fin_three, detThree]
  ring

/-- The adjacent two-square elementary determinant, with central coefficient b. -/
def rectangleTwo (a b c : R) : R := b ^ 2 - a * c

/-- The adjacent three-square elementary determinant, with central coefficient c. -/
def rectangleThree (a b c d e : R) : R :=
  c ^ 3 - 2 * b * c * d + a * d ^ 2 + e * b ^ 2 - e * c * a

theorem rectangleTwo_eq_matrix_det (a b c : R) :
    rectangleTwo a b c = Matrix.det !![b, c; a, b] := by
  simp [rectangleTwo, pow_two, mul_comm]

theorem rectangleThree_eq_matrix_det (a b c d e : R) :
    rectangleThree a b c d e = Matrix.det !![c, d, e; b, c, d; a, b, c] := by
  simp [Matrix.det_fin_three, rectangleThree]
  ring

/-- The coefficient of xy in the elementary two-deletion identity. -/
theorem twoDeletion_coefficient_constant (a b c d e : R) :
    (d * c - e * b) ^ 2 - (d ^ 2 - e * c) * (c ^ 2 - e * a) =
      e * rectangleThree a b c d e := by
  unfold rectangleThree
  ring

/-- The coefficient of xy(x+y) in the elementary two-deletion identity. -/
theorem twoDeletion_coefficient_linear (a b c d e : R) :
    (d * c - e * b) * (c ^ 2 - d * b) -
        (d ^ 2 - e * c) * (c * b - d * a) =
      d * rectangleThree a b c d e := by
  unfold rectangleThree
  ring

/-- The coefficient of (xy)^2 in the elementary two-deletion identity. -/
theorem twoDeletion_coefficient_quadratic (a b c d e : R) :
    (c ^ 2 - d * b) ^ 2 - (d ^ 2 - e * c) * (b ^ 2 - c * a) =
      c * rectangleThree a b c d e := by
  unfold rectangleThree
  ring

/-- Adding one alphabet letter to a two-square elementary determinant. -/
theorem rectangleTwo_oneLetter (b c d e x : R) :
    rectangleTwo (c + x * b) (d + x * c) (e + x * d) =
      rectangleTwo c d e + x * (d * c - e * b) +
        x ^ 2 * rectangleTwo b c d := by
  unfold rectangleTwo
  ring

/-- Adding two alphabet letters, with every coefficient displayed. -/
theorem rectangleTwo_twoLetters (a b c d e x y : R) :
    rectangleTwo
        (c + (x + y) * b + x * y * a)
        (d + (x + y) * c + x * y * b)
        (e + (x + y) * d + x * y * c) =
      rectangleTwo c d e + (x + y) * (d * c - e * b) +
        (x + y) ^ 2 * rectangleTwo b c d +
        x * y * (2 * d * b - c ^ 2 - e * a) +
        (x + y) * (x * y) * (c * b - d * a) +
        (x * y) ^ 2 * rectangleTwo a b c := by
  unfold rectangleTwo
  ring

/--
The complete two-deletion identity. The alphabet application substitutes
(a,b,c,d,e) = (e_(j-3),e_(j-2),e_(j-1),e_j,e_(j+1)).
The identity remains valid when any coefficient is zero.
-/
theorem rectangleTwo_twoDeletion (a b c d e x y : R) :
    rectangleTwo (c + x * b) (d + x * c) (e + x * d) *
        rectangleTwo (c + y * b) (d + y * c) (e + y * d) -
      rectangleTwo c d e *
        rectangleTwo
          (c + (x + y) * b + x * y * a)
          (d + (x + y) * c + x * y * b)
          (e + (x + y) * d + x * y * c) =
      x * y * (e + (x + y) * d + x * y * c) *
        rectangleThree a b c d e := by
  unfold rectangleTwo rectangleThree
  ring

/-- The first-two-column minor of two three-dimensional row vectors. -/
def rowMinorTwo (u v : Fin 3 → R) : R :=
  detTwo (u 0) (u 1) (v 0) (v 1)

/-- The determinant of three three-dimensional row vectors. -/
def rowMinorThree (u v w : Fin 3 → R) : R :=
  detThree (u 0) (u 1) (u 2) (v 0) (v 1) (v 2) (w 0) (w 1) (w 2)

theorem rowMinorTwo_eq_matrix_det (u v : Fin 3 → R) :
    rowMinorTwo u v = Matrix.det !![u 0, u 1; v 0, v 1] :=
  detTwo_eq_matrix_det _ _ _ _

theorem rowMinorThree_eq_matrix_det (u v w : Fin 3 → R) :
    rowMinorThree u v w = Matrix.det !![u 0, u 1, u 2;
      v 0, v 1, v 2; w 0, w 1, w 2] :=
  detThree_eq_matrix_det _ _ _ _ _ _ _ _ _

/-- The alternating-minor relation for four rows, proved in each coordinate. -/
theorem fourRows_alternating (v₀ v₁ v₂ v₃ : Fin 3 → R) (i : Fin 3) :
    v₀ i * rowMinorThree v₁ v₂ v₃ -
        v₁ i * rowMinorThree v₀ v₂ v₃ +
        v₂ i * rowMinorThree v₀ v₁ v₃ -
        v₃ i * rowMinorThree v₀ v₁ v₂ = 0 := by
  fin_cases i <;> simp only [rowMinorThree, detThree, Fin.reduceFinMk] <;> ring

/-- The first adjacent relation between two-row and three-row minors. -/
theorem adjacent_minors_first (v₀ v₁ v₂ v₃ : Fin 3 → R) :
    rowMinorTwo v₁ v₂ * rowMinorThree v₀ v₁ v₃ -
        rowMinorTwo v₀ v₁ * rowMinorThree v₁ v₂ v₃ =
      rowMinorTwo v₁ v₃ * rowMinorThree v₀ v₁ v₂ := by
  unfold rowMinorTwo rowMinorThree detTwo detThree
  ring

/-- The second adjacent relation between two-row and three-row minors. -/
theorem adjacent_minors_second (v₀ v₁ v₂ v₃ : Fin 3 → R) :
    rowMinorTwo v₁ v₂ * rowMinorThree v₀ v₂ v₃ -
        rowMinorTwo v₀ v₂ * rowMinorThree v₁ v₂ v₃ =
      rowMinorTwo v₂ v₃ * rowMinorThree v₀ v₁ v₂ := by
  unfold rowMinorTwo rowMinorThree detTwo detThree
  ring

/-- The adjacent-row expansion when adding one alphabet letter. -/
theorem rowMinorThree_oneLetter (v₀ v₁ v₂ v₃ : Fin 3 → R) (x : R) :
    rowMinorThree (fun i => v₀ i + x * v₁ i)
        (fun i => v₁ i + x * v₂ i) (fun i => v₂ i + x * v₃ i) =
      rowMinorThree v₀ v₁ v₂ + x * rowMinorThree v₀ v₁ v₃ +
        x ^ 2 * rowMinorThree v₀ v₂ v₃ +
        x ^ 3 * rowMinorThree v₁ v₂ v₃ := by
  unfold rowMinorThree detThree
  ring

/-- The two-row version of the same expansion. -/
theorem rowMinorTwo_oneLetter (v₀ v₁ v₂ : Fin 3 → R) (x : R) :
    rowMinorTwo (fun i => v₀ i + x * v₁ i) (fun i => v₁ i + x * v₂ i) =
      rowMinorTwo v₀ v₁ + x * rowMinorTwo v₀ v₂ +
        x ^ 2 * rowMinorTwo v₁ v₂ := by
  unfold rowMinorTwo detTwo
  ring

/--
The first adjacent identity specialized to consecutive elementary
coefficients. Here a,...,f stand for e_(r-3),...,e_(r+2).
-/
theorem rectangle_adjacent_first (a b c d e f x : R) :
    rectangleTwo (b + x * a) (c + x * b) (d + x * c) *
        rectangleThree b c d e f =
      rectangleTwo b c d *
        rectangleThree (b + x * a) (c + x * b) (d + x * c)
          (e + x * d) (f + x * e) -
        x * rectangleTwo (c + x * b) (d + x * c) (e + x * d) *
          rectangleThree a b c d e := by
  unfold rectangleTwo rectangleThree
  ring

/-- The second adjacent identity in the diagonal-entry calculation. -/
theorem rectangle_adjacent_second (a b c d e x : R) :
    rectangleTwo b c d *
        rectangleTwo (c + x * b) (d + x * c) (e + x * d) -
      rectangleTwo (b + x * a) (c + x * b) (d + x * c) *
        rectangleTwo c d e =
      x * (d + x * c) * rectangleThree a b c d e := by
  unfold rectangleTwo rectangleThree
  ring

/--
Combining the two adjacent identities gives the numerator identity for a
diagonal entry of the positive matrix certificate. This step is independent
of determinants and does not divide by any scalar.
-/
theorem diagonal_numerator_of_adjacent
    (c C T U f g x W K : R)
    (hfirst : f * U = c * W - x * K * T)
    (hsecond : c * K - f * C = x * g * T) :
    c ^ 2 * W - x ^ 2 * g * T ^ 2 = f * (c * U + x * T * C) := by
  calc
    c ^ 2 * W - x ^ 2 * g * T ^ 2 =
        c * (c * W - x * K * T) +
          x * T * ((c * K - f * C) - x * g * T) + x * f * C * T := by ring
    _ = c * (f * U) + x * T * 0 + x * f * C * T := by
      rw [← hfirst, hsecond, sub_self]
    _ = f * (c * U + x * T * C) := by ring

/-- The diagonal numerator identity with every elementary coefficient shown. -/
theorem rectangle_diagonal_numerator (a b c d e f x : R) :
    (rectangleTwo b c d) ^ 2 *
        rectangleThree (b + x * a) (c + x * b) (d + x * c)
          (e + x * d) (f + x * e) -
      x ^ 2 * (d + x * c) * (rectangleThree a b c d e) ^ 2 =
      rectangleTwo (b + x * a) (c + x * b) (d + x * c) *
        (rectangleTwo b c d * rectangleThree b c d e f +
          x * rectangleThree a b c d e * rectangleTwo c d e) := by
  exact diagonal_numerator_of_adjacent
    (rectangleTwo b c d) (rectangleTwo c d e)
    (rectangleThree a b c d e) (rectangleThree b c d e f)
    (rectangleTwo (b + x * a) (c + x * b) (d + x * c))
    (d + x * c) x
    (rectangleThree (b + x * a) (c + x * b) (d + x * c)
      (e + x * d) (f + x * e))
    (rectangleTwo (c + x * b) (d + x * c) (e + x * d))
    (rectangle_adjacent_first a b c d e f x)
    (rectangle_adjacent_second a b c d e x)

end CommRing

end CoefficientOne

