import Mathlib

/-!
# Weighted square decomposition and positivity

This file follows equation `eq:R-squares` and the following paragraph of
`paper/main.tex`. The proof expands each square,
uses symmetry to identify the two diagonal sums, and then proves positivity
term by term. There is no appeal to a stronger matrix-positivity criterion.

The first identity uses one half of the sum over all ordered pairs, so that it
works on an arbitrary finite type. The second identity proves that this equals
the manuscript's sum over `i < j` whenever the index type has a linear order.

The argument uses finite sums and real quadratic forms on a finite index type.
-/

open scoped BigOperators
open Matrix

namespace CoefficientOne

noncomputable section

variable {ι : Type*}

/-- The edge contribution in the weighted square decomposition. -/
def weightedEdgeSquare (R : Matrix ι ι ℝ) (a z : ι → ℝ) (i j : ι) : ℝ :=
  (-R i j) * a i * a j * (z i / a i - z j / a j) ^ 2

/-- Expansion of a single square; nonzero weights are sufficient. -/
theorem weightedEdgeSquare_expand (R : Matrix ι ι ℝ) (a z : ι → ℝ)
    (ha : ∀ i, a i ≠ 0) (i j : ι) :
    weightedEdgeSquare R a z i j =
      -(R i j * a j / a i * z i ^ 2) -
        (R i j * a i / a j * z j ^ 2) +
        2 * (z i * (R i j * z j)) := by
  unfold weightedEdgeSquare
  field_simp [ha i, ha j]
  ring

/-- Equation `eq:R-squares`, written as half the sum over ordered pairs.
The identity itself does not require any positivity assumption. -/
theorem quadraticForm_eq_weighted_squares [Fintype ι] (R : Matrix ι ι ℝ) (a z : ι → ℝ)
    (hR : R.IsSymm) (ha : ∀ i, a i ≠ 0) :
    z ⬝ᵥ (R *ᵥ z) =
      (∑ i, ∑ j, weightedEdgeSquare R a z i j) / 2 +
        ∑ i, (R *ᵥ a) i / a i * z i ^ 2 := by
  have hfirst :
      (∑ i, ∑ j, R i j * a j / a i * z i ^ 2) =
        ∑ i, (R *ᵥ a) i / a i * z i ^ 2 := by
    simp only [Matrix.mulVec, dotProduct, Finset.sum_div, Finset.sum_mul]
  have hsecond :
      (∑ i, ∑ j, R i j * a i / a j * z j ^ 2) =
        ∑ i, (R *ᵥ a) i / a i * z i ^ 2 := by
    calc
      _ = ∑ i, ∑ j, R j i * a j / a i * z i ^ 2 := Finset.sum_comm
      _ = ∑ i, ∑ j, R i j * a j / a i * z i ^ 2 := by
        apply Finset.sum_congr rfl
        intro i hi
        apply Finset.sum_congr rfl
        intro j hj
        rw [hR.apply i j]
      _ = _ := hfirst
  have hcross :
      (∑ i, ∑ j, z i * (R i j * z j)) = z ⬝ᵥ (R *ᵥ z) := by
    simp only [dotProduct, Matrix.mulVec, Finset.mul_sum]
  have hexpansion :
      (∑ i, ∑ j, weightedEdgeSquare R a z i j) =
        -(∑ i, ∑ j, R i j * a j / a i * z i ^ 2) -
          (∑ i, ∑ j, R i j * a i / a j * z j ^ 2) +
          2 * (∑ i, ∑ j, z i * (R i j * z j)) := by
    simp_rw [weightedEdgeSquare_expand R a z ha]
    simp only [Finset.sum_add_distrib, Finset.sum_sub_distrib,
      Finset.sum_neg_distrib, ← Finset.mul_sum]
  rw [hfirst, hsecond, hcross] at hexpansion
  linarith

/-- Symmetry of the square contribution. -/
theorem weightedEdgeSquare_symm (R : Matrix ι ι ℝ) (a z : ι → ℝ)
    (hR : R.IsSymm) (i j : ι) :
    weightedEdgeSquare R a z i j = weightedEdgeSquare R a z j i := by
  unfold weightedEdgeSquare
  rw [hR.apply i j]
  ring

@[simp]
theorem weightedEdgeSquare_self (R : Matrix ι ι ℝ) (a z : ι → ℝ) (i : ι) :
    weightedEdgeSquare R a z i i = 0 := by
  simp [weightedEdgeSquare]

/-- Passing from ordered pairs to `i < j` counts each nondiagonal pair twice.
This is a finite-sum identity, not an extra mathematical assumption. -/
theorem sum_symmetric_eq_two_sum_lt [Fintype ι] [LinearOrder ι]
    (f : ι → ι → ℝ) (hsymm : ∀ i j, f i j = f j i)
    (hdiag : ∀ i, f i i = 0) :
    (∑ i, ∑ j, f i j) =
      2 * (∑ i, ∑ j, if i < j then f i j else 0) := by
  have hsplit (i j : ι) :
      f i j = (if i < j then f i j else 0) +
        (if j < i then f j i else 0) := by
    rcases lt_trichotomy i j with hij | hij | hji
    · simp [hij, not_lt.mpr (le_of_lt hij)]
    · subst j
      simp [hdiag]
    · simp [hji, not_lt.mpr (le_of_lt hji), hsymm i j]
  have hswap :
      (∑ i, ∑ j, if j < i then f j i else 0) =
        ∑ i, ∑ j, if i < j then f i j else 0 := Finset.sum_comm
  calc
    (∑ i, ∑ j, f i j) =
        (∑ i, ∑ j, if i < j then f i j else 0) +
          (∑ i, ∑ j, if j < i then f j i else 0) := by
      calc
        _ = ∑ i, ∑ j, ((if i < j then f i j else 0) +
            (if j < i then f j i else 0)) := by
          apply Finset.sum_congr rfl
          intro i hi
          apply Finset.sum_congr rfl
          intro j hj
          exact hsplit i j
        _ = _ := by simp only [Finset.sum_add_distrib]
    _ = _ := by rw [hswap]; ring

/-- Exactly the `i < j` version of equation `eq:R-squares`. -/
theorem quadraticForm_eq_weighted_squares_lt [Fintype ι] [LinearOrder ι]
    (R : Matrix ι ι ℝ) (a z : ι → ℝ)
    (hR : R.IsSymm) (ha : ∀ i, a i ≠ 0) :
    z ⬝ᵥ (R *ᵥ z) =
      (∑ i, ∑ j, if i < j then weightedEdgeSquare R a z i j else 0) +
        ∑ i, (R *ᵥ a) i / a i * z i ^ 2 := by
  have h := quadraticForm_eq_weighted_squares R a z hR ha
  rw [sum_symmetric_eq_two_sum_lt (weightedEdgeSquare R a z)
    (weightedEdgeSquare_symm R a z hR) (weightedEdgeSquare_self R a z)] at h
  linarith

/-- Off-diagonal nonpositivity and positive weights make every edge term
nonnegative. The diagonal term vanishes independently of the sign of `R i i`. -/
theorem weightedEdgeSquare_nonneg (R : Matrix ι ι ℝ) (a z : ι → ℝ)
    (ha : ∀ i, 0 < a i) (hoff : ∀ i j, i ≠ j → R i j ≤ 0) (i j : ι) :
    0 ≤ weightedEdgeSquare R a z i j := by
  by_cases hij : i = j
  · subst j
    simp
  · exact mul_nonneg
      (mul_nonneg (mul_nonneg (neg_nonneg.mpr (hoff i j hij)) (ha i).le) (ha j).le)
      (sq_nonneg _)

/-- The final sum of equation `eq:R-squares` is strictly positive at every
nonzero vector when `a` and `R * a` are pointwise positive. -/
theorem weighted_row_sum_pos [Fintype ι] (R : Matrix ι ι ℝ) (a z : ι → ℝ)
    (ha : ∀ i, 0 < a i) (hRa : ∀ i, 0 < (R *ᵥ a) i) (hz : z ≠ 0) :
    0 < ∑ i, (R *ᵥ a) i / a i * z i ^ 2 := by
  apply Finset.sum_pos'
  · intro i hi
    exact mul_nonneg (div_pos (hRa i) (ha i)).le (sq_nonneg _)
  · have hexists : ∃ i, z i ≠ 0 := by
      by_contra! hzero
      apply hz
      funext i
      exact hzero i
    obtain ⟨i, hi⟩ := hexists
    exact ⟨i, Finset.mem_univ i,
      mul_pos (div_pos (hRa i) (ha i)) (sq_pos_of_ne_zero hi)⟩

/-- Strict positivity proved by the manuscript's sum-of-squares argument. -/
theorem quadraticForm_pos_of_weighted_row_sums [Fintype ι] (R : Matrix ι ι ℝ) (a z : ι → ℝ)
    (hR : R.IsSymm) (ha : ∀ i, 0 < a i)
    (hoff : ∀ i j, i ≠ j → R i j ≤ 0)
    (hRa : ∀ i, 0 < (R *ᵥ a) i) (hz : z ≠ 0) :
    0 < z ⬝ᵥ (R *ᵥ z) := by
  rw [quadraticForm_eq_weighted_squares R a z hR (fun i => (ha i).ne')]
  apply add_pos_of_nonneg_of_pos
  · apply div_nonneg _ (by norm_num)
    exact Finset.sum_nonneg fun i hi => Finset.sum_nonneg fun j hj =>
      weightedEdgeSquare_nonneg R a z ha hoff i j
  · exact weighted_row_sum_pos R a z ha hRa hz

/-- The same conclusion packaged in mathlib's standard matrix predicate. -/
theorem matrix_posDef_of_weighted_row_sums [Fintype ι] (R : Matrix ι ι ℝ) (a : ι → ℝ)
    (hR : R.IsSymm) (ha : ∀ i, 0 < a i)
    (hoff : ∀ i j, i ≠ j → R i j ≤ 0)
    (hRa : ∀ i, 0 < (R *ᵥ a) i) : R.PosDef := by
  apply Matrix.posDef_iff_dotProduct_mulVec.mpr
  refine ⟨Matrix.isHermitian_iff_isSymm.mpr hR, ?_⟩
  intro z hz
  simpa only [star_trivial] using
    quadraticForm_pos_of_weighted_row_sums R a z hR ha hoff hRa hz

end

end CoefficientOne
