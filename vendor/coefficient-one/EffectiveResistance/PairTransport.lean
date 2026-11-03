import EffectiveResistance.MatrixCorollary

/-!
# Decomposing zero-sum vectors into elementary pair transfers

This file supplies the finite transport decomposition used in the
edge-variation argument.  It is proved explicitly from the positive and
negative parts of a vector.
-/

open scoped BigOperators
open Matrix

namespace EffectiveResistance

noncomputable section

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- Positive part of a real-valued finite vector. -/
def positivePart (g : ι → ℝ) (i : ι) : ℝ := max (g i) 0

/-- Negative part, recorded as a nonnegative magnitude. -/
def negativePart (g : ι → ℝ) (i : ι) : ℝ := max (-g i) 0

/-- Total positive mass of a finite real-valued vector. -/
def positiveMass (g : ι → ℝ) : ℝ := ∑ i, positivePart g i

/-- The finite-dimensional `ℓ¹` norm, kept as an explicit sum. -/
def l1Norm (g : ι → ℝ) : ℝ := ∑ i, |g i|

theorem positivePart_nonnegative (g : ι → ℝ) (i : ι) :
    0 ≤ positivePart g i := by
  exact le_max_right _ _

theorem negativePart_nonnegative (g : ι → ℝ) (i : ι) :
    0 ≤ negativePart g i := by
  exact le_max_right _ _

theorem positivePart_sub_negativePart (g : ι → ℝ) (i : ι) :
    positivePart g i - negativePart g i = g i := by
  by_cases hi : 0 ≤ g i
  · rw [positivePart, max_eq_left hi, negativePart,
      max_eq_right (neg_nonpos.mpr hi)]
    ring
  · have hi' : g i ≤ 0 := le_of_not_ge hi
    rw [positivePart, max_eq_right hi', negativePart,
      max_eq_left (neg_nonneg.mpr hi')]
    ring

theorem positivePart_add_negativePart (g : ι → ℝ) (i : ι) :
    positivePart g i + negativePart g i = |g i| := by
  by_cases hi : 0 ≤ g i
  · rw [abs_of_nonneg hi]
    rw [positivePart, max_eq_left hi, negativePart,
      max_eq_right (neg_nonpos.mpr hi)]
    ring
  · have hi' : g i ≤ 0 := le_of_not_ge hi
    rw [abs_of_nonpos hi']
    rw [positivePart, max_eq_right hi', negativePart,
      max_eq_left (neg_nonneg.mpr hi')]
    ring

theorem sum_positivePart_eq_sum_negativePart
    {g : ι → ℝ} (hg : IsZeroSum g) :
    (∑ i, positivePart g i) = ∑ i, negativePart g i := by
  have hsum :
      (∑ i, positivePart g i) - ∑ i, negativePart g i = 0 := by
    rw [← Finset.sum_sub_distrib]
    simpa only [positivePart_sub_negativePart, IsZeroSum] using hg
  linarith

theorem two_mul_positiveMass_eq_l1Norm
    {g : ι → ℝ} (hg : IsZeroSum g) :
    2 * positiveMass g = l1Norm g := by
  rw [positiveMass, l1Norm]
  have hmass := sum_positivePart_eq_sum_negativePart hg
  calc
    2 * ∑ i, positivePart g i =
        (∑ i, positivePart g i) + ∑ i, negativePart g i := by linarith
    _ = ∑ i, (positivePart g i + negativePart g i) := by
      rw [Finset.sum_add_distrib]
    _ = ∑ i, |g i| := by
      apply Finset.sum_congr rfl
      intro i _
      exact positivePart_add_negativePart g i

/-- Amount transported from a positive coordinate `a` to a negative
coordinate `b`. -/
def transportCoefficient (g : ι → ℝ) (a b : ι) : ℝ :=
  positivePart g a * negativePart g b / positiveMass g

theorem transportCoefficient_nonnegative (g : ι → ℝ) (a b : ι) :
    0 ≤ transportCoefficient g a b := by
  unfold transportCoefficient
  exact div_nonneg
    (mul_nonneg (positivePart_nonnegative g a) (negativePart_nonnegative g b))
    (Finset.sum_nonneg fun i _ => positivePart_nonnegative g i)

/-- Explicit finite transport decomposition of a nonzero zero-sum vector. -/
theorem sum_transportCoefficient_smul_pairDemand
    {g : ι → ℝ} (hg : IsZeroSum g) (hmass : positiveMass g ≠ 0) :
    (fun k => ∑ a, ∑ b,
      transportCoefficient g a b * pairDemand a b k) = g := by
  have hneg : (∑ i, negativePart g i) = positiveMass g := by
    rw [positiveMass]
    exact (sum_positivePart_eq_sum_negativePart hg).symm
  funext k
  have hfirst :
      (∑ a, ∑ b, transportCoefficient g a b *
        (if k = a then 1 else 0)) = positivePart g k := by
    calc
      (∑ a, ∑ b, transportCoefficient g a b *
        (if k = a then 1 else 0)) =
          ∑ b, transportCoefficient g k b := by simp
      _ = positivePart g k := by
        unfold transportCoefficient
        simp_rw [div_eq_mul_inv]
        calc
          (∑ b, positivePart g k * negativePart g b *
              (positiveMass g)⁻¹) =
              (positivePart g k * (positiveMass g)⁻¹) *
                ∑ b, negativePart g b := by
                  rw [Finset.mul_sum]
                  apply Finset.sum_congr rfl
                  intro b _
                  ring
          _ = positivePart g k := by
                rw [hneg]
                field_simp
  have hsecond :
      (∑ a, ∑ b, transportCoefficient g a b *
        (if k = b then 1 else 0)) = negativePart g k := by
    calc
      (∑ a, ∑ b, transportCoefficient g a b *
        (if k = b then 1 else 0)) =
          ∑ a, transportCoefficient g a k := by simp
      _ = negativePart g k := by
        unfold transportCoefficient
        simp_rw [div_eq_mul_inv]
        calc
          (∑ a, positivePart g a * negativePart g k *
              (positiveMass g)⁻¹) =
              (∑ a, positivePart g a) *
                (negativePart g k * (positiveMass g)⁻¹) := by
                  rw [Finset.sum_mul]
                  apply Finset.sum_congr rfl
                  intro a _
                  ring
          _ = negativePart g k := by
                rw [← positiveMass]
                field_simp
  simp only [pairDemand]
  calc
    (∑ a, ∑ b, transportCoefficient g a b *
      ((if k = a then 1 else 0) - (if k = b then 1 else 0))) =
        (∑ a, ∑ b, transportCoefficient g a b *
          (if k = a then 1 else 0)) -
        (∑ a, ∑ b, transportCoefficient g a b *
          (if k = b then 1 else 0)) := by
            simp_rw [mul_sub, Finset.sum_sub_distrib]
    _ = positivePart g k - negativePart g k := by rw [hfirst, hsecond]
    _ = g k := positivePart_sub_negativePart g k

theorem sum_transportCoefficient
    {g : ι → ℝ} (hg : IsZeroSum g) (hmass : positiveMass g ≠ 0) :
    (∑ a, ∑ b, transportCoefficient g a b) =
      (2 : ℝ)⁻¹ * l1Norm g := by
  have hneg : (∑ i, negativePart g i) = positiveMass g := by
    rw [positiveMass]
    exact (sum_positivePart_eq_sum_negativePart hg).symm
  have hcoeff :
      (∑ a, ∑ b, transportCoefficient g a b) = positiveMass g := by
    unfold transportCoefficient
    simp_rw [div_eq_mul_inv]
    calc
      (∑ a, ∑ b, positivePart g a * negativePart g b *
          (positiveMass g)⁻¹) =
          ∑ a, (positivePart g a * (positiveMass g)⁻¹) *
            (∑ b, negativePart g b) := by
            apply Finset.sum_congr rfl
            intro a _
            rw [Finset.mul_sum]
            apply Finset.sum_congr rfl
            intro b _
            ring
      _ = (∑ a, positivePart g a) *
          ((positiveMass g)⁻¹ * ∑ b, negativePart g b) := by
            rw [Finset.sum_mul]
            apply Finset.sum_congr rfl
            intro a _
            ring
      _ = positiveMass g := by
            rw [hneg, ← positiveMass]
            field_simp
  calc
    (∑ a, ∑ b, transportCoefficient g a b) = positiveMass g := hcoeff
    _ = (2 : ℝ)⁻¹ * l1Norm g := by
      rw [← two_mul_positiveMass_eq_l1Norm hg]
      ring

end

end EffectiveResistance
