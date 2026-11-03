import Mathlib.Algebra.Order.BigOperators.Ring.Finset
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Data.Real.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-!
# Finite probability algebra

Small expectation, covariance, and Cauchy--Schwarz lemmas used by the
adjacent-rank part of the proof.  Everything is a finite sum.
-/

open scoped BigOperators

namespace EffectiveResistance

noncomputable section

variable {Ω : Type*} [Fintype Ω]

def finiteExpectation (p f : Ω → ℝ) : ℝ :=
  ∑ x, p x * f x

def finiteVariance (p f : Ω → ℝ) : ℝ :=
  finiteExpectation p fun x => (f x - finiteExpectation p f) ^ 2

def finiteCovariance (p f g : Ω → ℝ) : ℝ :=
  finiteExpectation p fun x =>
    (f x - finiteExpectation p f) * (g x - finiteExpectation p g)

theorem finiteExpectation_const
    {p : Ω → ℝ} (hp : ∑ x, p x = 1) (c : ℝ) :
    finiteExpectation p (fun _ => c) = c := by
  simp only [finiteExpectation]
  rw [← Finset.sum_mul, hp]
  simp

theorem finiteExpectation_add (p f g : Ω → ℝ) :
    finiteExpectation p (fun x => f x + g x) =
      finiteExpectation p f + finiteExpectation p g := by
  unfold finiteExpectation
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro x _
  ring

theorem finiteExpectation_product
    {Ω' : Type*} [Fintype Ω'] (p : Ω → ℝ) (p' : Ω' → ℝ)
    (f : Ω → ℝ) (g : Ω' → ℝ) :
    finiteExpectation (fun xy : Ω × Ω' => p xy.1 * p' xy.2)
        (fun xy => f xy.1 * g xy.2) =
      finiteExpectation p f * finiteExpectation p' g := by
  unfold finiteExpectation
  rw [Fintype.sum_prod_type]
  calc
    (∑ x, ∑ y, p x * p' y * (f x * g y)) =
        ∑ x, (p x * f x) * ∑ y, p' y * g y := by
      apply Finset.sum_congr rfl
      intro x _
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro y _
      ring
    _ = (∑ x, p x * f x) * ∑ y, p' y * g y := by
      rw [Finset.sum_mul]

theorem finiteExpectation_independent_sum
    {Ω' : Type*} [Fintype Ω'] {p : Ω → ℝ} {p' : Ω' → ℝ}
    (hp : ∑ x, p x = 1) (hp' : ∑ y, p' y = 1)
    (f : Ω → ℝ) (g : Ω' → ℝ) :
    finiteExpectation (fun xy : Ω × Ω' => p xy.1 * p' xy.2)
        (fun xy => f xy.1 + g xy.2) =
      finiteExpectation p f + finiteExpectation p' g := by
  rw [finiteExpectation_add]
  have hleft :
      finiteExpectation (fun xy : Ω × Ω' => p xy.1 * p' xy.2)
          (fun xy => f xy.1) = finiteExpectation p f := by
    calc
      _ = finiteExpectation (fun xy : Ω × Ω' => p xy.1 * p' xy.2)
          (fun xy => f xy.1 * 1) := by simp
      _ = finiteExpectation p f * finiteExpectation p' (fun _ => 1) :=
        finiteExpectation_product p p' f (fun _ => 1)
      _ = finiteExpectation p f := by rw [finiteExpectation_const hp']; ring
  have hright :
      finiteExpectation (fun xy : Ω × Ω' => p xy.1 * p' xy.2)
          (fun xy => g xy.2) = finiteExpectation p' g := by
    calc
      _ = finiteExpectation (fun xy : Ω × Ω' => p xy.1 * p' xy.2)
          (fun xy => 1 * g xy.2) := by simp
      _ = finiteExpectation p (fun _ => 1) * finiteExpectation p' g :=
        finiteExpectation_product p p' (fun _ => 1) g
      _ = finiteExpectation p' g := by rw [finiteExpectation_const hp]; ring
  rw [hleft, hright]

theorem finiteExpectation_mul_cauchy
    {p : Ω → ℝ} (hp : ∀ x, 0 ≤ p x) (f g : Ω → ℝ) :
    (finiteExpectation p fun x => f x * g x) ^ 2 ≤
      finiteExpectation p (fun x => f x ^ 2) *
        finiteExpectation p (fun x => g x ^ 2) := by
  have h := Finset.sum_sq_le_sum_mul_sum_of_sq_le_mul
    (s := Finset.univ)
    (r := fun x => p x * (f x * g x))
    (f := fun x => p x * f x ^ 2)
    (g := fun x => p x * g x ^ 2)
    (fun x _ => mul_nonneg (hp x) (sq_nonneg _))
    (fun x _ => mul_nonneg (hp x) (sq_nonneg _))
    (fun x _ => by
      rw [show (p x * (f x * g x)) ^ 2 =
          (p x * f x ^ 2) * (p x * g x ^ 2) by ring])
  simpa only [finiteExpectation] using h

theorem finiteVariance_expansion
    {p : Ω → ℝ} (hp : ∑ x, p x = 1) (f : Ω → ℝ) :
    finiteVariance p f =
      finiteExpectation p (fun x => f x ^ 2) -
        (finiteExpectation p f) ^ 2 := by
  simp only [finiteVariance, finiteExpectation]
  let μ : ℝ := ∑ x, p x * f x
  change (∑ x, p x * (f x - μ) ^ 2) =
    (∑ x, p x * f x ^ 2) - μ ^ 2
  calc
    (∑ x, p x * (f x - μ) ^ 2) =
        ∑ x, (p x * f x ^ 2 - 2 * μ * (p x * f x) + μ ^ 2 * p x) := by
      apply Finset.sum_congr rfl
      intro x _
      ring
    _ = (∑ x, p x * f x ^ 2) -
        2 * μ * (∑ x, p x * f x) + μ ^ 2 * (∑ x, p x) := by
      rw [Finset.sum_add_distrib, Finset.sum_sub_distrib,
        ← Finset.mul_sum, ← Finset.mul_sum]
    _ = (∑ x, p x * f x ^ 2) - μ ^ 2 := by
      rw [hp]
      dsimp only [μ]
      ring

/-- Bias--variance decomposition for a finite probability law. -/
theorem finiteExpectation_sq_residual
    {p : Ω → ℝ} (hp : ∑ x, p x = 1) (f : Ω → ℝ) (c : ℝ) :
    finiteExpectation p (fun x => (c - f x) ^ 2) =
      finiteVariance p f + (c - finiteExpectation p f) ^ 2 := by
  rw [finiteVariance_expansion hp]
  simp only [finiteExpectation]
  let μ : ℝ := ∑ x, p x * f x
  change (∑ x, p x * (c - f x) ^ 2) =
    ((∑ x, p x * f x ^ 2) - μ ^ 2) + (c - μ) ^ 2
  calc
    (∑ x, p x * (c - f x) ^ 2) =
        ∑ x, (p x * f x ^ 2 - 2 * c * (p x * f x) + c ^ 2 * p x) := by
      apply Finset.sum_congr rfl
      intro x _
      ring
    _ = (∑ x, p x * f x ^ 2) -
        2 * c * (∑ x, p x * f x) + c ^ 2 * (∑ x, p x) := by
      rw [Finset.sum_add_distrib, Finset.sum_sub_distrib,
        ← Finset.mul_sum, ← Finset.mul_sum]
    _ = ((∑ x, p x * f x ^ 2) - μ ^ 2) + (c - μ) ^ 2 := by
      rw [hp]
      dsimp only [μ]
      ring

theorem finiteVariance_nonnegative
    {p : Ω → ℝ} (hp : ∀ x, 0 ≤ p x) (f : Ω → ℝ) :
    0 ≤ finiteVariance p f := by
  exact Finset.sum_nonneg fun x _ =>
    mul_nonneg (hp x) (sq_nonneg _)

theorem finiteCovariance_cauchy
    {p : Ω → ℝ} (hp : ∀ x, 0 ≤ p x) (f g : Ω → ℝ) :
    finiteCovariance p f g ^ 2 ≤
      finiteVariance p f * finiteVariance p g := by
  exact finiteExpectation_mul_cauchy hp
    (fun x => f x - finiteExpectation p f)
    (fun x => g x - finiteExpectation p g)

theorem finiteCovariance_expansion
    {p : Ω → ℝ} (hnorm : ∑ x, p x = 1) (f g : Ω → ℝ) :
    finiteCovariance p f g =
      finiteExpectation p (fun x => f x * g x) -
        finiteExpectation p f * finiteExpectation p g := by
  simp only [finiteCovariance, finiteExpectation]
  let μf : ℝ := ∑ x, p x * f x
  let μg : ℝ := ∑ x, p x * g x
  change (∑ x, p x * ((f x - μf) * (g x - μg))) =
    (∑ x, p x * (f x * g x)) - μf * μg
  calc
    (∑ x, p x * ((f x - μf) * (g x - μg))) =
        ∑ x, (p x * (f x * g x) - μg * (p x * f x) -
          μf * (p x * g x) + (μf * μg) * p x) := by
      apply Finset.sum_congr rfl
      intro x _
      ring
    _ = (∑ x, p x * (f x * g x)) -
          μg * (∑ x, p x * f x) -
          μf * (∑ x, p x * g x) +
          (μf * μg) * (∑ x, p x) := by
      rw [Finset.sum_add_distrib, Finset.sum_sub_distrib,
        Finset.sum_sub_distrib, ← Finset.mul_sum, ← Finset.mul_sum,
        ← Finset.mul_sum]
    _ = (∑ x, p x * (f x * g x)) - μf * μg := by
      rw [hnorm]
      dsimp only [μf, μg]
      ring

theorem finiteVariance_unit_interval
    {p : Ω → ℝ} (hp : ∀ x, 0 ≤ p x) (hnorm : ∑ x, p x = 1)
    {φ : Ω → ℝ} (hφ0 : ∀ x, 0 ≤ φ x) (hφ1 : ∀ x, φ x ≤ 1) :
    finiteVariance p φ ≤
      finiteExpectation p φ * (1 - finiteExpectation p φ) := by
  rw [finiteVariance_expansion hnorm]
  have hsquare :
      finiteExpectation p (fun x => φ x ^ 2) ≤ finiteExpectation p φ := by
    unfold finiteExpectation
    apply Finset.sum_le_sum
    intro x _
    apply mul_le_mul_of_nonneg_left _ (hp x)
    nlinarith [hφ0 x, hφ1 x]
  nlinarith

/-- The variance of the sum of two independent identically distributed
finite random variables is twice the original variance. -/
theorem finiteVariance_iid_sum
    {p : Ω → ℝ} (hnorm : ∑ x, p x = 1) (f : Ω → ℝ) :
    finiteVariance (fun xy : Ω × Ω => p xy.1 * p xy.2)
        (fun xy => f xy.1 + f xy.2) =
      2 * finiteVariance p f := by
  have hpairnorm : ∑ xy : Ω × Ω, p xy.1 * p xy.2 = 1 := by
    rw [Fintype.sum_prod_type]
    calc
      (∑ x, ∑ y, p x * p y) = ∑ x, p x * ∑ y, p y := by
        apply Finset.sum_congr rfl
        intro x _
        rw [Finset.mul_sum]
      _ = (∑ x, p x) * ∑ y, p y := by rw [Finset.sum_mul]
      _ = 1 := by rw [hnorm]; norm_num
  rw [finiteVariance_expansion hpairnorm, finiteVariance_expansion hnorm]
  have hmean :
      finiteExpectation (fun xy : Ω × Ω => p xy.1 * p xy.2)
          (fun xy => f xy.1 + f xy.2) = 2 * finiteExpectation p f := by
    rw [finiteExpectation_add]
    have hleft := finiteExpectation_product p p f (fun _ => 1)
    have hright := finiteExpectation_product p p (fun _ => 1) f
    rw [finiteExpectation_const hnorm] at hleft hright
    simpa [two_mul] using congrArg₂ (· + ·) hleft hright
  have hsecond :
      finiteExpectation (fun xy : Ω × Ω => p xy.1 * p xy.2)
          (fun xy => (f xy.1 + f xy.2) ^ 2) =
        2 * finiteExpectation p (fun x => f x ^ 2) +
          2 * (finiteExpectation p f) ^ 2 := by
    have hxx := finiteExpectation_product p p (fun x => f x ^ 2) (fun _ => 1)
    have hyy := finiteExpectation_product p p (fun _ => 1) (fun y => f y ^ 2)
    have hxy := finiteExpectation_product p p f f
    rw [finiteExpectation_const hnorm] at hxx hyy
    have htwo :
        finiteExpectation (fun xy : Ω × Ω => p xy.1 * p xy.2)
            (fun xy => 2 * (f xy.1 * f xy.2)) =
          2 * finiteExpectation (fun xy : Ω × Ω => p xy.1 * p xy.2)
            (fun xy => f xy.1 * f xy.2) := by
      unfold finiteExpectation
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro xy _
      ring
    calc
      finiteExpectation (fun xy : Ω × Ω => p xy.1 * p xy.2)
          (fun xy => (f xy.1 + f xy.2) ^ 2) =
        finiteExpectation (fun xy : Ω × Ω => p xy.1 * p xy.2)
          (fun xy => f xy.1 ^ 2 * 1 + 1 * f xy.2 ^ 2 +
            2 * (f xy.1 * f xy.2)) := by
        unfold finiteExpectation
        apply Finset.sum_congr rfl
        intro xy _
        ring
      _ = finiteExpectation (fun xy : Ω × Ω => p xy.1 * p xy.2)
            (fun xy => f xy.1 ^ 2 * 1) +
          finiteExpectation (fun xy : Ω × Ω => p xy.1 * p xy.2)
            (fun xy => 1 * f xy.2 ^ 2) +
          finiteExpectation (fun xy : Ω × Ω => p xy.1 * p xy.2)
            (fun xy => 2 * (f xy.1 * f xy.2)) := by
        rw [finiteExpectation_add, finiteExpectation_add]
      _ = 2 * finiteExpectation p (fun x => f x ^ 2) +
          2 * (finiteExpectation p f) ^ 2 := by
        rw [hxx, hyy, htwo, hxy]
        ring
  rw [hmean, hsecond]
  ring

end

end EffectiveResistance
