import MsetsPaper.Upper.FiniteKL
import MsetsPaper.Upper.BoundedIncrements
import Mathlib.Algebra.QuadraticDiscriminant

/-!
# The actual one-step comparator estimates in manuscript Lemma 5

All finite conditional-on-the-past quantities are represented by their actual
finite sums under the weighted action law.  The comparator may have zero
probabilities.  Mean, second-moment, variance, range and exponential-moment
bounds are proved from the concrete estimator and aggregate loss normalization.
The history/measurability and finite-horizon probability bridge are separate.
-/

noncomputable section

open scoped BigOperators
open Matrix MsetsLower MsetsLower.History

namespace MsetsPaper.Upper

variable {d m : ℕ}

def comparatorEstimate (theta : Fin d → ℝ) (q : Action d m → ℝ)
    (ell : Fin d → ℝ) (a : Action d m) : ℝ :=
  finiteExpectation q (fun b => estimateScalar theta a ell b)

def comparatorTrue (q : Action d m → ℝ) (ell : Fin d → ℝ) : ℝ :=
  finiteExpectation q (fun b => actionLoss b ell)

def comparatorDelta (theta : Fin d → ℝ) (q : Action d m → ℝ)
    (ell : Fin d → ℝ) (a : Action d m) : ℝ :=
  comparatorEstimate theta q ell a - comparatorTrue q ell

def comparatorV (theta : Fin d → ℝ) (q : Action d m → ℝ) : ℝ :=
  finiteExpectation q
    (fun b => actionLoss b (correction (m : ℝ) (weightedMarginal (m := m) theta)))

/-- The comparator's mean action is exactly its actual inclusion marginal. -/
theorem comparatorEstimate_eq_marginal_dot (theta : Fin d → ℝ)
    (q : Action d m → ℝ) (ell : Fin d → ℝ) (a : Action d m) :
    comparatorEstimate theta q ell a = marginal q ⬝ᵥ estimateVector theta a ell :=
  mean_indicator_dot q (estimateVector theta a ell)

/-- The representation `bar x^T M^-1 X Y` in the manuscript. -/
theorem comparatorEstimate_eq_feedback_mul_bilinear (theta : Fin d → ℝ)
    (q : Action d m → ℝ) (ell : Fin d → ℝ) (a : Action d m) :
    comparatorEstimate theta q ell a = actionLoss a ell *
      (marginal q ⬝ᵥ ((secondMoment (weightedLaw (m := m) theta))⁻¹ *ᵥ
        (fun i => selectedIndicator i a))) := by
  rw [comparatorEstimate_eq_marginal_dot, estimateVector, dotProduct_smul, smul_eq_mul]

/-- The same scalar, moving the symmetric inverse to the mean-action vector. -/
theorem comparatorEstimate_eq_feedback_mul_actionLoss (theta : Fin d → ℝ)
    (q : Action d m → ℝ) (ell : Fin d → ℝ) (a : Action d m) :
    comparatorEstimate theta q ell a = actionLoss a ell *
      actionLoss a ((secondMoment (weightedLaw (m := m) theta))⁻¹ *ᵥ marginal q) := by
  rw [comparatorEstimate_eq_feedback_mul_bilinear,
    dot_secondMoment_inv_mulVec, dotProduct_comm, dot_indicator_eq_actionLoss]

/-- `eq:kw-concentration-comparator-unbiased`, from the actual vector estimator. -/
theorem comparatorEstimate_mean (theta : Fin d → ℝ) (q : Action d m → ℝ)
    (ell : Fin d → ℝ) (hmpos : 1 ≤ m) (hmtop : m ≤ d - 1) :
    finiteExpectation (weightedLaw (m := m) theta) (comparatorEstimate theta q ell) =
      comparatorTrue q ell := by
  classical
  unfold finiteExpectation comparatorEstimate comparatorTrue
  simp only [finiteExpectation, Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro b _
  calc
    (∑ a, weightedLaw theta a * (q b * estimateScalar theta a ell b)) =
        q b * ∑ a, weightedLaw theta a * estimateScalar theta a ell b := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro a _
      ring
    _ = _ := by rw [estimateScalar_mean theta ell hmpos hmtop]

/-- `eq:kw-concentration-unbiased`. -/
theorem comparatorDelta_mean (theta : Fin d → ℝ) (q : Action d m → ℝ)
    (ell : Fin d → ℝ) (hmpos : 1 ≤ m) (hmtop : m ≤ d - 1) :
    finiteExpectation (weightedLaw (m := m) theta) (comparatorDelta theta q ell) = 0 := by
  classical
  unfold finiteExpectation comparatorDelta
  simp only [mul_sub, Finset.sum_sub_distrib, ← Finset.sum_mul,
    sum_weightedLaw theta (show m ≤ d by omega), one_mul]
  change finiteExpectation (weightedLaw theta) (comparatorEstimate theta q ell) -
    comparatorTrue q ell = 0
  rw [comparatorEstimate_mean theta q ell hmpos hmtop, sub_self]

/-- Exact finite Jensen gap for a symmetric positive-semidefinite quadratic.
This proves the Jensen step from nonnegative centered quadratics. -/
theorem marginal_quadratic_jensen_gap (q : Action d m → ℝ) (hqsum : ∑ b, q b = 1)
    (A : Matrix (Fin d) (Fin d) ℝ) (hA : A.IsSymm) :
    (∑ b, q b * (((fun i => selectedIndicator i b) - marginal q) ⬝ᵥ
      (A *ᵥ ((fun i => selectedIndicator i b) - marginal q)))) =
      (∑ b, q b * ((fun i => selectedIndicator i b) ⬝ᵥ
        (A *ᵥ (fun i => selectedIndicator i b)))) - marginal q ⬝ᵥ (A *ᵥ marginal q) := by
  classical
  have hswap (b : Action d m) : marginal q ⬝ᵥ (A *ᵥ (fun i => selectedIndicator i b)) =
      (fun i => selectedIndicator i b) ⬝ᵥ (A *ᵥ marginal q) := by
    simpa only [hA.eq] using Matrix.dotProduct_transpose_mulVec A
      (marginal q) (fun i => selectedIndicator i b)
  have hexpand (b : Action d m) :
      q b * (((fun i => selectedIndicator i b) - marginal q) ⬝ᵥ
        (A *ᵥ ((fun i => selectedIndicator i b) - marginal q))) =
      q b * ((fun i => selectedIndicator i b) ⬝ᵥ (A *ᵥ (fun i => selectedIndicator i b))) -
        2 * (q b * ((fun i => selectedIndicator i b) ⬝ᵥ (A *ᵥ marginal q))) +
        q b * (marginal q ⬝ᵥ (A *ᵥ marginal q)) := by
    rw [Matrix.mulVec_sub, sub_dotProduct, dotProduct_sub, dotProduct_sub, hswap]
    ring
  simp_rw [hexpand]
  rw [Finset.sum_add_distrib, Finset.sum_sub_distrib, ← Finset.mul_sum,
    ← Finset.sum_mul, hqsum, one_mul, mean_indicator_dot]
  ring

/-- The actual finite Jensen inequality used in the second-moment display. -/
theorem marginal_quadratic_le_mean (q : Action d m → ℝ) (hq : ∀ b, 0 ≤ q b)
    (hqsum : ∑ b, q b = 1) (A : Matrix (Fin d) (Fin d) ℝ) (hA : A.PosSemidef) :
    marginal q ⬝ᵥ (A *ᵥ marginal q) ≤
      ∑ b, q b * ((fun i => selectedIndicator i b) ⬝ᵥ
        (A *ᵥ (fun i => selectedIndicator i b))) := by
  classical
  have hnonneg : 0 ≤ ∑ b, q b *
      (((fun i => selectedIndicator i b) - marginal q) ⬝ᵥ
        (A *ᵥ ((fun i => selectedIndicator i b) - marginal q))) := by
    apply Finset.sum_nonneg
    intro b _
    apply mul_nonneg (hq b)
    simpa only [star_trivial] using
      hA.dotProduct_mulVec_nonneg ((fun i => selectedIndicator i b) - marginal q)
  rw [marginal_quadratic_jensen_gap q hqsum A (Matrix.isHermitian_iff_isSymm.mp hA.1)]
    at hnonneg
  linarith

/-- The definition of M is literally the expectation of the outer product XX^T. -/
theorem secondMoment_eq_mean_outerProducts (p : Action d m → ℝ) :
    secondMoment p = ∑ a, p a •
      Matrix.vecMulVec (fun i => selectedIndicator i a) (fun i => selectedIndicator i a) := by
  classical
  ext i j
  simp only [secondMoment, Matrix.sum_apply, Matrix.smul_apply,
    smul_eq_mul, Matrix.vecMulVec_apply]
  apply Finset.sum_congr rfl
  intro a _
  ring

/-- Formal equality between the finite sum after dropping Y^2 and the matrix
sandwich in the first line of the paper's second-moment display. -/
theorem inverse_actionLoss_secondMoment_eq_sandwich
    (theta : Fin d → ℝ) (q : Action d m → ℝ) :
    finiteExpectation (weightedLaw (m := m) theta)
      (fun a => (actionLoss a
        ((secondMoment (weightedLaw (m := m) theta))⁻¹ *ᵥ marginal q)) ^ 2) =
    marginal q ⬝ᵥ ((secondMoment (weightedLaw (m := m) theta))⁻¹ *ᵥ
      (secondMoment (weightedLaw (m := m) theta) *ᵥ
        ((secondMoment (weightedLaw (m := m) theta))⁻¹ *ᵥ marginal q))) := by
  rw [finiteExpectation, ← secondMoment_quadratic]
  rw [dot_secondMoment_inv_mulVec]
  exact dotProduct_comm _ _

/-- Exact equality using E[XX^T]=M, after removing the bounded feedback factor. -/
theorem inverse_actionLoss_secondMoment (theta : Fin d → ℝ) (q : Action d m → ℝ)
    (hmpos : 1 ≤ m) (hmtop : m ≤ d - 1) :
    finiteExpectation (weightedLaw (m := m) theta)
      (fun a => (actionLoss a ((secondMoment (weightedLaw (m := m) theta))⁻¹ *ᵥ marginal q)) ^ 2) =
    marginal q ⬝ᵥ ((secondMoment (weightedLaw (m := m) theta))⁻¹ *ᵥ marginal q) := by
  letI := (weightedLaw_secondMoment_posDef theta hmpos hmtop).isUnit.invertible
  rw [inverse_actionLoss_secondMoment_eq_sandwich, Matrix.mulVec_mulVec,
    Matrix.inv_mul_of_invertible, Matrix.one_mulVec]

/-- The first matrix-sandwich inequality in the paper. Dropping the bounded
feedback factor gives the actual second-moment matrix in the middle. -/
theorem comparatorEstimate_secondMoment_le_sandwich (theta : Fin d → ℝ)
    (q : Action d m → ℝ) (ell : Fin d → ℝ)
    (hmpos : 1 ≤ m) (hmtop : m ≤ d - 1)
    (hloss : ∀ a : Action d m, |actionLoss a ell| ≤ 1) :
    finiteExpectation (weightedLaw (m := m) theta)
      (fun a => (comparatorEstimate theta q ell a) ^ 2) ≤
    marginal q ⬝ᵥ ((secondMoment (weightedLaw (m := m) theta))⁻¹ *ᵥ
      (secondMoment (weightedLaw (m := m) theta) *ᵥ
        ((secondMoment (weightedLaw (m := m) theta))⁻¹ *ᵥ marginal q))) := by
  classical
  calc
    _ ≤ finiteExpectation (weightedLaw (m := m) theta)
        (fun a => (actionLoss a
          ((secondMoment (weightedLaw (m := m) theta))⁻¹ *ᵥ marginal q)) ^ 2) := by
      apply Finset.sum_le_sum
      intro a _
      apply mul_le_mul_of_nonneg_left _ (weightedLaw_pos theta (by omega) a).le
      change (comparatorEstimate theta q ell a) ^ 2 ≤
        (actionLoss a ((secondMoment (weightedLaw (m := m) theta))⁻¹ *ᵥ marginal q)) ^ 2
      rw [comparatorEstimate_eq_feedback_mul_actionLoss, mul_pow]
      have hy : (actionLoss a ell) ^ 2 ≤ 1 := by
        have h := (sq_le_sq₀ (abs_nonneg (actionLoss a ell))
          (by norm_num : (0 : ℝ) ≤ 1)).mpr (hloss a)
        simpa only [sq_abs, one_pow] using h
      simpa only [one_mul] using mul_le_mul_of_nonneg_right hy
        (sq_nonneg (actionLoss a ((secondMoment (weightedLaw (m := m) theta))⁻¹ *ᵥ marginal q)))
    _ = _ := inverse_actionLoss_secondMoment_eq_sandwich theta q

/-- First two lines of `eq:kw-concentration-second-moment`: the operational
bound now first obtains the matrix sandwich, then cancels M with its inverse. -/
theorem comparatorEstimate_secondMoment_le_quadratic (theta : Fin d → ℝ)
    (q : Action d m → ℝ) (ell : Fin d → ℝ)
    (hmpos : 1 ≤ m) (hmtop : m ≤ d - 1)
    (hloss : ∀ a : Action d m, |actionLoss a ell| ≤ 1) :
    finiteExpectation (weightedLaw (m := m) theta)
      (fun a => (comparatorEstimate theta q ell a) ^ 2) ≤
      marginal q ⬝ᵥ ((secondMoment (weightedLaw (m := m) theta))⁻¹ *ᵥ marginal q) := by
  have h := comparatorEstimate_secondMoment_le_sandwich theta q ell hmpos hmtop hloss
  rw [← inverse_actionLoss_secondMoment_eq_sandwich,
    inverse_actionLoss_secondMoment theta q hmpos hmtop] at h
  exact h

theorem comparator_quadratic_le_mean_leverage (theta : Fin d → ℝ)
    (q : Action d m → ℝ) (hq : ∀ b, 0 ≤ q b) (hqsum : ∑ b, q b = 1)
    (hmpos : 1 ≤ m) (hmtop : m ≤ d - 1) :
    marginal q ⬝ᵥ ((secondMoment (weightedLaw (m := m) theta))⁻¹ *ᵥ marginal q) ≤
      finiteExpectation q (leverage theta) :=
  marginal_quadratic_le_mean q hq hqsum _
    (weightedLaw_secondMoment_posDef theta hmpos hmtop).inv.posSemidef

theorem comparator_mean_leverage_le_V_quarter (theta : Fin d → ℝ)
    (q : Action d m → ℝ) (hq : ∀ b, 0 ≤ q b)
    (hmpos : 1 ≤ m) (hmtop : m ≤ d - 1) :
    finiteExpectation q (leverage theta) ≤ comparatorV theta q / 4 := by
  classical
  calc
    _ ≤ finiteExpectation q (fun b =>
        phi (weightedMarginal (m := m) theta) (fun i => selectedIndicator i b)) := by
      apply Finset.sum_le_sum
      intro b _
      exact mul_le_mul_of_nonneg_left (leverage_le_phi theta hmpos hmtop b) (hq b)
    _ = comparatorV theta q / 4 := by
      unfold comparatorV finiteExpectation
      simp_rw [actionLoss_correction theta hmpos hmtop]
      rw [Finset.sum_div]
      apply Finset.sum_congr rfl
      intro b _
      ring

theorem comparatorEstimate_secondMoment_le_V_quarter (theta : Fin d → ℝ)
    (q : Action d m → ℝ) (ell : Fin d → ℝ)
    (hq : ∀ b, 0 ≤ q b) (hqsum : ∑ b, q b = 1)
    (hmpos : 1 ≤ m) (hmtop : m ≤ d - 1)
    (hloss : ∀ a : Action d m, |actionLoss a ell| ≤ 1) :
    finiteExpectation (weightedLaw (m := m) theta)
      (fun a => (comparatorEstimate theta q ell a) ^ 2) ≤ comparatorV theta q / 4 :=
  (comparatorEstimate_secondMoment_le_quadratic theta q ell hmpos hmtop hloss).trans
    ((comparator_quadratic_le_mean_leverage theta q hq hqsum hmpos hmtop).trans
      (comparator_mean_leverage_le_V_quarter theta q hq hmpos hmtop))

/-- The exact centered second-moment identity in `eq:kw-concentration-variance`. -/
theorem comparatorDelta_secondMoment_eq (theta : Fin d → ℝ)
    (q : Action d m → ℝ) (ell : Fin d → ℝ) (hmpos : 1 ≤ m) (hmtop : m ≤ d - 1) :
    finiteExpectation (weightedLaw (m := m) theta)
      (fun a => (comparatorDelta theta q ell a) ^ 2) =
      finiteExpectation (weightedLaw (m := m) theta)
        (fun a => (comparatorEstimate theta q ell a) ^ 2) - (comparatorTrue q ell) ^ 2 := by
  classical
  have heq (a : Action d m) : weightedLaw theta a * (comparatorDelta theta q ell a) ^ 2 =
      weightedLaw theta a * (comparatorEstimate theta q ell a) ^ 2 -
        (2 * comparatorTrue q ell) * (weightedLaw theta a * comparatorEstimate theta q ell a) +
        weightedLaw theta a * (comparatorTrue q ell) ^ 2 := by
    unfold comparatorDelta
    ring
  unfold finiteExpectation
  simp_rw [heq]
  rw [Finset.sum_add_distrib, Finset.sum_sub_distrib, ← Finset.mul_sum, ← Finset.sum_mul,
    sum_weightedLaw theta (show m ≤ d by omega), one_mul]
  change _ - (2 * comparatorTrue q ell) *
      finiteExpectation (weightedLaw theta) (comparatorEstimate theta q ell) + _ = _
  rw [comparatorEstimate_mean theta q ell hmpos hmtop]
  ring

theorem comparatorDelta_secondMoment_le_V_quarter (theta : Fin d → ℝ)
    (q : Action d m → ℝ) (ell : Fin d → ℝ)
    (hq : ∀ b, 0 ≤ q b) (hqsum : ∑ b, q b = 1)
    (hmpos : 1 ≤ m) (hmtop : m ≤ d - 1)
    (hloss : ∀ a : Action d m, |actionLoss a ell| ≤ 1) :
    finiteExpectation (weightedLaw (m := m) theta)
      (fun a => (comparatorDelta theta q ell a) ^ 2) ≤ comparatorV theta q / 4 := by
  rw [comparatorDelta_secondMoment_eq theta q ell hmpos hmtop]
  exact (sub_le_self _ (sq_nonneg _)).trans
    (comparatorEstimate_secondMoment_le_V_quarter theta q ell hq hqsum hmpos hmtop hloss)


theorem comparatorEstimate_abs_le_sqrt (theta : Fin d → ℝ)
    (q : Action d m → ℝ) (ell : Fin d → ℝ)
    (hmpos : 1 ≤ m) (hmtop : m ≤ d - 1) (a : Action d m)
    (hloss : |actionLoss a ell| ≤ 1) :
    |comparatorEstimate theta q ell a| ≤
      Real.sqrt (marginal q ⬝ᵥ
        ((secondMoment (weightedLaw (m := m) theta))⁻¹ *ᵥ marginal q)) *
      Real.sqrt (leverage theta a) := by
  rw [comparatorEstimate_eq_feedback_mul_bilinear, abs_mul]
  have hcs := abs_bilinear_le_sqrt_quadratic _
    (weightedLaw_secondMoment_posDef theta hmpos hmtop).inv.posSemidef
    (marginal q) (fun i => selectedIndicator i a)
  calc
    _ ≤ 1 * (Real.sqrt (marginal q ⬝ᵥ
        ((secondMoment (weightedLaw (m := m) theta))⁻¹ *ᵥ marginal q)) *
        Real.sqrt (leverage theta a)) :=
      mul_le_mul hloss hcs (abs_nonneg _) (by norm_num)
    _ = _ := one_mul _

/-- The paper's common leverage range after substituting lambda=128 eta d. -/
def kwRange (d : ℕ) (eta : ℝ) : ℝ := 1 + 4 * d / (128 * eta * d)

theorem one_le_kwRange (d : ℕ) {eta : ℝ} (heta : 0 < eta) : 1 ≤ kwRange d eta := by
  unfold kwRange
  have h : 0 ≤ 4 * (d : ℝ) / (128 * eta * d) := by positivity
  linarith

theorem eta_mul_kwRange {eta : ℝ} (heta : 0 < eta) (hd : 0 < d) :
    eta * kwRange d eta = eta + 1 / 32 :=
  eta_leverage_bound heta (by exact_mod_cast hd)

theorem eta_mul_kwRange_le {eta : ℝ} (heta : 0 < eta) (hsmall : eta ≤ 1 / 64)
    (hd : 0 < d) : eta * kwRange d eta ≤ 3 / 64 := by
  rw [eta_mul_kwRange heta hd]
  linarith

theorem comparatorV_quarter_eq_phi_mean (theta : Fin d → ℝ)
    (q : Action d m → ℝ) (hmpos : 1 ≤ m) (hmtop : m ≤ d - 1) :
    comparatorV theta q / 4 = finiteExpectation q (fun b =>
      phi (weightedMarginal (m := m) theta) (fun i => selectedIndicator i b)) := by
  classical
  unfold comparatorV finiteExpectation
  simp_rw [actionLoss_correction theta hmpos hmtop]
  rw [Finset.sum_div]
  apply Finset.sum_congr rfl
  intro b _
  ring

theorem comparatorV_quarter_le_kwRange (theta : Fin d → ℝ)
    (q : Action d m → ℝ) (hq : ∀ b, 0 ≤ q b) (hqsum : ∑ b, q b = 1)
    (hmpos : 1 ≤ m) (hmtop : m ≤ d - 1) {eta : ℝ} (heta : 0 < eta)
    (hlo : ∀ i, (128 * eta * d / 2) * ((m : ℝ) / d) ≤ weightedMarginal (m := m) theta i)
    (hhi : ∀ i, weightedMarginal (m := m) theta i ≤
      1 - (128 * eta * d / 2) * (1 - (m : ℝ) / d)) :
    comparatorV theta q / 4 ≤ kwRange d eta := by
  classical
  rw [comparatorV_quarter_eq_phi_mean theta q hmpos hmtop]
  calc
    _ ≤ ∑ b, q b * kwRange d eta := by
      apply Finset.sum_le_sum
      intro b _
      exact mul_le_mul_of_nonneg_left
        (phi_range_half_parameter theta hmpos hmtop heta hlo hhi b).2 (hq b)
    _ = _ := by rw [← Finset.sum_mul, hqsum, one_mul]

theorem comparator_quadratic_le_kwRange (theta : Fin d → ℝ)
    (q : Action d m → ℝ) (hq : ∀ b, 0 ≤ q b) (hqsum : ∑ b, q b = 1)
    (hmpos : 1 ≤ m) (hmtop : m ≤ d - 1) {eta : ℝ} (heta : 0 < eta)
    (hlo : ∀ i, (128 * eta * d / 2) * ((m : ℝ) / d) ≤ weightedMarginal (m := m) theta i)
    (hhi : ∀ i, weightedMarginal (m := m) theta i ≤
      1 - (128 * eta * d / 2) * (1 - (m : ℝ) / d)) :
    marginal q ⬝ᵥ ((secondMoment (weightedLaw (m := m) theta))⁻¹ *ᵥ marginal q) ≤
      kwRange d eta :=
  (comparator_quadratic_le_mean_leverage theta q hq hqsum hmpos hmtop).trans
    ((comparator_mean_leverage_le_V_quarter theta q hq hmpos hmtop).trans
      (comparatorV_quarter_le_kwRange theta q hq hqsum hmpos hmtop heta hlo hhi))

theorem leverage_le_kwRange (theta : Fin d → ℝ)
    (hmpos : 1 ≤ m) (hmtop : m ≤ d - 1) {eta : ℝ} (heta : 0 < eta)
    (hlo : ∀ i, (128 * eta * d / 2) * ((m : ℝ) / d) ≤ weightedMarginal (m := m) theta i)
    (hhi : ∀ i, weightedMarginal (m := m) theta i ≤
      1 - (128 * eta * d / 2) * (1 - (m : ℝ) / d)) (a : Action d m) :
    leverage theta a ≤ kwRange d eta :=
  (leverage_le_phi theta hmpos hmtop a).trans
    (phi_range_half_parameter theta hmpos hmtop heta hlo hhi a).2

theorem comparatorEstimate_abs_le_kwRange (theta : Fin d → ℝ)
    (q : Action d m → ℝ) (ell : Fin d → ℝ)
    (hq : ∀ b, 0 ≤ q b) (hqsum : ∑ b, q b = 1)
    (hmpos : 1 ≤ m) (hmtop : m ≤ d - 1) {eta : ℝ} (heta : 0 < eta)
    (hlo : ∀ i, (128 * eta * d / 2) * ((m : ℝ) / d) ≤ weightedMarginal (m := m) theta i)
    (hhi : ∀ i, weightedMarginal (m := m) theta i ≤
      1 - (128 * eta * d / 2) * (1 - (m : ℝ) / d))
    (a : Action d m) (hloss : |actionLoss a ell| ≤ 1) :
    |comparatorEstimate theta q ell a| ≤ kwRange d eta := by
  have hx := comparator_quadratic_le_kwRange theta q hq hqsum hmpos hmtop heta hlo hhi
  have hy := leverage_le_kwRange theta hmpos hmtop heta hlo hhi a
  calc
    _ ≤ Real.sqrt (marginal q ⬝ᵥ
        ((secondMoment (weightedLaw (m := m) theta))⁻¹ *ᵥ marginal q)) *
        Real.sqrt (leverage theta a) :=
      comparatorEstimate_abs_le_sqrt theta q ell hmpos hmtop a hloss
    _ ≤ Real.sqrt (kwRange d eta) * Real.sqrt (kwRange d eta) :=
      mul_le_mul (Real.sqrt_le_sqrt hx) (Real.sqrt_le_sqrt hy)
        (Real.sqrt_nonneg _) (Real.sqrt_nonneg _)
    _ = kwRange d eta := Real.mul_self_sqrt (by linarith [one_le_kwRange d heta])

theorem comparatorTrue_abs_le_one (q : Action d m → ℝ) (ell : Fin d → ℝ)
    (hq : ∀ b, 0 ≤ q b) (hqsum : ∑ b, q b = 1)
    (hloss : ∀ b : Action d m, |actionLoss b ell| ≤ 1) :
    |comparatorTrue q ell| ≤ 1 := by
  classical
  calc
    _ ≤ ∑ b, |q b * actionLoss b ell| := Finset.abs_sum_le_sum_abs _ _
    _ = ∑ b, q b * |actionLoss b ell| := by
      apply Finset.sum_congr rfl
      intro b _
      rw [abs_mul, abs_of_nonneg (hq b)]
    _ ≤ ∑ b, q b * 1 := by
      apply Finset.sum_le_sum
      intro b _
      exact mul_le_mul_of_nonneg_left (hloss b) (hq b)
    _ = 1 := by simpa only [mul_one] using hqsum

/-- The two intermediate upper bounds in `eq:kw-concentration-delta-range`. -/
theorem comparatorDelta_abs_le (theta : Fin d → ℝ)
    (q : Action d m → ℝ) (ell : Fin d → ℝ)
    (hq : ∀ b, 0 ≤ q b) (hqsum : ∑ b, q b = 1)
    (hmpos : 1 ≤ m) (hmtop : m ≤ d - 1) {eta : ℝ} (heta : 0 < eta)
    (hlo : ∀ i, (128 * eta * d / 2) * ((m : ℝ) / d) ≤ weightedMarginal (m := m) theta i)
    (hhi : ∀ i, weightedMarginal (m := m) theta i ≤
      1 - (128 * eta * d / 2) * (1 - (m : ℝ) / d))
    (hloss : ∀ a : Action d m, |actionLoss a ell| ≤ 1) (a : Action d m) :
    |comparatorDelta theta q ell a| ≤ 1 + kwRange d eta ∧
      1 + kwRange d eta ≤ 2 * kwRange d eta := by
  have hest := comparatorEstimate_abs_le_kwRange theta q ell hq hqsum hmpos hmtop
    heta hlo hhi a (hloss a)
  have htrue := comparatorTrue_abs_le_one q ell hq hqsum hloss
  constructor
  · exact (abs_sub _ _).trans (by linarith)
  · linarith [one_le_kwRange d heta]

/-- `eq:kw-concentration-increment`, with its exact three-thirty-seconds bound. -/
theorem comparatorDelta_scaled_abs_le (theta : Fin d → ℝ)
    (q : Action d m → ℝ) (ell : Fin d → ℝ)
    (hq : ∀ b, 0 ≤ q b) (hqsum : ∑ b, q b = 1)
    (hmpos : 1 ≤ m) (hmtop : m ≤ d - 1) {eta : ℝ} (heta : 0 < eta)
    (hsmall : eta ≤ 1 / 64)
    (hlo : ∀ i, (128 * eta * d / 2) * ((m : ℝ) / d) ≤ weightedMarginal (m := m) theta i)
    (hhi : ∀ i, weightedMarginal (m := m) theta i ≤
      1 - (128 * eta * d / 2) * (1 - (m : ℝ) / d))
    (hloss : ∀ a : Action d m, |actionLoss a ell| ≤ 1) (a : Action d m) :
    |eta * comparatorDelta theta q ell a| ≤ 3 / 32 := by
  have hb := comparatorDelta_abs_le theta q ell hq hqsum hmpos hmtop heta hlo hhi hloss a
  have hs := mul_le_mul_of_nonneg_left (hb.1.trans hb.2) heta.le
  have hetaB := eta_mul_kwRange_le heta hsmall (show 0 < d by omega)
  rw [abs_mul, abs_of_pos heta]
  nlinarith

theorem comparatorV_nonneg (theta : Fin d → ℝ)
    (q : Action d m → ℝ) (hq : ∀ b, 0 ≤ q b)
    (hmpos : 1 ≤ m) (hmtop : m ≤ d - 1) : 0 ≤ comparatorV theta q := by
  classical
  unfold comparatorV finiteExpectation
  apply Finset.sum_nonneg
  intro b _
  apply mul_nonneg (hq b)
  change 0 ≤ actionLoss b (correction (m : ℝ) (weightedMarginal (m := m) theta))
  rw [actionLoss_correction theta hmpos hmtop]
  apply mul_nonneg (by norm_num)
  exact phi_nonneg _ _ (weightedMarginal_pos theta hmpos hmtop)
    (weightedMarginal_lt_one theta hmtop)

/-- The exact scalar estimate used in `eq:kw-concentration-exponential-moment`. -/
theorem exp_le_one_add_add_sq {u : ℝ} (hu : |u| ≤ 1) :
    Real.exp u ≤ 1 + u + u ^ 2 := by
  have h := (abs_le.mp (Real.abs_exp_sub_one_sub_id_le hu)).2
  linarith

/-- The first line of the exponential-moment display for either sign. -/
theorem comparatorDelta_expMoment_le_quadratic (theta : Fin d → ℝ)
    (q : Action d m → ℝ) (ell : Fin d → ℝ)
    (hq : ∀ b, 0 ≤ q b) (hqsum : ∑ b, q b = 1)
    (hmpos : 1 ≤ m) (hmtop : m ≤ d - 1) {eta : ℝ} (heta : 0 < eta)
    (hsmall : eta ≤ 1 / 64)
    (hlo : ∀ i, (128 * eta * d / 2) * ((m : ℝ) / d) ≤ weightedMarginal (m := m) theta i)
    (hhi : ∀ i, weightedMarginal (m := m) theta i ≤
      1 - (128 * eta * d / 2) * (1 - (m : ℝ) / d))
    (hloss : ∀ a : Action d m, |actionLoss a ell| ≤ 1)
    (s : ℝ) (hs : s = 1 ∨ s = -1) :
    finiteExpectation (weightedLaw (m := m) theta)
      (fun a => Real.exp (s * eta * comparatorDelta theta q ell a)) ≤
      1 + s * eta * finiteExpectation (weightedLaw (m := m) theta)
        (comparatorDelta theta q ell) +
      eta ^ 2 * finiteExpectation (weightedLaw (m := m) theta)
        (fun a => (comparatorDelta theta q ell a) ^ 2) := by
  classical
  have habs : |s| = 1 := by rcases hs with rfl | rfl <;> norm_num
  have hsq : s ^ 2 = 1 := by rcases hs with rfl | rfl <;> norm_num
  have hexp (a : Action d m) :
      Real.exp (s * eta * comparatorDelta theta q ell a) ≤
        1 + s * eta * comparatorDelta theta q ell a +
          (s * eta * comparatorDelta theta q ell a) ^ 2 := by
    apply exp_le_one_add_add_sq
    have h := comparatorDelta_scaled_abs_le theta q ell hq hqsum hmpos hmtop
      heta hsmall hlo hhi hloss a
    rw [mul_assoc, abs_mul, habs, one_mul]
    exact h.trans (by norm_num)
  calc
    _ ≤ ∑ a, weightedLaw theta a *
        (1 + s * eta * comparatorDelta theta q ell a +
          (s * eta * comparatorDelta theta q ell a) ^ 2) := by
      apply Finset.sum_le_sum
      intro a _
      exact mul_le_mul_of_nonneg_left (hexp a) (weightedLaw_pos theta (by omega) a).le
    _ = _ := by
      have heq (a : Action d m) : weightedLaw theta a *
          (1 + s * eta * comparatorDelta theta q ell a +
            (s * eta * comparatorDelta theta q ell a) ^ 2) =
          weightedLaw theta a + (s * eta) *
            (weightedLaw theta a * comparatorDelta theta q ell a) +
          eta ^ 2 * (weightedLaw theta a * (comparatorDelta theta q ell a) ^ 2) := by
        simp only [mul_pow, hsq, one_mul]
        ring
      simp_rw [heq]
      rw [Finset.sum_add_distrib, Finset.sum_add_distrib, ← Finset.mul_sum,
        ← Finset.mul_sum, sum_weightedLaw theta (show m ≤ d by omega)]
      rfl

/-- All four lines of `eq:kw-concentration-exponential-moment`, valid for both
signs and derived from the actual mean and variance, not certificates. -/
theorem comparatorDelta_mgf_sign (theta : Fin d → ℝ)
    (q : Action d m → ℝ) (ell : Fin d → ℝ)
    (hq : ∀ b, 0 ≤ q b) (hqsum : ∑ b, q b = 1)
    (hmpos : 1 ≤ m) (hmtop : m ≤ d - 1) {eta : ℝ} (heta : 0 < eta)
    (hsmall : eta ≤ 1 / 64)
    (hlo : ∀ i, (128 * eta * d / 2) * ((m : ℝ) / d) ≤ weightedMarginal (m := m) theta i)
    (hhi : ∀ i, weightedMarginal (m := m) theta i ≤
      1 - (128 * eta * d / 2) * (1 - (m : ℝ) / d))
    (hloss : ∀ a : Action d m, |actionLoss a ell| ≤ 1)
    (s : ℝ) (hs : s = 1 ∨ s = -1) :
    finiteExpectation (weightedLaw (m := m) theta)
      (fun a => Real.exp (s * eta * comparatorDelta theta q ell a)) ≤
      Real.exp (eta ^ 2 / 4 * comparatorV theta q) := by
  calc
    _ ≤ 1 + s * eta * finiteExpectation (weightedLaw (m := m) theta)
        (comparatorDelta theta q ell) +
        eta ^ 2 * finiteExpectation (weightedLaw (m := m) theta)
          (fun a => (comparatorDelta theta q ell a) ^ 2) :=
      comparatorDelta_expMoment_le_quadratic theta q ell hq hqsum hmpos hmtop
        heta hsmall hlo hhi hloss s hs
    _ = 1 + eta ^ 2 * finiteExpectation (weightedLaw (m := m) theta)
        (fun a => (comparatorDelta theta q ell a) ^ 2) := by
      rw [comparatorDelta_mean theta q ell hmpos hmtop, mul_zero, add_zero]
    _ ≤ Real.exp (eta ^ 2 * finiteExpectation (weightedLaw (m := m) theta)
        (fun a => (comparatorDelta theta q ell a) ^ 2)) := by
      simpa only [add_comm] using Real.add_one_le_exp
        (eta ^ 2 * finiteExpectation (weightedLaw (m := m) theta)
          (fun a => (comparatorDelta theta q ell a) ^ 2))
    _ ≤ _ := by
      apply Real.exp_le_exp.mpr
      have hvar := comparatorDelta_secondMoment_le_V_quarter theta q ell hq hqsum
        hmpos hmtop hloss
      have h := mul_le_mul_of_nonneg_left hvar (sq_nonneg eta)
      nlinarith

/-- The paired one-step inequalities consumed by the two-sided tail argument. -/
theorem comparatorDelta_mgf (theta : Fin d → ℝ)
    (q : Action d m → ℝ) (ell : Fin d → ℝ)
    (hq : ∀ b, 0 ≤ q b) (hqsum : ∑ b, q b = 1)
    (hmpos : 1 ≤ m) (hmtop : m ≤ d - 1) {eta : ℝ} (heta : 0 < eta)
    (hsmall : eta ≤ 1 / 64)
    (hlo : ∀ i, (128 * eta * d / 2) * ((m : ℝ) / d) ≤ weightedMarginal (m := m) theta i)
    (hhi : ∀ i, weightedMarginal (m := m) theta i ≤
      1 - (128 * eta * d / 2) * (1 - (m : ℝ) / d))
    (hloss : ∀ a : Action d m, |actionLoss a ell| ≤ 1) :
    finiteExpectation (weightedLaw (m := m) theta)
      (fun a => Real.exp (eta * comparatorDelta theta q ell a)) ≤
        Real.exp (eta ^ 2 / 4 * comparatorV theta q) ∧
    finiteExpectation (weightedLaw (m := m) theta)
      (fun a => Real.exp (-eta * comparatorDelta theta q ell a)) ≤
        Real.exp (eta ^ 2 / 4 * comparatorV theta q) := by
  constructor
  · simpa only [one_mul] using comparatorDelta_mgf_sign theta q ell hq hqsum hmpos hmtop
      heta hsmall hlo hhi hloss 1 (Or.inl rfl)
  · simpa only [neg_one_mul] using comparatorDelta_mgf_sign theta q ell hq hqsum hmpos hmtop
      heta hsmall hlo hhi hloss (-1) (Or.inr rfl)

end MsetsPaper.Upper
