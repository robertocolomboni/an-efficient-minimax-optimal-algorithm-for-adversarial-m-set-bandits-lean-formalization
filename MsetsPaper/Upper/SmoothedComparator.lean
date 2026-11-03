import MsetsPaper.Upper.ProjectionDualExistence

/-!
# T1: the actual smoothed comparator and its entropy/smoothing cost

q_x=(1-lambda) delta_x+lambda U is a concrete distribution on m-sets.
Its marginals, feasibility, initial KL bound and loss approximation are
proved, including zero comparator coordinates at lambda=0.
-/

noncomputable section

open MsetsLower MsetsLower.History
open scoped BigOperators

namespace MsetsPaper.Upper

variable {d m : ℕ}

theorem weightedLaw_zero (a : Action d m) :
    weightedLaw (0 : Fin d → ℝ) a = 1 / (Nat.choose d m : ℝ) := by
  simp [weightedLaw, partition, actionLoss, card_MSetAction]

def smoothedComparator (lam : ℝ) (a b : Action d m) : ℝ :=
  (if b = a then 1 - lam else 0) + lam * weightedLaw (0 : Fin d → ℝ) b

theorem smoothedComparator_nonneg {lam : ℝ} (hlam : 0 ≤ lam) (hlam1 : lam ≤ 1)
    (a b : Action d m) : 0 ≤ smoothedComparator lam a b := by
  have hmd : m ≤ d := by
    simpa only [Fintype.card_fin, a.property] using Finset.card_le_univ a.val
  unfold smoothedComparator
  have hU := (weightedLaw_pos (0 : Fin d → ℝ) hmd b).le
  split_ifs <;> positivity

theorem sum_smoothedComparator (lam : ℝ) (a : Action d m) :
    ∑ b, smoothedComparator lam a b = 1 := by
  classical
  have hmd : m ≤ d := by
    simpa only [Fintype.card_fin, a.property] using Finset.card_le_univ a.val
  simp only [smoothedComparator, Finset.sum_add_distrib, ← Finset.mul_sum,
    sum_weightedLaw (0 : Fin d → ℝ) hmd, mul_one]
  simp

theorem smoothedComparator_expectation (lam : ℝ) (a : Action d m) (f : Action d m → ℝ) :
    finiteExpectation (smoothedComparator lam a) f =
      (1 - lam) * f a + lam * finiteExpectation (weightedLaw (0 : Fin d → ℝ)) f := by
  classical
  simp only [finiteExpectation, smoothedComparator, add_mul,
    ite_mul, zero_mul, Finset.sum_add_distrib]
  rw [Finset.sum_ite_eq', Finset.mul_sum]
  simp only [Finset.mem_univ, ite_true]
  congr 1
  apply Finset.sum_congr rfl
  intro b _
  ring

theorem smoothedComparator_marginal (lam : ℝ) (a : Action d m)
    (hmpos : 1 ≤ m) (hmtop : m ≤ d - 1) (i : Fin d) :
    marginal (smoothedComparator lam a) i =
      (1 - lam) * selectedIndicator i a + lam * ((m : ℝ) / d) := by
  have h := smoothedComparator_expectation lam a (fun b ↦ selectedIndicator i b)
  change marginal (smoothedComparator lam a) i =
    (1 - lam) * selectedIndicator i a + lam * weightedMarginal (m := m) (0 : Fin d → ℝ) i at h
  simpa only [weightedMarginal_zero_eq hmpos hmtop] using h

theorem smoothedComparator_marginal_mem (lam : ℝ) (a : Action d m)
    (hmpos : 1 ≤ m) (hmtop : m ≤ d - 1) (hlam1 : lam ≤ 1) (i : Fin d) :
    lam * ((m : ℝ) / d) ≤ marginal (smoothedComparator lam a) i ∧
      marginal (smoothedComparator lam a) i ≤ 1 - lam * (1 - (m : ℝ) / d) := by
  rw [smoothedComparator_marginal lam a hmpos hmtop i]
  rcases selectedIndicator_binary i a with hi | hi <;> rw [hi] <;>
    constructor <;> nlinarith

def finiteEntropy (q : Action d m → ℝ) : ℝ := -∑ a, q a * Real.log (q a)

theorem finiteEntropy_nonneg (q : Action d m → ℝ)
    (hq : ∀ a, 0 ≤ q a) (hqsum : ∑ a, q a = 1) : 0 ≤ finiteEntropy q := by
  unfold finiteEntropy
  apply neg_nonneg.mpr
  apply Finset.sum_nonpos
  intro a _
  have hq1 : q a ≤ 1 := by
    rw [← hqsum]
    exact Finset.single_le_sum (fun b _ ↦ hq b) (Finset.mem_univ a)
  exact Real.mul_log_nonpos (hq a) hq1

theorem finiteKL_uniform_eq_log_card_sub_entropy (q : Action d m → ℝ)
    (hqsum : ∑ a, q a = 1) (hmd : m ≤ d) :
    finiteKL q (weightedLaw (0 : Fin d → ℝ)) =
      Real.log (Nat.choose d m) - finiteEntropy q := by
  rw [finiteKL_eq_sum_mul_log_sub_log q _ (weightedLaw_pos (0 : Fin d → ℝ) hmd)]
  simp_rw [weightedLaw_zero, one_div, Real.log_inv, sub_neg_eq_add, mul_add]
  rw [Finset.sum_add_distrib, ← Finset.sum_mul, hqsum, one_mul]
  unfold finiteEntropy
  ring

theorem smoothedComparator_initialKL_le_log_card {lam : ℝ}
    (hlam : 0 ≤ lam) (hlam1 : lam ≤ 1) (a : Action d m) :
    finiteKL (smoothedComparator lam a) (weightedLaw (0 : Fin d → ℝ)) ≤
      Real.log (Nat.choose d m) := by
  have hmd : m ≤ d := by
    simpa only [Fintype.card_fin, a.property] using Finset.card_le_univ a.val
  rw [finiteKL_uniform_eq_log_card_sub_entropy _ (sum_smoothedComparator lam a) hmd]
  exact sub_le_self _ (finiteEntropy_nonneg _
    (smoothedComparator_nonneg hlam hlam1 a) (sum_smoothedComparator lam a))

theorem smoothedComparator_loss_cost {lam : ℝ} (hlam : 0 ≤ lam)
    (a : Action d m) (ell : Fin d → ℝ)
    (hloss : ∀ b : Action d m, |actionLoss b ell| ≤ 1) :
    finiteExpectation (smoothedComparator lam a) (fun b ↦ actionLoss b ell) -
      actionLoss a ell ≤ 2 * lam := by
  have hmd : m ≤ d := by
    simpa only [Fintype.card_fin, a.property] using Finset.card_le_univ a.val
  have hU : finiteExpectation (weightedLaw (0 : Fin d → ℝ))
      (fun b : Action d m ↦ actionLoss b ell) ≤ 1 := by
    calc
      _ ≤ ∑ b : Action d m, weightedLaw (0 : Fin d → ℝ) b * 1 := by
        apply Finset.sum_le_sum
        intro b _
        exact mul_le_mul_of_nonneg_left (abs_le.mp (hloss b)).2
          (weightedLaw_pos (0 : Fin d → ℝ) hmd b).le
      _ = 1 := by simpa using sum_weightedLaw (0 : Fin d → ℝ) hmd
  rw [smoothedComparator_expectation]
  have hdiff : finiteExpectation (weightedLaw (0 : Fin d → ℝ))
      (fun b : Action d m ↦ actionLoss b ell) - actionLoss a ell ≤ 2 := by
    linarith [(abs_le.mp (hloss a)).1]
  have h := mul_le_mul_of_nonneg_left hdiff hlam
  nlinarith

end MsetsPaper.Upper
