import MsetsPaper.Upper.OMD
import MsetsPaper.Upper.SurrogateSecondMoment
import MsetsPaper.Upper.SmoothedComparator

/-!
# T1: the pathwise estimated-loss bound

The real surrogate, pathwise learner-estimate identity and second-order
estimate are combined here. The sole projection premise is the precise
one-step Pythagorean inequality that P1 still has to supply.
-/

noncomputable section

open MsetsLower MsetsLower.History
open scoped BigOperators

namespace MsetsPaper.Upper

variable {d m : ℕ}

theorem mean_surrogate (theta ell : Fin d → ℝ) (eta : ℝ)
    (a : Action d m) (q : Action d m → ℝ) :
    finiteExpectation q (surrogate theta ell eta a) =
      finiteExpectation q (estimateScalar theta a ell) - eta * comparatorV theta q := by
  unfold surrogate comparatorV
  simp only [finiteExpectation, mul_sub, Finset.sum_sub_distrib, Finset.mul_sum]
  congr 1
  apply Finset.sum_congr rfl
  intro b _
  ring

theorem mean_learner_surrogate (theta ell : Fin d → ℝ) (eta : ℝ)
    (hmpos : 1 ≤ m) (hmtop : m ≤ d - 1) (a : Action d m) :
    finiteExpectation (weightedLaw theta) (surrogate theta ell eta a) =
      actionLoss a ell - 4 * eta * ((d : ℝ) + 1) := by
  rw [mean_surrogate]
  have hest := estimateScalar_pathwise_mean theta ell hmpos hmtop a
  change finiteExpectation (weightedLaw theta) (estimateScalar theta a ell) = _ at hest
  rw [hest]
  have hcorr : comparatorV theta (weightedLaw (m := m) theta) = 4 * ((d : ℝ) + 1) :=
    correction_mean theta hmpos hmtop
  rw [hcorr]
  ring

theorem estimated_regret_le_of_projection
    (theta ell : ℕ → Fin d → ℝ) (a : ℕ → Action d m) (q : Action d m → ℝ)
    (T : ℕ) (hT : 0 < T) (hmpos : 1 ≤ m) (hmtop : m ≤ d - 1)
    (eta : ℝ) (heta : 0 < eta) (hsmall : eta ≤ 1 / 64)
    (hq : ∀ b, 0 ≤ q b) (hqsum : ∑ b, q b = 1)
    (hloss : ∀ t, 1 ≤ t → t ≤ T → ∀ b : Action d m, |actionLoss b (ell t)| ≤ 1)
    (hlo : ∀ t, 1 ≤ t → t ≤ T → ∀ i,
      (128 * eta * d / 2) * ((m : ℝ) / d) ≤ weightedMarginal (m := m) (theta t) i)
    (hhi : ∀ t, 1 ≤ t → t ≤ T → ∀ i, weightedMarginal (m := m) (theta t) i ≤
      1 - (128 * eta * d / 2) * (1 - (m : ℝ) / d))
    (hprojection : ∀ t, 1 ≤ t → t ≤ T →
      finiteKL q (weightedLaw (m := m) (theta (t + 1))) ≤
        finiteKL q (weightedLaw (m := m)
          (theta t - eta • surrogateVector (theta t) (ell t) eta (a t))) -
        finiteKL (weightedLaw (m := m) (theta (t + 1)))
          (weightedLaw (m := m)
            (theta t - eta • surrogateVector (theta t) (ell t) eta (a t))) + eta / (T : ℝ)) :
    (∑ t ∈ Finset.Icc 1 T,
      (actionLoss (a t) (ell t) - finiteExpectation q (estimateScalar (theta t) (a t) (ell t)))) ≤
      finiteKL q (weightedLaw (m := m) (theta 1)) / eta + 1 +
        4 * eta * (∑ t ∈ Finset.Icc 1 T,
          phi (weightedMarginal (m := m) (theta t)) (fun i ↦ selectedIndicator i (a t))) +
        3 * eta ^ 2 * ((d : ℝ) + 1) * T + 4 * eta * ((d : ℝ) + 1) * T -
        eta * (∑ t ∈ Finset.Icc 1 T, comparatorV (theta t) q) := by
  classical
  have homd := weighted_surrogate_omd_stability_of_projection theta ell a q T hT hmpos hmtop
    eta heta hsmall hq hqsum hloss hlo hhi hprojection
  have hcount : (Finset.Icc 1 T).card = T := by simp
  have hleft : (∑ t ∈ Finset.Icc 1 T,
      (finiteExpectation (weightedLaw (m := m) (theta t))
          (surrogate (theta t) (ell t) eta (a t)) -
        finiteExpectation q (surrogate (theta t) (ell t) eta (a t)))) =
      (∑ t ∈ Finset.Icc 1 T,
        (actionLoss (a t) (ell t) - finiteExpectation q (estimateScalar (theta t) (a t) (ell t)))) -
      4 * eta * ((d : ℝ) + 1) * T + eta * (∑ t ∈ Finset.Icc 1 T, comparatorV (theta t) q) := by
    simp_rw [mean_learner_surrogate _ _ _ hmpos hmtop, mean_surrogate]
    have hp (t : ℕ) : actionLoss (a t) (ell t) - 4 * eta * ((d : ℝ) + 1) -
        (finiteExpectation q (estimateScalar (theta t) (a t) (ell t)) - eta * comparatorV (theta t) q) =
        (actionLoss (a t) (ell t) - finiteExpectation q (estimateScalar (theta t) (a t) (ell t))) -
          4 * eta * ((d : ℝ) + 1) + eta * comparatorV (theta t) q := by ring
    simp_rw [hp]
    rw [Finset.sum_add_distrib, Finset.sum_sub_distrib, ← Finset.mul_sum,
      Finset.sum_const, hcount, nsmul_eq_mul]
    simp only [Finset.mul_sum]
    ring
  have hsecond : 2 * eta * (∑ t ∈ Finset.Icc 1 T,
      finiteExpectation (weightedLaw (m := m) (theta t))
        (fun b ↦ (surrogate (theta t) (ell t) eta (a t) b) ^ 2)) ≤
      4 * eta * (∑ t ∈ Finset.Icc 1 T,
        phi (weightedMarginal (m := m) (theta t)) (fun i ↦ selectedIndicator i (a t))) +
      3 * eta ^ 2 * ((d : ℝ) + 1) * T := by
    have hsum := Finset.sum_le_sum (s := Finset.Icc 1 T) (fun t ht ↦
      scaled_surrogate_secondMoment_le (theta t) (ell t) hmpos hmtop heta hsmall
        (hlo t (Finset.mem_Icc.mp ht).1 (Finset.mem_Icc.mp ht).2)
        (hhi t (Finset.mem_Icc.mp ht).1 (Finset.mem_Icc.mp ht).2)
        (a t) (hloss t (Finset.mem_Icc.mp ht).1 (Finset.mem_Icc.mp ht).2 (a t)))
    simp only [← Finset.mul_sum, Finset.sum_add_distrib, Finset.sum_const,
      hcount, nsmul_eq_mul] at hsum
    nlinarith
  rw [hleft] at homd
  linarith

end MsetsPaper.Upper
