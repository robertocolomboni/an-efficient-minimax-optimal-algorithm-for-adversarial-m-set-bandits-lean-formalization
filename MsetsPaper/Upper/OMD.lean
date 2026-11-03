import MsetsPaper.Upper.FiniteKL
import MsetsPaper.Upper.BoundedIncrements

/-!
# Finite multiplicative-weights stability with approximate KL projection

This follows the proof of manuscript Lemma 4, equations `omd-kl-update`,
`omd-log-moment`, and `omd-one-step`, including the telescoping calculation.
The projection inequality is an explicit input to the stability theorem; this
module does not assert that the projection algorithm has already supplied it.
-/

noncomputable section

open scoped BigOperators
open MsetsLower MsetsLower.History

namespace MsetsPaper.Upper

section Finite

variable {α : Type*} [Fintype α]

/-- The scalar exponential inequality used in `eq:omd-log-moment`. -/
theorem exp_neg_le_one_sub_add_two_sq {u : ℝ} (hu : |u| ≤ 1 / 4) :
    Real.exp (-u) ≤ 1 - u + 2 * u ^ 2 := by
  have hrem := Real.abs_exp_sub_one_sub_id_le (x := -u)
    (by rw [abs_neg]; linarith : |-u| ≤ 1)
  have h := (abs_le.mp hrem).2
  nlinarith [sq_nonneg u]

/-- The positive exponential normalizer is bounded by the actual quadratic
moment polynomial. -/
theorem mwNormalizer_le_quadratic (p z : α → ℝ) (eta : ℝ)
    (hp : ∀ x, 0 ≤ p x) (hpsum : ∑ x, p x = 1)
    (hbound : ∀ x, |eta * z x| ≤ 1 / 4) :
    mwNormalizer p z eta ≤ 1 - eta * finiteExpectation p z +
      2 * eta ^ 2 * finiteExpectation p (fun x => (z x) ^ 2) := by
  classical
  calc
    mwNormalizer p z eta ≤ ∑ x, p x * (1 - eta * z x + 2 * (eta * z x) ^ 2) := by
      apply Finset.sum_le_sum
      intro x _
      exact mul_le_mul_of_nonneg_left
        (by simpa only [neg_mul] using exp_neg_le_one_sub_add_two_sq (hbound x)) (hp x)
    _ = _ := by
      have heq (x : α) : p x * (1 - eta * z x + 2 * (eta * z x) ^ 2) =
          p x - eta * (p x * z x) + 2 * eta ^ 2 * (p x * (z x) ^ 2) := by ring
      simp_rw [heq, Finset.sum_add_distrib, Finset.sum_sub_distrib, ← Finset.mul_sum,
        hpsum]
      rfl

/-- First line of `eq:omd-log-moment`: logarithmic monotonicity, with positivity
of the polynomial obtained from the strictly positive exponential moment. -/
theorem log_mwNormalizer_le_log_quadratic (p z : α → ℝ) (eta : ℝ)
    (hp : ∀ x, 0 < p x) (hpsum : ∑ x, p x = 1)
    (hbound : ∀ x, |eta * z x| ≤ 1 / 4) :
    Real.log (mwNormalizer p z eta) ≤ Real.log (1 - eta * finiteExpectation p z +
      2 * eta ^ 2 * finiteExpectation p (fun x => (z x) ^ 2)) :=
  Real.log_le_log (mwNormalizer_pos p z eta hp hpsum)
    (mwNormalizer_le_quadratic p z eta (fun x => (hp x).le) hpsum hbound)

/-- The second line, completing `eq:omd-log-moment`. -/
theorem log_mwNormalizer_le (p z : α → ℝ) (eta : ℝ)
    (hp : ∀ x, 0 < p x) (hpsum : ∑ x, p x = 1)
    (hbound : ∀ x, |eta * z x| ≤ 1 / 4) :
    Real.log (mwNormalizer p z eta) ≤ -eta * finiteExpectation p z +
      2 * eta ^ 2 * finiteExpectation p (fun x => (z x) ^ 2) := by
  have hpoly := (mwNormalizer_pos p z eta hp hpsum).trans_le
    (mwNormalizer_le_quadratic p z eta (fun x => (hp x).le) hpsum hbound)
  have hlog := Real.log_le_sub_one_of_pos hpoly
  have hmono := log_mwNormalizer_le_log_quadratic p z eta hp hpsum hbound
  linarith

/-- All three steps of `eq:omd-kl-update`: the assumed approximate projection,
proved nonnegativity of its subtracted KL, and the exact update identity. -/
theorem omd_kl_update (q p r z : α → ℝ) (eta eps : ℝ)
    (hqsum : ∑ x, q x = 1) (hp : ∀ x, 0 < p x) (hpsum : ∑ x, p x = 1)
    (hr : ∀ x, 0 < r x) (hrsum : ∑ x, r x = 1)
    (hprojection : finiteKL q r ≤ finiteKL q (mwUpdate p z eta) -
      finiteKL r (mwUpdate p z eta) + eps) :
    finiteKL q r ≤ finiteKL q p + eta * finiteExpectation q z +
      Real.log (mwNormalizer p z eta) + eps := by
  have hnonneg := finiteKL_nonneg r (mwUpdate p z eta) (fun x => (hr x).le) hrsum
    (mwUpdate_pos p z eta hp hpsum) (sum_mwUpdate p z eta hp hpsum)
  calc
    finiteKL q r ≤ finiteKL q (mwUpdate p z eta) + eps := by linarith
    _ = _ := by rw [finiteKL_mwUpdate q p z eta hqsum hp hpsum]

/-- The first rearrangement in `eq:omd-one-step`, before bounding the log moment. -/
theorem omd_one_step_before_logMoment (q p r z : α → ℝ) (eta eps : ℝ)
    (hqsum : ∑ x, q x = 1) (hp : ∀ x, 0 < p x) (hpsum : ∑ x, p x = 1)
    (hr : ∀ x, 0 < r x) (hrsum : ∑ x, r x = 1)
    (hprojection : finiteKL q r ≤ finiteKL q (mwUpdate p z eta) -
      finiteKL r (mwUpdate p z eta) + eps) :
    eta * (finiteExpectation p z - finiteExpectation q z) ≤
      finiteKL q p - finiteKL q r + eta * finiteExpectation p z +
        Real.log (mwNormalizer p z eta) + eps := by
  have h := omd_kl_update q p r z eta eps hqsum hp hpsum hr hrsum hprojection
  linarith

/-- The second rearrangement, completing `eq:omd-one-step`. -/
theorem omd_one_step (q p r z : α → ℝ) (eta eps : ℝ)
    (hqsum : ∑ x, q x = 1) (hp : ∀ x, 0 < p x) (hpsum : ∑ x, p x = 1)
    (hr : ∀ x, 0 < r x) (hrsum : ∑ x, r x = 1)
    (hbound : ∀ x, |eta * z x| ≤ 1 / 4)
    (hprojection : finiteKL q r ≤ finiteKL q (mwUpdate p z eta) -
      finiteKL r (mwUpdate p z eta) + eps) :
    eta * (finiteExpectation p z - finiteExpectation q z) ≤
      finiteKL q p - finiteKL q r +
        2 * eta ^ 2 * finiteExpectation p (fun x => (z x) ^ 2) + eps := by
  have hstep := omd_one_step_before_logMoment q p r z eta eps
    hqsum hp hpsum hr hrsum hprojection
  have hlog := log_mwNormalizer_le p z eta hp hpsum hbound
  linarith

/-- The exact telescoping identity for the KL terms, with zero-based time. -/
theorem finiteKL_telescoping (q : α → ℝ) (p : ℕ → α → ℝ) (T : ℕ) :
    ∑ t ∈ Finset.range T, (finiteKL q (p t) - finiteKL q (p (t + 1))) =
      finiteKL q (p 0) - finiteKL q (p T) := by
  exact Finset.sum_range_sub' (fun t => finiteKL q (p t)) T

/-- First final display in the manuscript: retain the terminal KL and total
projection error instead of dropping them prematurely. -/
theorem omd_stability_with_error (q : α → ℝ) (p z : ℕ → α → ℝ) (T : ℕ)
    (eta eps : ℝ) (heta : 0 < eta) (hqsum : ∑ x, q x = 1)
    (hp : ∀ t ≤ T, ∀ x, 0 < p t x) (hpsum : ∀ t ≤ T, ∑ x, p t x = 1)
    (hbound : ∀ t < T, ∀ x, |eta * z t x| ≤ 1 / 4)
    (hprojection : ∀ t < T, finiteKL q (p (t + 1)) ≤
      finiteKL q (mwUpdate (p t) (z t) eta) -
        finiteKL (p (t + 1)) (mwUpdate (p t) (z t) eta) + eps) :
    (∑ t ∈ Finset.range T, (finiteExpectation (p t) (z t) - finiteExpectation q (z t))) ≤
      (finiteKL q (p 0) - finiteKL q (p T)) / eta +
        2 * eta * (∑ t ∈ Finset.range T,
          finiteExpectation (p t) (fun x => (z t x) ^ 2)) + (T : ℝ) * eps / eta := by
  classical
  have h := Finset.sum_le_sum (fun t (ht : t ∈ Finset.range T) =>
    omd_one_step q (p t) (p (t + 1)) (z t) eta eps hqsum
      (hp t (Nat.le_of_lt (Finset.mem_range.mp ht)))
      (hpsum t (Nat.le_of_lt (Finset.mem_range.mp ht)))
      (hp (t + 1) (Nat.succ_le_of_lt (Finset.mem_range.mp ht)))
      (hpsum (t + 1) (Nat.succ_le_of_lt (Finset.mem_range.mp ht)))
      (hbound t (Finset.mem_range.mp ht)) (hprojection t (Finset.mem_range.mp ht)))
  simp only [← Finset.mul_sum, Finset.sum_add_distrib,
    finiteKL_telescoping, Finset.sum_const, Finset.card_range, nsmul_eq_mul] at h
  have hdiv := div_le_div_of_nonneg_right h heta.le
  have hn : eta ≠ 0 := heta.ne'
  convert! hdiv using 1 <;> field_simp

/-- Lemma 4's bound, conditional precisely on the per-round increment and
approximate-projection properties.  It permits zero comparator probabilities. -/
theorem omd_stability (q : α → ℝ) (p z : ℕ → α → ℝ) (T : ℕ)
    (hT : 0 < T) (eta : ℝ) (heta : 0 < eta)
    (hq : ∀ x, 0 ≤ q x) (hqsum : ∑ x, q x = 1)
    (hp : ∀ t ≤ T, ∀ x, 0 < p t x) (hpsum : ∀ t ≤ T, ∑ x, p t x = 1)
    (hbound : ∀ t < T, ∀ x, |eta * z t x| ≤ 1 / 4)
    (hprojection : ∀ t < T, finiteKL q (p (t + 1)) ≤
      finiteKL q (mwUpdate (p t) (z t) eta) -
        finiteKL (p (t + 1)) (mwUpdate (p t) (z t) eta) + eta / (T : ℝ)) :
    (∑ t ∈ Finset.range T, (finiteExpectation (p t) (z t) - finiteExpectation q (z t))) ≤
      finiteKL q (p 0) / eta + 1 +
        2 * eta * (∑ t ∈ Finset.range T,
          finiteExpectation (p t) (fun x => (z t x) ^ 2)) := by
  have h := omd_stability_with_error q p z T eta (eta / (T : ℝ)) heta hqsum
    hp hpsum hbound hprojection
  have hnonneg := finiteKL_nonneg q (p T) hq hqsum (hp T le_rfl) (hpsum T le_rfl)
  have hdrop := div_le_div_of_nonneg_right
    (sub_le_self (finiteKL q (p 0)) hnonneg) heta.le
  have herror : (T : ℝ) * (eta / (T : ℝ)) / eta = 1 := by
    have hn : eta ≠ 0 := heta.ne'
    have ht : (T : ℝ) ≠ 0 := by exact_mod_cast hT.ne'
    field_simp
  rw [herror] at h
  linarith

/-- Exact equivalence between the internal zero-based sum and manuscript indexing. -/
theorem sum_Icc_one_eq_sum_range_shift (f : ℕ → ℝ) (T : ℕ) :
    (∑ t ∈ Finset.Icc 1 T, f t) = ∑ t ∈ Finset.range T, f (t + 1) := by
  rw [← Finset.Ico_add_one_right_eq_Icc, Finset.sum_Ico_eq_sum_range]
  simp only [Nat.add_sub_cancel, Nat.add_comm]

/-- Same stability theorem with exactly the manuscript's indices: the initial
law is `p 1`, updates run from `1` to `T`, and the terminal law is `p (T+1)`. -/
theorem omd_stability_one_based (q : α → ℝ) (p z : ℕ → α → ℝ) (T : ℕ)
    (hT : 0 < T) (eta : ℝ) (heta : 0 < eta)
    (hq : ∀ x, 0 ≤ q x) (hqsum : ∑ x, q x = 1)
    (hp : ∀ t, 1 ≤ t → t ≤ T + 1 → ∀ x, 0 < p t x)
    (hpsum : ∀ t, 1 ≤ t → t ≤ T + 1 → ∑ x, p t x = 1)
    (hbound : ∀ t, 1 ≤ t → t ≤ T → ∀ x, |eta * z t x| ≤ 1 / 4)
    (hprojection : ∀ t, 1 ≤ t → t ≤ T → finiteKL q (p (t + 1)) ≤
      finiteKL q (mwUpdate (p t) (z t) eta) -
        finiteKL (p (t + 1)) (mwUpdate (p t) (z t) eta) + eta / (T : ℝ)) :
    (∑ t ∈ Finset.Icc 1 T, (finiteExpectation (p t) (z t) - finiteExpectation q (z t))) ≤
      finiteKL q (p 1) / eta + 1 +
        2 * eta * (∑ t ∈ Finset.Icc 1 T,
          finiteExpectation (p t) (fun x => (z t x) ^ 2)) := by
  have h := omd_stability q (fun t => p (t + 1)) (fun t => z (t + 1)) T hT
    eta heta hq hqsum
    (fun t ht => hp (t + 1) (by omega) (by omega))
    (fun t ht => hpsum (t + 1) (by omega) (by omega))
    (fun t ht => hbound (t + 1) (by omega) (by omega))
    (fun t ht => hprojection (t + 1) (by omega) (by omega))
  simpa only [sum_Icc_one_eq_sum_range_shift, Nat.zero_add] using h

end Finite

section Weighted

variable {d m : ℕ}

theorem actionLoss_sub_smul (a : Action d m) (theta v : Fin d → ℝ) (eta : ℝ) :
    actionLoss a (theta - eta • v) = actionLoss a theta - eta * actionLoss a v := by
  classical
  simp only [actionLoss_eq_finset_sum, Pi.sub_apply, Pi.smul_apply, smul_eq_mul,
    Finset.sum_sub_distrib, Finset.mul_sum]

/-- The normalizing constants transform exactly under a linear loss update. -/
theorem mwNormalizer_weightedLaw (theta v : Fin d → ℝ) (eta : ℝ) :
    mwNormalizer (weightedLaw (m := m) theta) (fun a => actionLoss a v) eta =
      partition (m := m) (theta - eta • v) / partition (m := m) theta := by
  classical
  have hexp (a : Action d m) : Real.exp (actionLoss a (theta - eta • v)) =
      Real.exp (actionLoss a theta) * Real.exp (-eta * actionLoss a v) := by
    rw [actionLoss_sub_smul, sub_eq_add_neg, Real.exp_add]
    simp only [neg_mul]
  change (∑ a : Action d m,
    (Real.exp (actionLoss a theta) / partition (m := m) theta) *
      Real.exp (-eta * actionLoss a v)) =
    (∑ a : Action d m, Real.exp (actionLoss a (theta - eta • v))) /
      partition (m := m) theta
  rw [Finset.sum_div]
  apply Finset.sum_congr rfl
  intro a _
  rw [hexp]
  ring

/-- Manuscript's identification of the actual normalized exponential update
with `p_(theta - eta v)`; this is proved, not assumed as an update certificate. -/
theorem mwUpdate_weightedLaw (theta v : Fin d → ℝ) (eta : ℝ) (hmd : m ≤ d) :
    mwUpdate (weightedLaw (m := m) theta) (fun a => actionLoss a v) eta =
      weightedLaw (m := m) (theta - eta • v) := by
  have hpart := (partition_pos (m := m) theta hmd).ne'
  have hnew := (partition_pos (m := m) (theta - eta • v) hmd).ne'
  funext a
  rw [mwUpdate, mwNormalizer_weightedLaw]
  change (Real.exp (actionLoss a theta) / partition (m := m) theta) *
    Real.exp (-eta * actionLoss a v) /
    (partition (m := m) (theta - eta • v) / partition (m := m) theta) =
    Real.exp (actionLoss a (theta - eta • v)) / partition (m := m) (theta - eta • v)
  rw [actionLoss_sub_smul, Real.exp_sub, neg_mul, Real.exp_neg]
  field_simp

/-- The actual vector whose action losses are the surrogate `Z_t`. -/
def surrogateVector (theta ell : Fin d → ℝ) (eta : ℝ) (a : Action d m) : Fin d → ℝ :=
  estimateVector theta a ell - eta • correction (m : ℝ) (weightedMarginal (m := m) theta)

theorem surrogate_eq_actionLoss_surrogateVector
    (theta ell : Fin d → ℝ) (eta : ℝ) (a b : Action d m) :
    surrogate theta ell eta a b = actionLoss b (surrogateVector theta ell eta a) := by
  rw [surrogateVector, actionLoss_sub_smul, surrogate, estimateScalar,
    dotProduct_comm, dot_indicator_eq_actionLoss]

theorem mwUpdate_surrogate_weightedLaw
    (theta ell : Fin d → ℝ) (eta : ℝ) (hmd : m ≤ d) (a : Action d m) :
    mwUpdate (weightedLaw (m := m) theta) (surrogate theta ell eta a) eta =
      weightedLaw (m := m) (theta - eta • surrogateVector theta ell eta a) := by
  have hfun : surrogate theta ell eta a =
      fun b => actionLoss b (surrogateVector theta ell eta a) :=
    funext (surrogate_eq_actionLoss_surrogateVector theta ell eta a)
  rw [hfun, mwUpdate_weightedLaw theta _ eta hmd]

/-- Pathwise Lemma 4 for the concrete weighted law and estimator.  Lemma 3 is
invoked for its increment bound.  The only remaining algorithmic input is the
actual projection inequality, to be supplied by Proposition 1. -/
theorem weighted_surrogate_omd_stability_of_projection
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
            (theta t - eta • surrogateVector (theta t) (ell t) eta (a t))) +
        eta / (T : ℝ)) :
    (∑ t ∈ Finset.Icc 1 T,
      (finiteExpectation (weightedLaw (m := m) (theta t))
          (surrogate (theta t) (ell t) eta (a t)) -
        finiteExpectation q (surrogate (theta t) (ell t) eta (a t)))) ≤
      finiteKL q (weightedLaw (m := m) (theta 1)) / eta + 1 +
        2 * eta * (∑ t ∈ Finset.Icc 1 T,
          finiteExpectation (weightedLaw (m := m) (theta t))
            (fun b => (surrogate (theta t) (ell t) eta (a t) b) ^ 2)) := by
  apply omd_stability_one_based q (fun t => weightedLaw (m := m) (theta t))
    (fun t => surrogate (theta t) (ell t) eta (a t)) T hT eta heta hq hqsum
  · intro t _ _
    exact weightedLaw_pos (theta t) (by omega)
  · intro t _ _
    exact sum_weightedLaw (theta t) (by omega)
  · intro t htlo hthi b
    rw [abs_mul, abs_of_pos heta]
    exact bounded_increments (theta t) (ell t) hmpos hmtop heta hsmall
      (hloss t htlo hthi) (hlo t htlo hthi) (hhi t htlo hthi) (a t) b
  · intro t htlo hthi
    simpa only [mwUpdate_surrogate_weightedLaw (theta t) (ell t) eta
      (show m ≤ d by omega) (a t)] using hprojection t htlo hthi

end Weighted

end MsetsPaper.Upper
