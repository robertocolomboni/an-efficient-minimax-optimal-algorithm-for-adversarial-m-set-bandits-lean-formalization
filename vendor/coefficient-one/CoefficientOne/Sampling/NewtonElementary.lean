import CoefficientOne.Sampling.NewtonRolle

/-!
# Newton's inequality for the elementary symmetric coefficients

The generating polynomial and its successive derivatives are the ones in
Appendix E.2. The normalized inequality is obtained from `realSplit_newton_at`.
-/

open scoped BigOperators
open Polynomial EffectiveResistance

namespace CoefficientOne.Sampling

noncomputable section

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

def samplingGeneratingPolynomial (w : ι → ℝ) (R : Finset ι) : ℝ[X] :=
  ∏ i ∈ R, (C (w i) * X + C 1)

theorem samplingGeneratingPolynomial_coeff (w : ι → ℝ) (R : Finset ι) (j : ℕ) :
    (samplingGeneratingPolynomial w R).coeff j = restrictedElementary w R j := by
  induction R using Finset.induction_on generalizing j with
  | empty =>
    cases j with
    | zero => simp [samplingGeneratingPolynomial]
    | succ j =>
      simp [samplingGeneratingPolynomial, restrictedElementary,
        Polynomial.coeff_one,
        Finset.powersetCard_eq_empty.mpr (show (∅ : Finset ι).card < j + 1 by simp)]
  | @insert i R hi ih =>
    rw [samplingGeneratingPolynomial, Finset.prod_insert hi]
    change ((C (w i) * X + C 1) * samplingGeneratingPolynomial w R).coeff j = _
    cases j with
    | zero => simp [Polynomial.coeff_mul, ih]
    | succ j =>
      rw [restrictedElementary_insert_succ w R i hi]
      simp only [add_mul, mul_assoc, Polynomial.coeff_add,
        Polynomial.coeff_C_mul, Polynomial.coeff_X_mul, one_mul, ih]
      ring

theorem samplingGeneratingPolynomial_splits (w : ι → ℝ) (R : Finset ι) :
    (samplingGeneratingPolynomial w R).Splits := by
  apply Polynomial.Splits.prod
  intro i _
  exact Polynomial.Splits.of_natDegree_le_one Polynomial.natDegree_linear_le

theorem samplingGeneratingPolynomial_natDegree (w : ι → ℝ) (hw : ∀ i, 0 < w i)
    (R : Finset ι) : (samplingGeneratingPolynomial w R).natDegree = R.card := by
  unfold samplingGeneratingPolynomial
  rw [Polynomial.natDegree_prod]
  · simp only [Polynomial.natDegree_linear (ne_of_gt (hw _)), Finset.sum_const,
      smul_eq_mul, mul_one]
  · intro i _
    exact Polynomial.ne_zero_of_natDegree_gt (n := 0)
      (by rw [Polynomial.natDegree_linear (hw i).ne']; norm_num)

theorem real_natDegree_iterated_derivative (p : ℝ[X]) (j : ℕ) :
    (Polynomial.derivative^[j] p).natDegree = p.natDegree - j := by
  induction j with
  | zero => simp
  | succ j ih =>
    rw [Function.iterate_succ_apply', Polynomial.natDegree_derivative, ih]
    omega

theorem samplingGeneratingPolynomial_iterated_eval_zero (w : ι → ℝ) (R : Finset ι)
    (j : ℕ) :
    (Polynomial.derivative^[j] (samplingGeneratingPolynomial w R)).eval 0 =
      (j.factorial : ℝ) * restrictedElementary w R j := by
  rw [← Polynomial.coeff_zero_eq_eval_zero, Polynomial.coeff_iterate_derivative]
  simp [samplingGeneratingPolynomial_coeff, Nat.descFactorial_self, nsmul_eq_mul]

/-- The normalized Newton inequality with all factorial factors cancelled.
Here `j+1` is the central elementary-symmetric index. -/
theorem restrictedElementary_newton_cross (w : ι → ℝ) (hw : ∀ i, 0 < w i)
    (R : Finset ι) (j : ℕ) (hj : j + 2 ≤ R.card) :
    ((j + 2 : ℕ) : ℝ) * (R.card - j : ℕ) *
        restrictedElementary w R j * restrictedElementary w R (j + 2) ≤
      ((j + 1 : ℕ) : ℝ) * ((R.card - j : ℕ) - (1 : ℝ)) *
        restrictedElementary w R (j + 1) ^ 2 := by
  let G := Polynomial.derivative^[j] (samplingGeneratingPolynomial w R)
  have hG : G.Splits := splits_iterated_derivative_by_rolle _
    (samplingGeneratingPolynomial_splits w R) j
  have hG0 : G.eval 0 ≠ 0 := by
    dsimp [G]
    rw [samplingGeneratingPolynomial_iterated_eval_zero]
    exact mul_ne_zero (by positivity) (restrictedElementary_pos w hw R j (by omega)).ne'
  have h := realSplit_newton_at G hG 0 hG0
  have hdeg : G.natDegree = R.card - j := by
    dsimp [G]
    rw [real_natDegree_iterated_derivative, samplingGeneratingPolynomial_natDegree w hw]
  have hd1 : G.derivative = Polynomial.derivative^[j + 1] (samplingGeneratingPolynomial w R) := by
    simp [G, Function.iterate_succ_apply']
  have hd2 : G.derivative.derivative =
      Polynomial.derivative^[j + 2] (samplingGeneratingPolynomial w R) := by
    rw [hd1]
    simp only [show j + 2 = (j + 1) + 1 by omega, Function.iterate_succ_apply']
  have he0 : G.eval 0 = (j.factorial : ℝ) * restrictedElementary w R j :=
    samplingGeneratingPolynomial_iterated_eval_zero w R j
  have he1 : G.derivative.eval 0 = ((j + 1).factorial : ℝ) * restrictedElementary w R (j + 1) := by
    rw [hd1]
    exact samplingGeneratingPolynomial_iterated_eval_zero w R (j + 1)
  have he2 : G.derivative.derivative.eval 0 = ((j + 2).factorial : ℝ) * restrictedElementary w R (j + 2) := by
    rw [hd2]
    exact samplingGeneratingPolynomial_iterated_eval_zero w R (j + 2)
  rw [hdeg, he0, he1, he2] at h
  have hfac1 : ((j + 1).factorial : ℝ) = (j + 1 : ℝ) * (j.factorial : ℝ) := by
    rw [Nat.factorial_succ]; push_cast; ring
  have hfac2 : ((j + 2).factorial : ℝ) =
      (j + 2 : ℝ) * (j + 1 : ℝ) * (j.factorial : ℝ) := by
    rw [show j + 2 = (j + 1) + 1 by omega, Nat.factorial_succ]
    push_cast
    rw [hfac1]
    ring
  rw [hfac1, hfac2] at h
  have hpos : 0 < (j + 1 : ℝ) * (j.factorial : ℝ) ^ 2 := by positivity
  apply (mul_le_mul_iff_right₀ hpos).mp
  convert! h using 1 <;> push_cast <;> ring

/-- The unnormalized log-concavity needed for quota monotonicity. -/
theorem restrictedElementary_logConcave (w : ι → ℝ) (hw : ∀ i, 0 < w i)
    (R : Finset ι) (j : ℕ) (hj : j + 2 ≤ R.card) :
    restrictedElementary w R j * restrictedElementary w R (j + 2) ≤
      restrictedElementary w R (j + 1) ^ 2 := by
  have h := restrictedElementary_newton_cross w hw R j hj
  have hm : (2 : ℝ) ≤ (R.card - j : ℕ) := by exact_mod_cast (show 2 ≤ R.card - j by omega)
  have he : 0 ≤ restrictedElementary w R j * restrictedElementary w R (j + 2) :=
    mul_nonneg (restrictedElementary_nonneg w (fun i => (hw i).le) R j)
      (restrictedElementary_nonneg w (fun i => (hw i).le) R (j + 2))
  have hpos : 0 < (j + 1 : ℝ) * ((R.card - j : ℕ) - (1 : ℝ)) :=
    mul_pos (by positivity) (by linarith)
  apply (mul_le_mul_iff_left₀ hpos).mp
  push_cast at h ⊢
  nlinarith [mul_nonneg (show 0 ≤ (j : ℝ) + (R.card - j : ℕ) + 1 by positivity) he]

/-- The displayed normalized Newton inequality, before discarding its factor. -/
theorem restrictedElementary_newton_normalized (w : ι → ℝ) (hw : ∀ i, 0 < w i)
    (R : Finset ι) (j : ℕ) (hj : j + 2 ≤ R.card) :
    (((j + 2 : ℕ) : ℝ) * (R.card - j : ℕ) /
      (((j + 1 : ℕ) : ℝ) * ((R.card - j : ℕ) - (1 : ℝ)))) *
      restrictedElementary w R j * restrictedElementary w R (j + 2) ≤
      restrictedElementary w R (j + 1) ^ 2 := by
  have hm : (2 : ℝ) ≤ (R.card - j : ℕ) := by exact_mod_cast (show 2 ≤ R.card - j by omega)
  have hp : 0 < ((j + 1 : ℕ) : ℝ) * ((R.card - j : ℕ) - (1 : ℝ)) :=
    mul_pos (by positivity) (by linarith)
  rw [div_mul_eq_mul_div, div_mul_eq_mul_div]
  apply (div_le_iff₀ hp).mpr
  simpa only [mul_comm (restrictedElementary w R (j + 1) ^ 2)] using
    restrictedElementary_newton_cross w hw R j hj

theorem sampling_derivative_coeff_nonneg (w : ι → ℝ) (hw : ∀ i, 0 < w i)
    (R : Finset ι) (j n : ℕ) :
    0 ≤ (Polynomial.derivative^[j] (samplingGeneratingPolynomial w R)).coeff n := by
  rw [Polynomial.coeff_iterate_derivative, samplingGeneratingPolynomial_coeff]
  exact nsmul_nonneg (restrictedElementary_nonneg w (fun i => (hw i).le) R (n + j)) _

theorem sampling_derivative_eval_pos_of_nonneg (w : ι → ℝ) (hw : ∀ i, 0 < w i)
    (R : Finset ι) (j : ℕ) (hj : j ≤ R.card) (x : ℝ) (hx : 0 ≤ x) :
    0 < (Polynomial.derivative^[j] (samplingGeneratingPolynomial w R)).eval x := by
  have h0 : 0 < (Polynomial.derivative^[j] (samplingGeneratingPolynomial w R)).coeff 0 := by
    rw [Polynomial.coeff_zero_eq_eval_zero, samplingGeneratingPolynomial_iterated_eval_zero]
    exact mul_pos (by positivity) (restrictedElementary_pos w hw R j hj)
  rw [Polynomial.eval_eq_sum_range]
  apply Finset.sum_pos'
  · intro n _
    exact mul_nonneg (sampling_derivative_coeff_nonneg w hw R j n) (pow_nonneg hx n)
  · exact ⟨0, by simp, by simpa using h0⟩

/-- The side claim in the Rolle paragraph: every derivative root is strictly
negative. Rolle supplies real splitting; positive coefficients exclude [0,∞). -/
theorem sampling_derivative_roots_neg (w : ι → ℝ) (hw : ∀ i, 0 < w i)
    (R : Finset ι) (j : ℕ) (hj : j ≤ R.card) (x : ℝ)
    (hx : x ∈ (Polynomial.derivative^[j] (samplingGeneratingPolynomial w R)).roots) : x < 0 := by
  by_contra hn
  have hp := sampling_derivative_eval_pos_of_nonneg w hw R j hj x (le_of_not_gt hn)
  have hz := (Polynomial.isRoot_of_mem_roots hx).eq_zero
  linarith

theorem sampling_derivative_card_roots (w : ι → ℝ) (hw : ∀ i, 0 < w i)
    (R : Finset ι) (j : ℕ) :
    (Polynomial.derivative^[j] (samplingGeneratingPolynomial w R)).roots.card = R.card - j := by
  rw [Polynomial.splits_iff_card_roots.mp
    (splits_iterated_derivative_by_rolle _ (samplingGeneratingPolynomial_splits w R) j),
    real_natDegree_iterated_derivative, samplingGeneratingPolynomial_natDegree w hw]

end
end CoefficientOne.Sampling
