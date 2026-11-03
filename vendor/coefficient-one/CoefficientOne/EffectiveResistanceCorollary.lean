import CoefficientOne.PseudoinverseIdentity

/-!
# Effective resistance from the coefficient-one pseudoinverse inequality

This module implements the new proof of Corollary 3.2 in Appendix E.3:
specialize the pseudoinverse inequality to the zero-sum demand `e_i - e_j`.
The earlier effective-resistance bound is not used by this derivation.
-/

open scoped BigOperators
open Matrix EffectiveResistance

namespace CoefficientOne

noncomputable section

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

theorem pairDemand_ne_zero (i j : ι) (hij : i ≠ j) :
    pairDemand i j ≠ 0 := by
  intro hzero
  have h := congrFun hzero i
  simp [pairDemand_apply_left hij] at h

/-- Evaluating the diagonal inverse quadratic form at `e_i - e_j`. -/
theorem pairDemand_inverse_diagonal_sum (v : ι → ℝ)
    (i j : ι) (hij : i ≠ j) :
    (∑ k, (pairDemand i j k) ^ 2 / v k) = 1 / v i + 1 / v j := by
  have hterm (k : ι) : (pairDemand i j k) ^ 2 / v k =
      (if k = i then 1 / v i else 0) + (if k = j then 1 / v j else 0) := by
    by_cases hki : k = i
    · subst k
      simp [pairDemand, hij]
    · by_cases hkj : k = j
      · subst k
        simp [pairDemand, Ne.symm hij]
      · simp [pairDemand, hki, hkj]
  simp_rw [hterm]
  rw [Finset.sum_add_distrib]
  simp

/-- Corollary 3.2, derived from Corollary 3.3 exactly as in Appendix E.3.
This theorem does not invoke the earlier effective-resistance theorem. -/
theorem externalField_effectiveResistance_from_pseudoinverse
    {n : ℕ} (w : Fin n → ℝ) (hw : ∀ i, 0 < w i) (m : ℕ)
    (hmpos : 1 ≤ m) (hmtop : m ≤ n - 1)
    (i j : Fin n) (hij : i ≠ j) :
    quadraticForm (externalFieldPseudoinverse w hw m hmpos
      (by simpa using hmtop)) (pairDemand i j) ≤
      1 / covarianceMatrix w m i i + 1 / covarianceMatrix w m j j := by
  have h := externalField_pseudoinverse_bound w hw m hmpos hmtop
    (pairDemand i j) (pairDemand_zeroSum hij)
  rw [pairDemand_inverse_diagonal_sum _ i j hij] at h
  exact h

end

end CoefficientOne
