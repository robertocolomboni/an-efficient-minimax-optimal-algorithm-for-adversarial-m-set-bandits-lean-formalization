import CoefficientOne.PseudoinverseIdentity
import CoefficientOne.InverseOrder

/-!
# Optimality of the coefficient-one pseudoinverse bound

This is the optimality argument in Appendix E.4. A uniform positive
coefficient `c < 1` for the inverse inequality would imply the covariance
comparison with coefficient `c⁻¹ > 1`, contradicting the existing sharpness
family. Nonpositive coefficients are excluded by positive inverse energy.
-/

open scoped BigOperators
open Matrix EffectiveResistance

namespace CoefficientOne

noncomputable section

variable {n : ℕ}

/-- The inverse-order step applied to the actual fixed-rank covariance. -/
theorem externalField_inverse_bound_implies_comparison
    (w : Fin n → ℝ) (hw : ∀ i, 0 < w i) (m : ℕ)
    (hmpos : 1 ≤ m) (hmtop : m ≤ n - 1)
    (c : ℝ) (hc : 0 < c)
    (hbound : ∀ y : Fin n → ℝ, IsZeroSum y →
      quadraticForm (externalFieldPseudoinverse w hw m hmpos
        (by simpa using hmtop)) y ≤ c * ∑ i, y i ^ 2 / covarianceVariance w m i) :
    LoewnerLE (c⁻¹ • comparisonMatrix (covarianceVariance w m))
      (covarianceMatrix w m) := by
  apply inverse_diagonal_bound_implies_comparison
    (covarianceMatrix w m)
    (externalFieldPseudoinverse w hw m hmpos (by simpa using hmtop))
    (covarianceVariance w m)
    (covarianceVariance_pos w hw m hmpos (by simpa using hmtop))
    (ne_of_gt (covarianceVariance_sum_pos w hw m hmpos (by simpa using hmtop)))
    (covariance_isSymm w m)
  · intro x
    exact covariance_quadratic_nonnegative w hw
      (by simpa using (hmtop.trans (Nat.sub_le n 1))) x
  · exact externalField_pseudoinverse_solves_zeroSum w hw m hmpos
      (by simpa using hmtop)
  · exact hc
  · exact hbound

/-- Every coefficient below one fails for a positive three-coordinate,
rank-one law and a nonzero zero-sum demand. -/
theorem externalField_pseudoinverse_constant_one_is_sharp
    (c : ℝ) (hc : c < 1) :
    ∃ (w : Fin 3 → ℝ) (hw : ∀ i, 0 < w i) (y : Fin 3 → ℝ),
      IsZeroSum y ∧ y ≠ 0 ∧
        c * (∑ i, y i ^ 2 / covarianceVariance w 1 i) <
          quadraticForm (externalFieldPseudoinverse w hw 1 (by decide) (by decide)) y := by
  classical
  by_cases hcpos : 0 < c
  · have hinv : 1 < c⁻¹ := (one_lt_inv₀ hcpos).mpr hc
    obtain ⟨w, hw, hfail⟩ := covariance_comparison_constant_one_is_sharp c⁻¹ hinv
    have hnot : ¬ ∀ y : Fin 3 → ℝ, IsZeroSum y →
        quadraticForm (externalFieldPseudoinverse w hw 1 (by decide) (by decide)) y ≤
          c * ∑ i, y i ^ 2 / covarianceVariance w 1 i := by
      intro hbound
      exact hfail (externalField_inverse_bound_implies_comparison
        w hw 1 (by decide) (by decide) c hcpos hbound)
    push Not at hnot
    obtain ⟨y, hy, hlt⟩ := hnot
    refine ⟨w, hw, y, hy, ?_, hlt⟩
    intro hz
    subst y
    simp [quadraticForm] at hlt
  · have hcnonpos : c ≤ 0 := le_of_not_gt hcpos
    let w : Fin 3 → ℝ := fun _ => 1
    have hw : ∀ i, 0 < w i := by intro i; norm_num [w]
    let y : Fin 3 → ℝ := pairDemand 0 1
    have hy : IsZeroSum y := pairDemand_zeroSum (by decide : (0 : Fin 3) ≠ 1)
    have hy0 : y ≠ 0 := by
      intro hz
      have h := congrFun hz 0
      norm_num [y, pairDemand] at h
    have hpos := externalField_pseudoinverse_quadratic_pos
      w hw 1 (by decide) (by decide) y hy hy0
    have hnonneg : 0 ≤ ∑ i, y i ^ 2 / covarianceVariance w 1 i := by
      apply Finset.sum_nonneg
      intro i hi
      exact div_nonneg (sq_nonneg _) (covarianceVariance_pos
        w hw 1 (by decide) (by decide) i).le
    exact ⟨w, hw, y, hy, hy0, lt_of_le_of_lt
      (mul_nonpos_of_nonpos_of_nonneg hcnonpos hnonneg) hpos⟩

/-- Coefficient one is valid uniformly and no smaller coefficient is. -/
theorem externalField_pseudoinverse_coefficient_one_optimal :
    (∀ (n : ℕ) (w : Fin n → ℝ) (hw : ∀ i, 0 < w i)
      (m : ℕ) (hmpos : 1 ≤ m) (hmtop : m ≤ n - 1)
      (y : Fin n → ℝ), IsZeroSum y →
      quadraticForm (externalFieldPseudoinverse w hw m hmpos
        (by simpa using hmtop)) y ≤ ∑ i, y i ^ 2 / covarianceVariance w m i) ∧
    (∀ c : ℝ, c < 1 →
      ∃ (w : Fin 3 → ℝ) (hw : ∀ i, 0 < w i) (y : Fin 3 → ℝ),
        IsZeroSum y ∧ y ≠ 0 ∧
          c * (∑ i, y i ^ 2 / covarianceVariance w 1 i) <
            quadraticForm (externalFieldPseudoinverse w hw 1 (by decide) (by decide)) y) := by
  exact ⟨fun _ w hw m hmpos hmtop y hy =>
    externalField_pseudoinverse_bound w hw m hmpos hmtop y hy,
    externalField_pseudoinverse_constant_one_is_sharp⟩

end

end CoefficientOne
