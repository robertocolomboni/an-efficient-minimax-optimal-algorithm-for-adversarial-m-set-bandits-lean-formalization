import CoefficientOne.UniformResistance
import CoefficientOne.Pseudoinverse

/-!
# Strictness and optimality of the effective-resistance bound

The strict estimate is the specialization of the strict pseudoinverse
corollary to a nonzero pair demand. Optimality uses the separate uniform-law
family, rather than optimality on arbitrary zero-sum vectors.
-/

open Matrix EffectiveResistance

namespace CoefficientOne

noncomputable section

theorem externalField_effectiveResistance_bound_strict
    {n : ℕ} (w : Fin n → ℝ) (hw : ∀ i, 0 < w i) (m : ℕ)
    (hmpos : 1 ≤ m) (hmtop : m ≤ n - 1)
    (i j : Fin n) (hij : i ≠ j) :
    quadraticForm (externalFieldPseudoinverse w hw m hmpos
      (by simpa using hmtop)) (pairDemand i j) <
      1 / covarianceMatrix w m i i + 1 / covarianceMatrix w m j j := by
  have h := externalField_pseudoinverse_bound_strict w hw m hmpos hmtop
    (pairDemand i j) (pairDemand_zeroSum hij) (pairDemand_ne_zero i j hij)
  rw [pairDemand_inverse_diagonal_sum _ i j hij] at h
  exact h

/-- Validity of coefficient one together with a genuine pair-demand
counterexample to every smaller universal coefficient. -/
theorem externalField_effectiveResistance_coefficient_one_optimal :
    (∀ (n : ℕ) (w : Fin n → ℝ) (hw : ∀ i, 0 < w i)
      (m : ℕ) (hmpos : 1 ≤ m) (hmtop : m ≤ n - 1)
      (i j : Fin n), i ≠ j →
      quadraticForm (externalFieldPseudoinverse w hw m hmpos
        (by simpa using hmtop)) (pairDemand i j) ≤
        1 / covarianceMatrix w m i i + 1 / covarianceMatrix w m j j) ∧
    (∀ c : ℝ, c < 1 →
      ∃ (n : ℕ) (hn : 2 ≤ n) (w : Fin n → ℝ) (hw : ∀ i, 0 < w i)
        (i j : Fin n), i ≠ j ∧
        c * (1 / covarianceMatrix w 1 i i + 1 / covarianceMatrix w 1 j j) <
          quadraticForm (externalFieldPseudoinverse w hw 1 (by omega)
            (by simpa using (show 1 ≤ n - 1 by omega))) (pairDemand i j)) := by
  exact ⟨fun _ w hw m hmpos hmtop i j hij =>
      externalField_effectiveResistance_from_pseudoinverse w hw m hmpos hmtop i j hij,
    externalField_effectiveResistance_constant_one_is_sharp⟩

end

end CoefficientOne
