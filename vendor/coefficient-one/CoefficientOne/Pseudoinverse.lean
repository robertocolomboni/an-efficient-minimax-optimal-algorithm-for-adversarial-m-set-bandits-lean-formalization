import CoefficientOne.PseudoinverseIdentity
import CoefficientOne.SpectralDefect

/-!
# Strictness of the coefficient-one pseudoinverse bound

The last term in the manuscript's two-term identity is strictly positive:
the canonical potential is nonzero and zero-sum, hence nonconstant.
-/

noncomputable section

open Matrix EffectiveResistance
open scoped BigOperators

namespace CoefficientOne

variable {n : ℕ}

/-- A nonzero zero-sum vector cannot be constant. -/
theorem pseudoinverse_zeroSum_nonconstant (x : Fin n → ℝ)
    (hx : IsZeroSum x) (hx0 : x ≠ 0) : ¬ ∀ i j, x i = x j := by
  intro hc
  apply hx0
  ext i
  have hni : 0 < n := Nat.lt_of_le_of_lt (Nat.zero_le i.val) i.isLt
  have hn : (n : ℝ) ≠ 0 := by exact_mod_cast (ne_of_gt hni)
  have hsum : (n : ℝ) * x i = 0 := by
    calc
      _ = ∑ j : Fin n, x i := by simp
      _ = ∑ j : Fin n, x j := Finset.sum_congr rfl (fun j _ => hc i j)
      _ = 0 := hx
  exact (mul_eq_zero.mp hsum).resolve_left hn

/-- Corollary 3.3, strict inequality for every nonzero zero-sum demand. -/
theorem externalField_pseudoinverse_bound_strict
    (w : Fin n → ℝ) (hw : ∀ i, 0 < w i) (m : ℕ)
    (hmpos : 1 ≤ m) (hmtop : m ≤ n - 1)
    (y : Fin n → ℝ) (hy : IsZeroSum y) (hy0 : y ≠ 0) :
    quadraticForm (externalFieldPseudoinverse w hw m hmpos
      (by simpa using hmtop)) y < ∑ i, y i ^ 2 / covarianceVariance w m i := by
  let h := externalFieldPseudoinverse w hw m hmpos (by simpa using hmtop) *ᵥ y
  have hzero : IsZeroSum h := externalField_pseudoinverse_mulVec_zeroSum
    w hw m hmpos (by simpa using hmtop) y
  have hne : h ≠ 0 := externalField_pseudoinverse_mulVec_ne_zero
    w hw m hmpos (by simpa using hmtop) y hy hy0
  have hnonconst := pseudoinverse_zeroSum_nonconstant h hzero hne
  have hid := externalField_pseudoinverse_gap_identity w hw m hmpos hmtop y hy
  have hv := covarianceVariance_pos w hw m hmpos (by simpa using hmtop)
  have hV := covarianceVariance_sum_pos w hw m hmpos (by simpa using hmtop)
  have hfirst := pseudoinverse_comparison_quadratic_nonneg (covarianceVariance w m)
    ((fun i => y i / covarianceVariance w m i) - h)
    (fun i => (hv i).le) (ne_of_gt hV)
  have hsecond := covariance_defect_quadratic_pos_from_spectrum w hw m hmpos hmtop h hnonconst
  change (∑ i, y i ^ 2 / covarianceVariance w m i) -
    quadraticForm (externalFieldPseudoinverse w hw m hmpos (by simpa using hmtop)) y =
      quadraticForm (comparisonMatrix (covarianceVariance w m))
        ((fun i => y i / covarianceVariance w m i) - h) +
      quadraticForm (covarianceMatrix w m - comparisonMatrix (covarianceVariance w m)) h at hid
  linarith

end CoefficientOne
