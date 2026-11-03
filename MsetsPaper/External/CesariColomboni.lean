import MsetsPaper.External.WeightedLawBridge
import MsetsPaper.Upper.CovariancePseudoinverse
import CoefficientOne.PseudoinverseIdentity

/-!
# The verified Cesari--Colomboni pseudoinverse bound

This is Corollary 1.2's coefficient-one pseudoinverse bound, specialized to
positive exponential weights. It is proved from the spectral companion's
theorem after identifying the two concrete laws and their covariance matrices.

`C` must satisfy all four Moore--Penrose equations for the ACTUAL covariance.
The spectral companion proves these equations for its canonical inverse;
uniqueness identifies that inverse with `C`. Thus this interface has no external
mathematical axiom, and its original statement is preserved.
-/

noncomputable section

open Matrix MsetsPaper.Upper
open scoped BigOperators

namespace MsetsPaper.External

theorem cesariColomboni {d m : ℕ} (theta : Fin d → ℝ)
    (hmpos : 1 ≤ m) (hmtop : m ≤ d - 1)
    (C : Matrix (Fin d) (Fin d) ℝ)
    (hC : IsMoorePenroseInverse (covariance (weightedLaw (m := m) theta)) C)
    (y : Fin d → ℝ) (hy : ∑ i, y i = 0) :
    y ⬝ᵥ (C *ᵥ y) ≤
      ∑ i, (y i) ^ 2 /
        (weightedMarginal (m := m) theta i * (1 - weightedMarginal (m := m) theta i)) := by
  let w : Fin d → ℝ := fun i => Real.exp (theta i)
  have hw : ∀ i, 0 < w i := fun i => Real.exp_pos (theta i)
  have htop : m ≤ Fintype.card (Fin d) - 1 := by simpa using hmtop
  have hcov : covariance (weightedLaw (m := m) theta) =
      EffectiveResistance.covarianceMatrix w m :=
    covariance_weightedLaw_eq theta (by omega)
  have hcanonical : IsMoorePenroseInverse (covariance (weightedLaw (m := m) theta))
      (EffectiveResistance.externalFieldPseudoinverse w hw m hmpos htop) := by
    rw [hcov]
    exact EffectiveResistance.externalFieldPseudoinverse_isMoorePenroseInverse
      w hw m hmpos htop
  have hCeq := hC.unique hcanonical
  rw [hCeq]
  have hbound := CoefficientOne.externalField_pseudoinverse_bound
    w hw m hmpos hmtop y hy
  simpa only [EffectiveResistance.quadraticForm, w,
    covarianceVariance_exp_eq theta (show m ≤ d by omega)] using hbound

end MsetsPaper.External
