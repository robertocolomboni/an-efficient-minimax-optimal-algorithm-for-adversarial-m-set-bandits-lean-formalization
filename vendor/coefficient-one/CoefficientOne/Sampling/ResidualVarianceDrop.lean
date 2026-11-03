import CoefficientOne.Sampling.ResidualRegression

/-! # Averaging the actual residual variance over the next uniform reveal -/

open scoped BigOperators
open EffectiveResistance Matrix
namespace CoefficientOne.Sampling
noncomputable section
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

def residualNextVariance (w : ι → ℝ) (R : Finset ι) (r : ℕ) (a : ι → ℝ) : ℝ :=
  if 0 < r ∧ r < R.card then
    (R.card : ℝ)⁻¹ * ∑ i ∈ R,
      (sequentialThreshold w R r i * quadraticForm (residualCovariance w (R.erase i) (r - 1)) a +
       (1 - sequentialThreshold w R r i) * quadraticForm (residualCovariance w (R.erase i) r) a)
  else 0

theorem residualCovariance_operator_ge_one (w : ι → ℝ) (hw : ∀ i, 0 < w i)
    (R : Finset ι) (r : ℕ) (hr0 : 0 < r) (hrtop : r < R.card) (a : ι → ℝ) :
    quadraticForm (residualCovariance w R r) a ≤
      ∑ i : R, ((residualCovariance w R r *ᵥ a) i.val) ^ 2 / residualCovariance w R r i.val i.val := by
  rw [residualCovariance_quadratic]
  simp_rw [residualCovariance_mulVec_subtype, residualCovariance_subtype]
  exact covariance_operator_ge_one (fun i : R => w i.val) (fun i => hw i.val) r
    (by omega) (by simpa using (show r ≤ R.card - 1 by omega)) (fun i : R => a i.val)

theorem residual_uniform_variance_drop_identity (w : ι → ℝ) (hw : ∀ i, 0 < w i)
    (R : Finset ι) (r : ℕ) (hr0 : 0 < r) (hrtop : r < R.card) (a : ι → ℝ) :
    quadraticForm (residualCovariance w R r) a - residualNextVariance w R r a =
      (R.card : ℝ)⁻¹ *
        ∑ i : R, ((residualCovariance w R r *ᵥ a) i.val) ^ 2 / residualCovariance w R r i.val i.val := by
  have hn : (R.card : ℝ) ≠ 0 := by exact_mod_cast (show R.card ≠ 0 by omega)
  have hsum := Finset.sum_congr (s₁ := R) (s₂ := R) rfl
    (fun i hi => residual_coordinate_variance_drop w hw R r hr0 hrtop a i hi)
  rw [Finset.sum_sub_distrib, Finset.sum_const, nsmul_eq_mul] at hsum
  have hs : (∑ i ∈ R, ((residualCovariance w R r *ᵥ a) i) ^ 2 / residualCovariance w R r i i) =
      ∑ i : R, ((residualCovariance w R r *ᵥ a) i.val) ^ 2 / residualCovariance w R r i.val i.val :=
    Finset.sum_subtype R (fun _ => Iff.rfl) _
  rw [hs] at hsum
  rw [residualNextVariance, if_pos ⟨hr0, hrtop⟩]
  calc
    _ = (R.card : ℝ)⁻¹ * ((R.card : ℝ) * quadraticForm (residualCovariance w R r) a -
        ∑ i ∈ R, (sequentialThreshold w R r i *
          quadraticForm (residualCovariance w (R.erase i) (r - 1)) a +
          (1 - sequentialThreshold w R r i) * quadraticForm (residualCovariance w (R.erase i) r) a)) := by
      field_simp
    _ = _ := by rw [hsum]

/-- The spectral gap and the exact conditional laws give the one-step drift
at every admissible residual state, including the forced states. -/
theorem residual_uniform_variance_drop (w : ι → ℝ) (hw : ∀ i, 0 < w i)
    (R : Finset ι) (r : ℕ) (hr : r ≤ R.card) (a : ι → ℝ) :
    quadraticForm (residualCovariance w R r) a / R.card ≤
      quadraticForm (residualCovariance w R r) a - residualNextVariance w R r a := by
  by_cases hactive : 0 < r ∧ r < R.card
  · rw [residual_uniform_variance_drop_identity w hw R r hactive.1 hactive.2]
    rw [div_eq_mul_inv, mul_comm]
    exact mul_le_mul_of_nonneg_left
      (residualCovariance_operator_ge_one w hw R r hactive.1 hactive.2 a)
      (inv_nonneg.mpr (Nat.cast_nonneg _))
  · have ht : r = 0 ∨ r = R.card := by omega
    have hz : residualCovariance w R r = 0 := by
      rcases ht with h | h
      · rw [h, residualCovariance_zero]
      · rw [h, residualCovariance_full w hw]
    simp [residualNextVariance, hactive, hz, quadraticForm]

end
end CoefficientOne.Sampling
