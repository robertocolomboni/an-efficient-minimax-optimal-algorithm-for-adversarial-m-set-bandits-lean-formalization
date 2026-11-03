import Mathlib.Analysis.Calculus.MeanValue

/-!
# The Dini step from local to global stretch

No derivative of the distance function is assumed.  The scalar fencing theorem
uses continuity and upper bounds for right-hand slopes, as in Appendix E.2.
-/

open Set Filter
open scoped Topology

namespace CoefficientOne.Sampling

/-- An epsilon formulation of a uniform upper-right Dini bound. -/
def HasUpperRightSlopeBound (g : ℝ → ℝ) (L a b : ℝ) : Prop :=
  ∀ x ∈ Ico a b, ∀ r, L < r → ∀ᶠ z in 𝓝[>] x, slope g x z < r

theorem dini_endpoint_bound (g : ℝ → ℝ) (L a b : ℝ) (hab : a ≤ b)
    (hg : ContinuousOn g (Icc a b)) (hbound : HasUpperRightSlopeBound g L a b) :
    g b - g a ≤ L * (b - a) := by
  let B : ℝ → ℝ := fun x => g a + L * (x - a)
  have ha : g a ≤ B a := by simp [B]
  have hB : ContinuousOn B (Icc a b) := by fun_prop
  have hB' : ∀ x ∈ Ico a b, HasDerivWithinAt B L (Ici x) x := by
    intro x _
    simpa [B] using
      (((hasDerivAt_id x).sub_const a).const_mul L).const_add (g a) |>.hasDerivWithinAt
  have h := image_le_of_liminf_slope_right_le_deriv_boundary hg ha hB hB'
    (fun x hx r hr => (hbound x hx r hr).frequently) (show b ∈ Icc a b from ⟨hab, le_rfl⟩)
  dsimp [B] at h
  linarith

theorem dini_unit_interval_bound (g : ℝ → ℝ) (L : ℝ)
    (hg : ContinuousOn g (Icc 0 1)) (hbound : HasUpperRightSlopeBound g L 0 1) :
    g 1 - g 0 ≤ L := by
  simpa using dini_endpoint_bound g L 0 1 (by norm_num) hg hbound

end CoefficientOne.Sampling
