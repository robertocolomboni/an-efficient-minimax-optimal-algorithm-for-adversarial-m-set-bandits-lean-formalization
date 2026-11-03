import MsetsLower.Feedback.Inverse
import Mathlib.Analysis.Calculus.InverseFunctionTheorem.ContDiff

/-!
# Smooth interval equivalence for the feedback map

This file makes the regularity clause of `lem:lower-feedback-density`
explicit. The map is polynomial. Its actual inverse, already identified with
the inverse of the interval bijection, is the rationalized quadratic formula.
The positive spatial derivative gives a smooth local inverse by the inverse
function theorem. Continuity and local inverse identities identify it with
the actual inverse, including at the endpoints. No smoothness or invertibility
is assumed.

In this Mathlib version `ContDiff` order `⊤` means analytic regularity;
these statements are consequently stronger than the required smoothness.
-/

namespace MsetsPaper.Lower.FeedbackSmooth

open MsetsLower.Feedback Set
open scoped Topology

noncomputable section

/-- The forward map is polynomial, hence analytic on the entire real line. -/
theorem contDiff_feedbackMap (u : ℝ) : ContDiff ℝ ⊤ (feedbackMap u) := by
  unfold feedbackMap shape
  fun_prop

/-- In particular, the forward map is smooth on the source interval. -/
theorem contDiffOn_feedbackMap (u : ℝ) :
    ContDiffOn ℝ ⊤ (feedbackMap u) (Icc (-1 : ℝ) 1) :=
  (contDiff_feedbackMap u).contDiffOn

/-- The inverse function theorem proves regularity from the nonzero forward
derivative. The argument uses an ambient neighborhood even at the endpoints. -/
theorem contDiffAt_feedbackInverse
    {u y : ℝ} (hu : |u| ≤ 1 / 16)
    (hy : y ∈ Icc (-1 / 2 : ℝ) (1 / 2 : ℝ)) :
    ContDiffAt ℝ ⊤ (feedbackInverse u) y := by
  let z := feedbackInverse u y
  have hz := feedbackInverse_mem_Icc hu hy
  have hslope : feedbackSlope u z ≠ 0 := (feedbackSlope_pos hu hz).ne'
  have hf := (contDiff_feedbackMap u).contDiffAt (x := z)
  have hd := (hasDerivAt_feedbackMap u z).hasFDerivAt_equiv hslope
  have hn : (⊤ : WithTop ℕ∞) ≠ 0 := by simp
  let e := hf.toOpenPartialHomeomorph (feedbackMap u) hd hn
  have hzy : feedbackMap u z = y := feedbackMap_feedbackInverse hu hy
  have hlocal : ContDiffAt ℝ ⊤ e.symm y := by
    simpa only [e, ContDiffAt.localInverse, ContDiffAt.toOpenPartialHomeomorph,
      HasStrictFDerivAt.localInverse_def, hzy] using hf.to_localInverse hd hn
  have hsource : ∀ᶠ w in 𝓝 y, feedbackInverse u w ∈ e.source :=
    (continuous_feedbackInverse u).continuousAt.preimage_mem_nhds
      (e.open_source.mem_nhds (hf.mem_toOpenPartialHomeomorph_source hd hn))
  have hdisc : ∀ᶠ w in 𝓝 y, 0 < feedbackDiscriminant u w :=
    (show ContinuousAt (feedbackDiscriminant u) y by unfold feedbackDiscriminant; fun_prop)
      (Ioi_mem_nhds (feedbackDiscriminant_pos hu hy))
  apply hlocal.congr_of_eventuallyEq
  filter_upwards [hsource, hdisc] with w hw hdw
  have hright : e (feedbackInverse u w) = w :=
    feedbackMap_feedbackInverse_of_discriminant_nonneg hdw.le
  exact (e.left_inv hw).symm.trans (congrArg e.symm hright)

/-- Smoothness of the actual inverse on the full closed target interval. -/
theorem contDiffOn_feedbackInverse
    {u : ℝ} (hu : |u| ≤ 1 / 16) :
    ContDiffOn ℝ ⊤ (feedbackInverse u) (Icc (-1 / 2 : ℝ) (1 / 2 : ℝ)) := by
  intro y hy
  exact (contDiffAt_feedbackInverse hu hy).contDiffWithinAt

/-- The complete increasing smooth-equivalence clause of L12: a strictly
increasing bijection of the two intervals, its explicit two-sided inverse,
smoothness in both directions, and the stated inverse derivative. -/
theorem feedbackMap_increasing_smooth_equivalence
    {u : ℝ} (hu : |u| ≤ 1 / 16) :
    StrictMonoOn (feedbackMap u) (Icc (-1 : ℝ) 1) ∧
    BijOn (feedbackMap u) (Icc (-1 : ℝ) 1) (Icc (-1 / 2 : ℝ) (1 / 2 : ℝ)) ∧
    (∀ z ∈ Icc (-1 : ℝ) 1, feedbackInverse u (feedbackMap u z) = z) ∧
    (∀ y ∈ Icc (-1 / 2 : ℝ) (1 / 2 : ℝ), feedbackMap u (feedbackInverse u y) = y) ∧
    ContDiffOn ℝ ⊤ (feedbackMap u) (Icc (-1 : ℝ) 1) ∧
    ContDiffOn ℝ ⊤ (feedbackInverse u) (Icc (-1 / 2 : ℝ) (1 / 2 : ℝ)) ∧
    (∀ y ∈ Icc (-1 / 2 : ℝ) (1 / 2 : ℝ),
      HasDerivAt (feedbackInverse u) (feedbackSlope u (feedbackInverse u y))⁻¹ y) := by
  exact ⟨feedbackMap_strictMonoOn hu, feedbackMap_bijOn hu,
    fun _ hz => feedbackInverse_feedbackMap hu hz,
    fun _ hy => feedbackMap_feedbackInverse hu hy,
    contDiffOn_feedbackMap u, contDiffOn_feedbackInverse hu,
    fun _ hy => hasDerivAt_feedbackInverse_observation hu hy⟩

end

end MsetsPaper.Lower.FeedbackSmooth
