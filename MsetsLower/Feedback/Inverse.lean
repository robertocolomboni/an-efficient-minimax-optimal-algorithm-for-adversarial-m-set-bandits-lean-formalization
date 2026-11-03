import MsetsLower.Feedback.Map
import Mathlib.Analysis.Calculus.Deriv.Inverse
import Mathlib.Analysis.Calculus.Deriv.Inv
import Mathlib.Analysis.Calculus.Deriv.Add
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.MeasureTheory.Constructions.BorelSpace.Basic

/-!
# The inverse of the scalar feedback map

This file constructs the inverse used in `lem:lower-feedback-density`.  The
definition is the rationalized quadratic formula; on the paper's rectangle it
is identified with the set-theoretic inverse supplied by `feedbackMap_bijOn`.
Keeping the formula as the definition makes the parameter dependence explicit
and gives a total continuous (hence measurable) extension away from the
rectangle.
-/

namespace MsetsLower.Feedback

open Filter Set
open scoped Topology

noncomputable section

/-- The discriminant in the quadratic equation `feedbackMap u z = y`. -/
def feedbackDiscriminant (u y : Real) : Real :=
  1 / 4 - 4 * u * (y - u)

/-- The branch of the quadratic formula which tends to `2 * y` at `u = 0`.
On the paper's parameter rectangle this is the unique inverse of
`feedbackMap u` on `[-1,1]`. -/
def feedbackInverse (u y : Real) : Real :=
  2 * (y - u) / (1 / 2 + Real.sqrt (feedbackDiscriminant u y))

private theorem feedbackDiscriminant_eq_slope_sq_of_map_eq
    {u y z : Real} (hmap : feedbackMap u z = y) :
    feedbackDiscriminant u y = feedbackSlope u z ^ 2 := by
  unfold feedbackDiscriminant feedbackMap feedbackSlope shape at *
  rw [← hmap]
  ring

/-- Whenever the quadratic discriminant is nonnegative, the rationalized
formula is a root of the feedback equation. -/
theorem feedbackMap_feedbackInverse_of_discriminant_nonneg
    {u y : Real} (hdisc : 0 ≤ feedbackDiscriminant u y) :
    feedbackMap u (feedbackInverse u y) = y := by
  have hsqrt_sq :
      Real.sqrt (feedbackDiscriminant u y) ^ 2 = feedbackDiscriminant u y :=
    Real.sq_sqrt hdisc
  have hden :
      (1 / 2 : Real) + Real.sqrt (feedbackDiscriminant u y) ≠ 0 := by
    have := Real.sqrt_nonneg (feedbackDiscriminant u y)
    norm_num
    linarith
  unfold feedbackMap feedbackInverse shape feedbackDiscriminant at *
  rw [div_pow]
  field_simp
  ring_nf at hsqrt_sq ⊢
  linear_combination (4 * (u - y)) * hsqrt_sq

/-- The explicit formula agrees with Mathlib's inverse-on-a-set construction.
This is the bridge from the formula to the bijection already proved in
`Feedback.Map`. -/
theorem feedbackInverse_eq_invFunOn
    {u y : Real} (hu : |u| ≤ 1 / 16)
    (hy : y ∈ Icc (-1 / 2 : Real) (1 / 2 : Real)) :
    feedbackInverse u y =
      Function.invFunOn (feedbackMap u) (Icc (-1 : Real) 1) y := by
  let z := Function.invFunOn (feedbackMap u) (Icc (-1 : Real) 1) y
  have hz : z ∈ Icc (-1 : Real) 1 :=
    (feedbackMap_bijOn hu).surjOn.mapsTo_invFunOn hy
  have hmap : feedbackMap u z = y :=
    (feedbackMap_bijOn hu).surjOn.rightInvOn_invFunOn hy
  have hslope : 0 < feedbackSlope u z := feedbackSlope_pos hu hz
  have hdisc : feedbackDiscriminant u y = feedbackSlope u z ^ 2 :=
    feedbackDiscriminant_eq_slope_sq_of_map_eq hmap
  have hyu : y - u = z * ((1 / 2 : Real) - u * z) := by
    unfold feedbackMap shape at hmap
    nlinarith
  have hden : (1 / 2 : Real) + feedbackSlope u z ≠ 0 := by
    positivity
  change 2 * (y - u) / (1 / 2 + Real.sqrt (feedbackDiscriminant u y)) = z
  rw [hdisc, Real.sqrt_sq_eq_abs, abs_of_pos hslope, hyu]
  rw [div_eq_iff hden]
  unfold feedbackSlope
  ring

/-- The inverse lies in the spatial interval. -/
theorem feedbackInverse_mem_Icc
    {u y : Real} (hu : |u| ≤ 1 / 16)
    (hy : y ∈ Icc (-1 / 2 : Real) (1 / 2 : Real)) :
    feedbackInverse u y ∈ Icc (-1 : Real) 1 := by
  rw [feedbackInverse_eq_invFunOn hu hy]
  exact (feedbackMap_bijOn hu).surjOn.mapsTo_invFunOn hy

/-- Right-inverse identity on the target interval. -/
@[simp] theorem feedbackMap_feedbackInverse
    {u y : Real} (hu : |u| ≤ 1 / 16)
    (hy : y ∈ Icc (-1 / 2 : Real) (1 / 2 : Real)) :
    feedbackMap u (feedbackInverse u y) = y := by
  rw [feedbackInverse_eq_invFunOn hu hy]
  exact (feedbackMap_bijOn hu).surjOn.rightInvOn_invFunOn hy

/-- Left-inverse identity on the source interval. -/
@[simp] theorem feedbackInverse_feedbackMap
    {u z : Real} (hu : |u| ≤ 1 / 16)
    (hz : z ∈ Icc (-1 : Real) 1) :
    feedbackInverse u (feedbackMap u z) = z := by
  have hy : feedbackMap u z ∈ Icc (-1 / 2 : Real) (1 / 2 : Real) :=
    (feedbackMap_bijOn hu).mapsTo hz
  rw [feedbackInverse_eq_invFunOn hu hy]
  exact (feedbackMap_bijOn hu).injOn.leftInvOn_invFunOn hz

/-- Uniqueness of the inverse in `[-1,1]`. -/
theorem eq_feedbackInverse_of_feedbackMap_eq
    {u y z : Real} (hu : |u| ≤ 1 / 16)
    (hy : y ∈ Icc (-1 / 2 : Real) (1 / 2 : Real))
    (hz : z ∈ Icc (-1 : Real) 1) (hzy : feedbackMap u z = y) :
    z = feedbackInverse u y := by
  apply (feedbackMap_bijOn hu).injOn hz (feedbackInverse_mem_Icc hu hy)
  rw [hzy, feedbackMap_feedbackInverse hu hy]

/-- Existence and uniqueness of the inverse point, stated without any bundled
equivalence. -/
theorem existsUnique_feedbackMap_preimage
    {u y : Real} (hu : |u| ≤ 1 / 16)
    (hy : y ∈ Icc (-1 / 2 : Real) (1 / 2 : Real)) :
    ∃! z : Real, z ∈ Icc (-1 : Real) 1 ∧ feedbackMap u z = y := by
  refine ⟨feedbackInverse u y,
    ⟨feedbackInverse_mem_Icc hu hy, feedbackMap_feedbackInverse hu hy⟩, ?_⟩
  intro z hz
  exact eq_feedbackInverse_of_feedbackMap_eq hu hy hz.1 hz.2

/-- The explicit total extension is continuous in both parameters. -/
theorem continuous_feedbackInverse_uncurry :
    Continuous (fun p : Real × Real => feedbackInverse p.1 p.2) := by
  unfold feedbackInverse feedbackDiscriminant
  apply Continuous.div
  · fun_prop
  · fun_prop
  · intro p
    have hsqrt : 0 ≤ Real.sqrt ((1 / 4 : Real) - 4 * p.1 * (p.2 - p.1)) :=
      Real.sqrt_nonneg _
    norm_num
    linarith

/-- Continuity in the observation variable. -/
theorem continuous_feedbackInverse (u : Real) :
    Continuous (feedbackInverse u) := by
  simpa [Function.comp_def] using
    continuous_feedbackInverse_uncurry.comp (continuous_const.prodMk continuous_id)

/-- Continuity in the feedback parameter. -/
theorem continuous_feedbackInverse_param (y : Real) :
    Continuous (fun u : Real => feedbackInverse u y) := by
  simpa [Function.comp_def] using
    continuous_feedbackInverse_uncurry.comp (continuous_id.prodMk continuous_const)

/-- Borel measurability of the joint inverse map. -/
theorem measurable_feedbackInverse_uncurry :
    Measurable (fun p : Real × Real => feedbackInverse p.1 p.2) :=
  continuous_feedbackInverse_uncurry.measurable

/-- Borel measurability in the observation variable. -/
theorem measurable_feedbackInverse (u : Real) :
    Measurable (feedbackInverse u) :=
  (continuous_feedbackInverse u).measurable

/-- Borel measurability in the feedback parameter. -/
theorem measurable_feedbackInverse_param (y : Real) :
    Measurable (fun u : Real => feedbackInverse u y) :=
  (continuous_feedbackInverse_param y).measurable

/-- A bundled equivalence of the two closed intervals. -/
def feedbackEquiv (u : Real) (hu : |u| ≤ 1 / 16) :
    {z // z ∈ Icc (-1 : Real) 1} ≃
      {y // y ∈ Icc (-1 / 2 : Real) (1 / 2 : Real)} where
  toFun z := ⟨feedbackMap u z, (feedbackMap_bijOn hu).mapsTo z.property⟩
  invFun y := ⟨feedbackInverse u y, feedbackInverse_mem_Icc hu y.property⟩
  left_inv z := Subtype.ext (feedbackInverse_feedbackMap hu z.property)
  right_inv y := Subtype.ext (feedbackMap_feedbackInverse hu y.property)

/-- The interval equivalence is a homeomorphism; its inverse coordinate is
the parametrically continuous function `feedbackInverse u`. -/
def feedbackHomeomorph (u : Real) (hu : |u| ≤ 1 / 16) :
    {z // z ∈ Icc (-1 : Real) 1} ≃ₜ
      {y // y ∈ Icc (-1 / 2 : Real) (1 / 2 : Real)} where
  toEquiv := feedbackEquiv u hu
  continuous_toFun :=
    Continuous.subtype_mk
      ((continuous_feedbackMap u).comp continuous_subtype_val) _
  continuous_invFun :=
    Continuous.subtype_mk
      ((continuous_feedbackInverse u).comp continuous_subtype_val) _

/-- Chain rule for simultaneous variation of the parameter and spatial
argument. -/
private theorem hasDerivAt_feedbackMap_param_comp
    {g : Real → Real} {u g' : Real} (hg : HasDerivAt g g' u) :
    HasDerivAt (fun v => feedbackMap v (g v))
      (shape (g u) + feedbackSlope u (g u) * g') u := by
  have hsq : HasDerivAt (fun v => (g v) ^ 2) (2 * g u * g') u := by
    simpa [mul_assoc] using! hg.pow 2
  have hshape : HasDerivAt (fun v => 1 - (g v) ^ 2) (-2 * g u * g') u := by
    convert! HasDerivAt.sub (hasDerivAt_const u (1 : Real)) hsq using 1
    ring
  have hlinear : HasDerivAt (fun v => g v / 2) (g' / 2) u :=
    hg.div_const 2
  have hpert :
      HasDerivAt (fun v => v * (1 - (g v) ^ 2))
        ((1 - (g u) ^ 2) + u * (-2 * g u * g')) u := by
    convert! HasDerivAt.mul (hasDerivAt_id u) hshape using 1
    simp only [id_eq]
    ring
  convert! HasDerivAt.add hlinear hpert using 1
  simp only [feedbackSlope, shape]
  ring

/-- The discriminant is uniformly separated from zero on the paper's
rectangle.  This qualitative form is enough for differentiability of the
square-root formula. -/
theorem feedbackDiscriminant_pos
    {u y : Real} (hu : |u| ≤ 1 / 16)
    (hy : y ∈ Icc (-1 / 2 : Real) (1 / 2 : Real)) :
    0 < feedbackDiscriminant u y := by
  have hmap := feedbackMap_feedbackInverse hu hy
  rw [feedbackDiscriminant_eq_slope_sq_of_map_eq hmap]
  exact sq_pos_of_pos (feedbackSlope_pos hu (feedbackInverse_mem_Icc hu hy))

private theorem eventually_feedbackMap_feedbackInverse_param
    {u y : Real} (hu : |u| ≤ 1 / 16)
    (hy : y ∈ Icc (-1 / 2 : Real) (1 / 2 : Real)) :
    (fun v => feedbackMap v (feedbackInverse v y)) =ᶠ[𝓝 u] fun _ => y := by
  have hcont : ContinuousAt (fun v => feedbackDiscriminant v y) u := by
    unfold feedbackDiscriminant
    fun_prop
  have hevent : ∀ᶠ v in 𝓝 u, 0 < feedbackDiscriminant v y :=
    hcont (Ioi_mem_nhds (feedbackDiscriminant_pos hu hy))
  filter_upwards [hevent] with v hv
  exact feedbackMap_feedbackInverse_of_discriminant_nonneg hv.le

private theorem eventually_feedbackMap_feedbackInverse_observation
    {u y : Real} (hu : |u| ≤ 1 / 16)
    (hy : y ∈ Icc (-1 / 2 : Real) (1 / 2 : Real)) :
    (fun w => feedbackMap u (feedbackInverse u w)) =ᶠ[𝓝 y] id := by
  have hcont : ContinuousAt (feedbackDiscriminant u) y := by
    unfold feedbackDiscriminant
    fun_prop
  have hevent : ∀ᶠ w in 𝓝 y, 0 < feedbackDiscriminant u w :=
    hcont (Ioi_mem_nhds (feedbackDiscriminant_pos hu hy))
  filter_upwards [hevent] with w hw
  exact feedbackMap_feedbackInverse_of_discriminant_nonneg hw.le

/-- Implicit derivative with respect to the observation `y`. -/
theorem hasDerivAt_feedbackInverse_observation
    {u y : Real} (hu : |u| ≤ 1 / 16)
    (hy : y ∈ Icc (-1 / 2 : Real) (1 / 2 : Real)) :
    HasDerivAt (feedbackInverse u)
      (feedbackSlope u (feedbackInverse u y))⁻¹ y := by
  apply (hasDerivAt_feedbackMap u (feedbackInverse u y)).of_local_left_inverse
  · exact (continuous_feedbackInverse u).continuousAt
  · exact ne_of_gt (feedbackSlope_pos hu (feedbackInverse_mem_Icc hu hy))
  · filter_upwards [eventually_feedbackMap_feedbackInverse_observation hu hy] with w hw
    simpa using hw

private theorem differentiableAt_feedbackInverse_param
    {u y : Real} (hu : |u| ≤ 1 / 16)
    (hy : y ∈ Icc (-1 / 2 : Real) (1 / 2 : Real)) :
    DifferentiableAt Real (fun v => feedbackInverse v y) u := by
  have hdisc_ne : feedbackDiscriminant u y ≠ 0 :=
    ne_of_gt (feedbackDiscriminant_pos hu hy)
  have hdisc_diff :
      DifferentiableAt Real (fun v => feedbackDiscriminant v y) u := by
    unfold feedbackDiscriminant
    fun_prop
  have hsqrt_diff :
      DifferentiableAt Real (fun v => Real.sqrt (feedbackDiscriminant v y)) u :=
    hdisc_diff.sqrt hdisc_ne
  have hden_ne :
      (1 / 2 : Real) + Real.sqrt (feedbackDiscriminant u y) ≠ 0 := by
    have := Real.sqrt_nonneg (feedbackDiscriminant u y)
    norm_num
    linarith
  unfold feedbackInverse
  fun_prop

/-- Implicit derivative with respect to the feedback parameter `u`. -/
theorem hasDerivAt_feedbackInverse_param
    {u y : Real} (hu : |u| ≤ 1 / 16)
    (hy : y ∈ Icc (-1 / 2 : Real) (1 / 2 : Real)) :
    HasDerivAt (fun v => feedbackInverse v y)
      (-shape (feedbackInverse u y) /
        feedbackSlope u (feedbackInverse u y)) u := by
  let z' := deriv (fun v => feedbackInverse v y) u
  have hzderiv : HasDerivAt (fun v => feedbackInverse v y) z' u :=
    (differentiableAt_feedbackInverse_param hu hy).hasDerivAt
  have hcomp := hasDerivAt_feedbackMap_param_comp hzderiv
  have hzero : HasDerivAt (fun v => feedbackMap v (feedbackInverse v y)) 0 u :=
    (hasDerivAt_const u y).congr_of_eventuallyEq
      (eventually_feedbackMap_feedbackInverse_param hu hy)
  have hderiv_eq :
      shape (feedbackInverse u y) +
          feedbackSlope u (feedbackInverse u y) * z' = 0 :=
    hcomp.unique hzero
  have hslope_ne : feedbackSlope u (feedbackInverse u y) ≠ 0 :=
    ne_of_gt (feedbackSlope_pos hu (feedbackInverse_mem_Icc hu hy))
  apply hzderiv.congr_deriv
  rw [eq_div_iff hslope_ne]
  nlinarith

/-- On `[-1,1]`, the perturbation shape lies in `[0,1]`. -/
theorem shape_mem_Icc {z : Real} (hz : z ∈ Icc (-1 : Real) 1) :
    shape z ∈ Icc (0 : Real) 1 := by
  have hprod : 0 ≤ (z + 1) * (1 - z) :=
    mul_nonneg (by linarith [hz.1]) (by linarith [hz.2])
  unfold shape
  constructor <;> nlinarith [sq_nonneg z]

/-- Algebraic bound behind the paper's estimate
`|∂_u z(u,y)| ≤ 8/3`. -/
theorem abs_feedbackInverse_param_deriv_value_le
    {u y : Real} (hu : |u| ≤ 1 / 16)
    (hy : y ∈ Icc (-1 / 2 : Real) (1 / 2 : Real)) :
    |-shape (feedbackInverse u y) /
        feedbackSlope u (feedbackInverse u y)| ≤ 8 / 3 := by
  have hz := feedbackInverse_mem_Icc hu hy
  have hg := shape_mem_Icc hz
  have hA := feedbackSlope_mem_Icc hu hz
  have hApos := feedbackSlope_pos hu hz
  rw [abs_div, abs_neg, abs_of_nonneg hg.1, abs_of_pos hApos,
    div_le_iff₀ hApos]
  nlinarith [hg.2, hA.1]

/-- Derivative-level form of the paper's bound `|∂_u z| ≤ 8/3`. -/
theorem abs_deriv_feedbackInverse_param_le
    {u y : Real} (hu : |u| ≤ 1 / 16)
    (hy : y ∈ Icc (-1 / 2 : Real) (1 / 2 : Real)) :
    |deriv (fun v => feedbackInverse v y) u| ≤ 8 / 3 := by
  rw [(hasDerivAt_feedbackInverse_param hu hy).deriv]
  exact abs_feedbackInverse_param_deriv_value_le hu hy

end

end MsetsLower.Feedback

#print axioms MsetsLower.Feedback.feedbackHomeomorph
#print axioms MsetsLower.Feedback.continuous_feedbackInverse_uncurry
#print axioms MsetsLower.Feedback.measurable_feedbackInverse_uncurry
#print axioms MsetsLower.Feedback.hasDerivAt_feedbackInverse_observation
#print axioms MsetsLower.Feedback.hasDerivAt_feedbackInverse_param
#print axioms MsetsLower.Feedback.abs_deriv_feedbackInverse_param_le
