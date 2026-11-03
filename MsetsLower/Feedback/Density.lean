import MsetsLower.Feedback.Inverse
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.MeasureTheory.Integral.IntervalIntegral.IntegrationByParts

/-!
# Density estimates for the scalar feedback law

This file formalizes the density calculation and the two information bounds in
`lem:lower-feedback-density`.  The total density is extended by zero outside
the observation interval, while `feedbackDensityCore` is the smooth expression
used inside interval integrals.
-/

namespace MsetsLower.Feedback

open Set MeasureTheory
open scoped Interval

noncomputable section

/-- The Jacobian `F'_u(F_u^{-1}(y))`. -/
def feedbackJacobian (u y : Real) : Real :=
  feedbackSlope u (feedbackInverse u y)

/-- The density formula on the common support `[-1/2,1/2]`. -/
def feedbackDensityCore (u y : Real) : Real :=
  1 / (2 * feedbackJacobian u y)

/-- The literal density, extended by zero off the common support. -/
def feedbackDensity (u y : Real) : Real :=
  if y ∈ Icc (-1 / 2 : Real) (1 / 2 : Real) then
    feedbackDensityCore u y
  else 0

theorem feedbackDensity_eq_core
    {u y : Real} (hy : y ∈ Icc (-1 / 2 : Real) (1 / 2 : Real)) :
    feedbackDensity u y = feedbackDensityCore u y := by
  unfold feedbackDensity
  rw [if_pos hy]

theorem feedbackDensity_eq_zero
    {u y : Real} (hy : y ∉ Icc (-1 / 2 : Real) (1 / 2 : Real)) :
    feedbackDensity u y = 0 := by
  unfold feedbackDensity
  rw [if_neg hy]

theorem continuous_feedbackJacobian (u : Real) :
    Continuous (feedbackJacobian u) := by
  unfold feedbackJacobian feedbackSlope
  exact continuous_const.sub (continuous_const.mul (continuous_feedbackInverse u))

theorem continuousOn_feedbackDensityCore
    {u : Real} (hu : |u| ≤ 1 / 16) :
    ContinuousOn (feedbackDensityCore u)
      (Icc (-1 / 2 : Real) (1 / 2 : Real)) := by
  intro y hy
  unfold feedbackDensityCore
  exact ContinuousAt.continuousWithinAt <|
    continuousAt_const.div
      (continuousAt_const.mul (continuous_feedbackJacobian u).continuousAt)
      (ne_of_gt (mul_pos (by norm_num)
        (feedbackSlope_pos hu (feedbackInverse_mem_Icc hu hy))))

theorem measurable_feedbackDensity (u : Real) :
    Measurable (feedbackDensity u) := by
  have hcore : Measurable (feedbackDensityCore u) := by
    unfold feedbackDensityCore
    exact measurable_const.div
      (measurable_const.mul (continuous_feedbackJacobian u).measurable)
  unfold feedbackDensity
  exact Measurable.ite measurableSet_Icc hcore measurable_const

theorem feedbackJacobian_mem_Icc
    {u y : Real} (hu : |u| ≤ 1 / 16)
    (hy : y ∈ Icc (-1 / 2 : Real) (1 / 2 : Real)) :
    feedbackJacobian u y ∈ Icc (3 / 8 : Real) (5 / 8 : Real) :=
  feedbackSlope_mem_Icc hu (feedbackInverse_mem_Icc hu hy)

theorem feedbackDensityCore_mem_Icc
    {u y : Real} (hu : |u| ≤ 1 / 16)
    (hy : y ∈ Icc (-1 / 2 : Real) (1 / 2 : Real)) :
    feedbackDensityCore u y ∈ Icc (4 / 5 : Real) (4 / 3 : Real) := by
  have hA := feedbackJacobian_mem_Icc hu hy
  have hApos : 0 < feedbackJacobian u y := by
    exact lt_of_lt_of_le (by norm_num) hA.1
  unfold feedbackDensityCore
  constructor
  · rw [div_le_div_iff₀ (by norm_num : (0 : Real) < 5)
      (mul_pos (by norm_num) hApos)]
    nlinarith [hA.2]
  · rw [div_le_div_iff₀ (mul_pos (by norm_num) hApos)
      (by norm_num : (0 : Real) < 3)]
    nlinarith [hA.1]

theorem feedbackDensity_nonneg
    {u y : Real} (hu : |u| ≤ 1 / 16) :
    0 ≤ feedbackDensity u y := by
  by_cases hy : y ∈ Icc (-1 / 2 : Real) (1 / 2 : Real)
  · rw [feedbackDensity_eq_core hy]
    exact le_trans (by norm_num) (feedbackDensityCore_mem_Icc hu hy).1
  · rw [feedbackDensity_eq_zero hy]

theorem feedbackDensity_le
    {u y : Real} (hu : |u| ≤ 1 / 16) :
    feedbackDensity u y ≤ 4 / 3 := by
  by_cases hy : y ∈ Icc (-1 / 2 : Real) (1 / 2 : Real)
  · rw [feedbackDensity_eq_core hy]
    exact (feedbackDensityCore_mem_Icc hu hy).2
  · rw [feedbackDensity_eq_zero hy]
    norm_num

/-- Pointwise cancellation of the inverse Jacobian. -/
theorem feedbackDensityCore_map_mul_slope
    {u z : Real} (hu : |u| ≤ 1 / 16)
    (hz : z ∈ Icc (-1 : Real) 1) :
    feedbackDensityCore u (feedbackMap u z) * feedbackSlope u z = 1 / 2 := by
  have hslope : feedbackSlope u z ≠ 0 :=
    ne_of_gt (feedbackSlope_pos hu hz)
  rw [feedbackDensityCore, feedbackJacobian, feedbackInverse_feedbackMap hu hz]
  field_simp

/-- Change of variables against a continuous test function.  This is the
literal density identity for the push-forward of the uniform law, expressed
at the level of expectations. -/
theorem feedback_pushforward_integral_continuous
    {u : Real} (hu : |u| ≤ 1 / 16) {f : Real → Real} (hf : Continuous f) :
    (∫ y in (-1 / 2 : Real)..(1 / 2 : Real),
        f y * feedbackDensityCore u y) =
      ∫ z in (-1 : Real)..1, (1 / 2 : Real) * f (feedbackMap u z) := by
  have hderiv : ∀ z ∈ [[(-1 : Real), 1]],
      HasDerivAt (feedbackMap u) (feedbackSlope u z) z := by
    intro z hz
    exact hasDerivAt_feedbackMap u z
  have hslope_cont : ContinuousOn (feedbackSlope u) [[(-1 : Real), 1]] := by
    unfold feedbackSlope
    fun_prop
  have htest_cont :
      ContinuousOn (fun y => f y * feedbackDensityCore u y)
        (feedbackMap u '' [[(-1 : Real), 1]]) := by
    rw [uIcc_of_le (by norm_num : (-1 : Real) ≤ 1), feedbackMap_image_Icc hu]
    exact hf.continuousOn.mul (continuousOn_feedbackDensityCore hu)
  have hsubst := intervalIntegral.integral_comp_mul_deriv'
    (a := (-1 : Real)) (b := 1)
    (f := feedbackMap u) (f' := feedbackSlope u)
    (g := fun y => f y * feedbackDensityCore u y)
    hderiv hslope_cont htest_cont
  rw [feedbackMap_neg_one, feedbackMap_one] at hsubst
  rw [← hsubst]
  apply intervalIntegral.integral_congr
  intro z hz
  have hz' : z ∈ Icc (-1 : Real) 1 := by
    simpa [uIcc_of_le (by norm_num : (-1 : Real) ≤ 1)] using hz
  change (f (feedbackMap u z) * feedbackDensityCore u (feedbackMap u z)) *
      feedbackSlope u z = (1 / 2 : Real) * f (feedbackMap u z)
  rw [mul_assoc, feedbackDensityCore_map_mul_slope hu hz']
  ring

/-- The density integrates to one on its common support. -/
theorem integral_feedbackDensityCore
    {u : Real} (hu : |u| ≤ 1 / 16) :
    (∫ y in (-1 / 2 : Real)..(1 / 2 : Real), feedbackDensityCore u y) = 1 := by
  have h := feedback_pushforward_integral_continuous hu
    (f := fun _ : Real => 1) continuous_const
  norm_num at h ⊢
  exact h

/-- The zero-extended literal density also integrates to one. -/
theorem integral_feedbackDensity
    {u : Real} (hu : |u| ≤ 1 / 16) :
    (∫ y in (-1 / 2 : Real)..(1 / 2 : Real), feedbackDensity u y) = 1 := by
  calc
    (∫ y in (-1 / 2 : Real)..(1 / 2 : Real), feedbackDensity u y) =
        ∫ y in (-1 / 2 : Real)..(1 / 2 : Real), feedbackDensityCore u y := by
      apply intervalIntegral.integral_congr
      intro y hy
      have hy' : y ∈ Icc (-1 / 2 : Real) (1 / 2 : Real) := by
        rw [uIcc_of_le (by norm_num : (-1 / 2 : Real) ≤ 1 / 2)] at hy
        exact hy
      exact feedbackDensity_eq_core hy'
    _ = 1 := integral_feedbackDensityCore hu

/-- The derivative of the inverse Jacobian with respect to the feedback
parameter, in the exact form used in the manuscript. -/
def feedbackJacobianParamDeriv (u y : Real) : Real :=
  -2 * feedbackInverse u y -
    2 * u * (-shape (feedbackInverse u y) /
      feedbackSlope u (feedbackInverse u y))

theorem hasDerivAt_feedbackJacobian_param
    {u y : Real} (hu : |u| ≤ 1 / 16)
    (hy : y ∈ Icc (-1 / 2 : Real) (1 / 2 : Real)) :
    HasDerivAt (fun v => feedbackJacobian v y)
      (feedbackJacobianParamDeriv u y) u := by
  have hz := hasDerivAt_feedbackInverse_param hu hy
  have hprod := HasDerivAt.mul
    ((hasDerivAt_id u).const_mul 2) hz
  unfold feedbackJacobian feedbackSlope feedbackJacobianParamDeriv
  convert! HasDerivAt.sub (hasDerivAt_const u (1 / 2 : Real)) hprod using 1 <;>
    simp only [id_eq] <;> ring

/-- The bound `|A'(u)| ≤ 7/3` from lines 4051--4059 of the manuscript. -/
theorem abs_feedbackJacobianParamDeriv_le
    {u y : Real} (hu : |u| ≤ 1 / 16)
    (hy : y ∈ Icc (-1 / 2 : Real) (1 / 2 : Real)) :
    |feedbackJacobianParamDeriv u y| ≤ 7 / 3 := by
  let z := feedbackInverse u y
  let z' := -shape z / feedbackSlope u z
  have hz : z ∈ Icc (-1 : Real) 1 := feedbackInverse_mem_Icc hu hy
  have hzabs : |z| ≤ (1 : Real) := (abs_le).2 hz
  have hz'abs : |z'| ≤ 8 / 3 := by
    exact abs_feedbackInverse_param_deriv_value_le hu hy
  change |-2 * z - 2 * u * z'| ≤ 7 / 3
  calc
    |-2 * z - 2 * u * z'| ≤ |-2 * z| + |2 * u * z'| := abs_sub _ _
    _ = 2 * |z| + 2 * |u| * |z'| := by
      norm_num [abs_mul]
    _ ≤ 2 * 1 + 2 * (1 / 16 : Real) * (8 / 3) := by
      gcongr
    _ = 7 / 3 := by norm_num

/-- The parameter derivative of the smooth density expression. -/
def feedbackDensityParamDeriv (u y : Real) : Real :=
  -(2 * feedbackJacobianParamDeriv u y) /
    (2 * feedbackJacobian u y) ^ 2

theorem hasDerivAt_feedbackDensityCore_param
    {u y : Real} (hu : |u| ≤ 1 / 16)
    (hy : y ∈ Icc (-1 / 2 : Real) (1 / 2 : Real)) :
    HasDerivAt (fun v => feedbackDensityCore v y)
      (feedbackDensityParamDeriv u y) u := by
  have hA := hasDerivAt_feedbackJacobian_param hu hy
  have hden : 2 * feedbackJacobian u y ≠ 0 := by
    exact ne_of_gt (mul_pos (by norm_num)
      (lt_of_lt_of_le (by norm_num) (feedbackJacobian_mem_Icc hu hy).1))
  have hinv := (hA.const_mul 2).inv hden
  simpa only [feedbackDensityCore, one_div, feedbackDensityParamDeriv] using! hinv

/-- The exact estimate `|∂_u p_u(y)| ≤ 224/27 < 9`. -/
theorem abs_feedbackDensityParamDeriv_le
    {u y : Real} (hu : |u| ≤ 1 / 16)
    (hy : y ∈ Icc (-1 / 2 : Real) (1 / 2 : Real)) :
    |feedbackDensityParamDeriv u y| ≤ 224 / 27 := by
  have hA := feedbackJacobian_mem_Icc hu hy
  have hApos : 0 < feedbackJacobian u y :=
    lt_of_lt_of_le (by norm_num) hA.1
  have hAp := abs_feedbackJacobianParamDeriv_le hu hy
  have hden : 0 < (2 * feedbackJacobian u y) ^ 2 :=
    sq_pos_of_pos (mul_pos (by norm_num) hApos)
  have hden_lower : (9 / 16 : Real) ≤ (2 * feedbackJacobian u y) ^ 2 := by
    have hbase : (3 / 4 : Real) ≤ 2 * feedbackJacobian u y := by
      linarith [hA.1]
    calc
      (9 / 16 : Real) = (3 / 4 : Real) ^ 2 := by norm_num
      _ ≤ (2 * feedbackJacobian u y) ^ 2 :=
        (sq_le_sq₀ (by norm_num) (le_trans (by norm_num) hbase)).2 hbase
  unfold feedbackDensityParamDeriv
  rw [abs_div, abs_neg, abs_of_pos hden, abs_mul]
  norm_num
  rw [div_le_iff₀ hden]
  nlinarith

theorem abs_feedbackDensityParamDeriv_lt_nine
    {u y : Real} (hu : |u| ≤ 1 / 16)
    (hy : y ∈ Icc (-1 / 2 : Real) (1 / 2 : Real)) :
    |feedbackDensityParamDeriv u y| < 9 := by
  calc
    |feedbackDensityParamDeriv u y| ≤ 224 / 27 :=
      abs_feedbackDensityParamDeriv_le hu hy
    _ < 9 := by norm_num

/-- Mean-value estimate for the density, with the manuscript's convenient
strict upper constant replaced by the weak bound `9`. -/
theorem abs_feedbackDensityCore_sub_le
    {u v y : Real} (hu : |u| ≤ 1 / 16) (hv : |v| ≤ 1 / 16)
    (hy : y ∈ Icc (-1 / 2 : Real) (1 / 2 : Real)) :
    |feedbackDensityCore u y - feedbackDensityCore v y| ≤
      9 * |u - v| := by
  have huD : u ∈ Icc (-1 / 16 : Real) (1 / 16 : Real) := by
    have h := (abs_le).1 hu
    constructor <;> linarith
  have hvD : v ∈ Icc (-1 / 16 : Real) (1 / 16 : Real) := by
    have h := (abs_le).1 hv
    constructor <;> linarith
  have hdiff : ∀ w ∈ Icc (-1 / 16 : Real) (1 / 16 : Real),
      DifferentiableAt Real (fun q => feedbackDensityCore q y) w := by
    intro w hw
    have haw : |w| ≤ (1 / 16 : Real) := by
      rw [abs_le]
      constructor <;> linarith [hw.1, hw.2]
    exact (hasDerivAt_feedbackDensityCore_param haw hy).differentiableAt
  have hbound : ∀ w ∈ Icc (-1 / 16 : Real) (1 / 16 : Real),
      ‖deriv (fun q => feedbackDensityCore q y) w‖ ≤ (9 : Real) := by
    intro w hw
    have haw : |w| ≤ (1 / 16 : Real) := by
      rw [abs_le]
      constructor <;> linarith [hw.1, hw.2]
    rw [(hasDerivAt_feedbackDensityCore_param haw hy).deriv,
      Real.norm_eq_abs]
    exact (abs_feedbackDensityParamDeriv_lt_nine haw hy).le
  have hmv := Convex.norm_image_sub_le_of_norm_deriv_le
    hdiff hbound (convex_Icc (-1 / 16 : Real) (1 / 16 : Real)) huD hvD
  simpa [Real.norm_eq_abs, abs_sub_comm] using hmv

/-- The chi-square integral which controls both information estimates. -/
def feedbackChiSquared (u v : Real) : Real :=
  ∫ y in (-1 / 2 : Real)..(1 / 2 : Real),
    (feedbackDensityCore u y - feedbackDensityCore v y) ^ 2 /
      feedbackDensityCore v y

theorem continuousOn_feedbackChiSquaredIntegrand
    {u v : Real} (hu : |u| ≤ 1 / 16) (hv : |v| ≤ 1 / 16) :
    ContinuousOn
      (fun y => (feedbackDensityCore u y - feedbackDensityCore v y) ^ 2 /
        feedbackDensityCore v y)
      (Icc (-1 / 2 : Real) (1 / 2 : Real)) := by
  apply ContinuousOn.div
    ((continuousOn_feedbackDensityCore hu).sub
      (continuousOn_feedbackDensityCore hv) |>.pow 2)
    (continuousOn_feedbackDensityCore hv)
  intro y hy
  exact ne_of_gt (lt_of_lt_of_le (by norm_num)
    (feedbackDensityCore_mem_Icc hv hy).1)

theorem intervalIntegrable_feedbackDensityCore
    {u : Real} (hu : |u| ≤ 1 / 16) :
    IntervalIntegrable (feedbackDensityCore u) volume
      (-1 / 2 : Real) (1 / 2 : Real) :=
  (continuousOn_feedbackDensityCore hu).intervalIntegrable_of_Icc (by norm_num)

theorem intervalIntegrable_feedbackChiSquaredIntegrand
    {u v : Real} (hu : |u| ≤ 1 / 16) (hv : |v| ≤ 1 / 16) :
    IntervalIntegrable
      (fun y => (feedbackDensityCore u y - feedbackDensityCore v y) ^ 2 /
        feedbackDensityCore v y) volume
      (-1 / 2 : Real) (1 / 2 : Real) :=
  (continuousOn_feedbackChiSquaredIntegrand hu hv).intervalIntegrable_of_Icc
    (by norm_num)

/-- Pointwise form of the strict estimate in lines 4070--4076, rounded up to
the exact constant `128`. -/
theorem feedbackChiSquaredIntegrand_le
    {u v y : Real} (hu : |u| ≤ 1 / 16) (hv : |v| ≤ 1 / 16)
    (hy : y ∈ Icc (-1 / 2 : Real) (1 / 2 : Real)) :
    (feedbackDensityCore u y - feedbackDensityCore v y) ^ 2 /
        feedbackDensityCore v y ≤
      128 * (u - v) ^ 2 := by
  have hpv := feedbackDensityCore_mem_Icc hv hy
  have hpvpos : 0 < feedbackDensityCore v y :=
    lt_of_lt_of_le (by norm_num) hpv.1
  have habs := abs_feedbackDensityCore_sub_le hu hv hy
  have hsq :
      (feedbackDensityCore u y - feedbackDensityCore v y) ^ 2 ≤
        81 * (u - v) ^ 2 := by
    have hsquare :
        (feedbackDensityCore u y - feedbackDensityCore v y) ^ 2 ≤
          (9 * |u - v|) ^ 2 := by
      rw [sq_le_sq]
      simpa using habs
    nlinarith [sq_abs (u - v)]
  rw [div_le_iff₀ hpvpos]
  calc
    (feedbackDensityCore u y - feedbackDensityCore v y) ^ 2 ≤
        81 * (u - v) ^ 2 := hsq
    _ ≤ (128 * (u - v) ^ 2) * feedbackDensityCore v y := by
      have hcoef : (81 : Real) ≤ 128 * feedbackDensityCore v y := by
        nlinarith [hpv.1]
      simpa [mul_assoc, mul_left_comm, mul_comm] using
        mul_le_mul_of_nonneg_right hcoef (sq_nonneg (u - v))

/-- Equation `eq:lower-feedback-kl`'s chi-square precursor, with the exact
constant used in the paper. -/
theorem feedbackChiSquared_le
    {u v : Real} (hu : |u| ≤ 1 / 16) (hv : |v| ≤ 1 / 16) :
    feedbackChiSquared u v ≤ 128 * (u - v) ^ 2 := by
  unfold feedbackChiSquared
  calc
    (∫ y in (-1 / 2 : Real)..(1 / 2 : Real),
        (feedbackDensityCore u y - feedbackDensityCore v y) ^ 2 /
          feedbackDensityCore v y) ≤
        ∫ _y in (-1 / 2 : Real)..(1 / 2 : Real),
          128 * (u - v) ^ 2 := by
      apply intervalIntegral.integral_mono_on (by norm_num)
        (intervalIntegrable_feedbackChiSquaredIntegrand hu hv)
        ((continuous_const : Continuous
          (fun _ : Real => 128 * (u - v) ^ 2)).intervalIntegrable _ _)
      intro y hy
      exact feedbackChiSquaredIntegrand_le hu hv hy
    _ = 128 * (u - v) ^ 2 := by norm_num

/-- Kullback--Leibler divergence of the two scalar feedback densities. -/
def feedbackKL (u v : Real) : Real :=
  ∫ y in (-1 / 2 : Real)..(1 / 2 : Real),
    feedbackDensityCore u y *
      Real.log (feedbackDensityCore u y / feedbackDensityCore v y)

theorem continuousOn_feedbackKLIntegrand
    {u v : Real} (hu : |u| ≤ 1 / 16) (hv : |v| ≤ 1 / 16) :
    ContinuousOn
      (fun y => feedbackDensityCore u y *
        Real.log (feedbackDensityCore u y / feedbackDensityCore v y))
      (Icc (-1 / 2 : Real) (1 / 2 : Real)) := by
  have hpu := continuousOn_feedbackDensityCore hu
  have hpv := continuousOn_feedbackDensityCore hv
  have hratio : ContinuousOn
      (fun y => feedbackDensityCore u y / feedbackDensityCore v y)
      (Icc (-1 / 2 : Real) (1 / 2 : Real)) := by
    apply hpu.div hpv
    intro y hy
    exact ne_of_gt (lt_of_lt_of_le (by norm_num)
      (feedbackDensityCore_mem_Icc hv hy).1)
  exact hpu.mul <| hratio.log <| by
    intro y hy
    exact ne_of_gt <| div_pos
      (lt_of_lt_of_le (by norm_num) (feedbackDensityCore_mem_Icc hu hy).1)
      (lt_of_lt_of_le (by norm_num) (feedbackDensityCore_mem_Icc hv hy).1)

theorem intervalIntegrable_feedbackKLIntegrand
    {u v : Real} (hu : |u| ≤ 1 / 16) (hv : |v| ≤ 1 / 16) :
    IntervalIntegrable
      (fun y => feedbackDensityCore u y *
        Real.log (feedbackDensityCore u y / feedbackDensityCore v y))
      volume (-1 / 2 : Real) (1 / 2 : Real) :=
  (continuousOn_feedbackKLIntegrand hu hv).intervalIntegrable_of_Icc
    (by norm_num)

/-- Pointwise `KL ≤ chi-square`, retaining the linear term which vanishes
after density normalization. -/
theorem feedbackKLIntegrand_le_chiSquared_add_sub
    {u v y : Real} (hu : |u| ≤ 1 / 16) (hv : |v| ≤ 1 / 16)
    (hy : y ∈ Icc (-1 / 2 : Real) (1 / 2 : Real)) :
    feedbackDensityCore u y *
        Real.log (feedbackDensityCore u y / feedbackDensityCore v y) ≤
      (feedbackDensityCore u y - feedbackDensityCore v y) ^ 2 /
          feedbackDensityCore v y +
        (feedbackDensityCore u y - feedbackDensityCore v y) := by
  have hpu : 0 < feedbackDensityCore u y :=
    lt_of_lt_of_le (by norm_num) (feedbackDensityCore_mem_Icc hu hy).1
  have hpv : 0 < feedbackDensityCore v y :=
    lt_of_lt_of_le (by norm_num) (feedbackDensityCore_mem_Icc hv hy).1
  have hlog := Real.log_le_sub_one_of_pos (div_pos hpu hpv)
  have hmul := mul_le_mul_of_nonneg_left hlog hpu.le
  calc
    feedbackDensityCore u y *
        Real.log (feedbackDensityCore u y / feedbackDensityCore v y) ≤
      feedbackDensityCore u y *
        (feedbackDensityCore u y / feedbackDensityCore v y - 1) := hmul
    _ = (feedbackDensityCore u y - feedbackDensityCore v y) ^ 2 /
          feedbackDensityCore v y +
        (feedbackDensityCore u y - feedbackDensityCore v y) := by
      field_simp [ne_of_gt hpv]
      ring

/-- The standard density inequality `KL ≤ chi-square`, proved here from
`log x ≤ x-1` and the two normalization identities. -/
theorem feedbackKL_le_chiSquared
    {u v : Real} (hu : |u| ≤ 1 / 16) (hv : |v| ≤ 1 / 16) :
    feedbackKL u v ≤ feedbackChiSquared u v := by
  have hpu := intervalIntegrable_feedbackDensityCore hu
  have hpv := intervalIntegrable_feedbackDensityCore hv
  have hkl := intervalIntegrable_feedbackKLIntegrand hu hv
  have hchi := intervalIntegrable_feedbackChiSquaredIntegrand hu hv
  unfold feedbackKL feedbackChiSquared
  calc
    (∫ y in (-1 / 2 : Real)..(1 / 2 : Real),
        feedbackDensityCore u y *
          Real.log (feedbackDensityCore u y / feedbackDensityCore v y)) ≤
      ∫ y in (-1 / 2 : Real)..(1 / 2 : Real),
        (feedbackDensityCore u y - feedbackDensityCore v y) ^ 2 /
            feedbackDensityCore v y +
          (feedbackDensityCore u y - feedbackDensityCore v y) := by
      apply intervalIntegral.integral_mono_on (by norm_num) hkl
        (hchi.add (hpu.sub hpv))
      intro y hy
      exact feedbackKLIntegrand_le_chiSquared_add_sub hu hv hy
    _ = (∫ y in (-1 / 2 : Real)..(1 / 2 : Real),
        (feedbackDensityCore u y - feedbackDensityCore v y) ^ 2 /
          feedbackDensityCore v y) := by
      rw [intervalIntegral.integral_add hchi (hpu.sub hpv),
        intervalIntegral.integral_sub hpu hpv,
        integral_feedbackDensityCore hu, integral_feedbackDensityCore hv]
      ring

/-- Equation `eq:lower-feedback-kl`, with the paper's exact constant. -/
theorem feedbackKL_le
    {u v : Real} (hu : |u| ≤ 1 / 16) (hv : |v| ≤ 1 / 16) :
    feedbackKL u v ≤ 128 * (u - v) ^ 2 :=
  (feedbackKL_le_chiSquared hu hv).trans (feedbackChiSquared_le hu hv)

/-- The likelihood-ratio second moment from
`eq:lower-feedback-second-moment`. -/
def feedbackSecondMoment (u v : Real) : Real :=
  ∫ y in (-1 / 2 : Real)..(1 / 2 : Real),
    feedbackDensityCore u y ^ 2 / feedbackDensityCore v y

theorem continuousOn_feedbackSecondMomentIntegrand
    {u v : Real} (hu : |u| ≤ 1 / 16) (hv : |v| ≤ 1 / 16) :
    ContinuousOn
      (fun y => feedbackDensityCore u y ^ 2 / feedbackDensityCore v y)
      (Icc (-1 / 2 : Real) (1 / 2 : Real)) := by
  apply ContinuousOn.div
    ((continuousOn_feedbackDensityCore hu).pow 2)
    (continuousOn_feedbackDensityCore hv)
  intro y hy
  exact ne_of_gt (lt_of_lt_of_le (by norm_num)
    (feedbackDensityCore_mem_Icc hv hy).1)

theorem intervalIntegrable_feedbackSecondMomentIntegrand
    {u v : Real} (hu : |u| ≤ 1 / 16) (hv : |v| ≤ 1 / 16) :
    IntervalIntegrable
      (fun y => feedbackDensityCore u y ^ 2 / feedbackDensityCore v y)
      volume (-1 / 2 : Real) (1 / 2 : Real) :=
  (continuousOn_feedbackSecondMomentIntegrand hu hv).intervalIntegrable_of_Icc
    (by norm_num)

theorem feedbackSecondMoment_eq_one_add_chiSquared
    {u v : Real} (hu : |u| ≤ 1 / 16) (hv : |v| ≤ 1 / 16) :
    feedbackSecondMoment u v = 1 + feedbackChiSquared u v := by
  have hpu := intervalIntegrable_feedbackDensityCore hu
  have hpv := intervalIntegrable_feedbackDensityCore hv
  have hchi := intervalIntegrable_feedbackChiSquaredIntegrand hu hv
  unfold feedbackSecondMoment feedbackChiSquared
  calc
    (∫ y in (-1 / 2 : Real)..(1 / 2 : Real),
        feedbackDensityCore u y ^ 2 / feedbackDensityCore v y) =
      ∫ y in (-1 / 2 : Real)..(1 / 2 : Real),
        ((feedbackDensityCore u y - feedbackDensityCore v y) ^ 2 /
          feedbackDensityCore v y + 2 * feedbackDensityCore u y) -
            feedbackDensityCore v y := by
      apply intervalIntegral.integral_congr
      intro y hy
      have hy' : y ∈ Icc (-1 / 2 : Real) (1 / 2 : Real) := by
        rw [uIcc_of_le (by norm_num : (-1 / 2 : Real) ≤ 1 / 2)] at hy
        exact hy
      have hpvne : feedbackDensityCore v y ≠ 0 :=
        ne_of_gt (lt_of_lt_of_le (by norm_num)
          (feedbackDensityCore_mem_Icc hv hy').1)
      field_simp
      ring
    _ = (∫ y in (-1 / 2 : Real)..(1 / 2 : Real),
          (feedbackDensityCore u y - feedbackDensityCore v y) ^ 2 /
            feedbackDensityCore v y) +
        2 * (∫ y in (-1 / 2 : Real)..(1 / 2 : Real),
          feedbackDensityCore u y) -
        (∫ y in (-1 / 2 : Real)..(1 / 2 : Real),
          feedbackDensityCore v y) := by
      rw [intervalIntegral.integral_sub (hchi.add (hpu.const_mul 2)) hpv,
        intervalIntegral.integral_add hchi (hpu.const_mul 2),
        intervalIntegral.integral_const_mul]
    _ = 1 + (∫ y in (-1 / 2 : Real)..(1 / 2 : Real),
          (feedbackDensityCore u y - feedbackDensityCore v y) ^ 2 /
            feedbackDensityCore v y) := by
      rw [integral_feedbackDensityCore hu, integral_feedbackDensityCore hv]
      ring

/-- Equation `eq:lower-feedback-second-moment`, including the final
`1+x ≤ exp x` step. -/
theorem feedbackSecondMoment_le_exp
    {u v : Real} (hu : |u| ≤ 1 / 16) (hv : |v| ≤ 1 / 16) :
    feedbackSecondMoment u v ≤ Real.exp (128 * (u - v) ^ 2) := by
  rw [feedbackSecondMoment_eq_one_add_chiSquared hu hv]
  calc
    1 + feedbackChiSquared u v ≤ 1 + 128 * (u - v) ^ 2 := by
      gcongr
      exact feedbackChiSquared_le hu hv
    _ ≤ Real.exp (128 * (u - v) ^ 2) := by
      simpa [add_comm] using Real.add_one_le_exp (128 * (u - v) ^ 2)

end

end MsetsLower.Feedback

#print axioms MsetsLower.Feedback.measurable_feedbackDensity
#print axioms MsetsLower.Feedback.integral_feedbackDensity
#print axioms MsetsLower.Feedback.hasDerivAt_feedbackDensityCore_param
#print axioms MsetsLower.Feedback.abs_feedbackDensityCore_sub_le
#print axioms MsetsLower.Feedback.feedbackKL_le
#print axioms MsetsLower.Feedback.feedbackSecondMoment_le_exp
