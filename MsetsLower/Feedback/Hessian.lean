import MsetsLower.Feedback.Density
import Mathlib.Analysis.SpecialFunctions.Log.Deriv

/-!
# Parameter Hessian and four-term density estimate

This file follows the last part of the proof of
`lem:lower-feedback-density`.  We differentiate the inverse relation a
second time, bound the resulting inverse and log-Jacobian Hessians, and use
the mean-value theorem twice to obtain `eq:lower-density-four-term` with the
paper's factor `128`.
-/

namespace MsetsLower.Feedback

open Set
open scoped Interval

noncomputable section

/-- The manuscript's value of the parameter derivative of `F_u^{-1}(y)`. -/
def feedbackInverseParamDeriv (u y : Real) : Real :=
  -shape (feedbackInverse u y) / feedbackJacobian u y

/-- The value obtained by differentiating the inverse relation twice. -/
def feedbackInverseParamSecondDeriv (u y : Real) : Real :=
  (4 * feedbackInverse u y * feedbackInverseParamDeriv u y +
      2 * u * feedbackInverseParamDeriv u y ^ 2) /
    feedbackJacobian u y

theorem hasDerivAt_feedbackInverse_param'
    {u y : Real} (hu : |u| ≤ 1 / 16)
    (hy : y ∈ Icc (-1 / 2 : Real) (1 / 2 : Real)) :
    HasDerivAt (fun v => feedbackInverse v y)
      (feedbackInverseParamDeriv u y) u := by
  simpa only [feedbackInverseParamDeriv, feedbackJacobian] using
    hasDerivAt_feedbackInverse_param hu hy

theorem hasDerivAt_feedbackInverseParamDeriv
    {u y : Real} (hu : |u| ≤ 1 / 16)
    (hy : y ∈ Icc (-1 / 2 : Real) (1 / 2 : Real)) :
    HasDerivAt (fun v => feedbackInverseParamDeriv v y)
      (feedbackInverseParamSecondDeriv u y) u := by
  let z := feedbackInverse u y
  let z' := feedbackInverseParamDeriv u y
  let A := feedbackJacobian u y
  have hz : HasDerivAt (fun v => feedbackInverse v y) z' u := by
    exact hasDerivAt_feedbackInverse_param' hu hy
  have hA : HasDerivAt (fun v => feedbackJacobian v y)
      (feedbackJacobianParamDeriv u y) u :=
    hasDerivAt_feedbackJacobian_param hu hy
  have hshape : HasDerivAt (fun v => shape (feedbackInverse v y))
      (-2 * z * z') u := by
    have hg : HasDerivAt (fun x : Real => shape x) (-2 * z) z := by
      unfold shape
      convert! HasDerivAt.sub (hasDerivAt_const z (1 : Real))
        ((hasDerivAt_id z).pow 2) using 1 <;> simp only [id_eq] <;> ring
    convert! hg.comp u hz using 1 <;> simp only [Function.comp_apply] <;> ring
  have hA_ne : A ≠ 0 := by
    exact ne_of_gt (feedbackSlope_pos hu (feedbackInverse_mem_Icc hu hy))
  have hquot := hshape.neg.div hA hA_ne
  have himplicit : A * z' = -shape z := by
    change A * (-shape z / A) = -shape z
    field_simp [hA_ne]
  have hAp : feedbackJacobianParamDeriv u y = -2 * z - 2 * u * z' := by
    simp only [feedbackJacobianParamDeriv, feedbackInverseParamDeriv,
      feedbackJacobian, z, z']
  change HasDerivAt
    ((-fun v => shape (feedbackInverse v y)) /
      fun v => feedbackJacobian v y)
    (feedbackInverseParamSecondDeriv u y) u
  apply hquot.congr_deriv
  change
    (-(-2 * z * z') * A - (-shape z) * feedbackJacobianParamDeriv u y) /
        A ^ 2 =
      (4 * z * z' + 2 * u * z' ^ 2) / A
  rw [hAp]
  field_simp [hA_ne]
  linear_combination (-2 * z - 2 * u * z') * himplicit

/-- The manuscript's bound for the second parameter derivative,
with value at most `832/27 < 31`. -/
theorem abs_feedbackInverseParamSecondDeriv_le
    {u y : Real} (hu : |u| ≤ 1 / 16)
    (hy : y ∈ Icc (-1 / 2 : Real) (1 / 2 : Real)) :
    |feedbackInverseParamSecondDeriv u y| ≤ 832 / 27 := by
  let z := feedbackInverse u y
  let z' := feedbackInverseParamDeriv u y
  let A := feedbackJacobian u y
  have hz := feedbackInverse_mem_Icc hu hy
  have hzabs : |z| ≤ (1 : Real) := (abs_le).2 hz
  have hz'abs : |z'| ≤ 8 / 3 := by
    simpa only [z', feedbackInverseParamDeriv, feedbackJacobian] using
      abs_feedbackInverse_param_deriv_value_le hu hy
  have hA := feedbackJacobian_mem_Icc hu hy
  have hApos : 0 < A := lt_of_lt_of_le (by norm_num) hA.1
  unfold feedbackInverseParamSecondDeriv
  change |(4 * z * z' + 2 * u * z' ^ 2) / A| ≤ 832 / 27
  rw [abs_div, abs_of_pos hApos, div_le_iff₀ hApos]
  calc
    |4 * z * z' + 2 * u * z' ^ 2| ≤
        |4 * z * z'| + |2 * u * z' ^ 2| := abs_add_le _ _
    _ = 4 * |z| * |z'| + 2 * |u| * |z'| ^ 2 := by
      rw [abs_mul, abs_mul, abs_mul, abs_mul, abs_pow]
      norm_num
    _ ≤ 4 * 1 * (8 / 3 : Real) +
        2 * (1 / 16 : Real) * (8 / 3 : Real) ^ 2 := by
      gcongr
    _ ≤ (832 / 27 : Real) * A := by
      nlinarith [hA.1]

theorem abs_deriv_feedbackInverseParamDeriv_lt_thirty_one
    {u y : Real} (hu : |u| ≤ 1 / 16)
    (hy : y ∈ Icc (-1 / 2 : Real) (1 / 2 : Real)) :
    |deriv (fun v => feedbackInverseParamDeriv v y) u| < 31 := by
  rw [(hasDerivAt_feedbackInverseParamDeriv hu hy).deriv]
  exact lt_of_le_of_lt (abs_feedbackInverseParamSecondDeriv_le hu hy) (by norm_num)

/-- The second parameter derivative of the inverse Jacobian. -/
def feedbackJacobianParamSecondDeriv (u y : Real) : Real :=
  -4 * feedbackInverseParamDeriv u y -
    2 * u * feedbackInverseParamSecondDeriv u y

theorem hasDerivAt_feedbackJacobianParamDeriv
    {u y : Real} (hu : |u| ≤ 1 / 16)
    (hy : y ∈ Icc (-1 / 2 : Real) (1 / 2 : Real)) :
    HasDerivAt (fun v => feedbackJacobianParamDeriv v y)
      (feedbackJacobianParamSecondDeriv u y) u := by
  have hz := hasDerivAt_feedbackInverse_param' hu hy
  have hz' := hasDerivAt_feedbackInverseParamDeriv hu hy
  have hprod := HasDerivAt.mul ((hasDerivAt_id u).const_mul 2) hz'
  convert! HasDerivAt.sub (hz.const_mul (-2)) hprod using 1 <;>
    simp only [feedbackInverseParamDeriv,
      feedbackJacobianParamSecondDeriv, id_eq] <;> ring

/-- The manuscript's convenient bound `|A''(u)| < 15`. -/
theorem abs_feedbackJacobianParamSecondDeriv_lt_fifteen
    {u y : Real} (hu : |u| ≤ 1 / 16)
    (hy : y ∈ Icc (-1 / 2 : Real) (1 / 2 : Real)) :
    |feedbackJacobianParamSecondDeriv u y| < 15 := by
  have hz' : |feedbackInverseParamDeriv u y| ≤ 8 / 3 := by
    simpa only [feedbackInverseParamDeriv, feedbackJacobian] using
      abs_feedbackInverse_param_deriv_value_le hu hy
  have hz'' := abs_feedbackInverseParamSecondDeriv_le hu hy
  unfold feedbackJacobianParamSecondDeriv
  calc
    |-4 * feedbackInverseParamDeriv u y -
        2 * u * feedbackInverseParamSecondDeriv u y| ≤
      |-4 * feedbackInverseParamDeriv u y| +
        |2 * u * feedbackInverseParamSecondDeriv u y| := abs_sub _ _
    _ = 4 * |feedbackInverseParamDeriv u y| +
        2 * |u| * |feedbackInverseParamSecondDeriv u y| := by
      rw [abs_mul, abs_mul, abs_mul]
      norm_num
    _ ≤ 4 * (8 / 3 : Real) + 2 * (1 / 16 : Real) * (832 / 27 : Real) := by
      gcongr
    _ < 15 := by norm_num

/-- `H_y(u)=log F'_u(F_u^{-1}(y))`. -/
def feedbackLogJacobian (u y : Real) : Real :=
  Real.log (feedbackJacobian u y)

/-- The first parameter derivative of `feedbackLogJacobian`. -/
def feedbackLogJacobianParamDeriv (u y : Real) : Real :=
  feedbackJacobianParamDeriv u y / feedbackJacobian u y

/-- The second parameter derivative of `feedbackLogJacobian`. -/
def feedbackLogJacobianParamSecondDeriv (u y : Real) : Real :=
  feedbackJacobianParamSecondDeriv u y / feedbackJacobian u y -
    (feedbackJacobianParamDeriv u y / feedbackJacobian u y) ^ 2

theorem hasDerivAt_feedbackLogJacobian_param
    {u y : Real} (hu : |u| ≤ 1 / 16)
    (hy : y ∈ Icc (-1 / 2 : Real) (1 / 2 : Real)) :
    HasDerivAt (fun v => feedbackLogJacobian v y)
      (feedbackLogJacobianParamDeriv u y) u := by
  have hA := hasDerivAt_feedbackJacobian_param hu hy
  have hA_ne : feedbackJacobian u y ≠ 0 := by
    exact ne_of_gt (lt_of_lt_of_le (by norm_num)
      (feedbackJacobian_mem_Icc hu hy).1)
  simpa only [feedbackLogJacobian, feedbackLogJacobianParamDeriv] using
    hA.log hA_ne

theorem hasDerivAt_feedbackLogJacobianParamDeriv
    {u y : Real} (hu : |u| ≤ 1 / 16)
    (hy : y ∈ Icc (-1 / 2 : Real) (1 / 2 : Real)) :
    HasDerivAt (fun v => feedbackLogJacobianParamDeriv v y)
      (feedbackLogJacobianParamSecondDeriv u y) u := by
  have hA := hasDerivAt_feedbackJacobian_param hu hy
  have hA' := hasDerivAt_feedbackJacobianParamDeriv hu hy
  have hA_ne : feedbackJacobian u y ≠ 0 := by
    exact ne_of_gt (lt_of_lt_of_le (by norm_num)
      (feedbackJacobian_mem_Icc hu hy).1)
  have hquot := hA'.div hA hA_ne
  change HasDerivAt
    ((fun v => feedbackJacobianParamDeriv v y) /
      fun v => feedbackJacobian v y)
    (feedbackLogJacobianParamSecondDeriv u y) u
  apply hquot.congr_deriv
  simp only [feedbackLogJacobianParamSecondDeriv]
  field_simp [hA_ne]

/-- The paper's numerical Hessian estimate `|H_y''(u)| < 79`. -/
theorem abs_feedbackLogJacobianParamSecondDeriv_lt_seventy_nine
    {u y : Real} (hu : |u| ≤ 1 / 16)
    (hy : y ∈ Icc (-1 / 2 : Real) (1 / 2 : Real)) :
    |feedbackLogJacobianParamSecondDeriv u y| < 79 := by
  have hA := feedbackJacobian_mem_Icc hu hy
  have hApos : 0 < feedbackJacobian u y :=
    lt_of_lt_of_le (by norm_num) hA.1
  have hA' := abs_feedbackJacobianParamDeriv_le hu hy
  have hA'' := abs_feedbackJacobianParamSecondDeriv_lt_fifteen hu hy
  unfold feedbackLogJacobianParamSecondDeriv
  calc
    |feedbackJacobianParamSecondDeriv u y / feedbackJacobian u y -
        (feedbackJacobianParamDeriv u y / feedbackJacobian u y) ^ 2| ≤
      |feedbackJacobianParamSecondDeriv u y / feedbackJacobian u y| +
        |(feedbackJacobianParamDeriv u y / feedbackJacobian u y) ^ 2| :=
      abs_sub _ _
    _ = |feedbackJacobianParamSecondDeriv u y| / feedbackJacobian u y +
        (|feedbackJacobianParamDeriv u y| / feedbackJacobian u y) ^ 2 := by
      rw [abs_div, abs_of_pos hApos, abs_pow, abs_div, abs_of_pos hApos]
    _ < (15 : Real) / (3 / 8 : Real) +
        ((7 / 3 : Real) / (3 / 8 : Real)) ^ 2 := by
      have hrecip : 0 < (feedbackJacobian u y)⁻¹ := inv_pos.mpr hApos
      have hden : (3 / 8 : Real) ≤ feedbackJacobian u y := hA.1
      have hinv : (feedbackJacobian u y)⁻¹ ≤ ((3 / 8 : Real))⁻¹ := by
        exact (inv_le_inv₀ hApos (by norm_num)).2 hden
      rw [div_eq_mul_inv, div_eq_mul_inv, div_eq_mul_inv, div_eq_mul_inv]
      have hfirst :
          |feedbackJacobianParamSecondDeriv u y| * (feedbackJacobian u y)⁻¹ <
            15 * ((3 / 8 : Real))⁻¹ := by
        exact (mul_lt_mul_of_pos_right hA'' hrecip).trans_le
          (mul_le_mul_of_nonneg_left hinv (by norm_num))
      have hsecond :
          |feedbackJacobianParamDeriv u y| * (feedbackJacobian u y)⁻¹ ≤
            (7 / 3 : Real) * ((3 / 8 : Real))⁻¹ := by
        exact (mul_le_mul hA' hinv (by positivity) (by positivity))
      have hx0 : 0 ≤
          |feedbackJacobianParamDeriv u y| * (feedbackJacobian u y)⁻¹ :=
        mul_nonneg (abs_nonneg _) hrecip.le
      have hy0 : 0 ≤ (7 / 3 : Real) * ((3 / 8 : Real))⁻¹ := by positivity
      have hsq :
          (|feedbackJacobianParamDeriv u y| * (feedbackJacobian u y)⁻¹) ^ 2 ≤
            ((7 / 3 : Real) * ((3 / 8 : Real))⁻¹) ^ 2 :=
        (sq_le_sq₀ hx0 hy0).2 hsecond
      nlinarith
    _ < 79 := by norm_num

theorem abs_deriv_feedbackLogJacobianParamDeriv_le
    {u y : Real} (hu : |u| ≤ 1 / 16)
    (hy : y ∈ Icc (-1 / 2 : Real) (1 / 2 : Real)) :
    |deriv (fun v => feedbackLogJacobianParamDeriv v y) u| ≤ 128 := by
  rw [(hasDerivAt_feedbackLogJacobianParamDeriv hu hy).deriv]
  exact (abs_feedbackLogJacobianParamSecondDeriv_lt_seventy_nine hu hy).le.trans
    (by norm_num)

/-- The first mean-value-theorem application: `H'_y` is `128`-Lipschitz
on the permitted parameter interval. -/
theorem abs_feedbackLogJacobianParamDeriv_sub_le
    {a b y : Real} (ha : |a| ≤ 1 / 16) (hb : |b| ≤ 1 / 16)
    (hy : y ∈ Icc (-1 / 2 : Real) (1 / 2 : Real)) :
    |feedbackLogJacobianParamDeriv a y -
        feedbackLogJacobianParamDeriv b y| ≤ 128 * |a - b| := by
  have haD : a ∈ Icc (-(1 / 16 : Real)) (1 / 16 : Real) := by
    exact Set.mem_Icc.mpr ((abs_le).1 ha)
  have hbD : b ∈ Icc (-(1 / 16 : Real)) (1 / 16 : Real) := by
    exact Set.mem_Icc.mpr ((abs_le).1 hb)
  have hdiff : ∀ w ∈ Icc (-(1 / 16 : Real)) (1 / 16 : Real),
      DifferentiableAt Real (fun q => feedbackLogJacobianParamDeriv q y) w := by
    intro w hw
    have haw : |w| ≤ (1 / 16 : Real) := by
      exact (abs_le).2 (Set.mem_Icc.mp hw)
    exact (hasDerivAt_feedbackLogJacobianParamDeriv haw hy).differentiableAt
  have hbound : ∀ w ∈ Icc (-(1 / 16 : Real)) (1 / 16 : Real),
      ‖deriv (fun q => feedbackLogJacobianParamDeriv q y) w‖ ≤ (128 : Real) := by
    intro w hw
    have haw : |w| ≤ (1 / 16 : Real) := by
      exact (abs_le).2 (Set.mem_Icc.mp hw)
    simpa only [Real.norm_eq_abs] using
      abs_deriv_feedbackLogJacobianParamDeriv_le haw hy
  have hmv := Convex.norm_image_sub_le_of_norm_deriv_le
    hdiff hbound (convex_Icc (-(1 / 16 : Real)) (1 / 16 : Real)) hbD haD
  simpa only [Real.norm_eq_abs] using hmv

/-- Equation `eq:lower-density-four-term`, with exactly the four parameter
domain assumptions stated in the manuscript. -/
theorem feedback_density_four_term
    {u s t y : Real}
    (hu : |u| ≤ 1 / 16)
    (hus : |u + s| ≤ 1 / 16)
    (hut : |u + t| ≤ 1 / 16)
    (hust : |u + s + t| ≤ 1 / 16)
    (hy : y ∈ Icc (-1 / 2 : Real) (1 / 2 : Real)) :
    |feedbackLogJacobian (u + s) y + feedbackLogJacobian (u + t) y -
        feedbackLogJacobian u y - feedbackLogJacobian (u + s + t) y| ≤
      128 * |s * t| := by
  let D : Real → Real := fun w =>
    feedbackLogJacobian (w + t) y - feedbackLogJacobian w y
  have hparam : ∀ w ∈ [[u, u + s]],
      |w| ≤ (1 / 16 : Real) ∧ |w + t| ≤ (1 / 16 : Real) := by
    intro w hw
    have huD : u ∈ Icc (-(1 / 16 : Real)) (1 / 16 : Real) := by
      exact Set.mem_Icc.mpr ((abs_le).1 hu)
    have husD : u + s ∈ Icc (-(1 / 16 : Real)) (1 / 16 : Real) := by
      exact Set.mem_Icc.mpr ((abs_le).1 hus)
    have hutD : u + t ∈ Icc (-(1 / 16 : Real)) (1 / 16 : Real) := by
      exact Set.mem_Icc.mpr ((abs_le).1 hut)
    have hustD : u + s + t ∈ Icc (-(1 / 16 : Real)) (1 / 16 : Real) := by
      exact Set.mem_Icc.mpr ((abs_le).1 hust)
    have hwD : w ∈ Icc (-(1 / 16 : Real)) (1 / 16 : Real) :=
      uIcc_subset_Icc huD husD hw
    have hwtU : w + t ∈ [[u + t, u + s + t]] := by
      have himage : w + t ∈ (fun q : Real => q + t) '' [[u, u + s]] :=
        ⟨w, hw, rfl⟩
      simpa only [image_add_const_uIcc] using himage
    have hwtD : w + t ∈ Icc (-(1 / 16 : Real)) (1 / 16 : Real) :=
      uIcc_subset_Icc hutD hustD hwtU
    exact ⟨(abs_le).2 (Set.mem_Icc.mp hwD),
      (abs_le).2 (Set.mem_Icc.mp hwtD)⟩
  have hdiff : ∀ w ∈ [[u, u + s]], DifferentiableAt Real D w := by
    intro w hw
    have hp := hparam w hw
    have hshift : HasDerivAt (fun q => feedbackLogJacobian (q + t) y)
        (feedbackLogJacobianParamDeriv (w + t) y) w := by
      exact (hasDerivAt_feedbackLogJacobian_param hp.2 hy).comp_add_const w t
    exact (hshift.sub
      (hasDerivAt_feedbackLogJacobian_param hp.1 hy)).differentiableAt
  have hbound : ∀ w ∈ [[u, u + s]],
      ‖deriv D w‖ ≤ 128 * |t| := by
    intro w hw
    have hp := hparam w hw
    have hderiv : deriv D w =
        feedbackLogJacobianParamDeriv (w + t) y -
          feedbackLogJacobianParamDeriv w y := by
      have hshift : HasDerivAt (fun q => feedbackLogJacobian (q + t) y)
          (feedbackLogJacobianParamDeriv (w + t) y) w := by
        exact (hasDerivAt_feedbackLogJacobian_param hp.2 hy).comp_add_const w t
      exact (hshift.sub
        (hasDerivAt_feedbackLogJacobian_param hp.1 hy)).deriv
    rw [hderiv, Real.norm_eq_abs]
    simpa only [add_sub_cancel_left] using
      abs_feedbackLogJacobianParamDeriv_sub_le hp.2 hp.1 hy
  have hmv := Convex.norm_image_sub_le_of_norm_deriv_le hdiff hbound
    (convex_uIcc u (u + s)) left_mem_uIcc right_mem_uIcc
  change ‖D (u + s) - D u‖ ≤ (128 * |t|) * ‖u + s - u‖ at hmv
  dsimp only [D] at hmv
  rw [Real.norm_eq_abs, Real.norm_eq_abs] at hmv
  calc
    |feedbackLogJacobian (u + s) y + feedbackLogJacobian (u + t) y -
        feedbackLogJacobian u y - feedbackLogJacobian (u + s + t) y| =
      |(feedbackLogJacobian (u + s + t) y - feedbackLogJacobian (u + s) y) -
        (feedbackLogJacobian (u + t) y - feedbackLogJacobian u y)| := by
          rw [show feedbackLogJacobian (u + s) y + feedbackLogJacobian (u + t) y -
              feedbackLogJacobian u y - feedbackLogJacobian (u + s + t) y =
            -((feedbackLogJacobian (u + s + t) y - feedbackLogJacobian (u + s) y) -
              (feedbackLogJacobian (u + t) y - feedbackLogJacobian u y)) by ring,
            abs_neg]
    _ ≤ (128 * |t|) * |u + s - u| := hmv
    _ = 128 * |s * t| := by rw [abs_mul]; ring

end

end MsetsLower.Feedback

#print axioms MsetsLower.Feedback.hasDerivAt_feedbackInverseParamDeriv
#print axioms MsetsLower.Feedback.abs_feedbackLogJacobianParamSecondDeriv_lt_seventy_nine
#print axioms MsetsLower.Feedback.feedback_density_four_term
