import MsetsLower.Feedback.Density

/-!
# Score-shape derivative estimate

This file closes `eq:lower-feedback-score-derivative` from
`lem:lower-feedback-density`.
-/

namespace MsetsLower.Feedback

open Set

noncomputable section

/-- The function `G_y(u)=g(F_u^{-1}(y))` from the manuscript. -/
def feedbackScoreShape (u y : Real) : Real :=
  shape (feedbackInverse u y)

/-- Exact derivative value of `G_y` with respect to `u`. -/
def feedbackScoreShapeParamDeriv (u y : Real) : Real :=
  2 * feedbackInverse u y * feedbackScoreShape u y /
    feedbackSlope u (feedbackInverse u y)

theorem hasDerivAt_feedbackScoreShape_param
    {u y : Real} (hu : |u| ≤ 1 / 16)
    (hy : y ∈ Icc (-1 / 2 : Real) (1 / 2 : Real)) :
    HasDerivAt (fun v => feedbackScoreShape v y)
      (feedbackScoreShapeParamDeriv u y) u := by
  have hz := hasDerivAt_feedbackInverse_param hu hy
  have hshape : HasDerivAt (fun z : Real => shape z)
      (-2 * feedbackInverse u y) (feedbackInverse u y) := by
    unfold shape
    convert! HasDerivAt.sub (hasDerivAt_const _ (1 : Real))
      ((hasDerivAt_id _).pow 2) using 1 <;> simp only [id_eq] <;> ring
  have hcomp := hshape.comp u hz
  convert! hcomp using 1 <;>
    simp only [Function.comp_apply, feedbackScoreShape,
      feedbackScoreShapeParamDeriv] <;> ring

theorem feedbackScoreShape_mem_Icc
    {u y : Real} (hu : |u| ≤ 1 / 16)
    (hy : y ∈ Icc (-1 / 2 : Real) (1 / 2 : Real)) :
    feedbackScoreShape u y ∈ Icc (0 : Real) 1 :=
  shape_mem_Icc (feedbackInverse_mem_Icc hu hy)

/-- The sharper intermediate estimate `|G'_y(u)| ≤ (16/3)G_y(u)` from
lines 4131--4142. -/
theorem abs_feedbackScoreShapeParamDeriv_le
    {u y : Real} (hu : |u| ≤ 1 / 16)
    (hy : y ∈ Icc (-1 / 2 : Real) (1 / 2 : Real)) :
    |feedbackScoreShapeParamDeriv u y| ≤
      (16 / 3 : Real) * feedbackScoreShape u y := by
  have hz := feedbackInverse_mem_Icc hu hy
  have hzabs : |feedbackInverse u y| ≤ (1 : Real) := (abs_le).2 hz
  have hG := feedbackScoreShape_mem_Icc hu hy
  have hA := feedbackSlope_mem_Icc hu hz
  have hApos := feedbackSlope_pos hu hz
  unfold feedbackScoreShapeParamDeriv
  rw [abs_div, abs_mul, abs_mul, abs_of_nonneg hG.1,
    abs_of_pos hApos, div_le_iff₀ hApos]
  have hnum :
      |(2 : Real)| * |feedbackInverse u y| * feedbackScoreShape u y ≤
        2 * feedbackScoreShape u y := by
    norm_num
    have htwo : 2 * |feedbackInverse u y| ≤ (2 : Real) := by
      nlinarith
    exact mul_le_mul_of_nonneg_right htwo hG.1
  calc
    |(2 : Real)| * |feedbackInverse u y| * feedbackScoreShape u y ≤
        2 * feedbackScoreShape u y := hnum
    _ ≤ (16 / 3 * feedbackScoreShape u y) *
        feedbackSlope u (feedbackInverse u y) := by
      have hcoef : (2 : Real) ≤ (16 / 3) *
          feedbackSlope u (feedbackInverse u y) := by
        nlinarith [hA.1]
      simpa [mul_assoc, mul_left_comm, mul_comm] using
        mul_le_mul_of_nonneg_right hcoef hG.1

/-- Equation `eq:lower-feedback-score-derivative`. -/
theorem abs_deriv_feedbackScoreShape_le
    {u y : Real} (hu : |u| ≤ 1 / 16)
    (hy : y ∈ Icc (-1 / 2 : Real) (1 / 2 : Real)) :
    |deriv (fun v => feedbackScoreShape v y) u| ≤
      6 * feedbackScoreShape u y := by
  rw [(hasDerivAt_feedbackScoreShape_param hu hy).deriv]
  calc
    |feedbackScoreShapeParamDeriv u y| ≤
        (16 / 3 : Real) * feedbackScoreShape u y :=
      abs_feedbackScoreShapeParamDeriv_le hu hy
    _ ≤ 6 * feedbackScoreShape u y := by
      exact mul_le_mul_of_nonneg_right (by norm_num) (feedbackScoreShape_mem_Icc hu hy).1

end

end MsetsLower.Feedback

#print axioms MsetsLower.Feedback.abs_deriv_feedbackScoreShape_le
