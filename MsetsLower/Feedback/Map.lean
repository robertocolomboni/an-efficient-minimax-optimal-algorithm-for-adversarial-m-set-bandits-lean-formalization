import MsetsLower.Prelude
import Mathlib.Topology.Order.IntermediateValue
import Mathlib.Analysis.Calculus.Deriv.MeanValue

/-!
# The scalar feedback map

This is the deterministic analytic core of `lem:lower-feedback-density`.
It formalizes the map `F_u(z)=z/2+u(1-z^2)`, the exact derivative bounds on
the paper's parameter rectangle, and the resulting bijection of intervals.
-/

namespace MsetsLower.Feedback

open Set

noncomputable section

/-- The perturbation shape `g(z)=1-z^2`. -/
def shape (z : Real) : Real := 1 - z ^ 2

/-- The feedback map `F_u`. -/
def feedbackMap (u z : Real) : Real := z / 2 + u * shape z

/-- The derivative of `F_u` in its spatial argument. -/
def feedbackSlope (u z : Real) : Real := 1 / 2 - 2 * u * z

/-- Exact quadratic increment formula.  In particular, after division by
`y-z` and passage to the limit, the spatial derivative is
`feedbackSlope u z`. -/
theorem feedbackMap_sub (u y z : Real) :
    feedbackMap u y - feedbackMap u z =
      (y - z) * ((1 / 2 : Real) - u * (y + z)) := by
  dsimp [feedbackMap, shape]
  ring

@[simp] theorem feedbackMap_neg_one (u : Real) :
    feedbackMap u (-1) = -1 / 2 := by
  norm_num [feedbackMap, shape]

@[simp] theorem feedbackMap_one (u : Real) :
    feedbackMap u 1 = 1 / 2 := by
  norm_num [feedbackMap, shape]

/-- Equation `eq:lower-feedback-derivative-range`. -/
theorem feedbackSlope_mem_Icc
    {u z : Real} (hu : |u| ≤ 1 / 16) (hz : z ∈ Icc (-1 : Real) 1) :
    feedbackSlope u z ∈ Icc (3 / 8 : Real) (5 / 8 : Real) := by
  have hzabs : |z| ≤ (1 : Real) := (abs_le).2 hz
  have huz : |u * z| ≤ (1 / 16 : Real) := by
    calc
      |u * z| = |u| * |z| := abs_mul u z
      _ ≤ (1 / 16 : Real) * 1 :=
        mul_le_mul hu hzabs (abs_nonneg z) (by norm_num)
      _ = (1 / 16 : Real) := by norm_num
  have huz' := (abs_le.mp huz)
  constructor <;> dsimp [feedbackSlope] <;> nlinarith

theorem feedbackSlope_pos
    {u z : Real} (hu : |u| ≤ 1 / 16) (hz : z ∈ Icc (-1 : Real) 1) :
    0 < feedbackSlope u z := by
  have h := (feedbackSlope_mem_Icc hu hz).1
  norm_num at h ⊢
  linarith

/-- The spatial derivative of `feedbackMap`, before the monotonicity argument. -/
theorem hasDerivAt_feedbackMap (u z : Real) :
    HasDerivAt (feedbackMap u) (feedbackSlope u z) z := by
  have hid : HasDerivAt (fun x : Real => x) 1 z := hasDerivAt_id z
  have hsq : HasDerivAt (fun x : Real => x ^ 2) (2 * z) z := by
    simpa using! hid.pow 2
  have hshape : HasDerivAt (fun x : Real => 1 - x ^ 2) (-2 * z) z := by
    convert! HasDerivAt.sub (hasDerivAt_const z (1 : Real)) hsq using 1
    ring
  have hlinear : HasDerivAt (fun x : Real => x / 2) (1 / 2) z :=
    hid.div_const 2
  have hpert : HasDerivAt (fun x : Real => u * (1 - x ^ 2)) (u * (-2 * z)) z :=
    HasDerivAt.const_mul u hshape
  convert! HasDerivAt.add hlinear hpert using 1
  simp only [feedbackSlope]
  ring

/-- As in the paper, the derivative lower bound gives strict monotonicity. -/
theorem feedbackMap_strictMonoOn
    {u : Real} (hu : |u| ≤ 1 / 16) :
    StrictMonoOn (feedbackMap u) (Icc (-1 : Real) 1) := by
  apply strictMonoOn_of_deriv_pos (convex_Icc _ _)
  · exact fun z _ => (hasDerivAt_feedbackMap u z).continuousAt.continuousWithinAt
  · intro z hz
    rw [(hasDerivAt_feedbackMap u z).deriv]
    exact feedbackSlope_pos hu (interior_subset hz)

theorem continuous_feedbackMap (u : Real) : Continuous (feedbackMap u) := by
  unfold feedbackMap shape
  fun_prop

/-- The interval image clause in the diffeomorphism statement. -/
theorem feedbackMap_image_Icc
    {u : Real} (hu : |u| ≤ 1 / 16) :
    feedbackMap u '' Icc (-1 : Real) 1 = Icc (-1 / 2 : Real) (1 / 2 : Real) := by
  have himage :=
    (continuous_feedbackMap u).continuousOn.image_Icc_of_monotoneOn
      (by norm_num : (-1 : Real) ≤ 1)
      (feedbackMap_strictMonoOn hu).monotoneOn
  simpa using himage

/-- Set-level bijectivity underlying the inverse `F_u^{-1}`. -/
theorem feedbackMap_bijOn
    {u : Real} (hu : |u| ≤ 1 / 16) :
    BijOn (feedbackMap u) (Icc (-1 : Real) 1)
      (Icc (-1 / 2 : Real) (1 / 2 : Real)) := by
  have h := (feedbackMap_strictMonoOn hu).injOn.bijOn_image
  rwa [feedbackMap_image_Icc hu] at h

end

end MsetsLower.Feedback
