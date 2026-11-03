import MsetsPaper.Upper.AdaptiveExecution
import MsetsPaper.Upper.OMD
import Mathlib.Topology.Instances.Matrix

/-! # The observable, feedback-only algorithm update

This constructs the history-dependent weighted policy from a measurable
projection function. It never reads the hidden full loss vector. Supplying
the certified projection function and its resource bound is still required.
-/

noncomputable section
open MsetsLower MsetsLower.History MeasureTheory Matrix
open scoped BigOperators

namespace MsetsPaper.Upper

variable {d m : ℕ}

instance realMatrixMeasurableSpace (d : ℕ) : MeasurableSpace (Matrix (Fin d) (Fin d) ℝ) :=
  inferInstanceAs (MeasurableSpace (Fin d → Fin d → ℝ))

instance realMatrixBorelSpace (d : ℕ) : BorelSpace (Matrix (Fin d) (Fin d) ℝ) :=
  inferInstanceAs (BorelSpace (Fin d → Fin d → ℝ))

def estimateFromFeedback (theta : Fin d → ℝ) (a : Action d m) (y : ℝ) : Fin d → ℝ :=
  y • ((secondMoment (weightedLaw (m := m) theta))⁻¹ *ᵥ (fun i ↦ selectedIndicator i a))

def unprojectedFromFeedback (theta : Fin d → ℝ) (eta : ℝ)
    (a : Action d m) (y : ℝ) : Fin d → ℝ :=
  theta - eta • (estimateFromFeedback theta a y -
    eta • correction (m : ℝ) (weightedMarginal (m := m) theta))

theorem estimateFromFeedback_eq_estimateVector (theta ell : Fin d → ℝ) (a : Action d m) :
    estimateFromFeedback theta a (actionLoss a ell) = estimateVector theta a ell := rfl

theorem unprojectedFromFeedback_eq (theta ell : Fin d → ℝ) (eta : ℝ) (a : Action d m) :
    unprojectedFromFeedback theta eta a (actionLoss a ell) =
      theta - eta • surrogateVector theta ell eta a := rfl

section Measurable
variable {Ω : Type*} [MeasurableSpace Ω]

theorem measurable_real_matrix_inverse
    (A : Ω → Matrix (Fin d) (Fin d) ℝ) (hA : Measurable A) :
    Measurable (fun w ↦ (A w)⁻¹) := by
  have hdet : Measurable (fun w ↦ (A w).det) :=
    (continuous_id.matrix_det.measurable).comp hA
  have hadj : Measurable (fun w ↦ (A w).adjugate) :=
    (continuous_id.matrix_adjugate.measurable).comp hA
  simp_rw [Matrix.inv_def, Ring.inverse_eq_inv]
  exact hdet.inv.smul hadj

theorem measurable_actual_secondMoment
    (theta : Ω → Fin d → ℝ) (htheta : Measurable theta) :
    Measurable (fun w ↦ secondMoment (weightedLaw (m := m) (theta w))) := by
  apply measurable_pi_lambda
  intro i
  apply measurable_pi_lambda
  intro j
  change Measurable (fun w ↦ ∑ a : Action d m,
    weightedLaw (theta w) a * selectedIndicator i a * selectedIndicator j a)
  exact Finset.measurable_sum _ (fun a _ ↦
    ((measurable_weightedLaw theta htheta a).mul_const _).mul_const _)

theorem measurable_actual_marginal
    (theta : Ω → Fin d → ℝ) (htheta : Measurable theta) :
    Measurable (fun w ↦ weightedMarginal (m := m) (theta w)) := by
  apply measurable_pi_lambda
  intro i
  change Measurable (fun w ↦ ∑ a : Action d m, weightedLaw (theta w) a * selectedIndicator i a)
  exact Finset.measurable_sum _ (fun a _ ↦
    (measurable_weightedLaw theta htheta a).mul_const _)

theorem measurable_actual_correction
    (theta : Ω → Fin d → ℝ) (htheta : Measurable theta) :
    Measurable (fun w ↦ correction (m : ℝ) (weightedMarginal (m := m) (theta w))) := by
  have hmu (i : Fin d) : Measurable (fun w ↦ weightedMarginal (m := m) (theta w) i) :=
    (measurable_pi_apply i).comp (measurable_actual_marginal (m := m) theta htheta)
  apply measurable_pi_lambda
  intro i
  unfold correction
  exact (((Finset.measurable_sum _ (fun j _ ↦ (hmu j).div ((hmu j).const_sub 1))).const_add 1).div_const _ |>.add
    (((hmu i).const_mul 2).const_sub 1 |>.div ((hmu i).mul ((hmu i).const_sub 1)))).const_mul 4

theorem measurable_estimateFromFeedback
    (theta : Ω → Fin d → ℝ) (a : Ω → Action d m) (y : Ω → ℝ)
    (htheta : Measurable theta) (ha : Measurable a) (hy : Measurable y) :
    Measurable (fun w ↦ estimateFromFeedback (theta w) (a w) (y w)) := by
  have hInv := measurable_real_matrix_inverse _ (measurable_actual_secondMoment (m := m) theta htheta)
  apply measurable_pi_lambda
  intro i
  change Measurable (fun w ↦ y w * ∑ j, (secondMoment (weightedLaw (m := m) (theta w)))⁻¹ i j *
    selectedIndicator j (a w))
  apply hy.mul
  apply Finset.measurable_sum
  intro j _
  exact ((measurable_pi_apply j).comp ((measurable_pi_apply i).comp hInv)).mul
    ((measurable_of_countable (selectedIndicator j : Action d m → ℝ)).comp ha)

theorem measurable_unprojectedFromFeedback
    (theta : Ω → Fin d → ℝ) (a : Ω → Action d m) (y : Ω → ℝ) (eta : ℝ)
    (htheta : Measurable theta) (ha : Measurable a) (hy : Measurable y) :
    Measurable (fun w ↦ unprojectedFromFeedback (theta w) eta (a w) (y w)) := by
  have he : Measurable (fun _ : Ω ↦ eta) := measurable_const
  exact htheta.sub (he.smul ((measurable_estimateFromFeedback theta a y htheta ha hy).sub
    (he.smul (measurable_actual_correction (m := m) theta htheta))))

end Measurable

def algorithmParameters (project : (Fin d → ℝ) → Fin d → ℝ) (eta : ℝ) :
    (t : ℕ) → History d m t → Fin d → ℝ
  | 0, _ => 0
  | t + 1, (h, (a, y)) => project (unprojectedFromFeedback (algorithmParameters project eta t h) eta a y)

theorem measurable_algorithmParameters
    (project : (Fin d → ℝ) → Fin d → ℝ) (hp : Measurable project) (eta : ℝ) :
    ∀ t, Measurable (algorithmParameters (m := m) project eta t) := by
  intro t
  induction t with
  | zero => exact measurable_const
  | succ t ih =>
    apply hp.comp
    exact measurable_unprojectedFromFeedback _ _ _ eta (ih.comp measurable_fst)
      (measurable_fst.comp measurable_snd) (measurable_snd.comp measurable_snd)

def algorithmPolicy (project : (Fin d → ℝ) → Fin d → ℝ) (hp : Measurable project)
    (eta : ℝ) (hmd : m ≤ d) : Policy d m :=
  observableWeightedPolicy (algorithmParameters project eta)
    (measurable_algorithmParameters project hp eta) hmd

theorem algorithmParameters_step
    (project : (Fin d → ℝ) → Fin d → ℝ) (eta : ℝ) (t : ℕ)
    (h : History d m t) (a : Action d m) (ell : Fin d → ℝ) :
    algorithmParameters project eta (t + 1) (h.snoc a (actionLoss a ell)) =
      project (algorithmParameters project eta t h -
        eta • surrogateVector (algorithmParameters project eta t h) ell eta a) := rfl

end MsetsPaper.Upper
