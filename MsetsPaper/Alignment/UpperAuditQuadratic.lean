import MsetsPaper.Upper.Leverage
import MsetsPaper.Upper.FiniteKL
import MsetsPaper.Upper.Estimator
import Mathlib.Tactic

/-! A concrete failure of exponential-family closure for the actual inverse
second-moment quadratic correction. The matrix below is computed from a
positive weighted 2-set law on four items, rather than chosen independently. -/

noncomputable section
open MsetsLower MsetsLower.History MsetsPaper.Upper Matrix
open scoped BigOperators

namespace MsetsPaper.Alignment.UpperAuditQuadratic

def a01 : Action 4 2 := ⟨{0, 1}, by decide⟩
def a02 : Action 4 2 := ⟨{0, 2}, by decide⟩
def a03 : Action 4 2 := ⟨{0, 3}, by decide⟩
def a12 : Action 4 2 := ⟨{1, 2}, by decide⟩
def a13 : Action 4 2 := ⟨{1, 3}, by decide⟩
def a23 : Action 4 2 := ⟨{2, 3}, by decide⟩

theorem action_univ : (Finset.univ : Finset (Action 4 2)) =
    {a01, a02, a03, a12, a13, a23} := by decide

def parameter : Fin 4 → ℝ := ![0, 0, Real.log 2, Real.log 2]

def explicitLaw (a : Action 4 2) : ℝ :=
  if a = a01 then 1 / 13 else if a = a23 then 4 / 13 else 2 / 13

theorem weightedLaw_parameter : weightedLaw (m := 2) parameter = explicitLaw := by
  classical
  funext a
  have ha : a ∈ ({a01, a02, a03, a12, a13, a23} : Finset (Action 4 2)) := by
    rw [← action_univ]
    exact Finset.mem_univ a
  simp only [Finset.mem_insert, Finset.mem_singleton] at ha
  rcases ha with rfl | rfl | rfl | rfl | rfl | rfl <;>
    norm_num [weightedLaw, partition, action_univ, explicitLaw, parameter,
      actionLoss_eq_finset_sum, a01, a02, a03, a12, a13, a23,
      Finset.ext_iff, Fin.forall_fin_succ,
      Real.exp_add, Real.exp_log (by norm_num : (0 : ℝ) < 2)]

def momentMatrix : Matrix (Fin 4) (Fin 4) ℝ :=
  ![![5/13, 1/13, 2/13, 2/13],
    ![1/13, 5/13, 2/13, 2/13],
    ![2/13, 2/13, 8/13, 4/13],
    ![2/13, 2/13, 4/13, 8/13]]

def inverseMatrix : Matrix (Fin 4) (Fin 4) ℝ :=
  ![![169/56, -13/56, -13/28, -13/28],
    ![-13/56, 169/56, -13/28, -13/28],
    ![-13/28, -13/28, 65/28, -13/14],
    ![-13/28, -13/28, -13/14, 65/28]]

set_option maxHeartbeats 800000 in
theorem secondMoment_parameter : secondMoment (weightedLaw (m := 2) parameter) =
    momentMatrix := by
  rw [weightedLaw_parameter]
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [secondMoment, action_univ, explicitLaw, selectedIndicator,
      a01, a02, a03, a12, a13, a23, momentMatrix, Finset.ext_iff,
      Fin.forall_fin_succ]

theorem matrix_right_inverse : momentMatrix * inverseMatrix = 1 := by
  ext i j
  change (∑ k : Fin 4, momentMatrix i k * inverseMatrix k j) =
    (1 : Matrix (Fin 4) (Fin 4) ℝ) i j
  fin_cases i <;> fin_cases j <;>
    norm_num [Matrix.mul_apply, Fin.sum_univ_succ, momentMatrix, inverseMatrix]

theorem inverse_secondMoment_parameter :
    (secondMoment (weightedLaw (m := 2) parameter))⁻¹ = inverseMatrix := by
  rw [secondMoment_parameter]
  exact Matrix.inv_eq_right_inv matrix_right_inverse

theorem leverage_values :
    leverage parameter a01 = 39/7 ∧ leverage parameter a23 = 39/14 ∧
    leverage parameter a02 = 247/56 ∧ leverage parameter a13 = 247/56 := by
  simp only [leverage, inverse_secondMoment_parameter]
  norm_num [dotProduct, Matrix.mulVec, Fin.sum_univ_succ, inverseMatrix,
    selectedIndicator, a01, a02, a13, a23]

/-- Every positive weighted 2-set law satisfies this multiplicative identity. -/
theorem weightedLaw_product_identity (theta : Fin 4 → ℝ) :
    weightedLaw theta a01 * weightedLaw theta a23 =
      weightedLaw theta a02 * weightedLaw theta a13 := by
  simp [weightedLaw_product_form, a01, a02, a13, a23]
  ring

def quadraticUpdate (eta : ℝ) : Action 4 2 → ℝ :=
  mwUpdate (weightedLaw parameter) (fun a ↦ -eta * leverage parameter a) eta

/-- With zero loss, the quadratic correction is exactly the exponential
tilt by eta squared times the actual inverse-second-moment leverage. -/
theorem quadraticUpdate_formula (eta : ℝ) (a : Action 4 2) :
    quadraticUpdate eta a = weightedLaw parameter a *
      Real.exp (eta ^ 2 * leverage parameter a) /
        mwNormalizer (weightedLaw (m := 2) parameter)
          (fun b ↦ -eta * leverage parameter b) eta := by
  unfold quadraticUpdate mwUpdate
  congr 2
  congr 1
  ring

theorem quadraticUpdate_not_weighted {eta : ℝ} (heta : 0 < eta) :
    ¬ ∃ theta : Fin 4 → ℝ, quadraticUpdate eta = weightedLaw (m := 2) theta := by
  rintro ⟨theta, htheta⟩
  have hprod := weightedLaw_product_identity theta
  rw [← htheta] at hprod
  simp only [quadraticUpdate_formula] at hprod
  have hZ := mwNormalizer_pos (weightedLaw (m := 2) parameter)
    (fun a ↦ -eta * leverage parameter a) eta (weightedLaw_pos parameter (by decide))
    (sum_weightedLaw parameter (by decide))
  obtain ⟨h01, h23, h02, h13⟩ := leverage_values
  rw [h01, h23, h02, h13] at hprod
  have hp01 : weightedLaw parameter a01 = 1/13 := by
    rw [weightedLaw_parameter]; norm_num [explicitLaw]
  have hp23 : weightedLaw parameter a23 = 4/13 := by
    rw [weightedLaw_parameter]
    norm_num [explicitLaw, a01, a23, Finset.ext_iff, Fin.forall_fin_succ]
  have hp02 : weightedLaw parameter a02 = 2/13 := by
    rw [weightedLaw_parameter]
    norm_num [explicitLaw, a01, a02, a23, Finset.ext_iff, Fin.forall_fin_succ]
  have hp13 : weightedLaw parameter a13 = 2/13 := by
    rw [weightedLaw_parameter]
    norm_num [explicitLaw, a01, a13, a23, Finset.ext_iff, Fin.forall_fin_succ]
  rw [hp01, hp23, hp02, hp13, div_mul_div_comm, div_mul_div_comm] at hprod
  have heq : Real.exp (eta ^ 2 * (39/7)) * Real.exp (eta ^ 2 * (39/14)) =
      Real.exp (eta ^ 2 * (247/56)) * Real.exp (eta ^ 2 * (247/56)) := by
    have hnum := (div_left_inj' (mul_ne_zero (ne_of_gt hZ) (ne_of_gt hZ))).mp hprod
    nlinarith only [hnum]
  rw [← Real.exp_add, ← Real.exp_add] at heq
  have hexponents := Real.exp_injective heq
  nlinarith [sq_pos_of_pos heta]

/-- A positive probability law inside the weighted family whose actual
quadratic-correction update leaves that family, at every positive step size. -/
theorem actual_leverage_counterexample (eta : ℝ) (heta : 0 < eta) :
    (∀ a : Action 4 2, 0 < weightedLaw parameter a) ∧
    (∑ a : Action 4 2, weightedLaw parameter a) = 1 ∧
    (∀ a : Action 4 2, 0 < quadraticUpdate eta a) ∧
    (∑ a : Action 4 2, quadraticUpdate eta a) = 1 ∧
    ¬ ∃ theta : Fin 4 → ℝ, quadraticUpdate eta = weightedLaw (m := 2) theta := by
  have hp := weightedLaw_pos (m := 2) parameter (by decide)
  have hs := sum_weightedLaw (m := 2) parameter (by decide)
  exact ⟨hp, hs, mwUpdate_pos _ _ _ hp hs, sum_mwUpdate _ _ _ hp hs,
    quadraticUpdate_not_weighted heta⟩

theorem estimateScalar_zero (a b : Action 4 2) :
    estimateScalar parameter a (0 : Fin 4 → ℝ) b = 0 := by
  have hz : actionLoss a (0 : Fin 4 → ℝ) = 0 := by
    simp [actionLoss_eq_finset_sum]
  simp [estimateScalar, estimateVector, hz]

/-- The quadratic surrogate from `eq:kw-surrogate-loss`, before the paper
replaces it with its affine majorant. This is not the final affine algorithm. -/
def zeroLossKWUpdate (eta : ℝ) (a : Action 4 2) : Action 4 2 → ℝ :=
  mwUpdate (weightedLaw parameter)
    (fun b ↦ estimateScalar parameter a (0 : Fin 4 → ℝ) b -
      eta * leverage parameter b) eta

theorem zeroLossKWUpdate_eq (eta : ℝ) (a : Action 4 2) :
    zeroLossKWUpdate eta a = quadraticUpdate eta := by
  simp only [zeroLossKWUpdate, estimateScalar_zero, zero_sub, quadraticUpdate, neg_mul]

/-- The nonclosure is realized by the paper's quadratic surrogate with an
admissible zero loss, independently of which of the six actions was sampled. -/
theorem actual_zero_loss_kw_counterexample (eta : ℝ) (heta : 0 < eta)
    (a : Action 4 2) :
    (∀ b : Action 4 2, 0 < zeroLossKWUpdate eta a b) ∧
    (∑ b : Action 4 2, zeroLossKWUpdate eta a b) = 1 ∧
    ¬ ∃ theta : Fin 4 → ℝ, zeroLossKWUpdate eta a = weightedLaw (m := 2) theta := by
  rw [zeroLossKWUpdate_eq]
  exact (actual_leverage_counterexample eta heta).2.2

end MsetsPaper.Alignment.UpperAuditQuadratic
