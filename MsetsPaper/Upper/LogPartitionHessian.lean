import MsetsPaper.Upper.ProjectionDualOptimality
import MsetsPaper.Upper.InverseCovariance

/-! Actual derivatives of the log partition function. The Hessian below is
defined by iterated coordinate derivatives, and is then proved equal to the
actual covariance; covariance is not used as its definition. -/

noncomputable section
open scoped BigOperators
open Matrix MsetsLower MsetsLower.History

namespace MsetsPaper.Upper
variable {d m : ℕ}

theorem weightedLaw_eq_exp_logPartition (theta : Fin d → ℝ) (hmd : m ≤ d)
    (a : Action d m) :
    weightedLaw theta a = Real.exp (actionLoss a theta - logPartition (m := m) theta) := by
  rw [← log_weightedLaw theta hmd a, Real.exp_log (weightedLaw_pos theta hmd a)]

theorem hasDerivAt_weightedLaw_line (theta z : Fin d → ℝ) (hmd : m ≤ d)
    (a : Action d m) (t : ℝ) :
    HasDerivAt (fun s : ℝ ↦ weightedLaw (theta + s • z) a)
      (weightedLaw (theta + t • z) a *
        (actionLoss a z - weightedMarginal (m := m) (theta + t • z) ⬝ᵥ z)) t := by
  have ha : HasDerivAt (fun s : ℝ ↦ actionLoss a (theta + s • z)) (actionLoss a z) t := by
    simp_rw [actionLoss_add_smul]
    simpa using ((hasDerivAt_id t).mul_const (actionLoss a z)).const_add (actionLoss a theta)
  have h := (ha.sub (hasDerivAt_logPartition_line theta z hmd t)).exp
  simpa only [Pi.sub_apply, ← weightedLaw_eq_exp_logPartition _ hmd a] using h

theorem covariance_mulVec_centered_sum (p : Action d m → ℝ) (z : Fin d → ℝ) (i : Fin d) :
    (covariance p *ᵥ z) i =
      ∑ a, p a * (actionLoss a z - marginal p ⬝ᵥ z) * selectedIndicator i a := by
  have hM := congrFun (secondMoment_mulVec_observation p z) i
  simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul] at hM
  have hr : (Matrix.vecMulVec (marginal p) (marginal p) *ᵥ z) i =
      marginal p i * (marginal p ⬝ᵥ z) := by
    simp only [Matrix.mulVec, dotProduct, Matrix.vecMulVec, Matrix.of_apply, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro j _
    ring
  rw [covariance, Matrix.sub_mulVec]
  change (secondMoment p *ᵥ z) i -
    (Matrix.vecMulVec (marginal p) (marginal p) *ᵥ z) i = _
  rw [hM, hr]
  simp only [mul_sub, sub_mul, Finset.sum_sub_distrib]
  congr 1
  simp only [marginal, Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro a _
  ring

theorem hasDerivAt_weightedMarginal_line (theta z : Fin d → ℝ) (hmd : m ≤ d)
    (i : Fin d) (t : ℝ) :
    HasDerivAt (fun s : ℝ ↦ weightedMarginal (m := m) (theta + s • z) i)
      ((covariance (weightedLaw (m := m) (theta + t • z)) *ᵥ z) i) t := by
  rw [covariance_mulVec_centered_sum]
  have h := HasDerivAt.sum (u := (Finset.univ : Finset (Action d m)))
    (fun a _ ↦ (hasDerivAt_weightedLaw_line theta z hmd a t).mul_const (selectedIndicator i a))
  have heq : (∑ a : Action d m, fun s : ℝ ↦
      weightedLaw (theta + s • z) a * selectedIndicator i a) =
      (fun s : ℝ ↦ weightedMarginal (m := m) (theta + s • z) i) := by
    funext s
    simp [weightedMarginal, marginal]
  rw [heq] at h
  exact h

/-- Every entry is an actual mixed second derivative, including at rank0
or rankd when those ranks are defined; only m<=d is needed. -/
theorem logPartition_mixed_second_derivative (theta : Fin d → ℝ) (hmd : m ≤ d)
    (i j : Fin d) :
    deriv (fun s : ℝ ↦ deriv (fun t : ℝ ↦
      logPartition (m := m) (theta + s • Pi.single j 1 + t • Pi.single i 1)) 0) 0 =
      covariance (weightedLaw (m := m) theta) i j := by
  have hf (s : ℝ) : deriv (fun t : ℝ ↦
      logPartition (m := m) (theta + s • Pi.single j 1 + t • Pi.single i 1)) 0 =
      weightedMarginal (m := m) (theta + s • Pi.single j 1) i := by
    simpa only [zero_smul, add_zero, dotProduct_single, mul_one] using
      (hasDerivAt_logPartition_line (theta + s • Pi.single j 1) (Pi.single i 1) hmd 0).deriv
  simp_rw [hf]
  simpa [Matrix.mulVec_single] using
    (hasDerivAt_weightedMarginal_line theta (Pi.single j 1) hmd i 0).deriv

def coordinateHessian (F : (Fin d → ℝ) → ℝ) (theta : Fin d → ℝ) :
    Matrix (Fin d) (Fin d) ℝ :=
  fun i j ↦ deriv (fun s : ℝ ↦ deriv (fun t : ℝ ↦
    F (theta + s • Pi.single j 1 + t • Pi.single i 1)) 0) 0

theorem logPartition_hessian_eq_covariance (theta : Fin d → ℝ) (hmd : m ≤ d) :
    coordinateHessian (logPartition (m := m)) theta = covariance (weightedLaw (m := m) theta) := by
  ext i j
  exact logPartition_mixed_second_derivative theta hmd i j

/-- The second derivative on an arbitrary line is the covariance quadratic
form; this exposes the second-order calculus independently of matrix notation. -/
theorem hasDerivAt_deriv_logPartition_line (theta z : Fin d → ℝ) (hmd : m ≤ d) (t : ℝ) :
    HasDerivAt (fun s : ℝ ↦ deriv (fun r : ℝ ↦ logPartition (m := m) (theta + r • z)) s)
      (z ⬝ᵥ (covariance (weightedLaw (m := m) (theta + t • z)) *ᵥ z)) t := by
  have hfirst (s : ℝ) := (hasDerivAt_logPartition_line theta z hmd s).deriv
  simp_rw [hfirst]
  have h := HasDerivAt.sum (u := (Finset.univ : Finset (Fin d)))
    (fun i _ ↦ (hasDerivAt_weightedMarginal_line theta z hmd i t).mul_const (z i))
  have heq : (∑ i : Fin d, fun s : ℝ ↦ weightedMarginal (m := m) (theta + s • z) i * z i) =
      (fun s : ℝ ↦ weightedMarginal (m := m) (theta + s • z) ⬝ᵥ z) := by
    funext s
    simp [dotProduct]
  rw [heq] at h
  simpa only [dotProduct, mul_comm] using h

end MsetsPaper.Upper
