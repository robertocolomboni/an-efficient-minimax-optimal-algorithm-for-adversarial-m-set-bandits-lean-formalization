import MsetsPaper.Upper.CovariancePseudoinverse

/-!
# The explicit kernel/range route in manuscript Lemma 2

These statements certify the intermediate claims of the English proof, including
the difference of two covariance solutions.  They complement the shorter
symmetry argument used by `quadratic_eq_of_covariance_mulVec_eq`.
-/

noncomputable section

open scoped BigOperators
open Matrix MsetsLower MsetsLower.History

namespace MsetsPaper.Upper

variable {d m : ℕ}

/-- The actual covariance kernel consists exactly of constant vectors. -/
theorem covariance_kernel_iff_constant
    (p : Action d m → ℝ) (hp : ∀ a, 0 < p a) (hsum : ∑ a, p a = 1)
    (hmpos : 1 ≤ m) (hmtop : m ≤ d - 1) (x : Fin d → ℝ) :
    covariance p *ᵥ x = 0 ↔ ∃ c : ℝ, x = fun _ => c := by
  constructor
  · intro hx
    exact ⟨_, eq_const_of_covariance_mulVec_eq_zero p hp hmpos hmtop x hx⟩
  · rintro ⟨c, rfl⟩
    have hc : (fun _ : Fin d => c) = c • (fun _ : Fin d => (1 : ℝ)) := by
      ext i
      simp
    rw [hc, Matrix.mulVec_smul, covariance_mulVec_one p hsum, smul_zero]

/-- The range of the actual covariance is precisely the zero-sum hyperplane. -/
theorem covariance_range_iff_sum_zero
    (p : Action d m → ℝ) (hp : ∀ a, 0 < p a) (hsum : ∑ a, p a = 1)
    (hmpos : 1 ≤ m) (hmtop : m ≤ d - 1) (y : Fin d → ℝ) :
    (∃ z, covariance p *ᵥ z = y) ↔ ∑ i, y i = 0 := by
  constructor
  · rintro ⟨z, rfl⟩
    exact sum_covariance_mulVec p hsum z
  · intro hy
    exact ⟨centeredInverseSolution p y,
      covariance_mulVec_centeredInverseSolution p hp hsum hmpos hmtop y hy⟩

/-- The difference of two covariance solutions is constant, as in the paper. -/
theorem covariance_solutions_difference_constant
    (p : Action d m → ℝ) (hp : ∀ a, 0 < p a) (hsum : ∑ a, p a = 1)
    (hmpos : 1 ≤ m) (hmtop : m ≤ d - 1)
    (y z v : Fin d → ℝ) (hz : covariance p *ᵥ z = y)
    (hv : covariance p *ᵥ v = y) : ∃ c : ℝ, z - v = fun _ => c := by
  apply (covariance_kernel_iff_constant p hp hsum hmpos hmtop _).mp
  rw [Matrix.mulVec_sub, hz, hv, sub_self]

/-- A zero-sum right-hand side is orthogonal to that difference. -/
theorem covariance_solutions_difference_orthogonal
    (p : Action d m → ℝ) (hp : ∀ a, 0 < p a) (hsum : ∑ a, p a = 1)
    (hmpos : 1 ≤ m) (hmtop : m ≤ d - 1)
    (y z v : Fin d → ℝ) (hy : ∑ i, y i = 0)
    (hz : covariance p *ᵥ z = y) (hv : covariance p *ᵥ v = y) :
    y ⬝ᵥ (z - v) = 0 := by
  obtain ⟨c, hc⟩ := covariance_solutions_difference_constant
    p hp hsum hmpos hmtop y z v hz hv
  rw [hc]
  simp only [dotProduct, ← Finset.sum_mul, hy, zero_mul]

/-- Lemma 2's quadratic identity, proved literally through the difference in
the covariance kernel rather than by the shorter symmetry shortcut. -/
theorem quadratic_eq_pseudoinverse_by_kernel_difference
    (p : Action d m → ℝ) (hp : ∀ a, 0 < p a) (hsum : ∑ a, p a = 1)
    (hmpos : 1 ≤ m) (hmtop : m ≤ d - 1)
    (y : Fin d → ℝ) (hy : ∑ i, y i = 0) :
    y ⬝ᵥ ((secondMoment p)⁻¹ *ᵥ y) =
      y ⬝ᵥ (covariancePseudoInverse p *ᵥ y) := by
  have hz := covariance_mulVec_secondMoment_inv_mulVec p hp hmpos hmtop y hy
  have hv : covariance p *ᵥ (covariancePseudoInverse p *ᵥ y) = y := by
    rw [Matrix.mulVec_mulVec,
      covariance_mul_covariancePseudoInverse p hp hsum hmpos hmtop,
      zeroSumProjection_mulVec, centerVector_eq_self_of_sum_eq_zero y hy]
  have ho := covariance_solutions_difference_orthogonal
    p hp hsum hmpos hmtop y _ _ hy hz hv
  rw [dotProduct_sub] at ho
  exact sub_eq_zero.mp ho

end MsetsPaper.Upper
