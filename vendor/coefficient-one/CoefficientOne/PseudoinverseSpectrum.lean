import CoefficientOne.PseudoinverseIdentity

/-!
# Spectral action of the concrete covariance pseudoinverse

This supplies the spectral description at the beginning of Appendix E.4.
The canonical inverse annihilates the constant kernel and inverts the
covariance on the zero-sum subspace. A nonzero-eigenvalue eigenvector lies
in that subspace by symmetry.
-/

open scoped BigOperators
open Matrix EffectiveResistance

namespace CoefficientOne

noncomputable section

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- The concrete pseudoinverse is also a left inverse on zero-sum vectors. -/
theorem externalField_pseudoinverse_left_inverse_zeroSum
    (w : ι → ℝ) (hw : ∀ i, 0 < w i) (m : ℕ)
    (hmpos : 1 ≤ m) (hmtop : m ≤ Fintype.card ι - 1)
    (x : ι → ℝ) (hx : IsZeroSum x) :
    externalFieldPseudoinverse w hw m hmpos hmtop *ᵥ (covarianceMatrix w m *ᵥ x) = x := by
  have hcard : 0 < Fintype.card ι := by omega
  letI : Nonempty ι := Fintype.card_pos_iff.mp hcard
  let N := externalFieldCovarianceNetwork w hw m hmpos hmtop
  let hcomplete := externalFieldCovarianceNetwork_strictlyComplete w hw m hmpos hmtop
  rw [← externalFieldCovarianceNetwork_laplacian w hw m hmpos hmtop]
  change N.canonicalGreenMatrix hcomplete *ᵥ (N.laplacian *ᵥ x) = x
  rw [N.canonicalGreenMatrix_mulVec, N.greenOperator_laplacian_mulVec]
  exact congrArg Subtype.val (zeroSumProjection_eq_self x hx)

/-- Constants are annihilated by the canonical Moore--Penrose inverse. -/
theorem externalField_pseudoinverse_mulVec_constant
    (w : ι → ℝ) (hw : ∀ i, 0 < w i) (m : ℕ)
    (hmpos : 1 ≤ m) (hmtop : m ≤ Fintype.card ι - 1) (c : ℝ) :
    externalFieldPseudoinverse w hw m hmpos hmtop *ᵥ (fun _ => c) = 0 := by
  have hcard : 0 < Fintype.card ι := by omega
  letI : Nonempty ι := Fintype.card_pos_iff.mp hcard
  let N := externalFieldCovarianceNetwork w hw m hmpos hmtop
  let hcomplete := externalFieldCovarianceNetwork_strictlyComplete w hw m hmpos hmtop
  change N.canonicalGreenMatrix hcomplete *ᵥ (fun _ => c) = 0
  rw [N.canonicalGreenMatrix_mulVec]
  have hcardne : (Fintype.card ι : ℝ) ≠ 0 := by exact_mod_cast hcard.ne'
  have hproj : zeroSumProjection (fun _ : ι => c) = 0 := by
    ext i
    simp [zeroSumProjection_apply, hcardne]
  simp [ConductanceNetwork.greenOperator, hproj]

/-- The covariance kernel is annihilated by its concrete pseudoinverse. -/
theorem externalField_pseudoinverse_mulVec_of_covariance_kernel
    (w : ι → ℝ) (hw : ∀ i, 0 < w i) (m : ℕ)
    (hmpos : 1 ≤ m) (hmtop : m ≤ Fintype.card ι - 1)
    (x : ι → ℝ) (hx : covarianceMatrix w m *ᵥ x = 0) :
    externalFieldPseudoinverse w hw m hmpos hmtop *ᵥ x = 0 := by
  have hcard : 0 < Fintype.card ι := by omega
  let i₀ : ι := Classical.choice (Fintype.card_pos_iff.mp hcard)
  have hc := (covariance_mulVec_eq_zero_iff_constant w hw m hmpos hmtop x).mp hx
  have heq : x = fun _ => x i₀ := by funext i; exact hc i i₀
  rw [heq]
  exact externalField_pseudoinverse_mulVec_constant w hw m hmpos hmtop (x i₀)

/-- A nonzero covariance eigenvalue is inverted by the pseudoinverse. -/
theorem externalField_pseudoinverse_eigenvector_nonzero
    (w : ι → ℝ) (hw : ∀ i, 0 < w i) (m : ℕ)
    (hmpos : 1 ≤ m) (hmtop : m ≤ Fintype.card ι - 1)
    (μ : ℝ) (hμ : μ ≠ 0) (x : ι → ℝ)
    (heig : covarianceMatrix w m *ᵥ x = μ • x) :
    externalFieldPseudoinverse w hw m hmpos hmtop *ᵥ x = μ⁻¹ • x := by
  have horth := kernel_dot_eigenvector_eq_zero (covarianceMatrix w m)
    (covariance_isSymm w m) (fun _ => 1) x
    (covariance_mulVec_one_eq_zero w hw m (hmtop.trans (Nat.sub_le _ _))) μ hμ heig
  have hx : IsZeroSum x := by simpa [IsZeroSum, dotProduct] using horth
  have hleft := externalField_pseudoinverse_left_inverse_zeroSum w hw m hmpos hmtop x hx
  rw [heig, Matrix.mulVec_smul] at hleft
  have h := congrArg (fun z : ι → ℝ => μ⁻¹ • z) hleft
  simpa [smul_smul, hμ] using h

/-- The piecewise spectral formula stated at the start of Appendix E.4. -/
theorem externalField_pseudoinverse_eigenvector_action
    (w : ι → ℝ) (hw : ∀ i, 0 < w i) (m : ℕ)
    (hmpos : 1 ≤ m) (hmtop : m ≤ Fintype.card ι - 1)
    (μ : ℝ) (hμ : 0 ≤ μ) (x : ι → ℝ)
    (heig : covarianceMatrix w m *ᵥ x = μ • x) :
    externalFieldPseudoinverse w hw m hmpos hmtop *ᵥ x =
      if 0 < μ then μ⁻¹ • x else 0 := by
  by_cases hpos : 0 < μ
  · rw [if_pos hpos]
    exact externalField_pseudoinverse_eigenvector_nonzero w hw m hmpos hmtop μ hpos.ne' x heig
  · rw [if_neg hpos]
    have hz : μ = 0 := le_antisymm (le_of_not_gt hpos) hμ
    apply externalField_pseudoinverse_mulVec_of_covariance_kernel w hw m hmpos hmtop x
    simpa [hz] using heig

end

end CoefficientOne
