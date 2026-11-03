import MsetsPaper.Upper.EllipsoidContainment
import Mathlib.Analysis.Matrix.Spectrum

/-! An ellipsoid containing a Euclidean ball cannot have arbitrarily small
determinant. This is proved from its eigenvectors, not assumed as volume lore. -/

noncomputable section
open scoped BigOperators
open Matrix

namespace MsetsPaper.Upper

variable {d : ℕ}

theorem euclideanNorm_smul (r : ℝ) (v : Fin d → ℝ) :
    euclideanNorm (r • v) = |r| * euclideanNorm v := by
  change ‖r • (WithLp.toLp 2 v : EuclideanSpace ℝ (Fin d))‖ = _
  rw [norm_smul, Real.norm_eq_abs]
  rfl

theorem ellipsoidQuadratic_parallelogram (Q : Matrix (Fin d) (Fin d) ℝ)
    (u v : Fin d → ℝ) :
    ellipsoidQuadratic Q (u + v) + ellipsoidQuadratic Q (u - v) =
      2 * ellipsoidQuadratic Q u + 2 * ellipsoidQuadratic Q v := by
  simp only [ellipsoidQuadratic, Matrix.mulVec_add, Matrix.mulVec_sub,
    dotProduct_add, dotProduct_sub, add_dotProduct, sub_dotProduct]
  ring

theorem ellipsoidQuadratic_smul (Q : Matrix (Fin d) (Fin d) ℝ)
    (r : ℝ) (v : Fin d → ℝ) :
    ellipsoidQuadratic Q (r • v) = r ^ 2 * ellipsoidQuadratic Q v := by
  simp only [ellipsoidQuadratic, Matrix.mulVec_smul,
    dotProduct_smul, smul_dotProduct, smul_eq_mul]
  ring

theorem ellipsoid_ball_inverse_quadratic (Q : Matrix (Fin d) (Fin d) ℝ)
    (hQ : Q.PosDef) (c u : Fin d → ℝ) (rho : ℝ) (hrho : 0 < rho)
    (hball : ∀ x, euclideanNorm (x - u) ≤ rho → x ∈ ellipsoidSet c Q)
    (v : Fin d → ℝ) (hv : euclideanNorm v = 1) :
    ellipsoidQuadratic Q⁻¹ v ≤ 1 / rho ^ 2 := by
  have hplus : euclideanNorm ((u + rho • v) - u) ≤ rho := by
    rw [add_sub_cancel_left, euclideanNorm_smul, abs_of_pos hrho, hv, mul_one]
  have hminus : euclideanNorm ((u - rho • v) - u) ≤ rho := by
    have heq : (u - rho • v) - u = (-rho) • v := by module
    rw [heq, euclideanNorm_smul, abs_neg, abs_of_pos hrho, hv, mul_one]
  have hp := hball (u + rho • v) hplus
  have hm := hball (u - rho • v) hminus
  change ellipsoidQuadratic Q⁻¹ ((u + rho • v) - c) ≤ 1 at hp
  change ellipsoidQuadratic Q⁻¹ ((u - rho • v) - c) ≤ 1 at hm
  have heqp : (u + rho • v) - c = (u - c) + rho • v := by abel
  have heqm : (u - rho • v) - c = (u - c) - rho • v := by abel
  rw [heqp] at hp
  rw [heqm] at hm
  have hpara := ellipsoidQuadratic_parallelogram Q⁻¹ (u - c) (rho • v)
  rw [ellipsoidQuadratic_smul] at hpara
  have hnonneg : 0 ≤ ellipsoidQuadratic Q⁻¹ (u - c) := by
    simpa only [ellipsoidQuadratic, star_trivial] using
      hQ.inv.posSemidef.dotProduct_mulVec_nonneg (u - c)
  apply (le_div_iff₀ (sq_pos_of_pos hrho)).mpr
  nlinarith

theorem ellipsoid_ball_inverse_eigenvalue (Q : Matrix (Fin d) (Fin d) ℝ)
    (hQ : Q.PosDef) (c u : Fin d → ℝ) (rho : ℝ) (hrho : 0 < rho)
    (hball : ∀ x, euclideanNorm (x - u) ≤ rho → x ∈ ellipsoidSet c Q)
    (i : Fin d) : hQ.inv.1.eigenvalues i ≤ 1 / rho ^ 2 := by
  let v : Fin d → ℝ := hQ.inv.1.eigenvectorBasis i
  have hv : euclideanNorm v = 1 := hQ.inv.1.eigenvectorBasis.norm_eq_one i
  have hbound := ellipsoid_ball_inverse_quadratic Q hQ c u rho hrho hball v hv
  have hvec := hQ.inv.1.mulVec_eigenvectorBasis i
  have hdot : v ⬝ᵥ v = 1 := by
    have hnorm := euclideanNorm_sq v
    rw [hv] at hnorm
    simpa only [dotProduct, pow_two, one_mul] using hnorm.symm
  change Q⁻¹ *ᵥ v = (hQ.inv.1.eigenvalues i) • v at hvec
  simpa only [ellipsoidQuadratic, hvec, dotProduct_smul, smul_eq_mul, hdot, mul_one] using hbound

theorem ellipsoid_ball_inverse_det (Q : Matrix (Fin d) (Fin d) ℝ)
    (hQ : Q.PosDef) (c u : Fin d → ℝ) (rho : ℝ) (hrho : 0 < rho)
    (hball : ∀ x, euclideanNorm (x - u) ≤ rho → x ∈ ellipsoidSet c Q) :
    Q⁻¹.det ≤ (1 / rho ^ 2) ^ d := by
  rw [hQ.inv.1.det_eq_prod_eigenvalues]
  have hprod := Finset.prod_le_prod₀
    (fun i (_ : i ∈ (Finset.univ : Finset (Fin d))) => hQ.inv.eigenvalues_pos i |>.le)
    (fun i (_ : i ∈ (Finset.univ : Finset (Fin d))) =>
      ellipsoid_ball_inverse_eigenvalue Q hQ c u rho hrho hball i)
  simpa only [RCLike.ofReal_real_eq_id, id_eq, Finset.prod_const, Finset.card_univ,
    Fintype.card_fin] using hprod

theorem ellipsoid_ball_det_lower (Q : Matrix (Fin d) (Fin d) ℝ)
    (hQ : Q.PosDef) (c u : Fin d → ℝ) (rho : ℝ) (hrho : 0 < rho)
    (hball : ∀ x, euclideanNorm (x - u) ≤ rho → x ∈ ellipsoidSet c Q) :
    (rho ^ 2) ^ d ≤ Q.det := by
  have hbound := ellipsoid_ball_inverse_det Q hQ c u rho hrho hball
  have hdet : Q.det * Q⁻¹.det = 1 := by
    rw [← Matrix.det_mul, ellipsoidShape_mul_inv Q hQ, Matrix.det_one]
  have hp : 0 < (rho ^ 2) ^ d := pow_pos (sq_pos_of_pos hrho) _
  have hscaled := mul_le_mul_of_nonneg_left hbound hQ.det_pos.le
  rw [hdet, _root_.one_div_pow] at hscaled
  have : 1 ≤ Q.det / (rho ^ 2) ^ d := by simpa only [mul_one_div] using hscaled
  simpa only [one_mul] using (le_div_iff₀ hp).mp this

end MsetsPaper.Upper
