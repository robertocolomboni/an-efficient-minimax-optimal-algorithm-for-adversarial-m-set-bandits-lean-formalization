import MsetsPaper.Upper.EllipsoidBall
import Mathlib.Analysis.Matrix.Order
import Mathlib.MeasureTheory.Measure.Lebesgue.EqHaar

/-! Lebesgue volume of the actual ellipsoid used by the projection algorithm.
The protected-ball comparison below follows the volume argument in the paper. -/

noncomputable section
open scoped BigOperators MatrixOrder
open Matrix MeasureTheory

namespace MsetsPaper.Upper

variable {d : ℕ}

def euclideanUnitBall (d : ℕ) : Set (Fin d → ℝ) := {x | euclideanNorm x ≤ 1}

theorem continuous_euclideanNorm : Continuous (euclideanNorm (d := d)) := by
  unfold euclideanNorm
  fun_prop

theorem euclideanUnitBall_compact : IsCompact (euclideanUnitBall d) := by
  have heq : euclideanUnitBall d = WithLp.ofLp ''
      Metric.closedBall (0 : EuclideanSpace ℝ (Fin d)) 1 := by
    ext x
    constructor
    · intro hx
      exact ⟨WithLp.toLp 2 x, by simpa [euclideanUnitBall, euclideanNorm,
        Metric.mem_closedBall, dist_zero_right] using hx, rfl⟩
    · rintro ⟨v, hv, rfl⟩
      simpa [euclideanUnitBall, euclideanNorm, Metric.mem_closedBall,
        dist_zero_right] using hv
  rw [heq]
  exact (isCompact_closedBall _ _).image (PiLp.continuous_ofLp _ _)

theorem euclideanUnitBall_volume_pos : 0 < volume (euclideanUnitBall d) := by
  have hopen : IsOpen {x : Fin d → ℝ | euclideanNorm x < 1} :=
    isOpen_lt continuous_euclideanNorm continuous_const
  have hnonempty : ({x : Fin d → ℝ | euclideanNorm x < 1} : Set _).Nonempty := by
    refine ⟨0, ?_⟩
    simp [euclideanNorm]
  exact (hopen.measure_pos volume hnonempty).trans_le
    (measure_mono (fun _ hx => show euclideanNorm _ ≤ 1 from le_of_lt hx))

theorem ellipsoid_sqrt_posDef (Q : Matrix (Fin d) (Fin d) ℝ) (hQ : Q.PosDef) :
    (CFC.sqrt Q).PosDef := by
  apply (CFC.sqrt_nonneg Q).posSemidef.posDef_iff_isUnit.mpr
  apply (CFC.sqrt Q).isUnit_iff_isUnit_det.mpr
  rw [hQ.posSemidef.det_sqrt, RCLike.sqrt_real]
  exact isUnit_iff_ne_zero.mpr (Real.sqrt_pos.mpr hQ.det_pos).ne'

theorem ellipsoidQuadratic_sqrt_image (Q : Matrix (Fin d) (Fin d) ℝ)
    (hQ : Q.PosDef) (v : Fin d → ℝ) :
    ellipsoidQuadratic Q⁻¹ (CFC.sqrt Q *ᵥ v) = euclideanNorm v ^ 2 := by
  let S := CFC.sqrt Q
  have hS := ellipsoid_sqrt_posDef Q hQ
  have hSS : S * S = Q := by
    simpa only [pow_two] using CFC.sq_sqrt Q hQ.posSemidef.nonneg
  have hinv : Q⁻¹ = S⁻¹ * S⁻¹ := by rw [← hSS, Matrix.mul_inv_rev]
  change (S *ᵥ v) ⬝ᵥ (Q⁻¹ *ᵥ (S *ᵥ v)) = _
  rw [hinv, ← Matrix.mulVec_mulVec, ellipsoidShape_inverse_cancel S hS,
    dotProduct_mulVec, ellipsoidShape_vec_inverse_cancel S hS]
  simpa only [dotProduct, pow_two] using (euclideanNorm_sq v).symm

theorem ellipsoidSet_zero_eq_sqrt_image (Q : Matrix (Fin d) (Fin d) ℝ)
    (hQ : Q.PosDef) :
    ellipsoidSet 0 Q = (Matrix.toLin' (CFC.sqrt Q)) '' euclideanUnitBall d := by
  ext x
  constructor
  · intro hx
    let v := (CFC.sqrt Q)⁻¹ *ᵥ x
    have hvx : CFC.sqrt Q *ᵥ v = x := by
      rw [Matrix.mulVec_mulVec, ellipsoidShape_mul_inv _ (ellipsoid_sqrt_posDef Q hQ),
        Matrix.one_mulVec]
    refine ⟨v, ?_, hvx⟩
    have hquad := ellipsoidQuadratic_sqrt_image Q hQ v
    rw [hvx] at hquad
    change ellipsoidQuadratic Q⁻¹ (x - 0) ≤ 1 at hx
    rw [sub_zero, hquad] at hx
    change euclideanNorm v ≤ 1
    nlinarith [euclideanNorm_nonneg v]
  · rintro ⟨v, hv, rfl⟩
    change ellipsoidQuadratic Q⁻¹ ((CFC.sqrt Q *ᵥ v) - 0) ≤ 1
    rw [sub_zero, ellipsoidQuadratic_sqrt_image Q hQ]
    change euclideanNorm v ≤ 1 at hv
    nlinarith [euclideanNorm_nonneg v]

theorem ellipsoidSet_volume (Q : Matrix (Fin d) (Fin d) ℝ)
    (hQ : Q.PosDef) (c : Fin d → ℝ) :
    volume (ellipsoidSet c Q) =
      ENNReal.ofReal (Real.sqrt Q.det) * volume (euclideanUnitBall d) := by
  have hshift : ellipsoidSet c Q = (fun x => -c + x) ⁻¹' ellipsoidSet 0 Q := by
    ext x
    simp only [ellipsoidSet, Set.mem_preimage, Set.mem_setOf_eq, sub_zero]
    congr 2
    abel
  rw [hshift, measure_preimage_add, ellipsoidSet_zero_eq_sqrt_image Q hQ,
    Measure.addHaar_image_linearMap, LinearMap.det_toLin', hQ.posSemidef.det_sqrt]
  simp only [RCLike.sqrt_real, abs_of_nonneg (Real.sqrt_nonneg _)]

theorem euclideanBall_eq_smul_image (rho : ℝ) (hrho : 0 < rho) :
    {x : Fin d → ℝ | euclideanNorm x ≤ rho} =
      (Matrix.toLin' (rho • (1 : Matrix (Fin d) (Fin d) ℝ))) '' euclideanUnitBall d := by
  ext x
  constructor
  · intro hx
    refine ⟨rho⁻¹ • x, ?_, ?_⟩
    · change euclideanNorm (rho⁻¹ • x) ≤ 1
      rw [euclideanNorm_smul, abs_of_pos (inv_pos.mpr hrho)]
      exact (inv_mul_le_iff₀ hrho).mpr (by simpa using hx)
    · simp [Matrix.toLin'_apply, Matrix.smul_mulVec, smul_smul, hrho.ne']
  · rintro ⟨v, hv, rfl⟩
    change euclideanNorm ((rho • (1 : Matrix (Fin d) (Fin d) ℝ)) *ᵥ v) ≤ rho
    rw [Matrix.smul_mulVec, Matrix.one_mulVec, euclideanNorm_smul, abs_of_pos hrho]
    exact (mul_le_mul_of_nonneg_left hv hrho.le).trans_eq (mul_one rho)

theorem euclideanBall_volume (u : Fin d → ℝ) (rho : ℝ) (hrho : 0 < rho) :
    volume {x : Fin d → ℝ | euclideanNorm (x - u) ≤ rho} =
      ENNReal.ofReal (rho ^ d) * volume (euclideanUnitBall d) := by
  have hshift : {x : Fin d → ℝ | euclideanNorm (x - u) ≤ rho} =
      (fun x => -u + x) ⁻¹' {x | euclideanNorm x ≤ rho} := by
    ext x
    simp only [Set.mem_preimage, Set.mem_setOf_eq]
    congr 2
    abel
  rw [hshift, measure_preimage_add, euclideanBall_eq_smul_image rho hrho,
    Measure.addHaar_image_linearMap, LinearMap.det_toLin', Matrix.det_smul,
    Matrix.det_one, mul_one, Fintype.card_fin, abs_of_pos (pow_pos hrho _)]

theorem ellipsoid_ball_det_lower_via_volume (Q : Matrix (Fin d) (Fin d) ℝ)
    (hQ : Q.PosDef) (c u : Fin d → ℝ) (rho : ℝ) (hrho : 0 < rho)
    (hball : ∀ x, euclideanNorm (x - u) ≤ rho → x ∈ ellipsoidSet c Q) :
    (rho ^ 2) ^ d ≤ Q.det := by
  have hvol := measure_mono (μ := volume) (s := {x | euclideanNorm (x - u) ≤ rho})
    (t := ellipsoidSet c Q) hball
  rw [euclideanBall_volume u rho hrho, ellipsoidSet_volume Q hQ c] at hvol
  have hcancel := (ENNReal.mul_le_mul_iff_left
    (euclideanUnitBall_volume_pos (d := d)).ne'
    euclideanUnitBall_compact.measure_ne_top).mp hvol
  have hroot : rho ^ d ≤ Real.sqrt Q.det := (ENNReal.ofReal_le_ofReal_iff
    (Real.sqrt_nonneg _)).mp hcancel
  have hsq := sq_le_sq₀ (pow_pos hrho d).le (Real.sqrt_nonneg Q.det) |>.mpr hroot
  rw [Real.sq_sqrt hQ.det_pos.le] at hsq
  simpa only [← pow_mul, Nat.mul_comm d 2] using hsq

/-- The actual Lebesgue volume, normalized by the dimension-dependent unit-ball
volume. Normalization cancels the same positive constant on both sides. -/
def normalizedEllipsoidVolume (c : Fin d → ℝ) (Q : Matrix (Fin d) (Fin d) ℝ) : ℝ :=
  (volume (ellipsoidSet c Q)).toReal / (volume (euclideanUnitBall d)).toReal

theorem normalizedEllipsoidVolume_eq (Q : Matrix (Fin d) (Fin d) ℝ)
    (hQ : Q.PosDef) (c : Fin d → ℝ) :
    normalizedEllipsoidVolume c Q = Real.sqrt Q.det := by
  have hk := ENNReal.toReal_pos (euclideanUnitBall_volume_pos (d := d)).ne'
    euclideanUnitBall_compact.measure_ne_top
  unfold normalizedEllipsoidVolume
  rw [ellipsoidSet_volume Q hQ c, ENNReal.toReal_mul,
    ENNReal.toReal_ofReal (Real.sqrt_nonneg _), mul_div_cancel_right₀ _ hk.ne']

theorem ellipsoid_ball_log_volume_lower (Q : Matrix (Fin d) (Fin d) ℝ)
    (hQ : Q.PosDef) (c u : Fin d → ℝ) (rho : ℝ) (hrho : 0 < rho)
    (hball : ∀ x, euclideanNorm (x - u) ≤ rho → x ∈ ellipsoidSet c Q) :
    (d : ℝ) * Real.log rho ≤ Real.log (normalizedEllipsoidVolume c Q) := by
  have hvol := measure_mono (μ := volume) (s := {x | euclideanNorm (x - u) ≤ rho})
    (t := ellipsoidSet c Q) hball
  rw [euclideanBall_volume u rho hrho, ellipsoidSet_volume Q hQ c] at hvol
  have hcancel := (ENNReal.mul_le_mul_iff_left
    (euclideanUnitBall_volume_pos (d := d)).ne'
    euclideanUnitBall_compact.measure_ne_top).mp hvol
  have hroot : rho ^ d ≤ Real.sqrt Q.det :=
    (ENNReal.ofReal_le_ofReal_iff (Real.sqrt_nonneg _)).mp hcancel
  rw [normalizedEllipsoidVolume_eq Q hQ c]
  simpa only [Real.log_pow] using Real.log_le_log (pow_pos hrho d) hroot

end MsetsPaper.Upper
