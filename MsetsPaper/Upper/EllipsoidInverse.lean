import MsetsPaper.Upper.EllipsoidShape

/-! Explicit inverses for the actual central-cut shape matrix. -/

noncomputable section
open scoped BigOperators
open Matrix

namespace MsetsPaper.Upper

variable {d : ℕ}

theorem ellipsoidShape_mul_inv (Q : Matrix (Fin d) (Fin d) ℝ) (hQ : Q.PosDef) :
    Q * Q⁻¹ = 1 :=
  Matrix.mul_nonsing_inv Q (isUnit_iff_ne_zero.mpr hQ.det_pos.ne')

theorem ellipsoidShape_inv_mul (Q : Matrix (Fin d) (Fin d) ℝ) (hQ : Q.PosDef) :
    Q⁻¹ * Q = 1 :=
  Matrix.nonsing_inv_mul Q (isUnit_iff_ne_zero.mpr hQ.det_pos.ne')

theorem ellipsoidShape_inverse_cancel (Q : Matrix (Fin d) (Fin d) ℝ)
    (hQ : Q.PosDef) (g : Fin d → ℝ) : Q⁻¹ *ᵥ (Q *ᵥ g) = g := by
  rw [Matrix.mulVec_mulVec, ellipsoidShape_inv_mul Q hQ, Matrix.one_mulVec]

theorem ellipsoidShape_vec_inverse_cancel (Q : Matrix (Fin d) (Fin d) ℝ)
    (hQ : Q.PosDef) (g : Fin d → ℝ) : (Q *ᵥ g) ᵥ* Q⁻¹ = g := by
  rw [Matrix.vecMul_mulVec, (Matrix.isHermitian_iff_isSymm.mp hQ.1).eq,
    ellipsoidShape_mul_inv Q hQ, Matrix.vecMul_one]

theorem ellipsoidRankOneDowndate_inv (Q : Matrix (Fin d) (Fin d) ℝ)
    (hQ : Q.PosDef) (g : Fin d → ℝ) (hg : g ≠ 0) (t : ℝ) (ht : t ≠ 1) :
    (ellipsoidRankOneDowndate Q g t)⁻¹ =
      Q⁻¹ + (t / ((1 - t) * ellipsoidQuadratic Q g)) • Matrix.vecMulVec g g := by
  have hq : ellipsoidQuadratic Q g ≠ 0 := (ellipsoidQuadratic_pos Q hQ g hg).ne'
  have ht' : 1 - t ≠ 0 := sub_ne_zero.mpr (Ne.symm ht)
  apply Matrix.inv_eq_right_inv
  simp only [ellipsoidRankOneDowndate, Matrix.sub_mul, Matrix.mul_add,
    Matrix.mul_smul, Matrix.smul_mul, Matrix.mul_vecMulVec, Matrix.vecMulVec_mul,
    Matrix.vecMul_vecMulVec, ellipsoidShape_mul_inv Q hQ,
    ellipsoidShape_vec_inverse_cancel Q hQ, Matrix.sub_mulVec, Matrix.smul_mulVec,
    Matrix.vecMulVec_mulVec, smul_smul]
  have hcomm : (Q *ᵥ g) ⬝ᵥ g = ellipsoidQuadratic Q g := dotProduct_comm _ _
  rw [hcomm]
  ext i j
  simp only [Matrix.sub_apply, Matrix.add_apply, Matrix.smul_apply,
    Matrix.vecMulVec_apply, Pi.sub_apply, Pi.smul_apply, smul_eq_mul, op_smul_eq_mul]
  field_simp [hq, ht']
  <;> ring

theorem ellipsoidNextShape_inv (hd : 2 ≤ d) (Q : Matrix (Fin d) (Fin d) ℝ)
    (hQ : Q.PosDef) (g : Fin d → ℝ) (hg : g ≠ 0) :
    (ellipsoidNextShape Q g)⁻¹ =
      (((d : ℝ) ^ 2 - 1) / (d : ℝ) ^ 2) •
        (Q⁻¹ + (2 / (((d : ℝ) - 1) * ellipsoidQuadratic Q g)) • Matrix.vecMulVec g g) := by
  have hdR : (2 : ℝ) ≤ d := by exact_mod_cast hd
  have hd0 : (d : ℝ) ≠ 0 := by linarith
  have hd1 : (d : ℝ) - 1 ≠ 0 := by linarith
  have hdp : (d : ℝ) + 1 ≠ 0 := by linarith
  have hds : (d : ℝ) ^ 2 - 1 ≠ 0 := by nlinarith
  have hq : ellipsoidQuadratic Q g ≠ 0 := (ellipsoidQuadratic_pos Q hQ g hg).ne'
  have ht : 2 / ((d : ℝ) + 1) ≠ 1 := by
    intro h
    have := (div_eq_iff hdp).mp h
    linarith
  have hcoeff : (2 / ((d : ℝ) + 1)) /
      ((1 - 2 / ((d : ℝ) + 1)) * ellipsoidQuadratic Q g) =
      2 / (((d : ℝ) - 1) * ellipsoidQuadratic Q g) := by
    rw [div_div]
    congr 1
    field_simp
    <;> ring
  have hinv := ellipsoidRankOneDowndate_inv Q hQ g hg _ ht
  rw [hcoeff] at hinv
  apply Matrix.inv_eq_right_inv
  have hnew := ellipsoidRankOneDowndate_posDef Q hQ g hg (2 / ((d : ℝ) + 1)) (by positivity)
    ((div_lt_one (by linarith : (0 : ℝ) < d + 1)).mpr (by linarith))
  rw [← hinv, ellipsoidNextShape, Matrix.smul_mul, Matrix.mul_smul,
    ellipsoidShape_mul_inv _ hnew,
    smul_smul]
  have hc : ((d : ℝ) ^ 2 / ((d : ℝ) ^ 2 - 1)) *
      (((d : ℝ) ^ 2 - 1) / (d : ℝ) ^ 2) = 1 := by field_simp
  rw [hc, one_smul]

end MsetsPaper.Upper
