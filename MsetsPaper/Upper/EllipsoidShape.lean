import MsetsPaper.Upper.EllipsoidCentralCut
import MsetsPaper.Upper.MatrixBounds
import Mathlib.LinearAlgebra.Matrix.SchurComplement

/-!
# The actual central-cut shape-matrix update

Positive definiteness is proved from the old shape matrix, nonzero cut, and
dimension >=2; it is not supplied as an invariant about the new matrix.
-/

noncomputable section
open scoped BigOperators
open Matrix

namespace MsetsPaper.Upper

variable {d : ℕ}

def ellipsoidQuadratic (Q : Matrix (Fin d) (Fin d) ℝ) (x : Fin d → ℝ) : ℝ :=
  x ⬝ᵥ (Q *ᵥ x)

def ellipsoidRankOneDowndate (Q : Matrix (Fin d) (Fin d) ℝ) (g : Fin d → ℝ) (t : ℝ) :=
  Q - (t / ellipsoidQuadratic Q g) • Matrix.vecMulVec (Q *ᵥ g) (Q *ᵥ g)

def ellipsoidNextShape (Q : Matrix (Fin d) (Fin d) ℝ) (g : Fin d → ℝ) :=
  ((d : ℝ) ^ 2 / ((d : ℝ) ^ 2 - 1)) • ellipsoidRankOneDowndate Q g (2 / ((d : ℝ) + 1))

def ellipsoidNextCenter (c g : Fin d → ℝ) (Q : Matrix (Fin d) (Fin d) ℝ) : Fin d → ℝ :=
  c - (1 / (((d : ℝ) + 1) * Real.sqrt (ellipsoidQuadratic Q g))) • (Q *ᵥ g)

theorem ellipsoidQuadratic_pos (Q : Matrix (Fin d) (Fin d) ℝ) (hQ : Q.PosDef)
    (g : Fin d → ℝ) (hg : g ≠ 0) : 0 < ellipsoidQuadratic Q g := by
  simpa only [ellipsoidQuadratic, star_trivial] using hQ.dotProduct_mulVec_pos hg

theorem ellipsoidQuadratic_cauchy_schwarz (Q : Matrix (Fin d) (Fin d) ℝ)
    (hQ : Q.PosSemidef) (x g : Fin d → ℝ) :
    (x ⬝ᵥ (Q *ᵥ g)) ^ 2 ≤ ellipsoidQuadratic Q x * ellipsoidQuadratic Q g := by
  have h := abs_bilinear_le_sqrt_quadratic Q hQ x g
  have hx : 0 ≤ x ⬝ᵥ (Q *ᵥ x) := by simpa only [star_trivial] using hQ.dotProduct_mulVec_nonneg x
  have hg : 0 ≤ g ⬝ᵥ (Q *ᵥ g) := by simpa only [star_trivial] using hQ.dotProduct_mulVec_nonneg g
  have hs := (sq_le_sq₀ (abs_nonneg _) (mul_nonneg (Real.sqrt_nonneg _) (Real.sqrt_nonneg _))).mpr h
  simpa only [sq_abs, mul_pow, Real.sq_sqrt hx, Real.sq_sqrt hg, ellipsoidQuadratic] using hs

theorem ellipsoidRankOneDowndate_quadratic (Q : Matrix (Fin d) (Fin d) ℝ)
    (g x : Fin d → ℝ) (t : ℝ) :
    ellipsoidQuadratic (ellipsoidRankOneDowndate Q g t) x =
      ellipsoidQuadratic Q x - (t / ellipsoidQuadratic Q g) * (x ⬝ᵥ (Q *ᵥ g)) ^ 2 := by
  simp only [ellipsoidQuadratic, ellipsoidRankOneDowndate, Matrix.sub_mulVec,
    Matrix.smul_mulVec, Matrix.vecMulVec_mulVec, dotProduct_sub, dotProduct_smul,
    smul_eq_mul, op_smul_eq_mul]
  rw [dotProduct_comm (Q *ᵥ g) x]
  ring

theorem ellipsoidRankOneDowndate_posDef (Q : Matrix (Fin d) (Fin d) ℝ)
    (hQ : Q.PosDef) (g : Fin d → ℝ) (hg : g ≠ 0) (t : ℝ) (ht0 : 0 ≤ t) (ht1 : t < 1) :
    (ellipsoidRankOneDowndate Q g t).PosDef := by
  have hsym : Q.IsSymm := Matrix.isHermitian_iff_isSymm.mp hQ.1
  have hnewSym : (ellipsoidRankOneDowndate Q g t).IsSymm := by
    apply Matrix.IsSymm.ext
    intro i j
    simp only [ellipsoidRankOneDowndate, Matrix.sub_apply, Matrix.smul_apply,
      Matrix.vecMulVec_apply, smul_eq_mul]
    rw [hsym.apply]
    ring
  apply Matrix.PosDef.of_dotProduct_mulVec_pos (Matrix.isHermitian_iff_isSymm.mpr hnewSym)
  intro x hx
  simp only [star_trivial]
  change 0 < ellipsoidQuadratic (ellipsoidRankOneDowndate Q g t) x
  rw [ellipsoidRankOneDowndate_quadratic]
  have hgQ := ellipsoidQuadratic_pos Q hQ g hg
  have hxQ := ellipsoidQuadratic_pos Q hQ x hx
  have hcs := ellipsoidQuadratic_cauchy_schwarz Q hQ.posSemidef x g
  have hscaled := mul_le_mul_of_nonneg_left hcs (div_nonneg ht0 hgQ.le)
  have hcancel : (t / ellipsoidQuadratic Q g) *
      (ellipsoidQuadratic Q x * ellipsoidQuadratic Q g) = t * ellipsoidQuadratic Q x := by
    field_simp
  rw [hcancel] at hscaled
  have hpositive := mul_pos (sub_pos.mpr ht1) hxQ
  nlinarith

theorem ellipsoidNextShape_posDef (hd : 2 ≤ d) (Q : Matrix (Fin d) (Fin d) ℝ)
    (hQ : Q.PosDef) (g : Fin d → ℝ) (hg : g ≠ 0) : (ellipsoidNextShape Q g).PosDef := by
  have hdR : (2 : ℝ) ≤ d := by exact_mod_cast hd
  have hdplus : (0 : ℝ) < d + 1 := by linarith
  have ht0 : (0 : ℝ) ≤ 2 / ((d : ℝ) + 1) := by positivity
  have ht1 : (2 : ℝ) / ((d : ℝ) + 1) < 1 := (div_lt_one hdplus).mpr (by linarith)
  have hden : (0 : ℝ) < (d : ℝ) ^ 2 - 1 := by nlinarith
  exact (ellipsoidRankOneDowndate_posDef Q hQ g hg _ ht0 ht1).smul (div_pos (by positivity) hden)

theorem det_one_add_vecMulVec (u v : Fin d → ℝ) :
    (1 + Matrix.vecMulVec u v).det = 1 + v ⬝ᵥ u := by
  have hprod : Matrix.replicateCol Unit u * Matrix.replicateRow Unit v = Matrix.vecMulVec u v := by
    ext i j
    simp [Matrix.mul_apply, Matrix.replicateCol, Matrix.replicateRow, Matrix.vecMulVec]
  simpa only [hprod] using Matrix.det_one_add_replicateCol_mul_replicateRow (ι := Unit) u v

theorem det_one_sub_smul_vecMulVec (u v : Fin d → ℝ) (c : ℝ) :
    (1 - c • Matrix.vecMulVec u v).det = 1 - c * (v ⬝ᵥ u) := by
  have heq : 1 - c • Matrix.vecMulVec u v = 1 + Matrix.vecMulVec ((-c) • u) v := by
    rw [Matrix.smul_vecMulVec, neg_smul, sub_eq_add_neg]
  rw [heq, det_one_add_vecMulVec, dotProduct_smul, smul_eq_mul]
  ring

theorem ellipsoidRankOneDowndate_factor (Q : Matrix (Fin d) (Fin d) ℝ)
    (g : Fin d → ℝ) (t : ℝ) :
    ellipsoidRankOneDowndate Q g t =
      Q * (1 - (t / ellipsoidQuadratic Q g) • Matrix.vecMulVec g (Q *ᵥ g)) := by
  simp only [Matrix.mul_sub, Matrix.mul_one, Matrix.mul_smul, Matrix.mul_vecMulVec,
    ellipsoidRankOneDowndate]

/-- Exact determinant of the rank-one downdate, proved by the matrix
determinant lemma rather than assumed from the ellipsoid analysis. -/
theorem ellipsoidRankOneDowndate_det (Q : Matrix (Fin d) (Fin d) ℝ)
    (hQ : Q.PosDef) (g : Fin d → ℝ) (hg : g ≠ 0) (t : ℝ) :
    (ellipsoidRankOneDowndate Q g t).det = Q.det * (1 - t) := by
  have hq := (ellipsoidQuadratic_pos Q hQ g hg).ne'
  rw [ellipsoidRankOneDowndate_factor, Matrix.det_mul, det_one_sub_smul_vecMulVec,
    dotProduct_comm (Q *ᵥ g) g]
  change Q.det * (1 - (t / ellipsoidQuadratic Q g) * ellipsoidQuadratic Q g) = _
  rw [div_mul_cancel₀ t hq]

/-- Exact determinant factor for the actual central-cut update. -/
theorem ellipsoidNextShape_det (hd : 2 ≤ d) (Q : Matrix (Fin d) (Fin d) ℝ)
    (hQ : Q.PosDef) (g : Fin d → ℝ) (hg : g ≠ 0) :
    (ellipsoidNextShape Q g).det =
      ((d : ℝ) ^ 2 / ((d : ℝ) ^ 2 - 1)) ^ d *
        (((d : ℝ) - 1) / ((d : ℝ) + 1)) * Q.det := by
  have hdR : (2 : ℝ) ≤ d := by exact_mod_cast hd
  have hden : (d : ℝ) + 1 ≠ 0 := by linarith
  have hc : 1 - 2 / ((d : ℝ) + 1) = ((d : ℝ) - 1) / ((d : ℝ) + 1) := by
    field_simp
    <;> ring
  rw [ellipsoidNextShape, Matrix.det_smul, Fintype.card_fin, ellipsoidRankOneDowndate_det Q hQ g hg, hc]
  ring

end MsetsPaper.Upper
