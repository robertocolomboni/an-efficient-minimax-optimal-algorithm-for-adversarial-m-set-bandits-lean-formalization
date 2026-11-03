import MsetsPaper.Upper.EllipsoidInverse

/-! Central-cut containment for an arbitrary positive definite shape. -/

noncomputable section
open scoped BigOperators
open Matrix

namespace MsetsPaper.Upper

variable {d : ℕ}

def ellipsoidSet (c : Fin d → ℝ) (Q : Matrix (Fin d) (Fin d) ℝ) : Set (Fin d → ℝ) :=
  {x | ellipsoidQuadratic Q⁻¹ (x - c) ≤ 1}

theorem ellipsoidQuadratic_inverse_shift (Q : Matrix (Fin d) (Fin d) ℝ)
    (hQ : Q.PosDef) (g z : Fin d → ℝ) (k : ℝ) :
    ellipsoidQuadratic Q⁻¹ (z + k • (Q *ᵥ g)) =
      ellipsoidQuadratic Q⁻¹ z + 2 * k * (z ⬝ᵥ g) + k ^ 2 * ellipsoidQuadratic Q g := by
  have hc : (Q *ᵥ g) ⬝ᵥ (Q⁻¹ *ᵥ z) = g ⬝ᵥ z := by
    rw [dotProduct_mulVec, ellipsoidShape_vec_inverse_cancel Q hQ]
  simp only [ellipsoidQuadratic, Matrix.mulVec_add, Matrix.mulVec_smul,
    ellipsoidShape_inverse_cancel Q hQ, dotProduct_add, dotProduct_smul,
    add_dotProduct, smul_dotProduct, smul_eq_mul]
  rw [hc, dotProduct_comm g z, dotProduct_comm (Q *ᵥ g) g]
  ring

theorem ellipsoidQuadratic_next_inverse (hd : 2 ≤ d)
    (Q : Matrix (Fin d) (Fin d) ℝ) (hQ : Q.PosDef)
    (g : Fin d → ℝ) (hg : g ≠ 0) (y : Fin d → ℝ) :
    ellipsoidQuadratic (ellipsoidNextShape Q g)⁻¹ y =
      (((d : ℝ) ^ 2 - 1) / (d : ℝ) ^ 2) *
        (ellipsoidQuadratic Q⁻¹ y +
          (2 / (((d : ℝ) - 1) * ellipsoidQuadratic Q g)) * (y ⬝ᵥ g) ^ 2) := by
  rw [ellipsoidNextShape_inv hd Q hQ g hg]
  simp only [ellipsoidQuadratic, Matrix.smul_mulVec, Matrix.add_mulVec,
    Matrix.vecMulVec_mulVec, dotProduct_add, dotProduct_smul,
    smul_eq_mul, op_smul_eq_mul]
  rw [dotProduct_comm g y]
  ring

theorem centralCut_metric_identity (n q h z : ℝ) (hn : 2 ≤ n) (hq : 0 < q) :
    ((n ^ 2 - 1) / n ^ 2) *
      (z + 2 * (1 / ((n + 1) * Real.sqrt q)) * h +
        (1 / ((n + 1) * Real.sqrt q)) ^ 2 * q +
        (2 / ((n - 1) * q)) * (h + (1 / ((n + 1) * Real.sqrt q)) * q) ^ 2) =
      centralCutForm n (h / Real.sqrt q) (z - (h / Real.sqrt q) ^ 2) := by
  have hn0 : n ≠ 0 := by linarith
  have hnp : n + 1 ≠ 0 := by linarith
  have hnm : n - 1 ≠ 0 := by linarith
  have hs : Real.sqrt q ≠ 0 := (Real.sqrt_pos.mpr hq).ne'
  have hsq := Real.sq_sqrt hq.le
  conv_lhs => rw [← hsq]
  conv_rhs => rw [← hsq]
  rw [Real.sqrt_sq (Real.sqrt_nonneg q)]
  unfold centralCutForm
  field_simp
  <;> ring

theorem ellipsoid_central_cut_contains (hd : 2 ≤ d)
    (Q : Matrix (Fin d) (Fin d) ℝ) (hQ : Q.PosDef)
    (c g x : Fin d → ℝ) (hg : g ≠ 0)
    (hx : x ∈ ellipsoidSet c Q) (hcut : (x - c) ⬝ᵥ g ≤ 0) :
    x ∈ ellipsoidSet (ellipsoidNextCenter c g Q) (ellipsoidNextShape Q g) := by
  let z := x - c
  let q := ellipsoidQuadratic Q g
  let s := (z ⬝ᵥ g) / Real.sqrt q
  let r := ellipsoidQuadratic Q⁻¹ z - s ^ 2
  have hq : 0 < q := ellipsoidQuadratic_pos Q hQ g hg
  have hsqrt : 0 < Real.sqrt q := Real.sqrt_pos.mpr hq
  have hcs := ellipsoidQuadratic_cauchy_schwarz Q⁻¹ hQ.inv.posSemidef z (Q *ᵥ g)
  have hinv : ellipsoidQuadratic Q⁻¹ (Q *ᵥ g) = q := by
    simp only [ellipsoidQuadratic, ellipsoidShape_inverse_cancel Q hQ]
    exact dotProduct_comm _ _
  rw [ellipsoidShape_inverse_cancel Q hQ, hinv] at hcs
  have hs2 : s ^ 2 ≤ ellipsoidQuadratic Q⁻¹ z := by
    dsimp [s]
    rw [div_pow, Real.sq_sqrt hq.le]
    exact (div_le_iff₀ hq).mpr hcs
  have hr : 0 ≤ r := sub_nonneg.mpr hs2
  have hs0 : s ≤ 0 := div_nonpos_of_nonpos_of_nonneg hcut hsqrt.le
  have hball : s ^ 2 + r ≤ 1 := by
    change ellipsoidQuadratic Q⁻¹ z ≤ 1 at hx
    dsimp [r]
    linarith
  have hmetric := centralCutForm_contains_half_ball (d : ℝ) s r
    (by exact_mod_cast hd) hr hs0 hball
  change ellipsoidQuadratic (ellipsoidNextShape Q g)⁻¹
    (x - ellipsoidNextCenter c g Q) ≤ 1
  have hcenter : x - ellipsoidNextCenter c g Q =
      z + (1 / (((d : ℝ) + 1) * Real.sqrt q)) • (Q *ᵥ g) := by
    ext i
    simp only [ellipsoidNextCenter, Pi.sub_apply, Pi.add_apply, Pi.smul_apply,
      smul_eq_mul, z, q]
    ring
  rw [hcenter, ellipsoidQuadratic_next_inverse hd Q hQ g hg,
    ellipsoidQuadratic_inverse_shift Q hQ]
  simp only [add_dotProduct, smul_dotProduct, smul_eq_mul]
  rw [dotProduct_comm (Q *ᵥ g) g]
  change ((d : ℝ) ^ 2 - 1) / (d : ℝ) ^ 2 *
    (ellipsoidQuadratic Q⁻¹ z + 2 * (1 / (((d : ℝ) + 1) * Real.sqrt q)) * (z ⬝ᵥ g) +
      (1 / (((d : ℝ) + 1) * Real.sqrt q)) ^ 2 * q +
      (2 / (((d : ℝ) - 1) * q)) *
        ((z ⬝ᵥ g) + (1 / (((d : ℝ) + 1) * Real.sqrt q)) * q) ^ 2) ≤ 1
  rw [centralCut_metric_identity _ _ _ _ (by exact_mod_cast hd) hq]
  exact hmetric

end MsetsPaper.Upper
