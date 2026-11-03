import MsetsPaper.Upper.Estimator
import Mathlib.Algebra.QuadraticDiscriminant

/-!
# The bounded-estimator step from actual inverse moments

Matrix Cauchy--Schwarz is proved with the two square roots in the manuscript,
then specialized to a common leverage bound. The leverages are not assumed bounded in the
final paper theorem: the caller must apply the separately proved majorant.
-/

noncomputable section

open Matrix MsetsLower MsetsLower.History

namespace MsetsPaper.Upper

/-- Matrix Cauchy--Schwarz, with the two square roots exactly as in the text. -/
theorem abs_bilinear_le_sqrt_quadratic {d : ℕ} (A : Matrix (Fin d) (Fin d) ℝ)
    (hA : A.PosSemidef) (x y : Fin d → ℝ) :
    |x ⬝ᵥ (A *ᵥ y)| ≤ Real.sqrt (x ⬝ᵥ (A *ᵥ x)) *
      Real.sqrt (y ⬝ᵥ (A *ᵥ y)) := by
  have hsymm : A.IsSymm := Matrix.isHermitian_iff_isSymm.mp hA.1
  have hswap : y ⬝ᵥ (A *ᵥ x) = x ⬝ᵥ (A *ᵥ y) := by
    simpa only [hsymm.eq] using Matrix.dotProduct_transpose_mulVec A y x
  have hx : 0 ≤ x ⬝ᵥ (A *ᵥ x) := by
    simpa only [star_trivial] using hA.dotProduct_mulVec_nonneg x
  have hy : 0 ≤ y ⬝ᵥ (A *ᵥ y) := by
    simpa only [star_trivial] using hA.dotProduct_mulVec_nonneg y
  have hdisc := discrim_le_zero (a := y ⬝ᵥ (A *ᵥ y))
    (b := 2 * (x ⬝ᵥ (A *ᵥ y))) (c := x ⬝ᵥ (A *ᵥ x)) (by
      intro t
      have h := hA.dotProduct_mulVec_nonneg (x + t • y)
      simp only [star_trivial, Matrix.mulVec_add, Matrix.mulVec_smul,
        add_dotProduct, dotProduct_add, smul_dotProduct, dotProduct_smul,
        smul_eq_mul, hswap] at h
      nlinarith)
  simp only [discrim] at hdisc
  have hsq : (x ⬝ᵥ (A *ᵥ y)) ^ 2 ≤
      (x ⬝ᵥ (A *ᵥ x)) * (y ⬝ᵥ (A *ᵥ y)) := by nlinarith
  apply (sq_le_sq₀ (abs_nonneg _) (mul_nonneg (Real.sqrt_nonneg _) (Real.sqrt_nonneg _))).mp
  rw [sq_abs, mul_pow, Real.sq_sqrt hx, Real.sq_sqrt hy]
  exact hsq

theorem abs_bilinear_le_common_bound {d : ℕ} (A : Matrix (Fin d) (Fin d) ℝ)
    (hA : A.PosSemidef) (x y : Fin d → ℝ) {B : ℝ}
    (hx : x ⬝ᵥ (A *ᵥ x) ≤ B) (hy : y ⬝ᵥ (A *ᵥ y) ≤ B) :
    |x ⬝ᵥ (A *ᵥ y)| ≤ B := by
  have hx0 : 0 ≤ x ⬝ᵥ (A *ᵥ x) := by
    simpa only [star_trivial] using hA.dotProduct_mulVec_nonneg x
  calc
    _ ≤ Real.sqrt (x ⬝ᵥ (A *ᵥ x)) * Real.sqrt (y ⬝ᵥ (A *ᵥ y)) :=
      abs_bilinear_le_sqrt_quadratic A hA x y
    _ ≤ Real.sqrt B * Real.sqrt B :=
      mul_le_mul (Real.sqrt_le_sqrt hx) (Real.sqrt_le_sqrt hy)
        (Real.sqrt_nonneg _) (Real.sqrt_nonneg _)
    _ = B := Real.mul_self_sqrt (hx0.trans hx)

theorem abs_estimateScalar_le_of_leverage_bound {d m : ℕ}
    (theta ell : Fin d → ℝ) (hmpos : 1 ≤ m) (hmtop : m ≤ d - 1)
    (a b : Action d m) {B : ℝ}
    (hloss : |actionLoss a ell| ≤ 1)
    (ha : (fun i ↦ selectedIndicator i a) ⬝ᵥ
      ((secondMoment (weightedLaw (m := m) theta))⁻¹ *ᵥ
        (fun i ↦ selectedIndicator i a)) ≤ B)
    (hb : (fun i ↦ selectedIndicator i b) ⬝ᵥ
      ((secondMoment (weightedLaw (m := m) theta))⁻¹ *ᵥ
        (fun i ↦ selectedIndicator i b)) ≤ B) :
    |estimateScalar theta a ell b| ≤ B := by
  have hcross := abs_bilinear_le_common_bound _
    ((weightedLaw_secondMoment_posDef theta hmpos hmtop).inv.posSemidef)
    (fun i ↦ selectedIndicator i b) (fun i ↦ selectedIndicator i a) hb ha
  simp only [estimateScalar, estimateVector, dotProduct_smul, smul_eq_mul, abs_mul]
  calc
    |actionLoss a ell| * |(fun i ↦ selectedIndicator i b) ⬝ᵥ
        ((secondMoment (weightedLaw theta))⁻¹ *ᵥ (fun i ↦ selectedIndicator i a))| ≤
        1 * B := mul_le_mul hloss hcross (abs_nonneg _) (by norm_num)
    _ = B := one_mul _

/-- The first displayed estimator inequality of L3, before either leverage
is replaced by its common majorant. -/
theorem abs_estimateScalar_le_sqrt_quadratic {d m : ℕ}
    (theta ell : Fin d → ℝ) (hmpos : 1 ≤ m) (hmtop : m ≤ d - 1)
    (a b : Action d m) (hloss : |actionLoss a ell| ≤ 1) :
    |estimateScalar theta a ell b| ≤
      Real.sqrt ((fun i ↦ selectedIndicator i b) ⬝ᵥ
        ((secondMoment (weightedLaw (m := m) theta))⁻¹ *ᵥ (fun i ↦ selectedIndicator i b))) *
      Real.sqrt ((fun i ↦ selectedIndicator i a) ⬝ᵥ
        ((secondMoment (weightedLaw (m := m) theta))⁻¹ *ᵥ (fun i ↦ selectedIndicator i a))) := by
  have hcs := abs_bilinear_le_sqrt_quadratic _
    (weightedLaw_secondMoment_posDef theta hmpos hmtop).inv.posSemidef
    (fun i ↦ selectedIndicator i b) (fun i ↦ selectedIndicator i a)
  simp only [estimateScalar, estimateVector, dotProduct_smul, smul_eq_mul, abs_mul]
  exact (mul_le_mul hloss hcs (abs_nonneg _) zero_le_one).trans_eq (one_mul _)

end MsetsPaper.Upper
