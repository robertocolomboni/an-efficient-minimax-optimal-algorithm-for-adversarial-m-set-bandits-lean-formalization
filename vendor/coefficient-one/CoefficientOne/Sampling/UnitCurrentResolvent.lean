import CoefficientOne.Sampling.UnitCurrentGram
import EffectiveResistance.FiniteProbability

/-! # The Gram operator and its resolvent estimate -/

open scoped BigOperators
open Matrix EffectiveResistance

namespace CoefficientOne.Sampling
noncomputable section

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

theorem dotProduct_sq_le_self (x y : ι → ℝ) :
    (x ⬝ᵥ y) ^ 2 ≤ (x ⬝ᵥ x) * (y ⬝ᵥ y) := by
  exact Finset.sum_sq_le_sum_mul_sum_of_sq_le_mul
    (s := Finset.univ) (r := fun i => x i * y i)
    (f := fun i => x i * x i) (g := fun i => y i * y i)
    (fun _ _ => mul_self_nonneg _) (fun _ _ => mul_self_nonneg _)
    (fun _ _ => by nlinarith [sq_nonneg (0 : ℝ)])

namespace NormalizedGram
variable {N : ConductanceNetwork ι} (G : NormalizedGram N)

def operator : Matrix ι ι ℝ :=
  ∑ i, stationaryMass N i • Matrix.vecMulVec (G.vectors i) (G.vectors i)

def moment (u : ι → ℝ) : ι → ℝ :=
  ∑ i, (stationaryMass N i * u i) • G.vectors i

theorem operator_isSymm : G.operator.IsSymm := by
  apply Matrix.IsSymm.ext
  intro i j
  simp only [operator, Matrix.sum_apply, Matrix.smul_apply, smul_eq_mul,
    Matrix.vecMulVec_apply]
  apply Finset.sum_congr rfl
  intro k _
  ring

theorem operator_mulVec (x : ι → ℝ) :
    G.operator *ᵥ x = ∑ i, (stationaryMass N i * (G.vectors i ⬝ᵥ x)) • G.vectors i := by
  simp only [operator, Matrix.sum_mulVec, Matrix.smul_mulVec, Matrix.vecMulVec_mulVec]
  simp [smul_smul, mul_comm]

theorem operator_quadratic (x : ι → ℝ) :
    quadraticForm G.operator x = ∑ i, stationaryMass N i * (G.vectors i ⬝ᵥ x) ^ 2 := by
  rw [quadraticForm, G.operator_mulVec]
  simp only [dotProduct_sum, dotProduct_smul, smul_eq_mul]
  apply Finset.sum_congr rfl
  intro i _
  rw [dotProduct_comm x (G.vectors i)]
  ring

theorem operator_posSemidef [Nonempty ι] (hd : ∀ i, 0 < N.degree i) :
    G.operator.PosSemidef := by
  apply Matrix.posSemidef_iff_dotProduct_mulVec.mpr
  refine ⟨Matrix.isHermitian_iff_isSymm.mpr G.operator_isSymm, ?_⟩
  intro x
  simp only [star_trivial]
  change 0 ≤ quadraticForm G.operator x
  rw [G.operator_quadratic]
  exact Finset.sum_nonneg (fun i _ => mul_nonneg (stationaryMass_pos N hd i).le
    (sq_nonneg _))

theorem operator_le_one [Nonempty ι] (hd : ∀ i, 0 < N.degree i) :
    LoewnerLE G.operator 1 := by
  intro x
  rw [G.operator_quadratic]
  simp only [quadraticForm, Matrix.one_mulVec]
  calc
    _ ≤ ∑ i, stationaryMass N i * (x ⬝ᵥ x) := by
      apply Finset.sum_le_sum
      intro i _
      apply mul_le_mul_of_nonneg_left _ (stationaryMass_pos N hd i).le
      simpa only [G.unit, one_mul] using dotProduct_sq_le_self (G.vectors i) x
    _ = x ⬝ᵥ x := by rw [← Finset.sum_mul, sum_stationaryMass N hd, one_mul]

end NormalizedGram

/-- The scalar estimate used in the resolvent bound. -/
theorem resolvent_scalar_bound {t : ℝ} (ht : 0 ≤ t) : t / (1 + t) ^ 2 ≤ 1 / 4 := by
  have hp : 0 < (1 + t) ^ 2 := sq_pos_of_pos (by linarith)
  apply (div_le_iff₀ hp).mpr
  nlinarith [sq_nonneg (t - 1)]

/-- Algebraic form of the same resolvent inequality:
||(I+K)x||² - 4<x,Kx> = ||(I-K)x||² ≥ 0.
It avoids choosing eigenvectors but retains exactly the manuscript's resolvent. -/
theorem four_quadratic_le_resolvent_norm (K : Matrix ι ι ℝ) (x : ι → ℝ) :
    4 * quadraticForm K x ≤ (x + K *ᵥ x) ⬝ᵥ (x + K *ᵥ x) := by
  have h : 0 ≤ (x - K *ᵥ x) ⬝ᵥ (x - K *ᵥ x) :=
    Finset.sum_nonneg (fun _ _ => mul_self_nonneg _)
  simp only [sub_dotProduct, dotProduct_sub] at h
  simp only [add_dotProduct, dotProduct_add, quadraticForm]
  rw [dotProduct_comm (K *ᵥ x) x] at h ⊢
  linarith

theorem resolvent_det_ne_zero (K : Matrix ι ι ℝ) (hK : K.PosSemidef) :
    (1 + K).det ≠ 0 := by
  have hkern : ∀ x : ι → ℝ, (1 + K) *ᵥ x = 0 → x = 0 := by
    intro x hx
    have hpos := hK.dotProduct_mulVec_nonneg x
    simp only [star_trivial] at hpos
    have hzero : x ⬝ᵥ x + x ⬝ᵥ (K *ᵥ x) = 0 := by
      have := congrArg (fun y => x ⬝ᵥ y) hx
      simpa [Matrix.add_mulVec, dotProduct_add] using this
    have hnorm : x ⬝ᵥ x = 0 := by
      have hn : 0 ≤ x ⬝ᵥ x := Finset.sum_nonneg (fun _ _ => mul_self_nonneg _)
      linarith
    exact dotProduct_self_eq_zero.mp hnorm
  have hinj : Function.Injective ((1 + K).mulVec) := by
    intro x y hxy
    apply sub_eq_zero.mp
    apply hkern
    rw [Matrix.mulVec_sub, hxy, sub_self]
  exact isUnit_iff_ne_zero.mp ((Matrix.isUnit_iff_isUnit_det _).mp
    (Matrix.mulVec_injective_iff_isUnit.mp hinj))

theorem resolvent_quadratic_bound (K : Matrix ι ι ℝ) (hK : K.PosSemidef)
    (b : ι → ℝ) :
    quadraticForm K ((1 + K)⁻¹ *ᵥ b) ≤ (1 / 4 : ℝ) * (b ⬝ᵥ b) := by
  have hsolve : (1 + K) *ᵥ ((1 + K)⁻¹ *ᵥ b) = b := by
    rw [Matrix.mulVec_mulVec, Matrix.mul_nonsing_inv _
      (isUnit_iff_ne_zero.mpr (resolvent_det_ne_zero K hK)), Matrix.one_mulVec]
  simp only [Matrix.add_mulVec, Matrix.one_mulVec] at hsolve
  have h := four_quadratic_le_resolvent_norm K ((1 + K)⁻¹ *ᵥ b)
  rw [hsolve] at h
  linarith

theorem quadratic_bound_of_resolvent_equation (K : Matrix ι ι ℝ)
    (x b : ι → ℝ) (hx : x + K *ᵥ x = b) :
    quadraticForm K x ≤ (1 / 4 : ℝ) * (b ⬝ᵥ b) := by
  have h := four_quadratic_le_resolvent_norm K x
  rw [hx] at h
  linarith

end
end CoefficientOne.Sampling
