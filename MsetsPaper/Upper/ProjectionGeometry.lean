import MsetsPaper.Upper.ProjectionAccuracy
import Mathlib.Analysis.InnerProductSpace.PiL2

/-!
# Geometry used by the ellipsoid argument

Norm comparison, Lipschitz bounds, the explicit L1-ball separator, and the
protected near-optimum Euclidean ball are proved. No ellipsoid update,
volume-decrease theorem, stopping bound or machine-cost theorem is assumed.
-/

noncomputable section
open scoped BigOperators
open Matrix

namespace MsetsPaper.Upper

variable {d m : ℕ}

def euclideanNorm (v : Fin d → ℝ) : ℝ :=
  ‖(WithLp.toLp 2 v : EuclideanSpace ℝ (Fin d))‖

theorem euclideanNorm_nonneg (v : Fin d → ℝ) : 0 ≤ euclideanNorm v := norm_nonneg _

theorem euclideanNorm_sq (v : Fin d → ℝ) : (euclideanNorm v) ^ 2 = ∑ i, (v i) ^ 2 := by
  exact EuclideanSpace.real_norm_sq_eq (WithLp.toLp 2 v)

theorem coordinateL1_nonneg (v : Fin d → ℝ) : 0 ≤ coordinateL1 v :=
  Finset.sum_nonneg fun i _ => abs_nonneg _

theorem coordinateL1_sub_comm (u v : Fin d → ℝ) : coordinateL1 (u - v) = coordinateL1 (v - u) := by
  unfold coordinateL1
  simp only [Pi.sub_apply, abs_sub_comm]

theorem coordinateL1_triangle (u v : Fin d → ℝ) :
    coordinateL1 (u + v) ≤ coordinateL1 u + coordinateL1 v := by
  unfold coordinateL1
  rw [← Finset.sum_add_distrib]
  exact Finset.sum_le_sum fun i _ => abs_add_le (u i) (v i)

theorem euclideanNorm_le_coordinateL1 (v : Fin d → ℝ) : euclideanNorm v ≤ coordinateL1 v := by
  have h := Finset.sum_sq_le_sq_sum_of_nonneg
    (s := Finset.univ) (f := fun i : Fin d => |v i|) (fun i _ => abs_nonneg _)
  simp only [sq_abs] at h
  have he := euclideanNorm_sq v
  have hn := euclideanNorm_nonneg v
  have hl := coordinateL1_nonneg v
  change (∑ i, (v i) ^ 2) ≤ (coordinateL1 v) ^ 2 at h
  nlinarith

theorem coordinateL1_le_sqrt_dim_mul_euclideanNorm (v : Fin d → ℝ) :
    coordinateL1 v ≤ Real.sqrt (d : ℝ) * euclideanNorm v := by
  have h := Finset.sum_mul_sq_le_sq_mul_sq Finset.univ
    (fun i : Fin d => |v i|) (fun _ => (1 : ℝ))
  simp only [mul_one, one_pow, sq_abs, Finset.sum_const, Finset.card_univ,
    Fintype.card_fin, nsmul_eq_mul, mul_one] at h
  have hsquare : (coordinateL1 v) ^ 2 ≤ (Real.sqrt (d : ℝ) * euclideanNorm v) ^ 2 := by
    rw [mul_pow, Real.sq_sqrt (Nat.cast_nonneg d), euclideanNorm_sq]
    change (∑ i, |v i|) ^ 2 ≤ _
    nlinarith
  have hn := mul_nonneg (Real.sqrt_nonneg (d : ℝ)) (euclideanNorm_nonneg v)
  have hl := coordinateL1_nonneg v
  nlinarith

theorem projectionDual_lipschitz_l1 (theta a b u v : Fin d → ℝ)
    (hmpos : 1 ≤ m) (hmtop : m ≤ d - 1)
    (ha : ∀ i, 0 ≤ a i ∧ a i ≤ 1) (hb : ∀ i, 0 ≤ b i ∧ b i ≤ 1)
    (hab : ∀ i, a i ≤ b i) :
    |projectionDual (m := m) theta a b u - projectionDual (m := m) theta a b v| ≤
      coordinateL1 (u - v) := by
  have hmd : m ≤ d := by omega
  have hu := projectionDual_subgradient theta a b v u hmd hab
  have hv := projectionDual_subgradient theta a b u v hmd hab
  have hgu := dot_le_coordinateL1_mul (projectionSubgradient (m := m) theta a b u)
    (u - v) 1 (projectionSubgradient_abs_le_one theta a b u hmpos hmtop ha hb)
  have hgv := dot_le_coordinateL1_mul (projectionSubgradient (m := m) theta a b v)
    (v - u) 1 (projectionSubgradient_abs_le_one theta a b v hmpos hmtop ha hb)
  have hneg (g : Fin d → ℝ) : g ⬝ᵥ (v - u) = -(g ⬝ᵥ (u - v)) := by
    simp only [dotProduct, Pi.sub_apply, mul_sub, Finset.sum_sub_distrib]
    ring
  rw [hneg] at hu hgv
  rw [coordinateL1_sub_comm v u] at hgv
  rw [abs_le]
  constructor <;> nlinarith

theorem projectionDual_lipschitz_euclidean (theta a b u v : Fin d → ℝ)
    (hmpos : 1 ≤ m) (hmtop : m ≤ d - 1)
    (ha : ∀ i, 0 ≤ a i ∧ a i ≤ 1) (hb : ∀ i, 0 ≤ b i ∧ b i ≤ 1)
    (hab : ∀ i, a i ≤ b i) :
    |projectionDual (m := m) theta a b u - projectionDual (m := m) theta a b v| ≤
      Real.sqrt (d : ℝ) * euclideanNorm (u - v) :=
  (projectionDual_lipschitz_l1 theta a b u v hmpos hmtop ha hb hab).trans
    (coordinateL1_le_sqrt_dim_mul_euclideanNorm (u - v))

def l1Separator (v : Fin d → ℝ) : Fin d → ℝ := fun i => if 0 ≤ v i then 1 else -1

theorem l1Separator_self (v : Fin d → ℝ) : l1Separator v ⬝ᵥ v = coordinateL1 v := by
  apply Finset.sum_congr rfl
  intro i _
  dsimp [l1Separator]
  split_ifs with hi
  · rw [one_mul, abs_of_nonneg hi]
  · rw [neg_one_mul, abs_of_nonpos (by linarith)]

/-- Explicit separating hyperplane for a point outside the L1 ball. -/
theorem l1Separator_separates (u v : Fin d → ℝ) (R : ℝ)
    (hu : coordinateL1 u ≤ R) (hv : R < coordinateL1 v) :
    l1Separator v ⬝ᵥ u ≤ R ∧ R < l1Separator v ⬝ᵥ v := by
  have hsign : ∀ i, |l1Separator v i| ≤ 1 := by intro i; dsimp [l1Separator]; split_ifs <;> norm_num
  have h := dot_le_coordinateL1_mul (l1Separator v) u 1 hsign
  rw [l1Separator_self]
  exact ⟨by linarith, hv⟩

/-- The near-minimum Euclidean ball is contained in the search L1 ball and in
the tau/2 objective sublevel set, exactly as used by the ellipsoid argument. -/
theorem projection_near_minimum_ball (theta a b vstar u : Fin d → ℝ)
    (hmpos : 1 ≤ m) (hmtop : m ≤ d - 1)
    (ha : ∀ i, 0 ≤ a i ∧ a i ≤ 1) (hb : ∀ i, 0 ≤ b i ∧ b i ≤ 1)
    (hab : ∀ i, a i ≤ b i) (R tau : ℝ)
    (hstar : coordinateL1 vstar ≤ R / 2) (htau : tau ≤ R)
    (hu : euclideanNorm (u - vstar) ≤ tau / (2 * Real.sqrt (d : ℝ))) :
    coordinateL1 u ≤ R ∧
      projectionDual (m := m) theta a b u ≤ projectionDual (m := m) theta a b vstar + tau / 2 := by
  have hd : (0 : ℝ) < d := by exact_mod_cast (show 0 < d by omega)
  have hsqrt := Real.sqrt_pos.mpr hd
  have hscale : Real.sqrt (d : ℝ) * (tau / (2 * Real.sqrt (d : ℝ))) = tau / 2 := by
    field_simp
  have hnorm := mul_le_mul_of_nonneg_left hu hsqrt.le
  rw [hscale] at hnorm
  have hl1 := coordinateL1_le_sqrt_dim_mul_euclideanNorm (u - vstar)
  have htriangle := coordinateL1_triangle (u - vstar) vstar
  rw [sub_add_cancel] at htriangle
  have hG := projectionDual_lipschitz_euclidean theta a b u vstar hmpos hmtop ha hb hab
  rw [abs_le] at hG
  exact ⟨by linarith, by linarith [hG.2]⟩

end MsetsPaper.Upper
