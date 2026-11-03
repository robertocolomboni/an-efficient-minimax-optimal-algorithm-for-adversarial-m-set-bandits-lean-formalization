import MsetsPaper.Upper.EllipsoidShape

/-! A quantitative determinant decrease for the actual central cut. -/

noncomputable section
open scoped BigOperators
open Matrix

namespace MsetsPaper.Upper

def ellipsoidDetFactor (d : ℕ) : ℝ :=
  ((d : ℝ) ^ 2 / ((d : ℝ) ^ 2 - 1)) ^ d * (((d : ℝ) - 1) / ((d : ℝ) + 1))

theorem ellipsoidDetFactor_axis_form {d : ℕ} (hd : 2 ≤ d) :
    ellipsoidDetFactor d =
      ((d : ℝ) ^ 2 / ((d : ℝ) + 1) ^ 2) *
        ((d : ℝ) ^ 2 / ((d : ℝ) ^ 2 - 1)) ^ (d - 1) := by
  have hdR : (2 : ℝ) ≤ d := by exact_mod_cast hd
  have hdp : (d : ℝ) + 1 ≠ 0 := by linarith
  have hds : (d : ℝ) ^ 2 - 1 ≠ 0 := by nlinarith
  have hpow : ((d : ℝ) ^ 2 / ((d : ℝ) ^ 2 - 1)) ^ d =
      ((d : ℝ) ^ 2 / ((d : ℝ) ^ 2 - 1)) ^ (d - 1) *
        ((d : ℝ) ^ 2 / ((d : ℝ) ^ 2 - 1)) := by
    rw [← pow_succ, Nat.sub_add_cancel (by omega : 1 ≤ d)]
  rw [ellipsoidDetFactor, hpow]
  have hc : ((d : ℝ) ^ 2 / ((d : ℝ) ^ 2 - 1)) *
      (((d : ℝ) - 1) / ((d : ℝ) + 1)) = (d : ℝ) ^ 2 / ((d : ℝ) + 1) ^ 2 := by
    field_simp
    <;> ring
  calc
    _ = (((d : ℝ) ^ 2 / ((d : ℝ) ^ 2 - 1)) *
        (((d : ℝ) - 1) / ((d : ℝ) + 1))) *
        ((d : ℝ) ^ 2 / ((d : ℝ) ^ 2 - 1)) ^ (d - 1) := by ring
    _ = _ := by rw [hc]

theorem ellipsoidDetFactor_pos {d : ℕ} (hd : 2 ≤ d) : 0 < ellipsoidDetFactor d := by
  have hdR : (2 : ℝ) ≤ d := by exact_mod_cast hd
  have hds : (0 : ℝ) < (d : ℝ) ^ 2 - 1 := by nlinarith
  unfold ellipsoidDetFactor
  exact mul_pos (pow_pos (div_pos (by positivity) hds) _)
    (div_pos (by linarith) (by linarith))

/-- A sufficient, slightly weaker-than-sharp exponential decrease. It gives
the same polynomial oracle-call order; no sharp volume constant is claimed. -/
theorem ellipsoidDetFactor_log_le {d : ℕ} (hd : 2 ≤ d) :
    Real.log (ellipsoidDetFactor d) ≤ -1 / (2 * ((d : ℝ) + 1)) := by
  have hdR : (2 : ℝ) ≤ d := by exact_mod_cast hd
  have hd0 : (0 : ℝ) < d := by linarith
  have hdp : (0 : ℝ) < d + 1 := by linarith
  have hdm : (0 : ℝ) < d - 1 := by linarith
  have hds : (0 : ℝ) < (d : ℝ) ^ 2 - 1 := by nlinarith
  have ha : (0 : ℝ) < (d : ℝ) ^ 2 / ((d : ℝ) + 1) ^ 2 := by positivity
  have hb : (0 : ℝ) < (d : ℝ) ^ 2 / ((d : ℝ) ^ 2 - 1) := by positivity
  rw [ellipsoidDetFactor_axis_form hd, Real.log_mul ha.ne' (pow_pos hb _).ne', Real.log_pow]
  have hlogA := Real.log_le_sub_one_of_pos ha
  have hlogB := mul_le_mul_of_nonneg_left (Real.log_le_sub_one_of_pos hb)
    (Nat.cast_nonneg (d - 1) : (0 : ℝ) ≤ ((d - 1 : ℕ) : ℝ))
  have hcast : ((d - 1 : ℕ) : ℝ) = (d : ℝ) - 1 := by
    simpa using (Nat.cast_sub (R := ℝ) (by omega : 1 ≤ d))
  rw [hcast] at hlogB ⊢
  have hsum : ((d : ℝ) ^ 2 / ((d : ℝ) + 1) ^ 2 - 1) +
      ((d : ℝ) - 1) * ((d : ℝ) ^ 2 / ((d : ℝ) ^ 2 - 1) - 1) =
      -(d : ℝ) / ((d : ℝ) + 1) ^ 2 := by
    field_simp
    <;> ring
  have hrate : -(d : ℝ) / ((d : ℝ) + 1) ^ 2 ≤ -1 / (2 * ((d : ℝ) + 1)) := by
    apply (div_le_div_iff₀ (sq_pos_of_pos hdp) (by positivity)).mpr
    nlinarith
  linarith

theorem ellipsoidDetFactor_le_exp {d : ℕ} (hd : 2 ≤ d) :
    ellipsoidDetFactor d ≤ Real.exp (-1 / (2 * ((d : ℝ) + 1))) :=
  (Real.log_le_iff_le_exp (ellipsoidDetFactor_pos hd)).mp (ellipsoidDetFactor_log_le hd)

theorem ellipsoidNextShape_det_contract {d : ℕ} (hd : 2 ≤ d)
    (Q : Matrix (Fin d) (Fin d) ℝ) (hQ : Q.PosDef) (g : Fin d → ℝ) (hg : g ≠ 0) :
    (ellipsoidNextShape Q g).det ≤
      Real.exp (-1 / (2 * ((d : ℝ) + 1))) * Q.det := by
  rw [ellipsoidNextShape_det hd Q hQ g hg]
  exact mul_le_mul_of_nonneg_right (ellipsoidDetFactor_le_exp hd) hQ.det_pos.le

end MsetsPaper.Upper
