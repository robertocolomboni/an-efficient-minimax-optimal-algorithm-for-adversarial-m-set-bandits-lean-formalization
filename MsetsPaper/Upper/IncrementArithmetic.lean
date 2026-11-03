import Mathlib.Data.Real.Basic
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Mathlib.Tactic.NormNum

/-!
# The explicit arithmetic at the end of Lemma 3

This is a reusable numerical step, not the entire bounded-increment lemma.
The matrix Cauchy--Schwarz and the actual estimator bound must supply
`|estimate| ≤ B`; the preceding affine-majorant result must supply `phi ≤ B`.
Nothing here assumes the claimed bound on the surrogate itself.
-/

namespace MsetsPaper.Upper

/-- Exact arithmetic after substituting `lam = 128 * eta * d`. -/
theorem eta_leverage_bound {eta d : ℝ} (heta : 0 < eta) (hd : 0 < d) :
    eta * (1 + 4 * d / (128 * eta * d)) = eta + 1 / 32 := by
  field_simp
  ring

/-- The manuscript actually proves the stronger constant `51/1024`. -/
theorem surrogate_increment_bound
    {eta B estimate majorant : ℝ} (heta : 0 < eta) (hsmall : eta ≤ 1 / 64)
    (hB : eta * B ≤ eta + 1 / 32)
    (hestimate : |estimate| ≤ B) (hphi : 0 ≤ majorant) (hphiB : majorant ≤ B) :
    eta * |estimate - eta * (4 * majorant)| ≤ 51 / 1024 := by
  have htriangle : |estimate - eta * (4 * majorant)| ≤
      B + 4 * eta * B := by
    calc
      |estimate - eta * (4 * majorant)| ≤
          |estimate| + |eta * (4 * majorant)| := abs_sub _ _
      _ = |estimate| + 4 * eta * majorant := by
        rw [abs_of_nonneg (by positivity : 0 ≤ eta * (4 * majorant))]
        ring
      _ ≤ B + 4 * eta * B := by
        have hh := mul_le_mul_of_nonneg_left hphiB
          (show 0 ≤ 4 * eta by positivity)
        linarith
  have hscaled := mul_le_mul_of_nonneg_left htriangle heta.le
  have hetab : eta * B ≤ 3 / 64 := by linarith
  have hfour : 4 * eta ≤ 1 / 16 := by linarith
  have hterm : (4 * eta) * (eta * B) ≤ (1 / 16 : ℝ) * (3 / 64) := by
    calc
      (4 * eta) * (eta * B) ≤ (4 * eta) * (3 / 64) :=
        mul_le_mul_of_nonneg_left hetab (by positivity)
      _ ≤ (1 / 16 : ℝ) * (3 / 64) :=
        mul_le_mul_of_nonneg_right hfour (by norm_num)
  nlinarith

theorem surrogate_increment_le_quarter
    {eta B estimate majorant : ℝ} (heta : 0 < eta) (hsmall : eta ≤ 1 / 64)
    (hB : eta * B ≤ eta + 1 / 32)
    (hestimate : |estimate| ≤ B) (hphi : 0 ≤ majorant) (hphiB : majorant ≤ B) :
    eta * |estimate - eta * (4 * majorant)| ≤ 1 / 4 :=
  (surrogate_increment_bound heta hsmall hB hestimate hphi hphiB).trans (by norm_num)

end MsetsPaper.Upper
