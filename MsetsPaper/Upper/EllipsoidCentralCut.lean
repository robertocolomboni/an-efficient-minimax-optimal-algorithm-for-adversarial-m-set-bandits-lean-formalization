import MsetsPaper.Upper.ProjectionGeometry

/-!
# The normalized central-cut ellipsoid

This is the geometric containment underlying the actual ellipsoid update.
It does not assume a contraction, iteration or algorithm-correctness theorem.
-/

noncomputable section
open scoped BigOperators

namespace MsetsPaper.Upper

/-- New ellipsoid quadratic form in coordinates split into cut direction s
and squared perpendicular radius r. Its center is -1/(n+1), cut-axis radius
n/(n+1), and perpendicular radius n/sqrt(n^2-1). -/
def centralCutForm (n s r : ℝ) : ℝ :=
  (((n + 1) * s + 1) ^ 2 + (n ^ 2 - 1) * r) / n ^ 2

theorem centralCutForm_axis_expression (n s r : ℝ) (hn : 2 ≤ n) :
    centralCutForm n s r =
      ((n + 1) ^ 2 / n ^ 2) * (s + 1 / (n + 1)) ^ 2 +
        ((n ^ 2 - 1) / n ^ 2) * r := by
  have hn0 : n ≠ 0 := by linarith
  have hn1 : n + 1 ≠ 0 := by linarith
  unfold centralCutForm
  field_simp
  <;> ring

/-- The negative half of the unit ball lies in the central-cut ellipsoid.
The hypotheses are just membership in that half-ball, not the conclusion. -/
theorem centralCutForm_contains_half_ball (n s r : ℝ) (hn : 2 ≤ n)
    (hr : 0 ≤ r) (hs : s ≤ 0) (hball : s ^ 2 + r ≤ 1) : centralCutForm n s r ≤ 1 := by
  have hn2 : 0 < n ^ 2 := sq_pos_of_pos (by linarith)
  have hslo : -1 ≤ s := by nlinarith
  have hncoef : 0 ≤ n ^ 2 - 1 := by nlinarith
  have hfirst : (n ^ 2 - 1) * (s ^ 2 + r - 1) ≤ 0 :=
    mul_nonpos_of_nonneg_of_nonpos hncoef (by linarith)
  have hprod : s * (s + 1) ≤ 0 := mul_nonpos_of_nonpos_of_nonneg hs (by linarith)
  have hsecond : 2 * (n + 1) * (s * (s + 1)) ≤ 0 :=
    mul_nonpos_of_nonneg_of_nonpos (by linarith) hprod
  have hidentity : ((n + 1) * s + 1) ^ 2 + (n ^ 2 - 1) * r =
      n ^ 2 + (n ^ 2 - 1) * (s ^ 2 + r - 1) + 2 * (n + 1) * (s * (s + 1)) := by ring
  unfold centralCutForm
  apply (div_le_iff₀ hn2).mpr
  rw [hidentity]
  linarith

variable {d : ℕ}

def normalizedCentralCutEllipsoid (i : Fin d) : Set (Fin d → ℝ) :=
  {x | centralCutForm (d : ℝ) (x i) (∑ j ∈ Finset.univ.erase i, (x j) ^ 2) ≤ 1}

/-- Containment in actual d-dimensional coordinates, with the ambient
Euclidean norm already connected to EuclideanSpace. -/
theorem normalizedCentralCutEllipsoid_contains (hd : 2 ≤ d) (i : Fin d)
    (x : Fin d → ℝ) (hx : euclideanNorm x ≤ 1) (hcut : x i ≤ 0) :
    x ∈ normalizedCentralCutEllipsoid i := by
  have hsum : (x i) ^ 2 + (∑ j ∈ Finset.univ.erase i, (x j) ^ 2) =
      (euclideanNorm x) ^ 2 := by
    rw [euclideanNorm_sq]
    exact Finset.add_sum_erase Finset.univ (fun j : Fin d => (x j) ^ 2) (Finset.mem_univ i)
  have hball : (x i) ^ 2 + (∑ j ∈ Finset.univ.erase i, (x j) ^ 2) ≤ 1 := by
    rw [hsum]
    nlinarith [euclideanNorm_nonneg x]
  exact centralCutForm_contains_half_ball _ _ _ (by exact_mod_cast hd)
    (Finset.sum_nonneg fun j _ => sq_nonneg _) hcut hball

end MsetsPaper.Upper
