import Mathlib.Data.Real.Basic
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-!
# The four-cell algebra in the resistance proof

This file formalizes the purely algebraic last step of the main theorem.
The four entries are the probabilities of the endpoint states `11`, `10`,
`01`, and `00`.
-/

namespace EffectiveResistance

noncomputable section

/-- A normalized four-cell table for two Bernoulli coordinates. -/
structure PairTable where
  p11 : ℝ
  p10 : ℝ
  p01 : ℝ
  p00 : ℝ
  nonneg11 : 0 ≤ p11
  nonneg10 : 0 ≤ p10
  nonneg01 : 0 ≤ p01
  nonneg00 : 0 ≤ p00
  total : p11 + p10 + p01 + p00 = 1

namespace PairTable

variable (P : PairTable)

def s : ℝ := P.p10 + P.p01
def μi : ℝ := P.p11 + P.p10
def μj : ℝ := P.p11 + P.p01
def δ : ℝ := P.p10 - P.p01
def vi : ℝ := P.μi * (1 - P.μi)
def vj : ℝ := P.μj * (1 - P.μj)
def ω : ℝ := P.p10 * P.p01 - P.p11 * P.p00
def h : ℝ := P.μi + P.μj - 2 * P.μi * P.μj

theorem μi_nonneg : 0 ≤ P.μi := by
  exact add_nonneg P.nonneg11 P.nonneg10

theorem μj_nonneg : 0 ≤ P.μj := by
  exact add_nonneg P.nonneg11 P.nonneg01

theorem one_sub_μi : 1 - P.μi = P.p01 + P.p00 := by
  simp only [μi]
  linarith [P.total]

theorem one_sub_μj : 1 - P.μj = P.p10 + P.p00 := by
  simp only [μj]
  linarith [P.total]

theorem μi_le_one : P.μi ≤ 1 := by
  rw [← sub_nonneg]
  rw [P.one_sub_μi]
  exact add_nonneg P.nonneg01 P.nonneg00

theorem μj_le_one : P.μj ≤ 1 := by
  rw [← sub_nonneg]
  rw [P.one_sub_μj]
  exact add_nonneg P.nonneg10 P.nonneg00

theorem vi_nonneg : 0 ≤ P.vi := by
  exact mul_nonneg P.μi_nonneg (sub_nonneg.mpr P.μi_le_one)

theorem vj_nonneg : 0 ≤ P.vj := by
  exact mul_nonneg P.μj_nonneg (sub_nonneg.mpr P.μj_le_one)

theorem h_decomposition :
    P.h = P.μi * (1 - P.μj) + P.μj * (1 - P.μi) := by
  simp only [h]
  ring

theorem h_nonneg : 0 ≤ P.h := by
  rw [P.h_decomposition]
  exact add_nonneg
    (mul_nonneg P.μi_nonneg (sub_nonneg.mpr P.μj_le_one))
    (mul_nonneg P.μj_nonneg (sub_nonneg.mpr P.μi_le_one))

/-- The exact polynomial certificate used to close the resistance proof. -/
theorem pair_table_identity :
    P.p10 * P.p01 * (P.vi + P.vj) +
        P.p11 * P.p00 * P.δ ^ 2 - P.s * P.vi * P.vj =
      P.ω * (2 * P.vi * P.vj + P.ω * P.h) := by
  have hp00 : P.p00 = 1 - P.p11 - P.p10 - P.p01 := by
    linarith [P.total]
  simp only [s, μi, μj, δ, vi, vj, ω, h]
  rw [hp00]
  ring

/-- If the external-field determinant `ω` is nonnegative, the numerator in
the last step of the proof dominates `s * vi * vj`. -/
theorem closing_numerator_nonnegative (hω : 0 ≤ P.ω) :
    0 ≤ P.p10 * P.p01 * (P.vi + P.vj) +
      P.p11 * P.p00 * P.δ ^ 2 - P.s * P.vi * P.vj := by
  rw [P.pair_table_identity]
  exact mul_nonneg hω (add_nonneg
    (mul_nonneg (mul_nonneg (by norm_num) P.vi_nonneg) P.vj_nonneg)
    (mul_nonneg hω P.h_nonneg))

/-- Division-free form of the conclusion obtained after the regression
estimate and the pair-table certificate have been combined. -/
theorem harmonic_conductance_bound (hω : 0 ≤ P.ω) :
    P.s * P.vi * P.vj ≤
      P.p10 * P.p01 * (P.vi + P.vj) +
        P.p11 * P.p00 * P.δ ^ 2 := by
  linarith [P.closing_numerator_nonnegative hω]

theorem s_pos (h10 : 0 < P.p10) : 0 < P.s := by
  simp only [s]
  linarith [P.nonneg01]

theorem vi_pos (h11 : 0 < P.p11) (h10 : 0 < P.p10)
    (h01 : 0 < P.p01) : 0 < P.vi := by
  apply mul_pos
  · simp only [μi]
    linarith
  · rw [P.one_sub_μi]
    linarith [P.nonneg00]

theorem vj_pos (h11 : 0 < P.p11) (h10 : 0 < P.p10)
    (h01 : 0 < P.p01) : 0 < P.vj := by
  apply mul_pos
  · simp only [μj]
    linarith
  · rw [P.one_sub_μj]
    linarith [P.nonneg00]

/-- Algebraic closure of the interior-rank proof.  Its hypothesis is exactly
the lower bound on reciprocal resistance supplied by the pair-exchange and
three-slice lemmas. -/
theorem resistance_bound_of_reciprocal_bound
    (h11 : 0 < P.p11) (h10 : 0 < P.p10) (h01 : 0 < P.p01)
    (hω : 0 ≤ P.ω) {R : ℝ} (hR : 0 < R)
    (hrecip :
      P.p10 * P.p01 / P.s +
          P.p11 * P.p00 * P.δ ^ 2 / (P.s * (P.vi + P.vj)) ≤ 1 / R) :
    R ≤ 1 / P.vi + 1 / P.vj := by
  have hs : 0 < P.s := P.s_pos h10
  have hvi : 0 < P.vi := P.vi_pos h11 h10 h01
  have hvj : 0 < P.vj := P.vj_pos h11 h10 h01
  have hvsum : 0 < P.vi + P.vj := add_pos hvi hvj
  have hnum := P.harmonic_conductance_bound hω
  have hscaled := (mul_le_mul_of_nonneg_right hrecip
    (mul_nonneg hs.le hvsum.le))
  have hconductance : P.vi * P.vj ≤ (P.vi + P.vj) / R := by
    have hleft :
        (P.p10 * P.p01 / P.s +
          P.p11 * P.p00 * P.δ ^ 2 / (P.s * (P.vi + P.vj))) *
            (P.s * (P.vi + P.vj)) =
          P.p10 * P.p01 * (P.vi + P.vj) +
            P.p11 * P.p00 * P.δ ^ 2 := by
      field_simp [ne_of_gt hs, ne_of_gt hvsum]
    have hright : (1 / R) * (P.s * (P.vi + P.vj)) =
        P.s * ((P.vi + P.vj) / R) := by ring
    rw [hleft, hright] at hscaled
    have hmul : P.s * (P.vi * P.vj) ≤
        P.s * ((P.vi + P.vj) / R) := by
      simpa [mul_assoc] using hnum.trans hscaled
    apply (mul_le_mul_iff_left₀ hs).mp
    simpa [mul_comm, mul_left_comm, mul_assoc] using hmul
  have hRmul : R * (P.vi * P.vj) ≤ P.vi + P.vj := by
    simpa [mul_assoc, mul_comm, mul_left_comm] using
      (le_div_iff₀ hR).mp hconductance
  have htarget : R ≤ (P.vi + P.vj) / (P.vi * P.vj) :=
    (le_div_iff₀ (mul_pos hvi hvj)).mpr hRmul
  calc
    R ≤ (P.vi + P.vj) / (P.vi * P.vj) := htarget
    _ = 1 / P.vi + 1 / P.vj := by
      field_simp [ne_of_gt hvi, ne_of_gt hvj]
      ring

end PairTable

end

end EffectiveResistance
