import EffectiveResistance.FiniteProbability
import Mathlib.Tactic.FieldSimp

/-!
# Analytic core of adjacent-rank curvature

This is the covariance/Cauchy--Schwarz part of the adjacent-rank lemma.  The
external-field combinatorics enters only through `hkappa` and `hOvar`: they
are exactly the likelihood-ratio identities for the two occupancy laws.
-/

open scoped BigOperators

namespace EffectiveResistance

noncomputable section

variable {Ω ι : Type*} [Fintype Ω] [Fintype ι]

/-- Cauchy--Schwarz turns the occupancy likelihood-ratio identity into the
adjacent-rank curvature inequality, in its variational (pseudoinverse-free)
form. -/
theorem adjacent_rank_curvature_of_occupancy_identity
    (p : Ω → ℝ) (hp : ∀ x, 0 ≤ p x) (hnorm : ∑ x, p x = 1)
    (φ : Ω → ℝ) (hφ0 : ∀ x, 0 ≤ φ x) (hφ1 : ∀ x, φ x ≤ 1)
    (θ : ℝ) (hθ : finiteExpectation p φ = θ) (hθpos : 0 < θ)
    (O : Ω → ι → ℝ) (κ : ι → ℝ) (rankVariance : (ι → ℝ) → ℝ)
    (hrank_nonneg : ∀ a : ι → ℝ, 0 ≤ rankVariance a)
    (hOvar : ∀ a : ι → ℝ,
      finiteVariance p (fun x => ∑ i, a i * O x i) = 2 * rankVariance a)
    (hkappa : ∀ a : ι → ℝ,
      (∑ i, a i * κ i) =
        finiteCovariance p (fun x => ∑ i, a i * O x i) φ / θ) :
    ∀ a : ι → ℝ,
      (∑ i, a i * κ i) ^ 2 ≤
        (2 * (1 - θ) / θ) * rankVariance a := by
  intro a
  let F : Ω → ℝ := fun x => ∑ i, a i * O x i
  have hcs := finiteCovariance_cauchy hp F φ
  have hvarφ := finiteVariance_unit_interval hp hnorm hφ0 hφ1
  rw [hθ] at hvarφ
  rw [hOvar a] at hcs
  have hscaled :
      2 * rankVariance a * finiteVariance p φ ≤
        2 * rankVariance a * (θ * (1 - θ)) :=
    mul_le_mul_of_nonneg_left hvarφ
      (mul_nonneg (by norm_num) (hrank_nonneg a))
  have hcov : finiteCovariance p F φ ^ 2 ≤
      2 * rankVariance a * (θ * (1 - θ)) := hcs.trans hscaled
  rw [hkappa a]
  have hθne : θ ≠ 0 := ne_of_gt hθpos
  rw [div_pow]
  apply (div_le_iff₀ (sq_pos_of_pos hθpos)).2
  field_simp [hθne]
  nlinarith

end

end EffectiveResistance
