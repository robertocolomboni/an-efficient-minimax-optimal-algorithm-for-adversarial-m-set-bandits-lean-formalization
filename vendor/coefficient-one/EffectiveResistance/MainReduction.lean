import EffectiveResistance.ThreeSlice

/-!
# Assembly of the main resistance argument

This file combines the pair-exchange identity, the three-slice estimate, and
the four-cell certificate.  The hypotheses named `hpair`, `hχ`, and `hε` are
the outputs of the probabilistic/regression part of the paper.
-/

namespace EffectiveResistance

noncomputable section

namespace PairTable

variable (P : PairTable)

/-- Once the pair-exchange and three-slice identities have been established,
the endpoint-degree effective-resistance estimate follows. -/
theorem endpoint_resistance_of_pair_exchange_and_curvature
    (h11 : 0 < P.p11) (h10 : 0 < P.p10) (h01 : 0 < P.p01)
    (h00 : 0 < P.p00) (hω : 0 ≤ P.ω)
    {χ ε R : ℝ} (hχ0 : 0 ≤ χ)
    (hχ : χ ≤ 2 * P.ω / (P.p11 * P.p00 * P.s))
    (hε : ε = 4 / (P.sliceDenominator + χ))
    (hR : 0 < R)
    (hpair : 1 / R =
      P.p10 * P.p01 / P.s + P.δ ^ 2 / (4 * P.s ^ 2) * ε) :
    R ≤ 1 / P.vi + 1 / P.vj := by
  have hs : 0 < P.s := P.s_pos h10
  have hvi : 0 < P.vi := P.vi_pos h11 h10 h01
  have hvj : 0 < P.vj := P.vj_pos h11 h10 h01
  have hvsum : 0 < P.vi + P.vj := add_pos hvi hvj
  have hthree := P.three_slice_residual_bound
    h11 h10 h01 h00 hχ0 hχ hε
  have hcoef : 0 ≤ P.δ ^ 2 / (4 * P.s ^ 2) := by positivity
  have hmul := mul_le_mul_of_nonneg_left hthree hcoef
  have hterm :
      P.p11 * P.p00 * P.δ ^ 2 / (P.s * (P.vi + P.vj)) ≤
        P.δ ^ 2 / (4 * P.s ^ 2) * ε := by
    calc
      P.p11 * P.p00 * P.δ ^ 2 / (P.s * (P.vi + P.vj)) =
          P.δ ^ 2 / (4 * P.s ^ 2) *
            (4 * P.p11 * P.p00 * P.s / (P.vi + P.vj)) := by
        field_simp [ne_of_gt hs, ne_of_gt hvsum]
      _ ≤ P.δ ^ 2 / (4 * P.s ^ 2) * ε := hmul
  have hrecip :
      P.p10 * P.p01 / P.s +
          P.p11 * P.p00 * P.δ ^ 2 / (P.s * (P.vi + P.vj)) ≤ 1 / R := by
    rw [hpair]
    linarith
  exact P.resistance_bound_of_reciprocal_bound h11 h10 h01 hω hR hrecip

end PairTable

end

end EffectiveResistance
