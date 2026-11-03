import MsetsPaper.Alignment.BinomialRates

/-! Algebra behind the introductory comparison of displayed regret rates.
The guarantees attributed to previous papers are not assumed as Lean axioms;
these identities compare their displayed expressions with our proved scale.
-/

namespace MsetsPaper.Alignment

theorem introduction_rate_factor_identities {d m T : ℝ}
    (hd : 0 ≤ d) (hm : 0 ≤ m) :
    d * Real.sqrt (m * T) = Real.sqrt d * Real.sqrt (d * m * T) ∧
    m * Real.sqrt (d * T) = Real.sqrt m * Real.sqrt (d * m * T) := by
  constructor
  · rw [show d * m * T = d * (m * T) by ring, Real.sqrt_mul hd,
      ← mul_assoc, Real.mul_self_sqrt hd]
  · rw [show d * m * T = m * (d * T) by ring, Real.sqrt_mul hm,
      ← mul_assoc, Real.mul_self_sqrt hm]

end MsetsPaper.Alignment
