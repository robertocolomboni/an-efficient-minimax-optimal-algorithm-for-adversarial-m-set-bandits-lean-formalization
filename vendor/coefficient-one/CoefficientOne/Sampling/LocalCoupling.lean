import CoefficientOne.Sampling.FirstDisagreementBound
import CoefficientOne.Sampling.StoppedDisagreement

/-! # The local common-seed coupling estimate

The first-disagreement bound is linear in the perturbation, while the
conditional second-disagreement probability is also linear. The exact
distance-two frozen continuation therefore leaves only a quadratic error.
-/

open scoped Topology
open MeasureTheory Filter

namespace CoefficientOne.Sampling
noncomputable section

theorem localCoupling_numeric (D p q b t n δ : ℝ) (hn : 0 ≤ n) (hδ : 0 ≤ δ)
    (hD : D ≤ 2 * p + n * q) (hq : q ≤ p * (n * δ)) (hp : p ≤ t * b) :
    D ≤ t * b * (2 + n ^ 2 * δ) := by
  calc
    D ≤ 2 * p + n * q := hD
    _ ≤ 2 * p + n * (p * (n * δ)) := by gcongr
    _ = p * (2 + n ^ 2 * δ) := by ring
    _ ≤ t * b * (2 + n ^ 2 * δ) :=
      mul_le_mul_of_nonneg_right hp (by positivity)

/-- A differentiable parameter path satisfies the manuscript's precise local
bound on the same seed measure as the actual recursive sampler. -/
theorem parameter_local_coupling {n : ℕ} (k : ℕ) (hk : k ≤ n)
    (θ : ℝ → Fin n → ℝ) (a : Fin n → ℝ) (hθ : HasDerivAt θ a 0) :
    ∀ ε > (0 : ℝ), ∀ᶠ t in 𝓝[≠] (0 : ℝ),
      expectedOutputDistance (seedMeasure n)
          (sequentialSampler (fun i => Real.exp (θ 0 i)) k)
          (sequentialSampler (fun i => Real.exp (θ t i)) k) / |t| ≤
        2 * samplerVariation (fun i => Real.exp (θ 0 i)) k a + ε := by
  obtain ⟨L, hL, hthreshold⟩ := residualThresholds_uniform_lipschitz θ a hθ
  let V := samplerVariation (fun i => Real.exp (θ 0 i)) k a
  have he := uniformThresholdError_tendsto θ a hθ
  have htlim : Tendsto (fun t : ℝ => |t|) (𝓝[≠] 0) (𝓝 0) := by
    simpa only [abs_zero] using (continuous_abs.tendsto (0 : ℝ)).mono_left nhdsWithin_le_nhds
  have hlim : Tendsto (fun t : ℝ =>
      (V + n * uniformThresholdError θ a t) * (2 + (n : ℝ) ^ 2 * (L * |t|)))
      (𝓝[≠] 0) (𝓝 (2 * V)) := by
    convert (tendsto_const_nhds.add (tendsto_const_nhds.mul he)).mul
      (tendsto_const_nhds.add (tendsto_const_nhds.mul (tendsto_const_nhds.mul htlim))) using 1 <;>
      first | rfl | simp <;> ring
  intro ε hε
  have hupper := hlim.eventually (Iio_mem_nhds (show 2 * V < 2 * V + ε by linarith))
  filter_upwards [hthreshold, hupper, self_mem_nhdsWithin] with t hT hR ht
  have ht0 : t ≠ 0 := by simpa using ht
  have htpos : 0 < |t| := abs_pos.mpr ht0
  have hδ : 0 ≤ L * |t| := mul_nonneg hL.le (abs_nonneg t)
  have hD := frozenCoupling_expectation_bound (fun i => Real.exp (θ 0 i))
    (fun i => Real.exp (θ t i)) (fun i => Real.exp_pos _) k hk
  have hq := secondDisagreement_probability_le_real (fun i => Real.exp (θ 0 i))
    (fun i => Real.exp (θ t i)) (fun i => Real.exp_pos _) (fun i => Real.exp_pos _)
    k hk (L * |t|) hδ (fun R q hq i hi => by
      rw [abs_sub_comm]
      exact hT R q hq i hi)
  have hp := firstDisagreement_probability_bound θ a k hk t
  have hb := localCoupling_numeric _ _ _ (V + n * uniformThresholdError θ a t)
    |t| n (L * |t|) (Nat.cast_nonneg n) hδ hD hq hp
  have hratio : expectedOutputDistance (seedMeasure n)
        (sequentialSampler (fun i => Real.exp (θ 0 i)) k)
        (sequentialSampler (fun i => Real.exp (θ t i)) k) / |t| ≤
      (V + n * uniformThresholdError θ a t) * (2 + (n : ℝ) ^ 2 * (L * |t|)) := by
    apply (div_le_iff₀ htpos).mpr
    calc
      _ ≤ |t| * (V + n * uniformThresholdError θ a t) * (2 + (n : ℝ) ^ 2 * (L * |t|)) := hb
      _ = _ := by ring
  exact hratio.trans hR.le

end
end CoefficientOne.Sampling
