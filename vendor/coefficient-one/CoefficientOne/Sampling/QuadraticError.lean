import CoefficientOne.Sampling.LocalCoupling

/-! # The explicit quadratic probability bound for a second disagreement -/

open scoped Topology
open MeasureTheory Filter

namespace CoefficientOne.Sampling
noncomputable section

theorem secondDisagreement_quadratic_bound {n : ℕ} (k : ℕ) (hk : k ≤ n)
    (θ : ℝ → Fin n → ℝ) (a : Fin n → ℝ) (hθ : HasDerivAt θ a 0) :
    ∃ C : ℝ, 0 < C ∧ ∀ᶠ t in 𝓝[≠] (0 : ℝ),
      (seedMeasure n (secondDisagreementEvent (fun i => Real.exp (θ 0 i))
        (fun i => Real.exp (θ t i)) k)).toReal ≤ C * t ^ 2 := by
  obtain ⟨L, hL, hthreshold⟩ := residualThresholds_uniform_lipschitz θ a hθ
  let V := samplerVariation (fun i => Real.exp (θ 0 i)) k a
  let B : ℝ := |V| + n + 1
  have hB : 0 < B := by dsimp [B]; positivity
  refine ⟨n * L * B + 1, by positivity, ?_⟩
  have herr := (uniformThresholdError_tendsto θ a hθ).eventually
    (Iio_mem_nhds (show (0 : ℝ) < 1 by norm_num))
  filter_upwards [hthreshold, herr] with t hT ht
  have hδ : 0 ≤ L * |t| := mul_nonneg hL.le (abs_nonneg t)
  have hsecond := secondDisagreement_probability_le_real (fun i => Real.exp (θ 0 i))
    (fun i => Real.exp (θ t i)) (fun i => Real.exp_pos _) (fun i => Real.exp_pos _)
    k hk (L * |t|) hδ (fun R q hq i hi => by
      rw [abs_sub_comm]
      exact hT R q hq i hi)
  have hfirst := firstDisagreement_probability_bound θ a k hk t
  have hVB : V + n * uniformThresholdError θ a t ≤ B := by
    have he := mul_le_mul_of_nonneg_left ht.le (Nat.cast_nonneg n : (0 : ℝ) ≤ n)
    have hv := le_abs_self V
    dsimp [B]
    linarith
  have hp : (seedMeasure n (firstDisagreementEvent (fun i => Real.exp (θ 0 i))
      (fun i => Real.exp (θ t i)) k)).toReal ≤ |t| * B :=
    hfirst.trans (mul_le_mul_of_nonneg_left hVB (abs_nonneg t))
  calc
    _ ≤ (seedMeasure n (firstDisagreementEvent (fun i => Real.exp (θ 0 i))
        (fun i => Real.exp (θ t i)) k)).toReal * ((n : ℝ) * (L * |t|)) := hsecond
    _ ≤ (|t| * B) * ((n : ℝ) * (L * |t|)) :=
      mul_le_mul_of_nonneg_right hp (mul_nonneg (Nat.cast_nonneg n) hδ)
    _ = (n * L * B) * t ^ 2 := by
      calc
        _ = (n * L * B) * |t| ^ 2 := by ring
        _ = _ := by rw [sq_abs]
    _ ≤ (n * L * B + 1) * t ^ 2 := by nlinarith [sq_nonneg t]

end
end CoefficientOne.Sampling
