import CoefficientOne.Sampling.ThresholdHazardProbability
import CoefficientOne.Sampling.UniformThresholdExpansion

/-! The first-disagreement union bound with a uniform differential remainder. -/

open scoped BigOperators
open EffectiveResistance Matrix MeasureTheory

namespace CoefficientOne.Sampling
noncomputable section
set_option maxHeartbeats 1000000

theorem uniformThresholdError_nonneg {n : ℕ} (θ : ℝ → Fin n → ℝ)
    (a : Fin n → ℝ) (t : ℝ) : 0 ≤ uniformThresholdError θ a t :=
  finiteDerivativeError_nonneg _ _ _

theorem thresholdGapMean_le_expansion {n : ℕ} (θ : ℝ → Fin n → ℝ)
    (a : Fin n → ℝ) (R : Finset (Fin n)) (r : ℕ) (hr : r ≤ R.card) (t : ℝ) :
    thresholdGapMean (fun i => Real.exp (θ 0 i)) (fun i => Real.exp (θ t i)) R r ≤
      |t| * (l1Norm (residualCovariance (fun i => Real.exp (θ 0 i)) R r *ᵥ a) /
        R.card + uniformThresholdError θ a t) := by
  classical
  let δ : Fin n → ℝ := fun i => residualThresholdVector (θ t) R r i -
    residualThresholdVector (θ 0) R r i
  let j := residualCovariance (fun i => Real.exp (θ 0 i)) R r *ᵥ a
  have hgap : thresholdGapMean (fun i => Real.exp (θ 0 i))
      (fun i => Real.exp (θ t i)) R r = l1Norm δ / R.card := by
    unfold thresholdGapMean l1Norm
    congr 1
    rw [← Finset.sum_subset (Finset.subset_univ R)]
    · apply Finset.sum_congr rfl
      intro i hi
      simp [δ, residualThresholdVector, hi, abs_sub_comm]
    · intro i _ hi
      simp [δ, residualThresholdVector, hi]
  have htri : l1Norm δ ≤ l1Norm (fun i => δ i - t * j i) + |t| * l1Norm j := by
    simp only [l1Norm, Finset.mul_sum, ← Finset.sum_add_distrib]
    apply Finset.sum_le_sum
    intro i _
    calc
      |δ i| = |(δ i - t * j i) + t * j i| := by congr 1; ring
      _ ≤ |δ i - t * j i| + |t * j i| := abs_add_le _ _
      _ = _ := by rw [abs_mul]
  have hex := uniformThresholdError_expansion θ a R r hr t
  change l1Norm (fun i => δ i - t * j i) ≤ |t| * uniformThresholdError θ a t at hex
  have htotal : l1Norm δ ≤ |t| * (l1Norm j + uniformThresholdError θ a t) := by
    linarith
  rw [hgap]
  change l1Norm δ / (R.card : ℝ) ≤ |t| * (l1Norm j / (R.card : ℝ) + _)
  by_cases hc : R.card = 0
  · simp only [hc, Nat.cast_zero, div_zero, zero_add]
    exact mul_nonneg (abs_nonneg t) (uniformThresholdError_nonneg θ a t)
  have hcpos : (0 : ℝ) < R.card := Nat.cast_pos.mpr (Nat.pos_of_ne_zero hc)
  have hcone : (1 : ℝ) ≤ R.card := by exact_mod_cast Nat.one_le_iff_ne_zero.mpr hc
  have herr : uniformThresholdError θ a t / (R.card : ℝ) ≤ uniformThresholdError θ a t :=
    div_le_self (uniformThresholdError_nonneg θ a t) hcone
  calc
    l1Norm δ / (R.card : ℝ) ≤ (|t| * (l1Norm j + uniformThresholdError θ a t)) / R.card :=
      div_le_div_of_nonneg_right htotal hcpos.le
    _ = |t| * (l1Norm j / R.card + uniformThresholdError θ a t / R.card) := by ring
    _ ≤ _ := mul_le_mul_of_nonneg_left (add_le_add le_rfl herr) (abs_nonneg t)

theorem thresholdHazard_probability_le_expansion {n : ℕ} (θ : ℝ → Fin n → ℝ)
    (a : Fin n → ℝ) (k : ℕ) (hk : k ≤ n) (t : ℝ) (ℓ : Fin n) :
    (seedMeasure n (thresholdHazard (fun i => Real.exp (θ 0 i))
      (fun i => Real.exp (θ t i)) k ℓ)).toReal ≤
      |t| * ((∫ ω, variationContribution (fun i => Real.exp (θ 0 i)) k ℓ.val a ω
        ∂seedMeasure n) + uniformThresholdError θ a t) := by
  let w := fun i => Real.exp (θ 0 i)
  let v := fun i => Real.exp (θ t i)
  rw [thresholdHazard_probability w v (fun _ => Real.exp_pos _) (fun _ => Real.exp_pos _) k hk ℓ]
  have hG := integrable_historyStatistic w k ℓ.val (fun z => thresholdGapMean w v z.1 z.2)
  change Integrable (fun ω => thresholdGapMean w v (historyRemaining ℓ.val ω)
    (historyQuota w k ℓ.val ω)) (seedMeasure n) at hG
  have hV := integrable_variationContribution w k ℓ.val a
  calc
    _ ≤ ∫ ω, |t| * (variationContribution w k ℓ.val a ω + uniformThresholdError θ a t)
        ∂seedMeasure n := by
      apply integral_mono hG ((hV.add (integrable_const _)).const_mul _)
      intro ω
      exact thresholdGapMean_le_expansion θ a _ _ (historyQuota_le_remaining_card w k ℓ.val hk ω) t
    _ = _ := by rw [integral_const_mul, integral_add hV (integrable_const _), integral_const]; simp [w]

/-- The probability of any first disagreement, before taking the derivative limit. -/
theorem firstDisagreement_probability_bound {n : ℕ} (θ : ℝ → Fin n → ℝ)
    (a : Fin n → ℝ) (k : ℕ) (hk : k ≤ n) (t : ℝ) :
    (seedMeasure n (firstDisagreementEvent (fun i => Real.exp (θ 0 i))
      (fun i => Real.exp (θ t i)) k)).toReal ≤
      |t| * (samplerVariation (fun i => Real.exp (θ 0 i)) k a +
        (n : ℝ) * uniformThresholdError θ a t) := by
  let w := fun i => Real.exp (θ 0 i)
  let v := fun i => Real.exp (θ t i)
  calc
    _ ≤ (seedMeasure n).real (⋃ ℓ : Fin n, thresholdHazard w v k ℓ) :=
      measureReal_mono (firstDisagreementEvent_subset_hazards w v k)
    _ ≤ ∑ ℓ : Fin n, (seedMeasure n).real (thresholdHazard w v k ℓ) :=
      measureReal_iUnion_fintype_le _
    _ ≤ ∑ ℓ : Fin n, |t| * ((∫ ω, variationContribution w k ℓ.val a ω ∂seedMeasure n) +
        uniformThresholdError θ a t) := by
      exact Finset.sum_le_sum (fun ℓ _ => thresholdHazard_probability_le_expansion θ a k hk t ℓ)
    _ = _ := by
      rw [← Finset.mul_sum, Finset.sum_add_distrib]
      simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
      rw [samplerVariation_eq_sum]
      have he := Fin.sum_univ_eq_sum_range (fun ℓ =>
        ∫ ω, variationContribution w k ℓ a ω ∂seedMeasure n) n
      rw [he]

end
end CoefficientOne.Sampling
