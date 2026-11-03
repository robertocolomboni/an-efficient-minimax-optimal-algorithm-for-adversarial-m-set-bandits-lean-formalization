import CoefficientOne.Sampling.NextReveal

/-! # Exact probability of a disagreement between two thresholds -/

open MeasureTheory Set
open scoped BigOperators ENNReal unitInterval

namespace CoefficientOne.Sampling
noncomputable section

theorem uniform_threshold_disagreement_of_le (p q : unitInterval) (hpq : p ≤ q) :
    (volume : Measure unitInterval) {u | ((u : ℝ) ≤ (p : ℝ)) ≠ ((u : ℝ) ≤ (q : ℝ))} =
      ENNReal.ofReal ((q : ℝ) - (p : ℝ)) := by
  have he : {u : unitInterval | ((u : ℝ) ≤ (p : ℝ)) ≠ ((u : ℝ) ≤ (q : ℝ))} = Ioc p q := by
    ext u
    change ((u ≤ p) ≠ (u ≤ q)) ↔ p < u ∧ u ≤ q
    by_cases hup : u ≤ p
    · have huq : u ≤ q := hup.trans hpq
      simp [hup, huq, not_lt.mpr hup]
    · have hpu : p < u := lt_of_not_ge hup
      simp [hup, hpu]
  rw [he, unitInterval.volume_Ioc]

theorem uniform_threshold_disagreement (p q : unitInterval) :
    (volume : Measure unitInterval) {u | ((u : ℝ) ≤ (p : ℝ)) ≠ ((u : ℝ) ≤ (q : ℝ))} =
      ENNReal.ofReal |(p : ℝ) - (q : ℝ)| := by
  rcases le_total p q with hpq | hqp
  · rw [uniform_threshold_disagreement_of_le p q hpq,
      abs_of_nonpos (sub_nonpos.mpr (show (p : ℝ) ≤ (q : ℝ) from hpq)), neg_sub]
  · have he : {u : unitInterval | ((u : ℝ) ≤ (p : ℝ)) ≠ ((u : ℝ) ≤ (q : ℝ))} =
        {u : unitInterval | ((u : ℝ) ≤ (q : ℝ)) ≠ ((u : ℝ) ≤ (p : ℝ))} := by
      ext u
      exact ne_comm
    rw [he, uniform_threshold_disagreement_of_le q p hqp,
      abs_of_nonneg (sub_nonneg.mpr (show (q : ℝ) ≤ (p : ℝ) from hqp))]

variable {α : Type*} [Fintype α] [MeasurableSpace α] [MeasurableSingletonClass α]

def thresholdDisagreementSet (p q : α → unitInterval) : Set (α × unitInterval) :=
  {z | ((z.2 : ℝ) ≤ (p z.1 : ℝ)) ≠ ((z.2 : ℝ) ≤ (q z.1 : ℝ))}

theorem measurableSet_thresholdDisagreement (p q : α → unitInterval) :
    MeasurableSet (thresholdDisagreementSet p q) := by
  have hp : MeasurableSet {z : α × unitInterval | z.2 ≤ p z.1} :=
    measurableSet_le measurable_snd ((measurable_of_finite p).comp measurable_fst)
  have hq : MeasurableSet {z : α × unitInterval | z.2 ≤ q z.1} :=
    measurableSet_le measurable_snd ((measurable_of_finite q).comp measurable_fst)
  have he : thresholdDisagreementSet p q =
      ({z : α × unitInterval | z.2 ≤ p z.1} \ {z : α × unitInterval | z.2 ≤ q z.1}) ∪
      ({z : α × unitInterval | z.2 ≤ q z.1} \ {z : α × unitInterval | z.2 ≤ p z.1}) := by
    ext z
    change ((z.2 ≤ p z.1) ≠ (z.2 ≤ q z.1)) ↔ _
    simp only [Set.mem_union, Set.mem_diff, Set.mem_setOf_eq]
    tauto
  rw [he]
  exact (hp.diff hq).union (hq.diff hp)

variable [Nonempty α]

theorem uniformIndex_threshold_disagreement (p q : α → unitInterval) :
    ((uniformMeasure α).prod (volume : Measure unitInterval)) (thresholdDisagreementSet p q) =
      (Fintype.card α : ℝ≥0∞)⁻¹ * ENNReal.ofReal (∑ i, |(p i : ℝ) - (q i : ℝ)|) := by
  rw [Measure.prod_apply (measurableSet_thresholdDisagreement p q), lintegral_fintype]
  have hf (i : α) : Prod.mk i ⁻¹' thresholdDisagreementSet p q =
      {u : unitInterval | ((u : ℝ) ≤ (p i : ℝ)) ≠ ((u : ℝ) ≤ (q i : ℝ))} := rfl
  simp only [hf, uniform_threshold_disagreement, uniformMeasure_singleton]
  rw [← Finset.sum_mul, ← ENNReal.ofReal_sum_of_nonneg (fun i _ => abs_nonneg ((p i : ℝ) - (q i : ℝ))), mul_comm]

theorem uniformIndex_threshold_disagreement_real (p q : α → unitInterval) :
    (((uniformMeasure α).prod (volume : Measure unitInterval)) (thresholdDisagreementSet p q)).toReal =
      (Fintype.card α : ℝ)⁻¹ * ∑ i, |(p i : ℝ) - (q i : ℝ)| := by
  rw [uniformIndex_threshold_disagreement, ENNReal.toReal_mul, ENNReal.toReal_inv,
    ENNReal.toReal_natCast, ENNReal.toReal_ofReal (Finset.sum_nonneg fun i _ => abs_nonneg _)]

theorem nextReveal_threshold_disagreement {n : ℕ} (ℓ : ℕ) (ρ : Equiv.Perm (Fin n))
    [Nonempty {i // ¬Revealed ℓ ρ i}]
    (j : {j : Fin n // ¬j.val < ℓ}) (p q : {i // ¬Revealed ℓ ρ i} → unitInterval) :
    (prefixFutureMeasure ℓ ρ)
      {z | ((z.2 (remainingOrder ℓ ρ z.1 j) : ℝ) ≤ (p (remainingOrder ℓ ρ z.1 j) : ℝ)) ≠
        ((z.2 (remainingOrder ℓ ρ z.1 j) : ℝ) ≤ (q (remainingOrder ℓ ρ z.1 j) : ℝ))} =
      (Fintype.card {i // ¬Revealed ℓ ρ i} : ℝ≥0∞)⁻¹ *
        ENNReal.ofReal (∑ i, |(p i : ℝ) - (q i : ℝ)|) := by
  have h := nextReveal_measurePreserving ℓ ρ j
  calc
    _ = ((uniformMeasure {i // ¬Revealed ℓ ρ i}).prod (volume : Measure unitInterval))
        (thresholdDisagreementSet p q) := by
      rw [← h.map_eq, Measure.map_apply h.measurable (measurableSet_thresholdDisagreement p q)]
      rfl
    _ = _ := uniformIndex_threshold_disagreement p q

theorem nextReveal_threshold_disagreement_real {n : ℕ} (ℓ : ℕ) (ρ : Equiv.Perm (Fin n))
    [Nonempty {i // ¬Revealed ℓ ρ i}]
    (j : {j : Fin n // ¬j.val < ℓ}) (p q : {i // ¬Revealed ℓ ρ i} → unitInterval) :
    ((prefixFutureMeasure ℓ ρ)
      {z | ((z.2 (remainingOrder ℓ ρ z.1 j) : ℝ) ≤ (p (remainingOrder ℓ ρ z.1 j) : ℝ)) ≠
        ((z.2 (remainingOrder ℓ ρ z.1 j) : ℝ) ≤ (q (remainingOrder ℓ ρ z.1 j) : ℝ))}).toReal =
      (Fintype.card {i // ¬Revealed ℓ ρ i} : ℝ)⁻¹ * ∑ i, |(p i : ℝ) - (q i : ℝ)| := by
  rw [nextReveal_threshold_disagreement, ENNReal.toReal_mul, ENNReal.toReal_inv,
    ENNReal.toReal_natCast, ENNReal.toReal_ofReal (Finset.sum_nonneg fun i _ => abs_nonneg _)]

end
end CoefficientOne.Sampling
