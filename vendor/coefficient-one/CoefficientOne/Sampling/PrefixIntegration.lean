import CoefficientOne.Sampling.NextReveal

/-! # Integrating the concrete future kernel over a revealed history -/

open MeasureTheory Set

namespace CoefficientOne.Sampling
noncomputable section

variable {n : ℕ} {α : Type*} [Fintype α]
  [MeasurableSpace α] [MeasurableSingletonClass α]

/-- A finite statistic that depends only on the unrevealed seed has the actual
future product law on every Borel past event. The hypothesis is pointwise
agreement of two deterministic functions, not a conditional-law assumption. -/
theorem prefixEvent_statistic_map (ℓ : ℕ) (ρ : Equiv.Perm (Fin n))
    (B : Set (PastUniforms ℓ ρ)) (hB : MeasurableSet B)
    (f : Seed n → α) (hf : Measurable f)
    (g : PrefixOrders ℓ ρ × FutureUniforms ℓ ρ → α) (hg : Measurable g)
    (he : ∀ z : SplitPrefixSeed ℓ ρ, z.2.1 ∈ B →
      f (assemblePrefixSeed ℓ ρ z) = g (z.1, z.2.2)) :
    ((seedMeasure n).restrict (prefixEvent ℓ ρ B Set.univ)).map f =
      seedMeasure n (prefixEvent ℓ ρ B Set.univ) • (prefixFutureMeasure ℓ ρ).map g := by
  apply Measure.ext_of_singleton
  intro a
  have hs : prefixEvent ℓ ρ B Set.univ ∩ f ⁻¹' {a} =
      prefixEvent ℓ ρ B (g ⁻¹' {a}) := by
    ext ω
    constructor
    · rintro ⟨⟨z, hz, rfl⟩, ha⟩
      refine ⟨z, ⟨hz.1, ?_⟩, rfl⟩
      change g (z.1, z.2.2) = a
      rw [← he z hz.1]
      exact ha
    · rintro ⟨z, hz, rfl⟩
      refine ⟨⟨z, ⟨hz.1, Set.mem_univ _⟩, rfl⟩, ?_⟩
      change f (assemblePrefixSeed ℓ ρ z) = a
      rw [he z hz.1]
      exact hz.2
  rw [Measure.map_apply hf (measurableSet_singleton a),
    Measure.restrict_apply (hf (measurableSet_singleton a)), Set.inter_comm, hs]
  rw [seedMeasure_prefixEvent_eq_past_mul_future ℓ ρ hB (hg (measurableSet_singleton a)),
    Measure.smul_apply, Measure.map_apply hg (measurableSet_singleton a)]
  rfl

theorem prefixEvent_integral (ℓ : ℕ) (ρ : Equiv.Perm (Fin n))
    (B : Set (PastUniforms ℓ ρ)) (hB : MeasurableSet B)
    (f : Seed n → α) (hf : Measurable f)
    (g : PrefixOrders ℓ ρ × FutureUniforms ℓ ρ → α) (hg : Measurable g)
    (he : ∀ z : SplitPrefixSeed ℓ ρ, z.2.1 ∈ B →
      f (assemblePrefixSeed ℓ ρ z) = g (z.1, z.2.2)) (F : α → ℝ) :
    (∫ ω in prefixEvent ℓ ρ B Set.univ, F (f ω) ∂seedMeasure n) =
      (seedMeasure n (prefixEvent ℓ ρ B Set.univ)).toReal *
        ∫ z, F (g z) ∂prefixFutureMeasure ℓ ρ := by
  rw [← integral_map hf.aemeasurable (measurable_of_finite F).aestronglyMeasurable,
    prefixEvent_statistic_map ℓ ρ B hB f hf g hg he, integral_smul_measure,
    integral_map hg.aemeasurable (measurable_of_finite F).aestronglyMeasurable]
  rfl

/-- Specialization to histories of the actual sequential recursion. -/
theorem historyEvent_integral (w : Fin n → ℝ) (k ℓ : ℕ)
    (ρ : Equiv.Perm (Fin n)) (A : Finset (Fin n))
    (f : Seed n → α) (hf : Measurable f)
    (g : PrefixOrders ℓ ρ × FutureUniforms ℓ ρ → α) (hg : Measurable g)
    (he : ∀ z : SplitPrefixSeed ℓ ρ, z.2.1 ∈ historyPastSection w k ℓ ρ A →
      f (assemblePrefixSeed ℓ ρ z) = g (z.1, z.2.2)) (F : α → ℝ) :
    (∫ ω in historyEvent w k ℓ ρ A, F (f ω) ∂seedMeasure n) =
      (seedMeasure n (historyEvent w k ℓ ρ A)).toReal *
        ∫ z, F (g z) ∂prefixFutureMeasure ℓ ρ := by
  rw [historyEvent_eq_prefix]
  exact prefixEvent_integral ℓ ρ _ (measurableSet_historyPastSection w k ℓ ρ A)
    f hf g hg he F

end
end CoefficientOne.Sampling
