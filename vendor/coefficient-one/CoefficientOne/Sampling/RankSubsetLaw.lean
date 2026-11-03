import CoefficientOne.Sampling.SequentialLaw

/-!
# The fixed-rank law of the sequential sampler

The ambient finite-subset law used for the recursion is exactly the pushforward
of the external-field law on fixed-rank subsets.
-/

open EffectiveResistance MeasureTheory

namespace CoefficientOne.Sampling

noncomputable section

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

@[simp] theorem restrictedElementary_univ (w : ι → ℝ) (k : ℕ) :
    restrictedElementary w Finset.univ k = elementarySum w k := by
  rw [restrictedElementary_eq_multiset, ElementaryDeletion.elementarySum_eq_multiset]

theorem restrictedMass_univ_rankSubset (w : ι → ℝ) (k : ℕ) (S : RankSubset ι k) :
    restrictedMass w Finset.univ k S.val = subsetProbability w k S := by
  simp [restrictedMass, Finset.mem_powersetCard, S.property, subsetProbability]

/-- Forgetting the rank proof preserves precisely the ambient residual law. -/
theorem externalFieldLaw_val_measurePreserving (w : ι → ℝ) (hw : ∀ i, 0 < w i)
    (k : ℕ) (hk : k ≤ Fintype.card ι) :
    MeasurePreserving (Subtype.val : RankSubset ι k → Finset ι)
      (lawMeasure (externalFieldLaw w hw hk))
      (lawMeasure (restrictedLaw w hw Finset.univ k (by simpa using hk))) := by
  classical
  refine ⟨measurable_of_finite _, Measure.ext_of_singleton fun S => ?_⟩
  rw [Measure.map_apply (measurable_of_finite _) (measurableSet_singleton S)]
  by_cases hS : S.card = k
  · have he : (Subtype.val : RankSubset ι k → Finset ι) ⁻¹' {S} = {⟨S, hS⟩} := by
      ext T
      simp only [Set.mem_preimage, Set.mem_singleton_iff, Subtype.ext_iff]
    rw [he, lawMeasure_singleton, lawMeasure_singleton]
    exact congrArg ENNReal.ofReal (restrictedMass_univ_rankSubset w k ⟨S, hS⟩).symm
  · have he : (Subtype.val : RankSubset ι k → Finset ι) ⁻¹' {S} = ∅ := by
      ext T
      simp only [Set.mem_preimage, Set.mem_singleton_iff, Set.mem_empty_iff_false,
        iff_false]
      intro h
      exact hS (h ▸ T.property)
    rw [he, measure_empty, lawMeasure_singleton]
    simp [restrictedLaw, restrictedMass, Finset.mem_powersetCard, hS]

theorem integral_restrictedLaw_univ (w : ι → ℝ) (hw : ∀ i, 0 < w i)
    (k : ℕ) (hk : k ≤ Fintype.card ι) (f : Finset ι → ℝ) :
    (∫ S, f S ∂lawMeasure (restrictedLaw w hw Finset.univ k (by simpa using hk))) =
      ∫ S : RankSubset ι k, f S.val ∂lawMeasure (externalFieldLaw w hw hk) := by
  have h := externalFieldLaw_val_measurePreserving w hw k hk
  rw [← h.map_eq]
  exact integral_map h.measurable.aemeasurable (measurable_of_finite _).aestronglyMeasurable

/-- Exact external-field law for the concrete common-seed sampler. -/
theorem sequentialSampler_map_externalFieldLaw {n : ℕ} (w : Fin n → ℝ)
    (hw : ∀ i, 0 < w i) (k : ℕ) (hk : k ≤ n) :
    (seedMeasure n).map (sequentialSampler w k) =
      (lawMeasure (externalFieldLaw w hw (by simpa using hk))).map
        (Subtype.val : RankSubset (Fin n) k → Finset (Fin n)) := by
  rw [(sequentialSampler_measurePreserving w hw k hk).map_eq,
    (externalFieldLaw_val_measurePreserving w hw k (by simpa using hk)).map_eq]

end
end CoefficientOne.Sampling
