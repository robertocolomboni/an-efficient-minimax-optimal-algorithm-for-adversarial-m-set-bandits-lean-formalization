import MsetsPaper.Probability.AmbientHistoryLaw

/-! The conditional-law hypothesis is exactly the usual family of conditional
probability identities for the finitely many possible actions. -/

namespace MsetsPaper.Probability.AmbientHistory

open MeasureTheory ProbabilityTheory MsetsLower MsetsPaper.Upper
open scoped ProbabilityTheory ENNReal

noncomputable section

variable {Ω A : Type*} [MeasurableSpace Ω] [MeasurableSpace A] {d m : ℕ}

theorem conditional_sampling_iff_indicators
    (μ : Measure Ω) [IsProbabilityMeasure μ] [Nonempty (Action d m)]
    (H : Ω → A) (X : Ω → Action d m) (p : Ω → Action d m → ℝ)
    (hH : Measurable H) (hX : Measurable X)
    (hp : ∀ᵐ ω ∂μ, IsDistribution (p ω)) :
    (∀ᵐ ω ∂μ, condDistrib X H μ (H ω) = finiteAtomicMeasure (p ω) id) ↔
      ∀ a : Action d m,
        μ⟦X ⁻¹' {a} | (inferInstance : MeasurableSpace A).comap H⟧ =ᵐ[μ]
          fun ω ↦ p ω a := by
  classical
  constructor
  · intro hs a
    have hc := condDistrib_ae_eq_condExp (μ := μ) hH hX (measurableSet_singleton a)
    filter_upwards [hs, hp, hc] with ω hsω hpω hcω
    rw [← hcω, hsω, finiteAtomicMeasure_real_apply _ hpω.1 id _ (measurableSet_singleton a)]
    simp
  · intro hc
    have hs (a : Action d m) :
        (fun ω ↦ (condDistrib X H μ (H ω)).real {a}) =ᵐ[μ] fun ω ↦ p ω a :=
      (condDistrib_ae_eq_condExp hH hX (measurableSet_singleton a)).trans (hc a)
    filter_upwards [ae_all_iff.mpr hs, hp] with ω hsω hpω
    letI : IsProbabilityMeasure (finiteAtomicMeasure (p ω) id) :=
      finiteAtomicMeasure_isProbabilityMeasure _ hpω.1 id hpω.2
    apply Measure.ext_of_measureReal_singleton
    intro a
    rw [hsω a, finiteAtomicMeasure_real_apply _ hpω.1 id _ (measurableSet_singleton a)]
    simp

end
end MsetsPaper.Probability.AmbientHistory
