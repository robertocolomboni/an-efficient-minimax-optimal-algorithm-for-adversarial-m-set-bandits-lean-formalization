import MsetsLower.Prelude
import Mathlib.MeasureTheory.Integral.Average

/-!
# Fixing an auxiliary random table

The lower-bound constructions first randomize an auxiliary table independently
of the learner's private randomization.  This module packages the exact
Tonelli/Fubini step which fixes one deterministic table without decreasing the
target event probability.
-/

namespace MsetsLower.Probability

open MeasureTheory
open scoped ENNReal

noncomputable section

/-- If an event under an independent product experiment has probability at
least `p`, then one deterministic first coordinate has section probability at
least `p`.  No discreteness assumption is made on the table space. -/
theorem exists_fixed_table
    {Ξ R : Type*} [MeasurableSpace Ξ] [MeasurableSpace R]
    (μ : Measure Ξ) (ν : Measure R)
    [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    {E : Set (Ξ × R)} (hE : MeasurableSet E) {p : ℝ≥0∞}
    (hp : p ≤ (μ.prod ν) E) :
    ∃ ξ : Ξ, p ≤ ν (Prod.mk ξ ⁻¹' E) := by
  have hfinite : (∫⁻ ξ, ν (Prod.mk ξ ⁻¹' E) ∂μ) ≠ ∞ := by
    rw [← Measure.prod_apply hE]
    exact ne_of_lt (measure_lt_top (μ.prod ν) E)
  obtain ⟨ξ, hξ⟩ := exists_lintegral_le hfinite
  exact ⟨ξ, hp.trans ((Measure.prod_apply hE).le.trans hξ)⟩

/-- The same fixing lemma with the hypothesis written as a joint probability
lower bound.  This name mirrors the paper's `lower-fixing-table` lemma. -/
theorem lower_fixing_table
    {Ξ R : Type*} [MeasurableSpace Ξ] [MeasurableSpace R]
    (μ : Measure Ξ) (ν : Measure R)
    [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    {E : Set (Ξ × R)} (hE : MeasurableSet E) {p : ℝ≥0∞}
    (hp : (μ.prod ν) E ≥ p) :
    ∃ ξ : Ξ, ν (Prod.mk ξ ⁻¹' E) ≥ p :=
  exists_fixed_table μ ν hE hp

end

end MsetsLower.Probability
