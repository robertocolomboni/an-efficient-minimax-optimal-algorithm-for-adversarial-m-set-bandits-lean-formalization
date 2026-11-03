import MsetsLower.Lower.Dense.Assouad
import Mathlib.InformationTheory.KullbackLeibler.Basic

/-! The measure-theoretic notation at definitive manuscript lines 3565--3585.
These are autonomous notation interfaces, not new premises of the lower bound.
The active feedback argument uses its proved common-support density formulas.
-/

namespace MsetsPaper.Alignment.LowerNotations

open MeasureTheory Set MsetsLower.Probability MsetsLower.Lower.Dense
open scoped ENNReal

noncomputable section

variable {Ω : Type*} [MeasurableSpace Ω]

/-- The project's Jordan normalization is exactly the paper's supremum over events. -/
theorem totalVariation_eq_sup_events (P Q : Measure Ω)
    [IsProbabilityMeasure P] [IsProbabilityMeasure Q] :
    totalVariationDistance P Q =
      sSup {r : ℝ | ∃ E : Set Ω, MeasurableSet E ∧ r = |P.real E - Q.real E|} := by
  let S : Set ℝ := {r | ∃ E : Set Ω, MeasurableSet E ∧ r = |P.real E - Q.real E|}
  have hbound : ∀ r ∈ S, r ≤ totalVariationDistance P Q := by
    rintro r ⟨E, hE, rfl⟩
    exact abs_eventProbability_sub_le_totalVariationDistance P Q hE
  have hnonempty : S.Nonempty := ⟨0, ∅, MeasurableSet.empty, by simp⟩
  have hbounded : BddAbove S := ⟨totalVariationDistance P Q, hbound⟩
  obtain ⟨E, hE, heq⟩ := exists_event_totalVariationDistance_eq P Q
  apply le_antisymm
  · apply le_csSup hbounded
    refine ⟨E, hE, ?_⟩
    rw [← heq, abs_of_nonneg (totalVariationDistance_nonneg P Q)]
  · exact csSup_le hnonempty hbound

open scoped Classical in
/-- Nonnegative extended integral gives the general chi-square definition,
including an infinite value when absolute continuity fails. -/
def chiSquared (Q P : Measure Ω) : ℝ≥0∞ :=
  if Q ≪ P then ∫⁻ x, ENNReal.ofReal (((Q.rnDeriv P x).toReal - 1) ^ 2) ∂P else ∞

theorem chiSquared_of_ac (Q P : Measure Ω) (h : Q ≪ P) :
    chiSquared Q P = ∫⁻ x, ENNReal.ofReal (((Q.rnDeriv P x).toReal - 1) ^ 2) ∂P := by
  simp [chiSquared, h]

theorem chiSquared_of_not_ac (Q P : Measure Ω) (h : ¬ Q ≪ P) :
    chiSquared Q P = ∞ := by
  simp [chiSquared, h]

/-- For probability laws the native KL correction for total masses cancels. -/
theorem klDiv_eq_integral_logLikelihood (Q P : Measure Ω)
    [IsProbabilityMeasure Q] [IsProbabilityMeasure P]
    (h : Q ≪ P) (hi : Integrable (llr Q P) Q) :
    InformationTheory.klDiv Q P = ENNReal.ofReal (∫ x, llr Q P x ∂Q) := by
  rw [InformationTheory.klDiv_of_ac_of_integrable h hi]
  simp

end
end MsetsPaper.Alignment.LowerNotations
