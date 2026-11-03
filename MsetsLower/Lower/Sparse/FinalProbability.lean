import MsetsLower.Lower.Sparse.FinalArithmetic
import MsetsLower.Probability.MeanToTail

/-!
# Final mean-to-event conversion for the sparse branch

This module instantiates the general bounded mean-to-tail lemma with the
literal sparse constants.  The construction-specific module only needs to
supply measurability, the proved mean lower bound, and the pathwise range of
`Gamma`.
-/

namespace MsetsLower.Lower.Sparse

open MsetsLower MeasureTheory

noncomputable section

theorem sparse_positive_event_of_mean
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    [IsProbabilityMeasure P] (Gamma : Ω → Real)
    (hGammaMeasurable : Measurable Gamma)
    (hGammaIntegrable : Integrable Gamma P)
    {k T0 : Real} (hk : 0 < k) (hT0 : 0 < T0)
    (hmean : sparseA / 4 * k * T0 ≤ ∫ ω, Gamma ω ∂P)
    (hupper : ∀ᵐ ω ∂P, Gamma ω ≤ 2 * k * T0) :
    sparseA / 16 ≤
      P.real {ω | sparseA / 8 * k * T0 ≤ Gamma ω} := by
  have ha : 0 < sparseA := by norm_num [sparseA]
  have hmu : 0 < sparseA / 4 * k * T0 := by positivity
  have htail :=
    MsetsLower.Probability.probability_ge_half_mean_of_ae_le
      P Gamma hGammaMeasurable hGammaIntegrable hmu hmean hupper
  convert htail using 1 <;> field_simp <;> ring

theorem sparse_positive_event_probability_two_neg_ten
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    [IsProbabilityMeasure P] (Gamma : Ω → Real)
    (hGammaMeasurable : Measurable Gamma)
    (hGammaIntegrable : Integrable Gamma P)
    {k T0 : Real} (hk : 0 < k) (hT0 : 0 < T0)
    (hmean : sparseA / 4 * k * T0 ≤ ∫ ω, Gamma ω ∂P)
    (hupper : ∀ᵐ ω ∂P, Gamma ω ≤ 2 * k * T0) :
    1 / (2 : Real) ^ 10 ≤
      P.real {ω | sparseA / 8 * k * T0 ≤ Gamma ω} := by
  rw [← sparse_probability_constant]
  exact sparse_positive_event_of_mean P Gamma hGammaMeasurable
    hGammaIntegrable hk hT0 hmean hupper

#print axioms sparse_positive_event_of_mean
#print axioms sparse_positive_event_probability_two_neg_ten

end

end MsetsLower.Lower.Sparse
