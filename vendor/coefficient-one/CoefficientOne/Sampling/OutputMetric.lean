import CoefficientOne.Sampling.FiniteLawMeasure
import Mathlib

/-!
# Expected symmetric-difference distance

This is the pseudometric on actual measurable output functions used before
passing to the almost-everywhere quotient in the manuscript.
-/

open MeasureTheory

namespace CoefficientOne.Sampling

noncomputable section

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

theorem outputDistance_nonneg (S T : Finset ι) : 0 ≤ outputDistance S T := by
  unfold outputDistance
  positivity

@[simp] theorem outputDistance_self (S : Finset ι) : outputDistance S S = 0 := by
  simp [outputDistance]

theorem outputDistance_comm (S T : Finset ι) : outputDistance S T = outputDistance T S := by
  simp only [outputDistance, symmDiff_comm S T]

@[simp] theorem outputDistance_eq_zero (S T : Finset ι) : outputDistance S T = 0 ↔ S = T := by
  simp [outputDistance]

theorem outputDistance_le_card (S T : Finset ι) : outputDistance S T ≤ Fintype.card ι := by
  unfold outputDistance
  exact_mod_cast Finset.card_le_univ (symmDiff S T)

theorem outputDistance_triangle (S T U : Finset ι) :
    outputDistance S U ≤ outputDistance S T + outputDistance T U := by
  have hs : symmDiff S U ⊆ symmDiff S T ∪ symmDiff T U := by
    intro i
    simp only [Finset.mem_symmDiff, Finset.mem_union]
    tauto
  have hc := (Finset.card_le_card hs).trans (Finset.card_union_le _ _)
  unfold outputDistance
  exact_mod_cast hc

variable {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) [IsFiniteMeasure μ]

theorem measurable_outputDistance_pair :
    Measurable (fun p : Finset ι × Finset ι => outputDistance p.1 p.2) :=
  measurable_of_finite _

theorem measurable_outputDistance {F G : Ω → Finset ι} (hF : Measurable F) (hG : Measurable G) :
    Measurable (fun ω => outputDistance (F ω) (G ω)) :=
  fun _ hs => (hF.prodMk hG) (measurable_outputDistance_pair hs)

theorem integrable_outputDistance {F G : Ω → Finset ι} (hF : Measurable F) (hG : Measurable G) :
    Integrable (fun ω => outputDistance (F ω) (G ω)) μ := by
  apply Integrable.mono' (integrable_const (Fintype.card ι : ℝ))
    (measurable_outputDistance hF hG).aestronglyMeasurable
  exact Filter.Eventually.of_forall fun ω => by
    rw [Real.norm_eq_abs, abs_of_nonneg (outputDistance_nonneg _ _)]
    exact outputDistance_le_card _ _

def expectedOutputDistance (F G : Ω → Finset ι) : ℝ :=
  ∫ ω, outputDistance (F ω) (G ω) ∂μ

theorem expectedOutputDistance_nonneg (F G : Ω → Finset ι) :
    0 ≤ expectedOutputDistance μ F G :=
  integral_nonneg (fun _ => outputDistance_nonneg _ _)

@[simp] theorem expectedOutputDistance_self (F : Ω → Finset ι) :
    expectedOutputDistance μ F F = 0 := by
  simp [expectedOutputDistance]

theorem expectedOutputDistance_comm (F G : Ω → Finset ι) :
    expectedOutputDistance μ F G = expectedOutputDistance μ G F := by
  simp only [expectedOutputDistance, outputDistance_comm]

theorem expectedOutputDistance_triangle {F G H : Ω → Finset ι}
    (hF : Measurable F) (hG : Measurable G) (hH : Measurable H) :
    expectedOutputDistance μ F H ≤ expectedOutputDistance μ F G + expectedOutputDistance μ G H := by
  unfold expectedOutputDistance
  rw [← integral_add (integrable_outputDistance μ hF hG) (integrable_outputDistance μ hG hH)]
  exact integral_mono (integrable_outputDistance μ hF hH)
    ((integrable_outputDistance μ hF hG).add (integrable_outputDistance μ hG hH))
    (fun _ => outputDistance_triangle _ _ _)

theorem expectedOutputDistance_eq_zero_iff {F G : Ω → Finset ι}
    (hF : Measurable F) (hG : Measurable G) :
    expectedOutputDistance μ F G = 0 ↔ F =ᵐ[μ] G := by
  rw [expectedOutputDistance,
    integral_eq_zero_iff_of_nonneg_ae (Filter.Eventually.of_forall (fun ω => outputDistance_nonneg (F ω) (G ω)))
      (integrable_outputDistance μ hF hG)]
  change (∀ᵐ ω ∂μ, outputDistance (F ω) (G ω) = 0) ↔ F =ᵐ[μ] G
  constructor
  · intro h
    exact h.mono fun ω hω => (outputDistance_eq_zero _ _).mp hω
  · intro h
    exact h.mono fun ω hω => (outputDistance_eq_zero _ _).mpr hω

end
end CoefficientOne.Sampling
