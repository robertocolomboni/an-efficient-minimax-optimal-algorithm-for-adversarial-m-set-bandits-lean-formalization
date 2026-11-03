import CoefficientOne.Sampling.FiniteLawMeasure
import Mathlib

/-! # Exact output laws from finite observables -/

open MeasureTheory

namespace CoefficientOne.Sampling
noncomputable section

variable {Y : Type*} [Fintype Y] [MeasurableSpace Y] [MeasurableSingletonClass Y]

theorem finiteMeasure_eq_of_integral (μ ν : Measure Y) [IsFiniteMeasure μ] [IsFiniteMeasure ν]
    (h : ∀ φ : Y → ℝ, (∫ y, φ y ∂μ) = ∫ y, φ y ∂ν) : μ = ν := by
  classical
  apply Measure.ext_of_singleton
  intro y
  have hh := h (({y} : Set Y).indicator (fun _ => (1 : ℝ)))
  simp only [integral_indicator_const (1 : ℝ) (measurableSet_singleton y), smul_eq_mul, mul_one] at hh
  exact (ENNReal.toReal_eq_toReal_iff' (measure_ne_top μ _) (measure_ne_top ν _)).mp hh

variable {X : Type*} [MeasurableSpace X] {Z : Type*} [Fintype Z]
  [MeasurableSpace Z] [MeasurableSingletonClass Z]

theorem sampler_map_law_of_integral (μ : Measure X) [IsFiniteMeasure μ]
    (F : X → Y) (hF : Measurable F) (p : FiniteLaw Z) (v : Z → Y)
    (hint : ∀ φ : Y → ℝ, (∫ x, φ (F x) ∂μ) = lawExpectation p (fun z => φ (v z))) :
    μ.map F = (lawMeasure p).map v := by
  apply finiteMeasure_eq_of_integral
  intro φ
  rw [integral_map hF.aemeasurable (measurable_of_finite φ).aestronglyMeasurable,
    integral_map (measurable_of_finite v).aemeasurable (measurable_of_finite φ).aestronglyMeasurable,
    integral_lawMeasure]
  exact hint φ

end
end CoefficientOne.Sampling
