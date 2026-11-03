import CoefficientOne.Sampling.Coarea

/-! # Integration over finite state partitions

These identities are the finite-state instance of the Fubini/Tonelli step:
all level integrals are justified before finite sums are interchanged.
-/

open scoped BigOperators
open EffectiveResistance Matrix MeasureTheory
namespace CoefficientOne.Sampling
noncomputable section

variable {Ω α : Type*} [MeasurableSpace Ω] [Fintype α]
  [MeasurableSpace α] [MeasurableSingletonClass α]

theorem integral_eq_sum_fibers (μ : Measure Ω) (f : Ω → α) (hf : Measurable f)
    (g : Ω → ℝ) (hg : Integrable g μ) :
    (∫ ω, g ω ∂μ) = ∑ a : α, ∫ ω in f ⁻¹' {a}, g ω ∂μ := by
  classical
  have he (ω : Ω) : g ω = ∑ a : α, (f ⁻¹' {a}).indicator g ω := by
    simp [Set.indicator, eq_comm]
  conv_lhs => arg 2; ext ω; rw [he ω]
  rw [integral_finsetSum _ (fun a _ => hg.indicator (hf (measurableSet_singleton a)))]
  apply Finset.sum_congr rfl
  intro a _
  exact integral_indicator (hf (measurableSet_singleton a))

theorem integral_finite_factor (μ : Measure Ω) [IsFiniteMeasure μ]
    (f : Ω → α) (hf : Measurable f) (g : α → ℝ) :
    (∫ ω, g (f ω) ∂μ) = ∑ a : α, (μ (f ⁻¹' {a})).toReal * g a := by
  rw [← integral_map hf.aemeasurable (measurable_of_finite g).aestronglyMeasurable]
  rw [integral_fintype Integrable.of_finite]
  apply Finset.sum_congr rfl
  intro a _
  rw [measureReal_def, Measure.map_apply hf (measurableSet_singleton a)]
  rfl

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

theorem integrable_finite_state_cut (μ : Measure Ω) [IsFiniteMeasure μ]
    (f : Ω → α) (hf : Measurable f) (N : α → ConductanceNetwork ι)
    (c : α → ℝ) (a : ι → ℝ) :
    Integrable (fun s : ℝ => ∫ ω, c (f ω) *
      quadraticForm (N (f ω)).laplacian (cutVector a s) ∂μ) := by
  have he (s : ℝ) := integral_finite_factor μ f hf
    (fun z => c z * quadraticForm (N z).laplacian (cutVector a s))
  simp_rw [he]
  apply integrable_finsetSum
  intro z _
  exact ((integrable_cut_energy (N z) a).const_mul (c z)).const_mul _

theorem finite_state_coarea (μ : Measure Ω) [IsFiniteMeasure μ]
    (f : Ω → α) (hf : Measurable f) (N : α → ConductanceNetwork ι)
    (c : α → ℝ) (a : ι → ℝ) :
    (∫ ω, c (f ω) * (N (f ω)).edgeVariation a ∂μ) =
      ∫ s : ℝ, ∫ ω, c (f ω) * quadraticForm (N (f ω)).laplacian (cutVector a s) ∂μ := by
  rw [integral_finite_factor μ f hf (fun z => c z * (N z).edgeVariation a)]
  have he (s : ℝ) := integral_finite_factor μ f hf
    (fun z => c z * quadraticForm (N z).laplacian (cutVector a s))
  simp_rw [he]
  rw [integral_finsetSum _ (fun z _ =>
    ((integrable_cut_energy (N z) a).const_mul (c z)).const_mul _)]
  apply Finset.sum_congr rfl
  intro z _
  rw [integral_const_mul, integral_const_mul, ← edgeVariation_eq_integral_cut_energy]

end
end CoefficientOne.Sampling
