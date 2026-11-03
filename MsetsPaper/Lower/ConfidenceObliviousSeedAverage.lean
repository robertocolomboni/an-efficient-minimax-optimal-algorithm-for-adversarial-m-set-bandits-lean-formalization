import MsetsPaper.Lower.ConfidenceObliviousSeeded
import MsetsPaper.Lower.ConfidenceObliviousTableBridge
import MsetsPaper.Lower.ConfidenceObliviousEvents

/-! # Independent private-seed averaging before choosing the planted coordinate -/

namespace MsetsPaper.Lower.ConfidenceOblivious

open MsetsLower MsetsLower.Lower MsetsLower.Lower.Confidence MsetsPaper.Probability
open MsetsPaper.Probability.PolicySeed
open MeasureTheory ProbabilityTheory Set
open scoped ENNReal ProbabilityTheory BigOperators

noncomputable section

theorem auxiliary_parametric_mixture_eq_map {Ξ : Type*} [MeasurableSpace Ξ] {d m T : ℕ}
    (P : Policy d m) (hmd : m ≤ d) (r : Seeds T) (budget : ℝ)
    (defaultAction : MSetAction d m) (L : ParametricLossProcess Ξ d m)
    (μ : Measure Ξ) (t : ℕ) :
    parametricRunKernel (auxiliaryPolicy P hmd r budget defaultAction) L t ∘ₘ μ =
      μ.map (fun x => auxiliaryRun P hmd r budget defaultAction (L.at x) t) := by
  have hm : Measurable (fun x => auxiliaryRun P hmd r budget defaultAction (L.at x) t) :=
    (measurable_auxiliaryRun_parametric P hmd budget defaultAction L t).comp
      measurable_prodMk_left
  have hk : parametricRunKernel (auxiliaryPolicy P hmd r budget defaultAction) L t =
      Kernel.deterministic (fun x => auxiliaryRun P hmd r budget defaultAction (L.at x) t) hm := by
    ext x : 1
    rw [parametricRunKernel_apply, auxiliaryPolicy_runLaw]
    rfl
  rw [hk, Measure.deterministic_comp_eq_map]

def auxiliaryPlantedEvent {d m T : ℕ}
    (P : Policy d m) (hm : 1 ≤ m) (hmd : m ≤ d) (defaultAction : MSetAction d m)
    (Delta : ℝ) (hDelta : 0 ≤ Delta) (hsmall : (m : ℝ) * Delta ≤ 1 / 2 ^ 13)
    (i : Fin d) : Set (Seeds T × Table T) :=
  {x | auxiliaryRun P hmd x.1 (Delta * T / 8) defaultAction
    ((plantedTableLossProcess hm hmd Delta hDelta hsmall i T).at x.2) T ∈ scoreEvent hmd Delta i T}

theorem measurableSet_auxiliaryPlantedEvent {d m T : ℕ}
    (P : Policy d m) (hm : 1 ≤ m) (hmd : m ≤ d) (defaultAction : MSetAction d m)
    (Delta : ℝ) (hDelta : 0 ≤ Delta) (hsmall : (m : ℝ) * Delta ≤ 1 / 2 ^ 13) (i : Fin d) :
    MeasurableSet (auxiliaryPlantedEvent (T := T) P hm hmd defaultAction Delta hDelta hsmall i) :=
  (measurable_auxiliaryRun_parametric P hmd (Delta * T / 8) defaultAction
    (plantedTableLossProcess hm hmd Delta hDelta hsmall i T) T)
    (measurableSet_scoreEvent hmd Delta i T)

theorem auxiliaryPlantedEvent_iff_regret {d m T : ℕ}
    (P : Policy d m) (hm : 1 ≤ m) (hmd : m ≤ d) (defaultAction : MSetAction d m)
    (Delta : ℝ) (hDelta : 0 ≤ Delta) (hsmall : (m : ℝ) * Delta ≤ 1 / 2 ^ 13)
    (i : Fin d) (hi : i ∈ confidenceCandidates d m hmd) (r : Seeds T) (Z : Table T) :
    (r, Z) ∈ auxiliaryPlantedEvent P hm hmd defaultAction Delta hDelta hsmall i ↔
      Delta * T / 8 ≤ pathRegret ((plantedTableLossProcess hm hmd Delta hDelta hsmall i T).at Z) T
        (auxiliaryRun P hmd r (Delta * T / 8) defaultAction
          ((plantedTableLossProcess hm hmd Delta hDelta hsmall i T).at Z) T) := by
  letI : Nonempty (MSetAction d m) := nonempty_MSetAction hmd
  have hh := observableScore_eq_planted_regret_ae
    (auxiliaryPolicy P hmd r (Delta * T / 8) defaultAction) hm hmd Delta hDelta hsmall Z i hi T
  rw [auxiliaryPolicy_runLaw] at hh
  have heq := (ae_dirac_iff (measurableSet_eq_fun (measurable_observableScore hmd Delta i T)
    (measurable_pathRegret _ T))).1 hh
  change (Delta * T / 8 ≤ observableScore hmd Delta i T _) ↔ _
  rw [heq]

def auxiliaryPlantedProbability {d m T : ℕ}
    (P : Policy d m) (hm : 1 ≤ m) (hmd : m ≤ d) (defaultAction : MSetAction d m)
    (Delta : ℝ) (hDelta : 0 ≤ Delta) (hsmall : (m : ℝ) * Delta ≤ 1 / 2 ^ 13)
    (i : Fin d) (r : Seeds T) : ℝ :=
  (DenseCommonNoise.noiseTableMeasure T).real
    (Prod.mk r ⁻¹' auxiliaryPlantedEvent P hm hmd defaultAction Delta hDelta hsmall i)

theorem measurable_auxiliaryPlantedProbability {d m T : ℕ}
    (P : Policy d m) (hm : 1 ≤ m) (hmd : m ≤ d) (defaultAction : MSetAction d m)
    (Delta : ℝ) (hDelta : 0 ≤ Delta) (hsmall : (m : ℝ) * Delta ≤ 1 / 2 ^ 13) (i : Fin d) :
    Measurable (auxiliaryPlantedProbability (T := T) P hm hmd defaultAction Delta hDelta hsmall i) :=
  (measurable_measure_prodMk_left
    (measurableSet_auxiliaryPlantedEvent P hm hmd defaultAction Delta hDelta hsmall i)).ennreal_toReal

theorem auxiliaryPlantedProbability_mem_Icc {d m T : ℕ}
    (P : Policy d m) (hm : 1 ≤ m) (hmd : m ≤ d) (defaultAction : MSetAction d m)
    (Delta : ℝ) (hDelta : 0 ≤ Delta) (hsmall : (m : ℝ) * Delta ≤ 1 / 2 ^ 13)
    (i : Fin d) (r : Seeds T) :
    auxiliaryPlantedProbability P hm hmd defaultAction Delta hDelta hsmall i r ∈ Icc (0 : ℝ) 1 := by
  constructor
  · exact measureReal_nonneg
  · exact (measureReal_mono (subset_univ _)).trans_eq probReal_univ

theorem auxiliaryPlantedProbability_eq_mixture {d m T : ℕ}
    (P : Policy d m) (hm : 1 ≤ m) (hmd : m ≤ d) (defaultAction : MSetAction d m)
    (Delta : ℝ) (hDelta : 0 ≤ Delta) (hsmall : (m : ℝ) * Delta ≤ 1 / 2 ^ 13)
    (i : Fin d) (r : Seeds T) :
    auxiliaryPlantedProbability P hm hmd defaultAction Delta hDelta hsmall i r =
      (plantedMixture (auxiliaryPolicy P hmd r (Delta * T / 8) defaultAction)
        hm hmd Delta hDelta hsmall i T).real (scoreEvent hmd Delta i T) := by
  unfold plantedMixture
  rw [auxiliary_parametric_mixture_eq_map]
  have hmeas : Measurable (fun Z : Table T => auxiliaryRun P hmd r (Delta * T / 8) defaultAction
      ((plantedTableLossProcess hm hmd Delta hDelta hsmall i T).at Z) T) :=
    (measurable_auxiliaryRun_parametric P hmd (Delta * T / 8) defaultAction
      (plantedTableLossProcess hm hmd Delta hDelta hsmall i T) T).comp measurable_prodMk_left
  rw [measureReal_def, Measure.map_apply hmeas (measurableSet_scoreEvent hmd Delta i T)]
  rfl

theorem real_prod_event_left {Ξ Ω : Type*} [MeasurableSpace Ξ] [MeasurableSpace Ω]
    (μ : Measure Ξ) (ν : Measure Ω) [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    (E : Set (Ξ × Ω)) (hE : MeasurableSet E) :
    (μ.prod ν).real E = ∫ x, ν.real (Prod.mk x ⁻¹' E) ∂μ := by
  rw [measureReal_def, Measure.prod_apply hE]
  exact (integral_toReal (measurable_measure_prodMk_left hE).aemeasurable
    (ae_of_all _ fun _ => measure_lt_top _ _)).symm

theorem real_prod_event_right {Ξ Ω : Type*} [MeasurableSpace Ξ] [MeasurableSpace Ω]
    (μ : Measure Ξ) (ν : Measure Ω) [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    (E : Set (Ξ × Ω)) (hE : MeasurableSet E) :
    (μ.prod ν).real E = ∫ y, μ.real ((fun x => (x, y)) ⁻¹' E) ∂ν := by
  rw [measureReal_def, Measure.prod_apply_symm hE]
  exact (integral_toReal (measurable_measure_prodMk_right hE).aemeasurable
    (ae_of_all _ fun _ => measure_lt_top _ _)).symm

theorem auxiliary_seed_average_le_original_joint {d m T : ℕ}
    (P : Policy d m) (hm : 1 ≤ m) (hmd : m ≤ d) (hT : 0 < T)
    (defaultAction : MSetAction d m) (Delta : ℝ) (hDelta : 0 < Delta)
    (hsmall : (m : ℝ) * Delta ≤ 1 / 2 ^ 13)
    (i : Fin d) (hi : i ∈ confidenceCandidates d m hmd) :
    (∫ r, auxiliaryPlantedProbability P hm hmd defaultAction Delta hDelta.le hsmall i r
      ∂seedMeasure T) ≤
      (parametricRunWithParameterKernel P (plantedTableLossProcess hm hmd Delta hDelta.le hsmall i T) T
        ∘ₘ DenseCommonNoise.noiseTableMeasure T).real
        (parametricRegretEvent (plantedTableLossProcess hm hmd Delta hDelta.le hsmall i T) T
          (Delta * T / 8)) := by
  let L := plantedTableLossProcess hm hmd Delta hDelta.le hsmall i T
  let E := auxiliaryPlantedEvent (T := T) P hm hmd defaultAction Delta hDelta.le hsmall i
  have hE : MeasurableSet E := measurableSet_auxiliaryPlantedEvent P hm hmd defaultAction Delta hDelta.le hsmall i
  have hswap : (∫ r, auxiliaryPlantedProbability P hm hmd defaultAction Delta hDelta.le hsmall i r
      ∂seedMeasure T) =
      ∫ Z, (seedMeasure T).real ((fun r => (r, Z)) ⁻¹' E) ∂DenseCommonNoise.noiseTableMeasure T := by
    change (∫ r, (DenseCommonNoise.noiseTableMeasure T).real (Prod.mk r ⁻¹' E) ∂seedMeasure T) = _
    rw [← real_prod_event_left (seedMeasure T) (DenseCommonNoise.noiseTableMeasure T) E hE,
      real_prod_event_right (seedMeasure T) (DenseCommonNoise.noiseTableMeasure T) E hE]
  rw [hswap]
  let κ := parametricRunWithParameterKernel P L T
  let F := parametricRegretEvent L T (Delta * T / 8)
  have hF : MeasurableSet F := measurableSet_parametricRegretEvent L T _
  have hκ : Measurable (fun Z : Table T => (κ Z).real F) := (Kernel.measurable_coe κ hF).ennreal_toReal
  have hprob (μ : Measure (Table T × History d m T)) [IsProbabilityMeasure μ] :
      μ.real F ∈ Icc (0 : ℝ) 1 :=
    ⟨measureReal_nonneg, (measureReal_mono (subset_univ F)).trans_eq probReal_univ⟩
  have hg : Integrable (fun Z : Table T => (κ Z).real F) (DenseCommonNoise.noiseTableMeasure T) := by
    apply Integrable.of_mem_Icc 0 1 hκ.aemeasurable
    exact ae_of_all _ fun Z => hprob (κ Z)
  have hf : Integrable (fun Z => (seedMeasure T).real ((fun r => (r, Z)) ⁻¹' E))
      (DenseCommonNoise.noiseTableMeasure T) := by
    apply Integrable.of_mem_Icc 0 1 (measurable_measure_prodMk_right hE).ennreal_toReal.aemeasurable
    exact ae_of_all _ fun _ => ⟨measureReal_nonneg,
      (measureReal_mono (subset_univ _)).trans_eq probReal_univ⟩
  have hpoint (Z : Table T) :
      (seedMeasure T).real ((fun r => (r, Z)) ⁻¹' E) ≤ (κ Z).real F := by
    change _ ≤ ENNReal.toReal (parametricRunWithParameterKernel P L T Z F)
    rw [parametricRunWithParameterKernel_regretEvent_apply hmd]
    have hevent : ((fun r => (r, Z)) ⁻¹' E) =
        {r | Delta * T / 8 ≤ pathRegret (L.at Z) T
          (auxiliaryRun P hmd r (Delta * T / 8) defaultAction (L.at Z) T)} := by
      ext r
      exact auxiliaryPlantedEvent_iff_regret P hm hmd defaultAction Delta hDelta.le hsmall i hi r Z
    rw [hevent]
    exact auxiliary_seed_probability_le_original P hm hmd (Delta * T / 8)
      (by positivity) defaultAction Delta hDelta.le hsmall i hi Z
  have hmono := integral_mono hf hg hpoint
  apply hmono.trans_eq
  rw [measureReal_def, Measure.bind_apply hF (Kernel.aemeasurable κ)]
  exact integral_toReal (Kernel.measurable_coe κ hF).aemeasurable
    (ae_of_all _ fun _ => measure_lt_top _ _)

end
end MsetsPaper.Lower.ConfidenceOblivious
