import MsetsPaper.Lower.SparseCappedSurvivalProbability
import MsetsPaper.Probability.BinaryKL

/-! # The two separate binary-KL averaging steps of P2 -/

namespace MsetsPaper.Lower.SparseCapped

open MsetsLower MeasureTheory ProbabilityTheory InformationTheory Set
open MsetsPaper.Probability
open scoped BigOperators ENNReal ProbabilityTheory

noncomputable section

theorem sum_real_singletons_eq_one {ι : Type*} [Fintype ι]
    [MeasurableSpace ι] [MeasurableSingletonClass ι]
    (μ : Measure ι) [IsProbabilityMeasure μ] : (∑ i, μ.real {i}) = 1 := by
  have h : (∫ _i : ι, (1 : ℝ) ∂μ) = 1 := by simp
  rw [integral_fintype Integrable.of_finite] at h
  simpa only [smul_eq_mul, mul_one] using h

/-- Jensen for the actual finite distribution of the other bits. -/
theorem binaryKL_integral_finite {ι : Type*} [Fintype ι]
    [MeasurableSpace ι] [MeasurableSingletonClass ι]
    (μ : Measure ι) [IsProbabilityMeasure μ] (p q : ι → ℝ)
    (hp : ∀ i, p i ∈ Icc (0 : ℝ) 1) (hq : ∀ i, q i ∈ Icc (0 : ℝ) 1)
    (hc : ∀ i, BinaryCompatible (p i) (q i)) :
    binaryKL (∫ i, p i ∂μ) (∫ i, q i ∂μ) ≤ ∫ i, binaryKL (p i) (q i) ∂μ := by
  simpa only [integral_fintype Integrable.of_finite, smul_eq_mul] using
    binaryKL_finite_mixture (fun i => μ.real {i}) p q (fun _ => measureReal_nonneg)
      (sum_real_singletons_eq_one μ) hp hq hc

theorem BinaryCompatible_integral_finite {ι : Type*} [Fintype ι]
    [MeasurableSpace ι] [MeasurableSingletonClass ι]
    (μ : Measure ι) [IsProbabilityMeasure μ] (p q : ι → ℝ)
    (hp : ∀ i, p i ∈ Icc (0 : ℝ) 1) (hq : ∀ i, q i ∈ Icc (0 : ℝ) 1)
    (hc : ∀ i, BinaryCompatible (p i) (q i)) :
    BinaryCompatible (∫ i, p i ∂μ) (∫ i, q i ∂μ) := by
  simpa only [integral_fintype Integrable.of_finite, smul_eq_mul] using
    BinaryCompatible_finite_mixture (fun i => μ.real {i}) p q (fun _ => measureReal_nonneg)
      (sum_real_singletons_eq_one μ) hp hq hc

def sectionTestProbability {d m : ℕ} (P : Policy d m) (hm : 0 < m) (c : ℕ)
    (eta : ℝ) (heta : 0 ≤ eta) (hs : eta ≤ 1 / 16) (T : ℕ)
    (U : Bits d) (i : Fin d) (b : Bool) : ℝ :=
  (noiseMixture P hm c eta heta hs (Function.update U i b) (T + 1)).real
    (finalSurvivalTest c T U i)

theorem sectionTestProbability_mem_Icc {d m : ℕ}
    (P : Policy d m) (hm : 0 < m) (c : ℕ)
    (eta : ℝ) (heta : 0 ≤ eta) (hs : eta ≤ 1 / 16) (T : ℕ)
    (U : Bits d) (i : Fin d) (b : Bool) :
    sectionTestProbability P hm c eta heta hs T U i b ∈ Icc (0 : ℝ) 1 := by
  letI := noiseMixture_isProbabilityMeasure P hm c eta heta hs
    (Function.update U i b) (T + 1)
  exact ⟨measureReal_nonneg, measureReal_le_one⟩

theorem averageTestProbability_mem_Icc {d m : ℕ}
    (P : Policy d m) (hm : 0 < m) (hmd : m ≤ d) (c : ℕ)
    (eta : ℝ) (heta : 0 ≤ eta) (hs : eta ≤ 1 / 16) (T : ℕ) (b : Bool) :
    averageTestProbability P hm c eta heta hs T b ∈ Icc (0 : ℝ) 1 := by
  have hd : (0 : ℝ) < d := by exact_mod_cast lt_of_lt_of_le hm hmd
  constructor
  · exact div_nonneg (Finset.sum_nonneg fun i _ =>
      (conditionalTestProbability_mem_Icc P hm c eta heta hs T i b).1) hd.le
  · apply (div_le_one hd).2
    calc
      _ ≤ ∑ _i : Fin d, (1 : ℝ) := Finset.sum_le_sum fun i _ =>
        (conditionalTestProbability_mem_Icc P hm c eta heta hs T i b).2
      _ = _ := by simp

theorem uniform_item_weights {d : ℕ} (hd : 0 < d) :
    (∑ _i : Fin d, (1 / (d : ℝ))) = 1 := by
  have hdR : (d : ℝ) ≠ 0 := by exact_mod_cast Nat.ne_of_gt hd
  simp [hdR]

theorem section_nativeKL_le_cap {d m : ℕ}
    (P : Policy d m) (hm : 0 < m) (hmd : m ≤ d) (c : ℕ)
    (eta : ℝ) (heta : 0 ≤ eta) (hs : eta ≤ 1 / 16) (T : ℕ) (U : Bits d) (i : Fin d) :
    klDiv (noiseMixture P hm c eta heta hs (Function.update U i false) (T + 1))
      (noiseMixture P hm c eta heta hs (Function.update U i true) (T + 1)) ≤
        ENNReal.ofReal (128 * (eta / m) ^ 2 * c) := by
  simp_rw [noiseMixture_eq_observableProcess]
  exact observable_bit_KL_le_cap P hm hmd c heta hs U i

theorem sectionTestProbability_compatible {d m : ℕ}
    (P : Policy d m) (hm : 0 < m) (hmd : m ≤ d) (c : ℕ)
    (eta : ℝ) (heta : 0 ≤ eta) (hs : eta ≤ 1 / 16) (T : ℕ) (U : Bits d) (i : Fin d) :
    BinaryCompatible (sectionTestProbability P hm c eta heta hs T U i false)
      (sectionTestProbability P hm c eta heta hs T U i true) := by
  letI := noiseMixture_isProbabilityMeasure P hm c eta heta hs
    (Function.update U i false) (T + 1)
  letI := noiseMixture_isProbabilityMeasure P hm c eta heta hs
    (Function.update U i true) (T + 1)
  have hfinite := ne_top_of_le_ne_top ENNReal.ofReal_ne_top
    (section_nativeKL_le_cap P hm hmd c eta heta hs T U i)
  exact binaryKL_event_compatible _ _ (measurableSet_finalSurvivalTest c T U i)
    (klDiv_ne_top_iff.mp hfinite).1

theorem section_binaryKL_le_native {d m : ℕ}
    (P : Policy d m) (hm : 0 < m) (hmd : m ≤ d) (c : ℕ)
    (eta : ℝ) (heta : 0 ≤ eta) (hs : eta ≤ 1 / 16) (T : ℕ) (U : Bits d) (i : Fin d) :
    binaryKL (sectionTestProbability P hm c eta heta hs T U i false)
      (sectionTestProbability P hm c eta heta hs T U i true) ≤
      (klDiv (noiseMixture P hm c eta heta hs (Function.update U i false) (T + 1))
        (noiseMixture P hm c eta heta hs (Function.update U i true) (T + 1))).toReal := by
  letI := noiseMixture_isProbabilityMeasure P hm c eta heta hs
    (Function.update U i false) (T + 1)
  letI := noiseMixture_isProbabilityMeasure P hm c eta heta hs
    (Function.update U i true) (T + 1)
  exact binaryKL_event_le_klDiv _ _ (measurableSet_finalSurvivalTest c T U i)
    (ne_top_of_le_ne_top ENNReal.ofReal_ne_top
      (section_nativeKL_le_cap P hm hmd c eta heta hs T U i))

theorem conditionalTestProbability_compatible {d m : ℕ}
    (P : Policy d m) (hm : 0 < m) (hmd : m ≤ d) (c : ℕ)
    (eta : ℝ) (heta : 0 ≤ eta) (hs : eta ≤ 1 / 16) (T : ℕ) (i : Fin d) :
    BinaryCompatible (conditionalTestProbability P hm c eta heta hs T i false)
      (conditionalTestProbability P hm c eta heta hs T i true) :=
  BinaryCompatible_integral_finite (bitsMeasure d) _ _
    (fun U => sectionTestProbability_mem_Icc P hm c eta heta hs T U i false)
    (fun U => sectionTestProbability_mem_Icc P hm c eta heta hs T U i true)
    (fun U => sectionTestProbability_compatible P hm hmd c eta heta hs T U i)

/-- Jensen over the other hidden bits, after policy randomness was already
integrated in the common conditional policy kernel. -/
theorem binaryKL_conditional_le_sectionAverage {d m : ℕ}
    (P : Policy d m) (hm : 0 < m) (hmd : m ≤ d) (c : ℕ)
    (eta : ℝ) (heta : 0 ≤ eta) (hs : eta ≤ 1 / 16) (T : ℕ) (i : Fin d) :
    binaryKL (conditionalTestProbability P hm c eta heta hs T i false)
      (conditionalTestProbability P hm c eta heta hs T i true) ≤
      ∫ U, binaryKL (sectionTestProbability P hm c eta heta hs T U i false)
        (sectionTestProbability P hm c eta heta hs T U i true) ∂bitsMeasure d :=
  binaryKL_integral_finite (bitsMeasure d) _ _
    (fun U => sectionTestProbability_mem_Icc P hm c eta heta hs T U i false)
    (fun U => sectionTestProbability_mem_Icc P hm c eta heta hs T U i true)
    (fun U => sectionTestProbability_compatible P hm hmd c eta heta hs T U i)

theorem binaryKL_conditional_le_cap {d m : ℕ}
    (P : Policy d m) (hm : 0 < m) (hmd : m ≤ d) (c : ℕ)
    (eta : ℝ) (heta : 0 ≤ eta) (hs : eta ≤ 1 / 16) (T : ℕ) (i : Fin d) :
    binaryKL (conditionalTestProbability P hm c eta heta hs T i false)
      (conditionalTestProbability P hm c eta heta hs T i true) ≤ 128 * (eta / m) ^ 2 * c := by
  apply (binaryKL_conditional_le_sectionAverage P hm hmd c eta heta hs T i).trans
  calc
    _ ≤ ∫ _U : Bits d, 128 * (eta / m) ^ 2 * c ∂bitsMeasure d := by
      apply integral_mono Integrable.of_finite (integrable_const _)
      intro U
      apply (section_binaryKL_le_native P hm hmd c eta heta hs T U i).trans
      exact ENNReal.toReal_le_of_le_ofReal (by positivity)
        (section_nativeKL_le_cap P hm hmd c eta heta hs T U i)
    _ = _ := by simp

theorem averageTestProbability_compatible {d m : ℕ}
    (P : Policy d m) (hm : 0 < m) (hmd : m ≤ d) (c : ℕ)
    (eta : ℝ) (heta : 0 ≤ eta) (hs : eta ≤ 1 / 16) (T : ℕ) :
    BinaryCompatible (averageTestProbability P hm c eta heta hs T false)
      (averageTestProbability P hm c eta heta hs T true) := by
  have h := BinaryCompatible_finite_mixture (fun _ : Fin d => 1 / (d : ℝ))
    (fun i => conditionalTestProbability P hm c eta heta hs T i false)
    (fun i => conditionalTestProbability P hm c eta heta hs T i true)
    (fun _ => by positivity) (uniform_item_weights (lt_of_lt_of_le hm hmd))
    (fun i => conditionalTestProbability_mem_Icc P hm c eta heta hs T i false)
    (fun i => conditionalTestProbability_mem_Icc P hm c eta heta hs T i true)
    (fun i => conditionalTestProbability_compatible P hm hmd c eta heta hs T i)
  simpa only [one_div, inv_mul_eq_div, ← Finset.sum_div, averageTestProbability] using h

/-- The separate Jensen step over items. -/
theorem binaryKL_average_le_conditionalAverage {d m : ℕ}
    (P : Policy d m) (hm : 0 < m) (hmd : m ≤ d) (c : ℕ)
    (eta : ℝ) (heta : 0 ≤ eta) (hs : eta ≤ 1 / 16) (T : ℕ) :
    binaryKL (averageTestProbability P hm c eta heta hs T false)
      (averageTestProbability P hm c eta heta hs T true) ≤
      (∑ i : Fin d, binaryKL (conditionalTestProbability P hm c eta heta hs T i false)
        (conditionalTestProbability P hm c eta heta hs T i true)) / d := by
  have h := binaryKL_finite_mixture (fun _ : Fin d => 1 / (d : ℝ))
    (fun i => conditionalTestProbability P hm c eta heta hs T i false)
    (fun i => conditionalTestProbability P hm c eta heta hs T i true)
    (fun _ => by positivity) (uniform_item_weights (lt_of_lt_of_le hm hmd))
    (fun i => conditionalTestProbability_mem_Icc P hm c eta heta hs T i false)
    (fun i => conditionalTestProbability_mem_Icc P hm c eta heta hs T i true)
    (fun i => conditionalTestProbability_compatible P hm hmd c eta heta hs T i)
  simpa only [one_div, inv_mul_eq_div, ← Finset.sum_div, averageTestProbability] using h

theorem binaryKL_average_le_cap {d m : ℕ}
    (P : Policy d m) (hm : 0 < m) (hmd : m ≤ d) (c : ℕ)
    (eta : ℝ) (heta : 0 ≤ eta) (hs : eta ≤ 1 / 16) (T : ℕ) :
    binaryKL (averageTestProbability P hm c eta heta hs T false)
      (averageTestProbability P hm c eta heta hs T true) ≤ 128 * (eta / m) ^ 2 * c := by
  have hd : (d : ℝ) ≠ 0 := by exact_mod_cast Nat.ne_of_gt (lt_of_lt_of_le hm hmd)
  apply (binaryKL_average_le_conditionalAverage P hm hmd c eta heta hs T).trans
  calc
    _ ≤ (∑ _i : Fin d, (128 : ℝ) * (eta / m) ^ 2 * c) / (d : ℝ) :=
      div_le_div_of_nonneg_right
        (Finset.sum_le_sum fun i _ => binaryKL_conditional_le_cap P hm hmd c eta heta hs T i)
        (Nat.cast_nonneg d)
    _ = _ := by simp [hd]

theorem binaryKL_average_le_log {d m T : ℕ}
    (P : Policy d m) (hm : 0 < m) (hmd : m ≤ d) (hT : 64 * d ^ 2 ≤ T + 1) :
    binaryKL (averageTestProbability P hm (selectionCap d m (T + 1)) (perturbation d m (T + 1))
      (perturbation_nonneg d m (T + 1)) (perturbation_lt_sixteenth hm hmd hT).le T false)
      (averageTestProbability P hm (selectionCap d m (T + 1)) (perturbation d m (T + 1))
      (perturbation_nonneg d m (T + 1)) (perturbation_lt_sixteenth hm hmd hT).le T true) ≤
        (1 / (2 : ℝ) ^ 29) * Real.log (1 / ratio d m) := by
  have h := binaryKL_average_le_cap P hm hmd (selectionCap d m (T + 1))
    (perturbation d m (T + 1)) (perturbation_nonneg d m (T + 1))
    (perturbation_lt_sixteenth hm hmd hT).le T
  rwa [capped_bit_budget_identity hm hmd hT] at h

end

end MsetsPaper.Lower.SparseCapped
