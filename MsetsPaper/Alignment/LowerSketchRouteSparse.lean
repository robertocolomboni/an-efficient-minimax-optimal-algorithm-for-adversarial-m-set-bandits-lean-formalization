import MsetsPaper.Alignment.LowerSketch
import MsetsPaper.Probability.ProductFixingBridge

/-! Autonomous coefficient-80 branch of the definitive T2 proof sketch.
All probability bounds below are rebuilt from the sketch's information bound;
the appendix lower-bound endpoints are not invoked. -/

namespace MsetsPaper.Alignment.LowerSketchRoute.Sparse
open MsetsLower MsetsLower.Feedback MsetsLower.Lower
open MsetsPaper.Lower MsetsPaper.Lower.SparseCapped
open MeasureTheory ProbabilityTheory InformationTheory Set
open MsetsPaper.Probability MsetsPaper.Probability.PolicySeed
open scoped ENNReal ProbabilityTheory BigOperators
noncomputable section

theorem section_nativeKL_le_cap {d m : ℕ}
    (P : Policy d m) (hm : 0 < m) (hmd : m ≤ d) (c : ℕ)
    (eta : ℝ) (heta : 0 ≤ eta) (hs : eta ≤ 1 / 16) (T : ℕ) (U : Bits d) (i : Fin d) :
    klDiv (noiseMixture P hm c eta heta hs (Function.update U i false) (T + 1))
      (noiseMixture P hm c eta heta hs (Function.update U i true) (T + 1)) ≤
        ENNReal.ofReal (80 * (eta / m) ^ 2 * c) := by
  simp_rw [noiseMixture_eq_observableProcess]
  exact LowerSketch.Sparse.history_KL_eighty_cap P hm hmd c heta hs U i


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


def fixedBitsLossProcess {d m : ℕ} (hm : 0 < m) (c : ℕ)
    (eta : ℝ) (heta : 0 ≤ eta) (hs : eta ≤ 1 / 16) (U : Bits d) (T : ℕ) :
    ParametricLossProcess (Fin T → Noise) d m where
  itemLoss t Z h := (tableLossProcess hm c eta heta hs T).itemLoss t (U, Z) h
  measurable_itemLoss t := (tableLossProcess hm c eta heta hs T).measurable_itemLoss t |>.comp
    ((measurable_const.prodMk measurable_fst).prodMk measurable_snd)
  action_nonneg Z t h a := (tableLossProcess hm c eta heta hs T).action_nonneg (U, Z) t h a
  action_le_one Z t h a := (tableLossProcess hm c eta heta hs T).action_le_one (U, Z) t h a

theorem fixedBitsRunKernel_eq_parametric {d m : ℕ} (P : Policy d m) (hm : 0 < m) (c : ℕ)
    (eta : ℝ) (heta : 0 ≤ eta) (hs : eta ≤ 1 / 16) (U : Bits d) (T : ℕ) :
    fixedBitsRunKernel P hm c eta heta hs U T =
      parametricRunKernel P (fixedBitsLossProcess hm c eta heta hs U T) T := by
  ext Z : 1
  rw [fixedBitsRunKernel_apply, parametricRunKernel_apply]
  rfl

theorem noiseMixture_eq_parametric {d m : ℕ} (P : Policy d m) (hm : 0 < m) (c : ℕ)
    (eta : ℝ) (heta : 0 ≤ eta) (hs : eta ≤ 1 / 16) (U : Bits d) (T : ℕ) :
    noiseMixture P hm c eta heta hs U T =
      parametricRunKernel P (fixedBitsLossProcess hm c eta heta hs U T) T ∘ₘ DenseCommonNoise.noiseTableMeasure T := by
  rw [noiseMixture, fixedBitsRunKernel_eq_parametric]

theorem measurable_fixedSeed_sectionTestProbability {d m : ℕ}
    (P : Policy d m) (hm : 0 < m) (hmd : m ≤ d) (c : ℕ)
    (eta : ℝ) (heta : 0 ≤ eta) (hs : eta ≤ 1 / 16) (T : ℕ)
    (U : Bits d) (i : Fin d) (b : Bool) :
    Measurable (fun r : Seeds (T + 1) =>
      sectionTestProbability (fixedPolicy P hmd r) hm c eta heta hs T U i b) := by
  unfold sectionTestProbability
  simp_rw [noiseMixture_eq_parametric]
  exact measurable_fixedPolicy_parametric_event P hmd _ _ _
    (measurableSet_finalSurvivalTest c T U i)

theorem fixedSeed_sectionTestProbability_average {d m : ℕ}
    (P : Policy d m) (hm : 0 < m) (hmd : m ≤ d) (c : ℕ)
    (eta : ℝ) (heta : 0 ≤ eta) (hs : eta ≤ 1 / 16) (T : ℕ)
    (U : Bits d) (i : Fin d) (b : Bool) :
    (∫ r : Seeds (T + 1),
      sectionTestProbability (fixedPolicy P hmd r) hm c eta heta hs T U i b ∂seedMeasure (T + 1)) =
        sectionTestProbability P hm c eta heta hs T U i b := by
  unfold sectionTestProbability
  simp_rw [noiseMixture_eq_parametric]
  exact fixedPolicy_parametric_event_average P hmd _ _ _
    (measurableSet_finalSurvivalTest c T U i)

def fixedSeedNativeKL {d m : ℕ}
    (P : Policy d m) (hm : 0 < m) (hmd : m ≤ d) (c : ℕ)
    (eta : ℝ) (heta : 0 ≤ eta) (hs : eta ≤ 1 / 16) (T : ℕ)
    (U : Bits d) (i : Fin d) (r : Seeds (T + 1)) : ℝ :=
    (klDiv (noiseMixture (fixedPolicy P hmd r) hm c eta heta hs (Function.update U i false) (T + 1))
      (noiseMixture (fixedPolicy P hmd r) hm c eta heta hs (Function.update U i true) (T + 1))).toReal

theorem measurable_fixedSeedNativeKL {d m : ℕ}
    (P : Policy d m) (hm : 0 < m) (hmd : m ≤ d) (c : ℕ)
    (eta : ℝ) (heta : 0 ≤ eta) (hs : eta ≤ 1 / 16) (T : ℕ)
    (U : Bits d) (i : Fin d) :
    Measurable (fixedSeedNativeKL P hm hmd c eta heta hs T U i) := by
  unfold fixedSeedNativeKL
  simp_rw [noiseMixture_eq_parametric]
  apply Measurable.ennreal_toReal
  apply measurable_fixedPolicy_mixture_klDiv
  intro r
  rw [← noiseMixture_eq_parametric (fixedPolicy P hmd r) hm c eta heta hs
      (Function.update U i false) (T + 1),
    ← noiseMixture_eq_parametric (fixedPolicy P hmd r) hm c eta heta hs
      (Function.update U i true) (T + 1)]
  exact (klDiv_ne_top_iff.mp (ne_top_of_le_ne_top ENNReal.ofReal_ne_top
    (section_nativeKL_le_cap (fixedPolicy P hmd r) hm hmd c eta heta hs T U i))).1

theorem fixedSeedNativeKL_mem_Icc {d m : ℕ}
    (P : Policy d m) (hm : 0 < m) (hmd : m ≤ d) (c : ℕ)
    (eta : ℝ) (heta : 0 ≤ eta) (hs : eta ≤ 1 / 16) (T : ℕ)
    (U : Bits d) (i : Fin d) (r : Seeds (T + 1)) :
    fixedSeedNativeKL P hm hmd c eta heta hs T U i r ∈ Icc 0 (80 * (eta / m) ^ 2 * c) := by
  exact ⟨ENNReal.toReal_nonneg, ENNReal.toReal_le_of_le_ofReal (by positivity)
    (section_nativeKL_le_cap (fixedPolicy P hmd r) hm hmd c eta heta hs T U i)⟩

def seedBitMeasure (d T : ℕ) : Measure (Bits d × Seeds (T + 1)) :=
  (bitsMeasure d).prod (seedMeasure (T + 1))

instance seedBitMeasure_isProbability (d T : ℕ) : IsProbabilityMeasure (seedBitMeasure d T) := by
  unfold seedBitMeasure
  infer_instance

section JointJensen
variable {d m : ℕ} (P : Policy d m) (hm : 0 < m) (hmd : m ≤ d) (c : ℕ)
    (eta : ℝ) (heta : 0 ≤ eta) (hs : eta ≤ 1 / 16) (T : ℕ)

def seededTestProbability (i : Fin d) (b : Bool) (x : Bits d × Seeds (T + 1)) : ℝ :=
  sectionTestProbability (fixedPolicy P hmd x.2) hm c eta heta hs T x.1 i b

def seededNativeKL (i : Fin d) (x : Bits d × Seeds (T + 1)) : ℝ :=
  fixedSeedNativeKL P hm hmd c eta heta hs T x.1 i x.2

theorem measurable_seededTestProbability (i : Fin d) (b : Bool) :
    Measurable (seededTestProbability P hm hmd c eta heta hs T i b) :=
  measurable_from_prod_countable_right fun U =>
    measurable_fixedSeed_sectionTestProbability P hm hmd c eta heta hs T U i b

theorem seededTestProbability_mem_Icc (i : Fin d) (b : Bool) (x : Bits d × Seeds (T + 1)) :
    seededTestProbability P hm hmd c eta heta hs T i b x ∈ Icc (0 : ℝ) 1 :=
  sectionTestProbability_mem_Icc (fixedPolicy P hmd x.2) hm c eta heta hs T x.1 i b

theorem integrable_seededTestProbability (i : Fin d) (b : Bool) :
    Integrable (seededTestProbability P hm hmd c eta heta hs T i b) (seedBitMeasure d T) :=
  Integrable.of_mem_Icc 0 1
    (measurable_seededTestProbability P hm hmd c eta heta hs T i b).aemeasurable
    (ae_of_all _ (seededTestProbability_mem_Icc P hm hmd c eta heta hs T i b))

/-- Literal averaging over the independent pair (other bits, private seed). -/
theorem seededTestProbability_average (i : Fin d) (b : Bool) :
    (∫ x, seededTestProbability P hm hmd c eta heta hs T i b x ∂seedBitMeasure d T) =
      conditionalTestProbability P hm c eta heta hs T i b := by
  rw [seedBitMeasure, integral_prod _ (integrable_seededTestProbability P hm hmd c eta heta hs T i b)]
  unfold seededTestProbability
  simp_rw [fixedSeed_sectionTestProbability_average P hm hmd c eta heta hs T]
  rfl

theorem measurable_seededNativeKL (i : Fin d) :
    Measurable (seededNativeKL P hm hmd c eta heta hs T i) :=
  measurable_from_prod_countable_right fun U => measurable_fixedSeedNativeKL P hm hmd c eta heta hs T U i

theorem seededNativeKL_mem_Icc (i : Fin d) (x : Bits d × Seeds (T + 1)) :
    seededNativeKL P hm hmd c eta heta hs T i x ∈ Icc 0 (80 * (eta / m) ^ 2 * c) :=
  fixedSeedNativeKL_mem_Icc P hm hmd c eta heta hs T x.1 i x.2

theorem integrable_seededNativeKL (i : Fin d) :
    Integrable (seededNativeKL P hm hmd c eta heta hs T i) (seedBitMeasure d T) :=
  Integrable.of_mem_Icc 0 _
    (measurable_seededNativeKL P hm hmd c eta heta hs T i).aemeasurable
    (ae_of_all _ (seededNativeKL_mem_Icc P hm hmd c eta heta hs T i))

theorem seeded_binaryKL_le_native (i : Fin d) (x : Bits d × Seeds (T + 1)) :
    binaryKL (seededTestProbability P hm hmd c eta heta hs T i false x)
      (seededTestProbability P hm hmd c eta heta hs T i true x) ≤
        seededNativeKL P hm hmd c eta heta hs T i x :=
  section_binaryKL_le_native (fixedPolicy P hmd x.2) hm hmd c eta heta hs T x.1 i

theorem integrable_seededBinaryKL (i : Fin d) :
    Integrable (fun x => binaryKL (seededTestProbability P hm hmd c eta heta hs T i false x)
      (seededTestProbability P hm hmd c eta heta hs T i true x)) (seedBitMeasure d T) := by
  apply (integrable_seededNativeKL P hm hmd c eta heta hs T i).mono'
    (measurable_binaryKL (measurable_seededTestProbability P hm hmd c eta heta hs T i false)
      (measurable_seededTestProbability P hm hmd c eta heta hs T i true)).aestronglyMeasurable
  exact ae_of_all _ fun x => by
    rw [Real.norm_eq_abs, abs_of_nonneg (binaryKL_nonneg
      (seededTestProbability_mem_Icc P hm hmd c eta heta hs T i false x)
      (seededTestProbability_mem_Icc P hm hmd c eta heta hs T i true x))]
    exact seeded_binaryKL_le_native P hm hmd c eta heta hs T i x

def seedBitBinaryAverage (i : Fin d) : ℝ :=
  ∫ x, binaryKL (seededTestProbability P hm hmd c eta heta hs T i false x)
    (seededTestProbability P hm hmd c eta heta hs T i true x) ∂seedBitMeasure d T

def seedBitNativeAverage (i : Fin d) : ℝ :=
  ∫ x, seededNativeKL P hm hmd c eta heta hs T i x ∂seedBitMeasure d T

/-- Second line of the displayed P2 chain: Jensen over R and U_{-i} together. -/
theorem binaryKL_conditional_le_seedBitBinaryAverage (i : Fin d) :
    binaryKL (conditionalTestProbability P hm c eta heta hs T i false)
      (conditionalTestProbability P hm c eta heta hs T i true) ≤
        seedBitBinaryAverage P hm hmd c eta heta hs T i := by
  rw [← seededTestProbability_average P hm hmd c eta heta hs T i false,
    ← seededTestProbability_average P hm hmd c eta heta hs T i true]
  exact binaryKL_integral_mixture (seedBitMeasure d T) _ _
    (measurable_seededTestProbability P hm hmd c eta heta hs T i false)
    (measurable_seededTestProbability P hm hmd c eta heta hs T i true)
    (seededTestProbability_mem_Icc P hm hmd c eta heta hs T i false)
    (seededTestProbability_mem_Icc P hm hmd c eta heta hs T i true)
    (fun x => sectionTestProbability_compatible (fixedPolicy P hmd x.2) hm hmd c eta heta hs T x.1 i)
    (integrable_seededBinaryKL P hm hmd c eta heta hs T i)

/-- Third line: data processing for the same measurable H_i, section by section. -/
theorem seedBitBinaryAverage_le_native (i : Fin d) :
    seedBitBinaryAverage P hm hmd c eta heta hs T i ≤
      seedBitNativeAverage P hm hmd c eta heta hs T i :=
  integral_mono (integrable_seededBinaryKL P hm hmd c eta heta hs T i)
    (integrable_seededNativeKL P hm hmd c eta heta hs T i)
    (seeded_binaryKL_le_native P hm hmd c eta heta hs T i)

theorem seedBitNativeAverage_le_cap (i : Fin d) :
    seedBitNativeAverage P hm hmd c eta heta hs T i ≤ 80 * (eta / m) ^ 2 * c := by
  have h := integral_mono (integrable_seededNativeKL P hm hmd c eta heta hs T i)
    (integrable_const (80 * (eta / m) ^ 2 * c))
    (fun x => (seededNativeKL_mem_Icc P hm hmd c eta heta hs T i x).2)
  simpa [seedBitNativeAverage] using h

theorem binaryKL_average_le_seedBitBinaryAverage :
    binaryKL (averageTestProbability P hm c eta heta hs T false)
      (averageTestProbability P hm c eta heta hs T true) ≤
        (∑ i : Fin d, seedBitBinaryAverage P hm hmd c eta heta hs T i) / d := by
  apply (binaryKL_average_le_conditionalAverage P hm hmd c eta heta hs T).trans
  exact div_le_div_of_nonneg_right
    (Finset.sum_le_sum fun i _ => binaryKL_conditional_le_seedBitBinaryAverage P hm hmd c eta heta hs T i)
    (Nat.cast_nonneg d)

theorem sum_seedBitBinaryAverage_le_native :
    (∑ i : Fin d, seedBitBinaryAverage P hm hmd c eta heta hs T i) / d ≤
      (∑ i : Fin d, seedBitNativeAverage P hm hmd c eta heta hs T i) / d :=
  div_le_div_of_nonneg_right
    (Finset.sum_le_sum fun i _ => seedBitBinaryAverage_le_native P hm hmd c eta heta hs T i)
    (Nat.cast_nonneg d)

theorem sum_seedBitNativeAverage_le_cap :
    (∑ i : Fin d, seedBitNativeAverage P hm hmd c eta heta hs T i) / d ≤
      80 * (eta / m) ^ 2 * c := by
  have hd : (d : ℝ) ≠ 0 := by exact_mod_cast Nat.ne_of_gt (lt_of_lt_of_le hm hmd)
  calc
    _ ≤ (∑ _i : Fin d, (80 : ℝ) * (eta / m) ^ 2 * c) / (d : ℝ) :=
      div_le_div_of_nonneg_right
        (Finset.sum_le_sum fun i _ => seedBitNativeAverage_le_cap P hm hmd c eta heta hs T i)
        (Nat.cast_nonneg d)
    _ = _ := by simp [hd]

end JointJensen

theorem sum_seedBitNativeAverage_le_log {d m T : ℕ}
    (P : Policy d m) (hm : 0 < m) (hmd : m ≤ d) (hT : 64 * d ^ 2 ≤ T + 1) :
    (∑ i : Fin d, seedBitNativeAverage P hm hmd (selectionCap d m (T + 1))
      (perturbation d m (T + 1)) (perturbation_nonneg d m (T + 1))
      (perturbation_lt_sixteenth hm hmd hT).le T i) / d ≤
        (1 / (2 : ℝ) ^ 29) * Real.log (1 / ratio d m) := by
  have h := sum_seedBitNativeAverage_le_cap P hm hmd (selectionCap d m (T + 1))
    (perturbation d m (T + 1)) (perturbation_nonneg d m (T + 1))
    (perturbation_lt_sixteenth hm hmd hT).le T
  apply h.trans
  have hnonneg : 0 ≤ (perturbation d m (T + 1) / m) ^ 2 *
      (selectionCap d m (T + 1) : ℝ) := by positivity
  calc
    _ ≤ 128 * (perturbation d m (T + 1) / m) ^ 2 *
        (selectionCap d m (T + 1) : ℝ) := by nlinarith
    _ = _ := capped_bit_budget_identity hm hmd hT

/-- The final displayed information bound, now explicitly routed through
the integrals over the fixed private-seed transcript laws. -/
theorem binaryKL_average_le_log_via_private_seeds {d m T : ℕ}
    (P : Policy d m) (hm : 0 < m) (hmd : m ≤ d) (hT : 64 * d ^ 2 ≤ T + 1) :
    binaryKL (averageTestProbability P hm (selectionCap d m (T + 1)) (perturbation d m (T + 1))
      (perturbation_nonneg d m (T + 1)) (perturbation_lt_sixteenth hm hmd hT).le T false)
      (averageTestProbability P hm (selectionCap d m (T + 1)) (perturbation d m (T + 1))
      (perturbation_nonneg d m (T + 1)) (perturbation_lt_sixteenth hm hmd hT).le T true) ≤
        (1 / (2 : ℝ) ^ 29) * Real.log (1 / ratio d m) :=
  (binaryKL_average_le_seedBitBinaryAverage P hm hmd (selectionCap d m (T + 1))
    (perturbation d m (T + 1)) (perturbation_nonneg d m (T + 1))
    (perturbation_lt_sixteenth hm hmd hT).le T).trans
    ((sum_seedBitBinaryAverage_le_native P hm hmd (selectionCap d m (T + 1))
      (perturbation d m (T + 1)) (perturbation_nonneg d m (T + 1))
      (perturbation_lt_sixteenth hm hmd hT).le T).trans
      (sum_seedBitNativeAverage_le_log P hm hmd hT))


theorem average_false_le_three_sixtyfour {d m T : ℕ}
    (P : Policy d m) (hm : 0 < m) (hmd : m ≤ d) (hT : 64 * d ^ 2 ≤ T + 1)
    (hcut : ratio d m ≤ 1 / (2 : ℝ) ^ 32) :
    averageTestProbability P hm (selectionCap d m (T + 1)) (perturbation d m (T + 1))
      (perturbation_nonneg d m (T + 1)) (perturbation_lt_sixteenth hm hmd hT).le T false ≤
      3 / 64 := by
  let c := selectionCap d m (T + 1)
  let eta := perturbation d m (T + 1)
  have he := perturbation_nonneg d m (T + 1)
  have hs := (perturbation_lt_sixteenth hm hmd hT).le
  let a := averageTestProbability P hm c eta he hs T false
  let b := averageTestProbability P hm c eta he hs T true
  have ha := averageTestProbability_mem_Icc P hm hmd c eta he hs T false
  have hb := averageTestProbability_mem_Icc P hm hmd c eta he hs T true
  have hbsmall : b ≤ 256 * ratio d m := average_true_le_ratio P hm hmd c eta he hs T
  have hcomp : BinaryCompatible a b := averageTestProbability_compatible P hm hmd c eta he hs T
  change a ≤ 3 / 64
  by_cases hzero : b = 0
  · rw [hcomp.1 hzero]
    norm_num
  have hbpos : 0 < b := lt_of_le_of_ne hb.1 (Ne.symm hzero)
  have hblt : b < 1 := by
    have hbound := mul_le_mul_of_nonneg_left hcut (by norm_num : (0 : ℝ) ≤ 256)
    norm_num at hbound
    linarith
  apply sparse_entropy_probability_le ha.1 hbpos (ratio_pos hm hmd) hcut hbsmall
  exact (binaryKL_lower_bound ha.1 ha.2 hbpos hblt).trans
    (binaryKL_average_le_log_via_private_seeds P hm hmd hT)


theorem badSurvival_probability_le {d m T : ℕ}
    (P : Policy d m) (hm : 0 < m) (hmd : m ≤ d) (hT : 64 * d ^ 2 ≤ T + 1)
    (hcut : ratio d m ≤ 1 / (2 : ℝ) ^ 32) :
    (bitsHistoryLaw P hm (selectionCap d m (T + 1)) (perturbation d m (T + 1))
      (perturbation_nonneg d m (T + 1)) (perturbation_lt_sixteenth hm hmd hT).le (T + 1)).real
      (badSurvival (selectionCap d m (T + 1)) T) ≤ 1 / 16 := by
  let c := selectionCap d m (T + 1)
  let eta := perturbation d m (T + 1)
  have he := perturbation_nonneg d m (T + 1)
  have hs := (perturbation_lt_sixteenth hm hmd hT).le
  have hcount := average_false_controls_bad P hm hmd c (selectionCap_pos hm hmd hT)
    eta he hs T (selectionCap_budget hm hmd)
  have hsmall : ratio d m ≤ 1 / 8 := hcut.trans (by norm_num)
  obtain ⟨h₁, h₂⟩ := sparse_counting_probability_le measureReal_nonneg hsmall
    (average_false_le_three_sixtyfour P hm hmd hT hcut) hcount
  exact h₁.trans h₂


theorem integral_topScore_ge_twenty_nine {d m T : ℕ}
    (P : Policy d m) (hm : 0 < m) (hmd : m ≤ d) (hT : 64 * d ^ 2 ≤ T + 1)
    (hcut : ratio d m ≤ 1 / (2 : ℝ) ^ 32) :
    (29 / 48 : ℝ) * m * (T + 1) ≤
      ∫ x, topScore m (itemScore (selectionCap d m (T + 1)) x.1 (T + 1) x.2)
        ∂jointLaw P hm (selectionCap d m (T + 1)) (perturbation d m (T + 1))
          (perturbation_nonneg d m (T + 1)) (perturbation_lt_sixteenth hm hmd hT).le
          (T + 1) (T + 1) := by
  have h := integral_topScore_ge_shape_sub_bad P hm hmd (selectionCap d m (T + 1))
    (perturbation d m (T + 1)) (perturbation_nonneg d m (T + 1))
    (perturbation_lt_sixteenth hm hmd hT).le T
  have hb := badSurvival_probability_le P hm hmd hT hcut
  have hmul := mul_le_mul_of_nonneg_left hb
    (by positivity : (0 : ℝ) ≤ m * (T + 1))
  nlinarith


theorem integral_deficit_ge_four_thirtyseven {d m T : ℕ}
    (P : Policy d m) (hm : 0 < m) (hmd : m ≤ d) (hT : 64 * d ^ 2 ≤ T + 1)
    (hcut : ratio d m ≤ 1 / (2 : ℝ) ^ 32) :
    (437 / 768 : ℝ) * m * (T + 1) ≤
      ∫ x, deficit (selectionCap d m (T + 1)) x.1 (T + 1) x.2
        ∂jointLaw P hm (selectionCap d m (T + 1)) (perturbation d m (T + 1))
          (perturbation_nonneg d m (T + 1)) (perturbation_lt_sixteenth hm hmd hT).le
          (T + 1) (T + 1) := by
  unfold deficit
  letI := jointLaw_isProbabilityMeasure P hm (selectionCap d m (T + 1))
    (perturbation d m (T + 1)) (perturbation_nonneg d m (T + 1))
    (perturbation_lt_sixteenth hm hmd hT).le (T + 1) (T + 1)
  rw [integral_sub (integrable_topScore hmd _ _) (integrable_learnerScore hmd _ _)]
  have htop := integral_topScore_ge_twenty_nine P hm hmd hT hcut
  have hlearner := integral_learnerScore_le_nine P hm hmd hT
  push_cast at hlearner
  linarith


theorem deficit_joint_tail {d m T : ℕ}
    (P : Policy d m) (hm : 0 < m) (hmd : m ≤ d) (hT : 64 * d ^ 2 ≤ T + 1)
    (hcut : ratio d m ≤ 1 / (2 : ℝ) ^ 32) :
    (1 : ℝ) / 8 ≤ (jointLaw P hm (selectionCap d m (T + 1)) (perturbation d m (T + 1))
      (perturbation_nonneg d m (T + 1)) (perturbation_lt_sixteenth hm hmd hT).le
      (T + 1) (T + 1)).real
      {x | (m : ℝ) * (T + 1) / 8 ≤ deficit (selectionCap d m (T + 1)) x.1 (T + 1) x.2} := by
  letI := jointLaw_isProbabilityMeasure P hm (selectionCap d m (T + 1))
    (perturbation d m (T + 1)) (perturbation_nonneg d m (T + 1))
    (perturbation_lt_sixteenth hm hmd hT).le (T + 1) (T + 1)
  apply MsetsPaper.Lower.deficit_tail_one_eighth _ _ (measurable_deficit _ _)
    (integrable_deficit hmd _ _)
  · positivity
  · have hmean := integral_deficit_ge_four_thirtyseven P hm hmd hT hcut
    have hmT : (0 : ℝ) ≤ m * (T + 1) := by positivity
    nlinarith
  · exact ae_of_all _ fun x => by
      simpa only [Nat.cast_add, Nat.cast_one] using deficit_le hmd _ x.1 (T + 1) x.2


theorem eta_scaled_threshold {m T : ℕ} (hm : 0 < m) (eta : ℝ) :
    eta / m * ((m : ℝ) * T / 8) = eta * T / 8 := by
  have hm0 : (m : ℝ) ≠ 0 := by exact_mod_cast Nat.ne_of_gt hm
  field_simp


theorem regret_joint_tail {d m T : ℕ}
    (P : Policy d m) (hm : 0 < m) (hmd : m ≤ d) (hT : 64 * d ^ 2 ≤ T + 1)
    (hcut : ratio d m ≤ 1 / (2 : ℝ) ^ 32) :
    (1 : ℝ) / 8 ≤ (jointLaw P hm (selectionCap d m (T + 1)) (perturbation d m (T + 1))
      (perturbation_nonneg d m (T + 1)) (perturbation_lt_sixteenth hm hmd hT).le
      (T + 1) (T + 1)).real
      (parametricRegretEvent
        (tableLossProcess hm (selectionCap d m (T + 1)) (perturbation d m (T + 1))
          (perturbation_nonneg d m (T + 1)) (perturbation_lt_sixteenth hm hmd hT).le (T + 1))
        (T + 1) ((1 / (2 : ℝ) ^ 24) *
          Real.sqrt ((d : ℝ) * (T + 1) * Real.log (d.choose m : ℝ)))) := by
  let c := selectionCap d m (T + 1)
  let eta := perturbation d m (T + 1)
  have he := perturbation_nonneg d m (T + 1)
  have hs := (perturbation_lt_sixteenth hm hmd hT).le
  let L := tableLossProcess (d := d) hm c eta he hs (T + 1)
  letI := jointLaw_isProbabilityMeasure P hm c eta he hs (T + 1) (T + 1)
  letI : Nonempty (MSetAction d m) := nonempty_MSetAction hmd
  have hpath (x : Table d (T + 1) × History d m (T + 1)) :
      parametricPathRegret L (T + 1) x = eta / m * deficit c x.1 (T + 1) x.2 := by
    rw [show x = (x.1, x.2) from rfl, parametricPathRegret_eq_at]
    exact pathRegret_eq_scaled_deficit hm hmd c eta he hs (T + 1) x.1 (T + 1) x.2
  have hcomp := sparse_threshold_comparisons hm hmd hT hcut
  have hthreshold : (1 / (2 : ℝ) ^ 24) *
      Real.sqrt ((d : ℝ) * (T + 1) * Real.log (d.choose m : ℝ)) ≤ eta * (T + 1) / 8 := by
    simpa only [Nat.cast_add, Nat.cast_one] using hcomp.2.trans hcomp.1
  have hsubset : {x : Table d (T + 1) × History d m (T + 1) |
      (m : ℝ) * (T + 1) / 8 ≤ deficit c x.1 (T + 1) x.2} ⊆
      parametricRegretEvent L (T + 1) ((1 / (2 : ℝ) ^ 24) *
        Real.sqrt ((d : ℝ) * (T + 1) * Real.log (d.choose m : ℝ))) := by
    intro x hx
    change _ ≤ parametricPathRegret L (T + 1) x
    rw [hpath]
    have hscaled := mul_le_mul_of_nonneg_left hx (div_nonneg he (Nat.cast_nonneg m))
    have heq : eta / m * ((m : ℝ) * (T + 1) / 8) = eta * (T + 1) / 8 := by
      have hm0 : (m : ℝ) ≠ 0 := by exact_mod_cast Nat.ne_of_gt hm
      field_simp
    rw [heq] at hscaled
    exact hthreshold.trans hscaled
  exact (deficit_joint_tail P hm hmd hT hcut).trans
    (ENNReal.toReal_mono (measure_ne_top _ _) (measure_mono hsubset))


theorem exists_sparse_table_successor {d m T : ℕ}
    (P : Policy d m) (hm : 0 < m) (hmd : m ≤ d) (hT : 64 * d ^ 2 ≤ T + 1)
    (hcut : ratio d m ≤ 1 / (2 : ℝ) ^ 32) :
    ∃ L : LossProcess d m,
      (∀ t (h : History d m t) i, L.itemLoss t h i ∈ Icc (0 : ℝ) (1 / m)) ∧
      (1 : ℝ) / 8 ≤ (runLaw P L (T + 1)).real
        {h | (1 / (2 : ℝ) ^ 24) *
          Real.sqrt ((d : ℝ) * (T + 1) * Real.log (d.choose m : ℝ)) ≤ pathRegret L (T + 1) h} := by
  let c := selectionCap d m (T + 1)
  let eta := perturbation d m (T + 1)
  have he := perturbation_nonneg d m (T + 1)
  have hs := (perturbation_lt_sixteenth hm hmd hT).le
  obtain ⟨xi, hxi⟩ := MsetsPaper.Probability.exists_fixed_parametric_regret_via_product hmd (tableMeasure d (T + 1)) P
    (tableLossProcess hm c eta he hs (T + 1)) (T + 1)
    ((1 / (2 : ℝ) ^ 24) * Real.sqrt ((d : ℝ) * (T + 1) * Real.log (d.choose m : ℝ)))
    ((1 : ℝ) / 8) (regret_joint_tail P hm hmd hT hcut)
  exact ⟨(tableLossProcess hm c eta he hs (T + 1)).at xi,
    tableLossProcess_item_mem_Icc hm c eta he hs (T + 1) xi, hxi⟩


theorem lower_action_count_sparse {d m T : ℕ}
    (hm : 1 ≤ m) (h2m : 2 * m ≤ d) (hT : 64 * d ^ 2 ≤ T)
    (hr : (m : ℝ) / d ≤ (2 : ℝ) ^ (-32 : ℤ)) (P : Policy d m) :
    ∃ L : LossProcess d m,
      (∀ t (h : History d m t) i, L.itemLoss t h i ∈ Icc (0 : ℝ) (1 / m)) ∧
      (1 : ℝ) / 8 ≤ (runLaw P L T).real
        {h | (2 : ℝ) ^ (-24 : ℤ) *
          Real.sqrt ((d : ℝ) * T * Real.log (d.choose m : ℝ)) ≤ pathRegret L T h} := by
  have hm0 : 0 < m := by omega
  have hmd : m ≤ d := by omega
  have hcut : ratio d m ≤ 1 / (2 : ℝ) ^ 32 := by
    norm_num [ratio] at hr ⊢
    exact hr
  cases T with
  | zero =>
      have hd : 0 < d := by omega
      exact False.elim ((not_le_of_gt (show 0 < 64 * d ^ 2 by positivity)) hT)
  | succ T =>
      have h := exists_sparse_table_successor P hm0 hmd hT hcut
      norm_num only [zpow_neg, zpow_ofNat, pow_succ, pow_zero, one_mul, Nat.cast_add,
        Nat.cast_one] at h ⊢
      exact h


end
end MsetsPaper.Alignment.LowerSketchRoute.Sparse
