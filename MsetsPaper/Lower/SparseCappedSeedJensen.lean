import MsetsPaper.Lower.SparseCappedBinaryAverage
import MsetsPaper.Probability.BinaryKLMixture
import MsetsPaper.Probability.PolicySeedMixtureKernel

/-! # P2: the literal Jensen chain over private seeds and the other hidden bits

The policies are first made deterministic by fixing the same master seed in
both bit environments. All probabilities and KL divergences below are those
of the actual adaptive sparse experiment, and all real integrals are proved
integrable. The unused bit coordinate in `Bits d` is integrated out harmlessly
by `Function.update`; this is the already proved conditional-prior convention.
-/

namespace MsetsPaper.Lower.SparseCapped
open MsetsLower MeasureTheory ProbabilityTheory InformationTheory Set
open MsetsPaper.Probability MsetsPaper.Probability.PolicySeed
open scoped ENNReal ProbabilityTheory BigOperators
noncomputable section

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
    fixedSeedNativeKL P hm hmd c eta heta hs T U i r ∈ Icc 0 (128 * (eta / m) ^ 2 * c) := by
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
    seededNativeKL P hm hmd c eta heta hs T i x ∈ Icc 0 (128 * (eta / m) ^ 2 * c) :=
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
    seedBitNativeAverage P hm hmd c eta heta hs T i ≤ 128 * (eta / m) ^ 2 * c := by
  have h := integral_mono (integrable_seededNativeKL P hm hmd c eta heta hs T i)
    (integrable_const (128 * (eta / m) ^ 2 * c))
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
      128 * (eta / m) ^ 2 * c := by
  have hd : (d : ℝ) ≠ 0 := by exact_mod_cast Nat.ne_of_gt (lt_of_lt_of_le hm hmd)
  calc
    _ ≤ (∑ _i : Fin d, (128 : ℝ) * (eta / m) ^ 2 * c) / (d : ℝ) :=
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
  rwa [capped_bit_budget_identity hm hmd hT] at h

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

end
end MsetsPaper.Lower.SparseCapped
