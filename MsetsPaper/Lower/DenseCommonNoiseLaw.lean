import MsetsPaper.Lower.DenseCommonNoiseScores
import MsetsLower.Feedback.Moments
import Mathlib.MeasureTheory.Constructions.Pi
import Mathlib.Probability.Distributions.Uniform
import Mathlib.Probability.Independence.Basic

/-!
# The genuine joint experiment for the common-noise dense construction

The sign coordinates are independent fair bits, the noise coordinates are iid
uniform on `[-1,1]`, and these two tables are independent. Histories are generated
by the actual policy kernel against the corresponding oblivious table section.
No regret or information inequality is assumed in these definitions.
-/

namespace MsetsPaper.Lower.DenseCommonNoise

open MsetsLower MsetsLower.Feedback MsetsLower.Lower MeasureTheory ProbabilityTheory Set
open scoped ENNReal ProbabilityTheory BigOperators

noncomputable section

/-- The uniform law on the bounded noise subtype. -/
def noiseMeasure : Measure Noise := sourceUniformMeasure.comap Subtype.val

instance noiseMeasure_isProbabilityMeasure : IsProbabilityMeasure noiseMeasure := by
  apply (MeasurableEmbedding.subtype_coe measurableSet_Icc).isProbabilityMeasure_comap
  simpa only [Subtype.range_coe] using ae_sourceUniformMeasure_mem_Icc

/-- Forgetting the subtype gives exactly the previously constructed uniform law. -/
theorem map_noiseMeasure : noiseMeasure.map (fun z : Noise => z.val) = sourceUniformMeasure := by
  rw [noiseMeasure, map_comap_subtype_coe measurableSet_Icc]
  exact Measure.restrict_eq_self_of_ae_mem ae_sourceUniformMeasure_mem_Icc

theorem integral_shape_noiseMeasure :
    ∫ z : Noise, shape z.val ∂noiseMeasure = (2 / 3 : ℝ) := by
  rw [← integral_shape_sourceUniformMeasure, ← map_noiseMeasure]
  exact (integral_map measurable_subtype_coe.aemeasurable
    measurable_shape.aestronglyMeasurable).symm

def bitMeasure : Measure Bool := Measure.uniformOfFinset Finset.univ

instance bitMeasure_isProbabilityMeasure : IsProbabilityMeasure bitMeasure := by
  constructor
  norm_num [bitMeasure, Measure.uniformOfFinset_apply]
  exact ENNReal.div_self (by norm_num) (by norm_num)

def signsMeasure (m : ℕ) : Measure (Signs m) := Measure.pi fun _ => bitMeasure

instance signsMeasure_isProbabilityMeasure (m : ℕ) : IsProbabilityMeasure (signsMeasure m) := by
  unfold signsMeasure
  infer_instance

def noiseTableMeasure (T : ℕ) : Measure (Fin T → Noise) := Measure.pi fun _ => noiseMeasure

instance noiseTableMeasure_isProbabilityMeasure (T : ℕ) :
    IsProbabilityMeasure (noiseTableMeasure T) := by
  unfold noiseTableMeasure
  infer_instance

def tableMeasure (m T : ℕ) : Measure (Table m T) :=
  (signsMeasure m).prod (noiseTableMeasure T)

instance tableMeasure_isProbabilityMeasure (m T : ℕ) : IsProbabilityMeasure (tableMeasure m T) := by
  unfold tableMeasure
  infer_instance

theorem signs_coordinates_independent (m : ℕ) :
    iIndepFun (fun i (U : Signs m) => U i) (signsMeasure m) := by
  exact iIndepFun_pi (X := fun _ => id) (fun _ => aemeasurable_id)

theorem noise_coordinates_independent (T : ℕ) :
    iIndepFun (fun t (Z : Fin T → Noise) => Z t) (noiseTableMeasure T) := by
  exact iIndepFun_pi (X := fun _ => id) (fun _ => aemeasurable_id)

theorem map_signs_coordinate {m : ℕ} (i : Fin (2 * m)) :
    (signsMeasure m).map (fun U => U i) = bitMeasure :=
  (measurePreserving_eval (fun _ : Fin (2 * m) => bitMeasure) i).map_eq

theorem map_noise_coordinate {T : ℕ} (t : Fin T) :
    (noiseTableMeasure T).map (fun Z => Z t) = noiseMeasure :=
  (measurePreserving_eval (fun _ : Fin T => noiseMeasure) t).map_eq

/-- The joint law retains both the sampled table and its actual observable history. -/
def jointLaw {d m : ℕ} (P : Policy d m) (hm : 0 < m)
    (eta : ℝ) (heta : 0 ≤ eta) (hetaSmall : eta ≤ 1 / 16) (T t : ℕ) :
    Measure (Table m T × History d m t) :=
  parametricRunWithParameterKernel P (tableLossProcess hm eta heta hetaSmall T) t ∘ₘ
    tableMeasure m T

instance jointLaw_isProbabilityMeasure {d m : ℕ} (P : Policy d m) (hm : 0 < m)
    (eta : ℝ) (heta : 0 ≤ eta) (hetaSmall : eta ≤ 1 / 16) (T t : ℕ) :
    IsProbabilityMeasure (jointLaw P hm eta heta hetaSmall T t) := by
  unfold jointLaw
  infer_instance

/-- Each conditional section is the original run law against one fixed
oblivious loss sequence, not an independently postulated history distribution. -/
theorem runKernel_at_table {d m : ℕ} (P : Policy d m) (hm : 0 < m)
    (eta : ℝ) (heta : 0 ≤ eta) (hetaSmall : eta ≤ 1 / 16)
    (T : ℕ) (xi : Table m T) (t : ℕ) :
    parametricRunKernel P (tableLossProcess hm eta heta hetaSmall T) t xi =
      runLaw P ((tableLossProcess hm eta heta hetaSmall T).at xi) t :=
  parametricRunKernel_apply P (tableLossProcess hm eta heta hetaSmall T) xi t

end

end MsetsPaper.Lower.DenseCommonNoise
