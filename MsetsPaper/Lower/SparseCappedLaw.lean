import MsetsPaper.Lower.SparseCappedCounts
import MsetsPaper.Lower.DenseCommonNoiseLaw
import Mathlib.Probability.Distributions.Bernoulli

/-! # Actual independent Bernoulli/noise table and adaptive sparse run law -/

namespace MsetsPaper.Lower.SparseCapped

open MsetsLower MsetsLower.History MsetsLower.Feedback MsetsLower.Lower
open MeasureTheory ProbabilityTheory Set
open scoped BigOperators ENNReal ProbabilityTheory

noncomputable section

def bitProbability : unitInterval := ⟨1 / 256, by constructor <;> norm_num⟩

/-- A favorable bit has probability exactly 1/256, not one half. -/
def bitMeasure : Measure Bool := bernoulliMeasure true false bitProbability

instance bitMeasure_isProbabilityMeasure : IsProbabilityMeasure bitMeasure := by
  unfold bitMeasure
  infer_instance

theorem integral_bitMeasure (f : Bool → ℝ) :
    ∫ b, f b ∂bitMeasure = (1 / 256 : ℝ) * f true + (255 / 256 : ℝ) * f false := by
  rw [bitMeasure, integral_bernoulliMeasure]
  norm_num [bitProbability, smul_eq_mul]

theorem integral_bitValue : ∫ b, bitValue b ∂bitMeasure = (1 / 256 : ℝ) := by
  rw [integral_bitMeasure]
  norm_num [bitValue]

def bitsMeasure (d : ℕ) : Measure (Bits d) := Measure.pi fun _ => bitMeasure

instance bitsMeasure_isProbabilityMeasure (d : ℕ) : IsProbabilityMeasure (bitsMeasure d) := by
  unfold bitsMeasure
  infer_instance

def tableMeasure (d T : ℕ) : Measure (Table d T) :=
  (bitsMeasure d).prod (DenseCommonNoise.noiseTableMeasure T)

instance tableMeasure_isProbabilityMeasure (d T : ℕ) :
    IsProbabilityMeasure (tableMeasure d T) := by
  unfold tableMeasure
  infer_instance

theorem bits_coordinates_independent (d : ℕ) :
    iIndepFun (fun i (U : Bits d) => U i) (bitsMeasure d) := by
  exact iIndepFun_pi (X := fun _ => id) (fun _ => aemeasurable_id)

theorem map_bits_coordinate {d : ℕ} (i : Fin d) :
    (bitsMeasure d).map (fun U => U i) = bitMeasure :=
  (measurePreserving_eval (fun _ : Fin d => bitMeasure) i).map_eq

theorem integral_bit_coordinate {d : ℕ} (i : Fin d) :
    ∫ U : Bits d, bitValue (U i) ∂bitsMeasure d = (1 / 256 : ℝ) := by
  rw [← integral_bitValue, ← map_bits_coordinate i]
  exact (integral_map (measurable_pi_apply i).aemeasurable
    (measurable_of_finite bitValue).aestronglyMeasurable).symm

theorem integral_sum_bits (d : ℕ) :
    (∫ U : Bits d, ∑ i : Fin d, bitValue (U i) ∂bitsMeasure d) = (d : ℝ) / 256 := by
  rw [integral_finsetSum _ (fun _ _ => Integrable.of_finite)]
  simp only [integral_bit_coordinate, Finset.sum_const, Finset.card_univ, Fintype.card_fin,
    nsmul_eq_mul]
  ring

/-- Both the adversary table and its actual generated history are retained. -/
def jointLaw {d m : ℕ} (P : Policy d m) (hm : 0 < m) (c : ℕ)
    (eta : ℝ) (heta : 0 ≤ eta) (hs : eta ≤ 1 / 16) (T t : ℕ) :
    Measure (Table d T × History d m t) :=
  parametricRunWithParameterKernel P (tableLossProcess hm c eta heta hs T) t ∘ₘ tableMeasure d T

instance jointLaw_isProbabilityMeasure {d m : ℕ} (P : Policy d m) (hm : 0 < m) (c : ℕ)
    (eta : ℝ) (heta : 0 ≤ eta) (hs : eta ≤ 1 / 16) (T t : ℕ) :
    IsProbabilityMeasure (jointLaw P hm c eta heta hs T t) := by
  unfold jointLaw
  infer_instance

theorem runKernel_at_table {d m : ℕ} (P : Policy d m) (hm : 0 < m) (c : ℕ)
    (eta : ℝ) (heta : 0 ≤ eta) (hs : eta ≤ 1 / 16) (T : ℕ) (xi : Table d T) (t : ℕ) :
    parametricRunKernel P (tableLossProcess hm c eta heta hs T) t xi =
      runLaw P ((tableLossProcess hm c eta heta hs T).at xi) t :=
  parametricRunKernel_apply P _ xi t

theorem jointLaw_eq_compProd {d m : ℕ} (P : Policy d m) (hm : 0 < m) (c : ℕ)
    (eta : ℝ) (heta : 0 ≤ eta) (hs : eta ≤ 1 / 16) (T t : ℕ) :
    jointLaw P hm c eta heta hs T t =
      tableMeasure d T ⊗ₘ parametricRunKernel P (tableLossProcess hm c eta heta hs T) t := by
  letI := parametricRunKernel_isMarkov P (tableLossProcess hm c eta heta hs T) t
  ext s hset
  rw [jointLaw, Measure.bind_apply hset (Kernel.aemeasurable _), Measure.compProd_apply hset]
  apply lintegral_congr
  intro xi
  rw [parametricRunWithParameterKernel_apply,
    Measure.map_apply measurable_prodMk_left hset, parametricRunKernel_apply]

theorem jointLaw_map_table {d m : ℕ} (P : Policy d m) (hm : 0 < m) (c : ℕ)
    (eta : ℝ) (heta : 0 ≤ eta) (hs : eta ≤ 1 / 16) (T t : ℕ) :
    (jointLaw P hm c eta heta hs T t).map Prod.fst = tableMeasure d T := by
  letI := parametricRunKernel_isMarkov P (tableLossProcess hm c eta heta hs T) t
  rw [jointLaw_eq_compProd]
  exact Measure.fst_compProd _ _

end

end MsetsPaper.Lower.SparseCapped
