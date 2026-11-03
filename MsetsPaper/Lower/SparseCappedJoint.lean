import MsetsPaper.Lower.SparseCappedSurvivalCounts
import MsetsPaper.Lower.SparseCappedBitAveraging

/-! # The bit/history marginal of the original table experiment -/

namespace MsetsPaper.Lower.SparseCapped

open MsetsLower MeasureTheory ProbabilityTheory Set
open scoped BigOperators ENNReal ProbabilityTheory

noncomputable section

def bitsRunKernel {d m : ℕ} (P : Policy d m) (hm : 0 < m) (c : ℕ)
    (eta : ℝ) (heta : 0 ≤ eta) (hs : eta ≤ 1 / 16) (T : ℕ) :
    Kernel (Bits d) (History d m T) where
  toFun U := noiseMixture P hm c eta heta hs U T
  measurable' := measurable_of_finite _

instance bitsRunKernel_isMarkov {d m : ℕ} (P : Policy d m) (hm : 0 < m) (c : ℕ)
    (eta : ℝ) (heta : 0 ≤ eta) (hs : eta ≤ 1 / 16) (T : ℕ) :
    IsMarkovKernel (bitsRunKernel P hm c eta heta hs T) := ⟨fun U => by
      change IsProbabilityMeasure (noiseMixture P hm c eta heta hs U T)
      infer_instance⟩

def bitsHistoryLaw {d m : ℕ} (P : Policy d m) (hm : 0 < m) (c : ℕ)
    (eta : ℝ) (heta : 0 ≤ eta) (hs : eta ≤ 1 / 16) (T : ℕ) :
    Measure (Bits d × History d m T) :=
  bitsMeasure d ⊗ₘ bitsRunKernel P hm c eta heta hs T

instance bitsHistoryLaw_isProbabilityMeasure {d m : ℕ} (P : Policy d m)
    (hm : 0 < m) (c : ℕ) (eta : ℝ) (heta : 0 ≤ eta) (hs : eta ≤ 1 / 16) (T : ℕ) :
    IsProbabilityMeasure (bitsHistoryLaw P hm c eta heta hs T) := by
  unfold bitsHistoryLaw
  infer_instance

/-- Forgetting just the noise table gives the actual bit/history mixture. -/
theorem jointLaw_map_bitsHistory {d m : ℕ} (P : Policy d m) (hm : 0 < m) (c : ℕ)
    (eta : ℝ) (heta : 0 ≤ eta) (hs : eta ≤ 1 / 16) (T : ℕ) :
    (jointLaw P hm c eta heta hs T T).map
      (fun x : Table d T × History d m T => (x.1.1, x.2)) =
        bitsHistoryLaw P hm c eta heta hs T := by
  letI := parametricRunKernel_isMarkov P (tableLossProcess hm c eta heta hs T) T
  ext s hset
  have hproj : Measurable (fun x : Table d T × History d m T => (x.1.1, x.2)) := by
    fun_prop
  rw [Measure.map_apply hproj hset, jointLaw_eq_compProd,
    Measure.compProd_apply (hproj hset)]
  have hf : Measurable (fun xi : Table d T =>
      parametricRunKernel P (tableLossProcess hm c eta heta hs T) T xi
        {h | (xi.1, h) ∈ s}) :=
    Kernel.measurable_kernel_prodMk_left
      (κ := parametricRunKernel P (tableLossProcess hm c eta heta hs T) T) (hproj hset)
  change (∫⁻ xi : Table d T,
    parametricRunKernel P (tableLossProcess hm c eta heta hs T) T xi
      {h | (xi.1, h) ∈ s} ∂(bitsMeasure d).prod (DenseCommonNoise.noiseTableMeasure T)) = _
  rw [MeasureTheory.lintegral_prod _ hf.aemeasurable, bitsHistoryLaw,
    Measure.compProd_apply hset]
  apply lintegral_congr
  intro U
  change (∫⁻ Z, parametricRunKernel P (tableLossProcess hm c eta heta hs T) T (U, Z)
    {h | (U, h) ∈ s} ∂DenseCommonNoise.noiseTableMeasure T) =
      noiseMixture P hm c eta heta hs U T {h | (U, h) ∈ s}
  have hsection : MeasurableSet {h : History d m T | (U, h) ∈ s} :=
    measurable_prodMk_left hset
  rw [noiseMixture, Measure.bind_apply hsection (Kernel.aemeasurable _)]
  apply lintegral_congr
  intro Z
  rfl

theorem integral_bitsHistoryLaw {d m : ℕ} (P : Policy d m) (hm : 0 < m) (c : ℕ)
    (eta : ℝ) (heta : 0 ≤ eta) (hs : eta ≤ 1 / 16) (T : ℕ)
    (f : Bits d × History d m T → ℝ) (hf : Measurable f)
    (C : ℝ) (hC : ∀ x, |f x| ≤ C) :
    (∫ x, f x ∂bitsHistoryLaw P hm c eta heta hs T) =
      ∫ U, ∫ h, f (U, h) ∂noiseMixture P hm c eta heta hs U T ∂bitsMeasure d := by
  exact Measure.integral_compProd (Integrable.of_bound hf.aestronglyMeasurable C
    (ae_of_all _ fun x => by simpa only [Real.norm_eq_abs] using hC x))

theorem integral_joint_bitsHistory {d m : ℕ} (P : Policy d m) (hm : 0 < m) (c : ℕ)
    (eta : ℝ) (heta : 0 ≤ eta) (hs : eta ≤ 1 / 16) (T : ℕ)
    (f : Bits d × History d m T → ℝ) (hf : Measurable f) :
    (∫ x, f (x.1.1, x.2) ∂jointLaw P hm c eta heta hs T T) =
      ∫ x, f x ∂bitsHistoryLaw P hm c eta heta hs T := by
  rw [← jointLaw_map_bitsHistory]
  exact (integral_map (by fun_prop) hf.aestronglyMeasurable).symm

end

end MsetsPaper.Lower.SparseCapped
