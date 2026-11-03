import MsetsPaper.Lower.DenseCommonNoiseProcess
import MsetsLower.Core.HistoryStats

/-! # The exact selection-count form of the dense information budget

This supplies the intermediate inequality `KL(P+ || P-) ≤ 128(2η/m)² E+N_i`
explicitly used in the manuscript, before the coarse bound `N_i ≤ T`.
-/

namespace MsetsPaper.Lower.DenseCommonNoise

open MsetsLower MsetsLower.Feedback MsetsLower.Lower MeasureTheory ProbabilityTheory InformationTheory Set
open scoped ENNReal ProbabilityTheory BigOperators

noncomputable section

theorem observableRoundKernel_fst {d m : ℕ} (P : Policy d m) (hm : 0 < m)
    {eta : ℝ} (heta : 0 ≤ eta) (hs : eta ≤ 1 / 16)
    (U : Fin d → ℝ) (hU : ∀ i, |U i| ≤ 1) (t : ℕ) :
    Kernel.fst (observableRoundKernel P eta U t) = P.kernel t := by
  letI := latentFeedbackKernel_isMarkov hm heta hs U hU t
  unfold observableRoundKernel
  rw [Kernel.fst_eq, ← Kernel.map_comp_right _ observationShift.measurable measurable_fst]
  change Kernel.map (latentRoundKernel P eta U t) Prod.fst = P.kernel t
  rw [← Kernel.fst_eq]
  unfold latentRoundKernel
  exact Kernel.fst_compProd _ _

theorem observable_law_succ_map_historyAction {d m : ℕ} (P : Policy d m) (hm : 0 < m)
    {eta : ℝ} (heta : 0 ≤ eta) (hs : eta ≤ 1 / 16)
    (U : Fin d → ℝ) (hU : ∀ i, |U i| ≤ 1) (t : ℕ) :
    ((observableProcess P hm eta heta hs U hU).law (t + 1)).map
      (fun h : History d m (t + 1) => (h.1, h.2.1)) =
        (observableProcess P hm eta heta hs U hU).law t ⊗ₘ P.kernel t := by
  letI := observableRoundKernel_isMarkov P hm heta hs U hU t
  rw [HistoryKernelProcess.law_succ]
  change (((observableProcess P hm eta heta hs U hU).law t ⊗ₘ
    observableRoundKernel P eta U t).map (Prod.map id Prod.fst)) = _
  rw [← Measure.compProd_map measurable_fst, ← Kernel.fst_eq,
    observableRoundKernel_fst P hm heta hs U hU]

def selectedENN {d m : ℕ} (i : Fin d) (a : MSetAction d m) : ℝ≥0∞ :=
  ENNReal.ofReal (History.selectedIndicator i a)

theorem lintegral_selectedCount_succ {d m : ℕ} (P : Policy d m) (hm : 0 < m)
    {eta : ℝ} (heta : 0 ≤ eta) (hs : eta ≤ 1 / 16)
    (U : Fin d → ℝ) (hU : ∀ j, |U j| ≤ 1) (i : Fin d) (t : ℕ) :
    (∫⁻ h, ENNReal.ofReal (History.selectedCount i (t + 1) h)
      ∂(observableProcess P hm eta heta hs U hU).law (t + 1)) =
      (∫⁻ h, ENNReal.ofReal (History.selectedCount i t h)
        ∂(observableProcess P hm eta heta hs U hU).law t) +
      ∫⁻ ha, selectedENN i ha.2
        ∂((observableProcess P hm eta heta hs U hU).law t ⊗ₘ P.kernel t) := by
  let F : History d m t × MSetAction d m → ℝ≥0∞ := fun ha =>
    ENNReal.ofReal (History.selectedCount i t ha.1) + selectedENN i ha.2
  have hF : Measurable F :=
    ((History.measurable_selectedCount (m := m) i t).ennreal_ofReal.comp measurable_fst).add
      ((measurable_of_finite (selectedENN i)).comp measurable_snd)
  have hproj : Measurable (fun h : History d m (t + 1) => (h.1, h.2.1)) := by fun_prop
  calc
    _ = ∫⁻ h, F (h.1, h.2.1)
        ∂(observableProcess P hm eta heta hs U hU).law (t + 1) := by
      apply lintegral_congr
      intro h
      exact ENNReal.ofReal_add (History.selectedCount_mem_Icc i t h.1).1
        (History.selectedIndicator_mem_Icc i h.2.1).1
    _ = ∫⁻ ha, F ha ∂(((observableProcess P hm eta heta hs U hU).law (t + 1)).map
        (fun h : History d m (t + 1) => (h.1, h.2.1))) :=
      (MeasureTheory.lintegral_map hF hproj).symm
    _ = ∫⁻ ha, F ha ∂((observableProcess P hm eta heta hs U hU).law t ⊗ₘ P.kernel t) := by
      rw [observable_law_succ_map_historyAction]
    _ = (∫⁻ ha, ENNReal.ofReal (History.selectedCount i t ha.1)
        ∂((observableProcess P hm eta heta hs U hU).law t ⊗ₘ P.kernel t)) +
        ∫⁻ ha, selectedENN i ha.2
          ∂((observableProcess P hm eta heta hs U hU).law t ⊗ₘ P.kernel t) :=
      lintegral_add_left
        ((History.measurable_selectedCount (m := m) i t).ennreal_ofReal.comp measurable_fst) _
    _ = _ := by
      congr 1
      calc
        _ = ∫⁻ h, ∫⁻ _a, ENNReal.ofReal (History.selectedCount i t h)
            ∂P.kernel t h ∂(observableProcess P hm eta heta hs U hU).law t := by
          exact Measure.lintegral_compProd
            ((History.measurable_selectedCount (m := m) i t).ennreal_ofReal.comp measurable_fst)
        _ = _ := by simp

theorem lintegral_selectedCount_eq_sum {d m : ℕ} (P : Policy d m) (hm : 0 < m)
    {eta : ℝ} (heta : 0 ≤ eta) (hs : eta ≤ 1 / 16)
    (U : Fin d → ℝ) (hU : ∀ j, |U j| ≤ 1) (i : Fin d) :
    ∀ T : ℕ, (∫⁻ h, ENNReal.ofReal (History.selectedCount i T h)
      ∂(observableProcess P hm eta heta hs U hU).law T) =
      ∑ t ∈ Finset.range T, ∫⁻ ha, selectedENN i ha.2
        ∂((observableProcess P hm eta heta hs U hU).law t ⊗ₘ P.kernel t) := by
  intro T
  induction T with
  | zero => simp [History.selectedCount, History.actionSum]
  | succ T ih =>
      rw [lintegral_selectedCount_succ P hm heta hs U hU i T, ih, Finset.sum_range_succ]

theorem observable_flip_KL_le_expectedCount {d m T : ℕ}
    (P : Policy d m) (hm : 0 < m)
    {eta : ℝ} (heta : 0 ≤ eta) (hs : eta ≤ 1 / 16)
    (U : Fin d → ℝ) (hU : ∀ j, |U j| ≤ 1) (i : Fin d) :
    klDiv
      ((observableProcess P hm eta heta hs (Function.update U i 1)
        (update_signs_bounded U hU i (by norm_num))).law T)
      ((observableProcess P hm eta heta hs (Function.update U i (-1))
        (update_signs_bounded U hU i (by norm_num))).law T) ≤
      ENNReal.ofReal (128 * (2 * eta / m) ^ 2) *
        ENNReal.ofReal (∫ h, History.selectedCount i T h
          ∂(observableProcess P hm eta heta hs (Function.update U i 1)
            (update_signs_bounded U hU i (by norm_num))).law T) := by
  let K := observableProcess P hm eta heta hs (Function.update U i 1)
    (update_signs_bounded U hU i (by norm_num))
  let L := observableProcess P hm eta heta hs (Function.update U i (-1))
    (update_signs_bounded U hU i (by norm_num))
  let c := ENNReal.ofReal (128 * (2 * eta / m) ^ 2)
  have hr (t : ℕ) : K.roundKL L t ≤
      c * ∫⁻ ha, selectedENN i ha.2 ∂(K.law t ⊗ₘ P.kernel t) := by
    apply (observable_roundKL_flip_le_indicator P hm heta hs U hU i t).trans_eq
    calc
      _ = ∫⁻ ha, c * selectedENN i ha.2 ∂(K.law t ⊗ₘ P.kernel t) := by
        apply lintegral_congr
        intro ha
        simp only [selectedENN, History.selectedIndicator,
          ENNReal.ofReal_mul (by positivity : (0 : ℝ) ≤ 128 * (2 * eta / m) ^ 2)]
        rfl
      _ = _ := lintegral_const_mul c ((measurable_of_finite (selectedENN i)).comp measurable_snd)
  change klDiv (K.law T) (L.law T) ≤ _
  rw [K.klDiv_law_eq_sum_roundKL L T]
  calc
    _ ≤ ∑ t ∈ Finset.range T, c * ∫⁻ ha, selectedENN i ha.2 ∂(K.law t ⊗ₘ P.kernel t) :=
      Finset.sum_le_sum fun t _ => hr t
    _ = c * ∫⁻ h, ENNReal.ofReal (History.selectedCount i T h) ∂K.law T := by
      rw [← Finset.mul_sum]
      congr 1
      exact (lintegral_selectedCount_eq_sum P hm heta hs _ _ i T).symm
    _ = _ := by
      congr 1
      symm
      apply ofReal_integral_eq_lintegral_ofReal
      · exact Integrable.of_mem_Icc 0 (T : ℝ)
          (History.measurable_selectedCount (m := m) i T).aemeasurable
          (ae_of_all _ (History.selectedCount_mem_Icc i T))
      · exact ae_of_all _ fun h => (History.selectedCount_mem_Icc i T h).1

end

end MsetsPaper.Lower.DenseCommonNoise
