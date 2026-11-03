import MsetsPaper.Lower.SparseCappedProcess
import MsetsPaper.Lower.SparseCappedParameters

/-! # Sequential information is charged to the actual capped selections -/

namespace MsetsPaper.Lower.SparseCapped

open MsetsLower MsetsLower.History MsetsLower.Feedback MsetsLower.Lower
open MeasureTheory ProbabilityTheory InformationTheory Set
open scoped ENNReal ProbabilityTheory BigOperators

noncomputable section

theorem measurable_cast_cappedCount {d m : ℕ} (c : ℕ) (i : Fin d) :
    ∀ t, Measurable (fun h : History d m t => (cappedCount c i t h : ℝ)) := by
  intro t
  induction t with
  | zero => simpa only [cappedCount, Nat.cast_zero] using
      (measurable_const : Measurable (fun _ : History d m 0 => (0 : ℝ)))
  | succ t ih =>
    simp only [cast_cappedCount_succ]
    exact (ih.comp measurable_fst).add
      (((measurable_activeIndicator c t i).comp measurable_fst).mul
        ((measurable_of_finite (selectedIndicator i)).comp measurable_snd.fst))

def activeSelectedENN {d m : ℕ} (c : ℕ) (i : Fin d) (t : ℕ)
    (ha : History d m t × MSetAction d m) : ℝ≥0∞ :=
  ENNReal.ofReal (activeIndicator c t ha.1 i * selectedIndicator i ha.2)

theorem measurable_activeSelectedENN {d m : ℕ} (c : ℕ) (i : Fin d) (t : ℕ) :
    Measurable (activeSelectedENN (m := m) c i t) :=
  (((measurable_activeIndicator c t i).comp measurable_fst).mul
    ((measurable_of_finite (selectedIndicator i)).comp measurable_snd)).ennreal_ofReal

theorem observableRoundKernel_fst {d m : ℕ} (P : Policy d m) (hm : 0 < m) (c : ℕ)
    {eta : ℝ} (heta : 0 ≤ eta) (hs : eta ≤ 1 / 16) (U : Bits d) (t : ℕ) :
    Kernel.fst (observableRoundKernel P c eta U t) = P.kernel t := by
  letI := latentFeedbackKernel_isMarkov hm c heta hs U t
  unfold observableRoundKernel
  rw [Kernel.fst_eq, ← Kernel.map_comp_right _
    DenseCommonNoise.observationShift.measurable measurable_fst]
  change Kernel.map (latentRoundKernel P c eta U t) Prod.fst = P.kernel t
  rw [← Kernel.fst_eq]
  unfold latentRoundKernel
  exact Kernel.fst_compProd _ _

theorem observable_law_succ_map_historyAction {d m : ℕ} (P : Policy d m)
    (hm : 0 < m) (c : ℕ) {eta : ℝ} (heta : 0 ≤ eta) (hs : eta ≤ 1 / 16)
    (U : Bits d) (t : ℕ) :
    ((observableProcess P hm c eta heta hs U).law (t + 1)).map
      (fun h : History d m (t + 1) => (h.1, h.2.1)) =
        (observableProcess P hm c eta heta hs U).law t ⊗ₘ P.kernel t := by
  letI := observableRoundKernel_isMarkov P hm c heta hs U t
  rw [HistoryKernelProcess.law_succ]
  change (((observableProcess P hm c eta heta hs U).law t ⊗ₘ
    observableRoundKernel P c eta U t).map (Prod.map id Prod.fst)) = _
  rw [← Measure.compProd_map measurable_fst, ← Kernel.fst_eq,
    observableRoundKernel_fst P hm c heta hs U t]

theorem lintegral_cappedCount_succ {d m : ℕ} (P : Policy d m) (hm : 0 < m) (c : ℕ)
    {eta : ℝ} (heta : 0 ≤ eta) (hs : eta ≤ 1 / 16) (U : Bits d) (i : Fin d) (t : ℕ) :
    (∫⁻ h, ENNReal.ofReal (cappedCount c i (t + 1) h : ℝ)
      ∂(observableProcess P hm c eta heta hs U).law (t + 1)) =
      (∫⁻ h, ENNReal.ofReal (cappedCount c i t h : ℝ)
        ∂(observableProcess P hm c eta heta hs U).law t) +
      ∫⁻ ha, activeSelectedENN c i t ha
        ∂((observableProcess P hm c eta heta hs U).law t ⊗ₘ P.kernel t) := by
  let F : History d m t × MSetAction d m → ℝ≥0∞ := fun ha =>
    ENNReal.ofReal (cappedCount c i t ha.1 : ℝ) + activeSelectedENN c i t ha
  have hF : Measurable F :=
    ((measurable_cast_cappedCount c i t).ennreal_ofReal.comp measurable_fst).add
      (measurable_activeSelectedENN c i t)
  have hproj : Measurable (fun h : History d m (t + 1) => (h.1, h.2.1)) := by fun_prop
  calc
    _ = ∫⁻ h, F (h.1, h.2.1)
        ∂(observableProcess P hm c eta heta hs U).law (t + 1) := by
      apply lintegral_congr
      intro h
      rw [cast_cappedCount_succ]
      exact ENNReal.ofReal_add (Nat.cast_nonneg _)
        (mul_nonneg (activeIndicator_mem_Icc c t h.1 i).1
          (selectedIndicator_mem_Icc i h.2.1).1)
    _ = ∫⁻ ha, F ha ∂(((observableProcess P hm c eta heta hs U).law (t + 1)).map
        (fun h : History d m (t + 1) => (h.1, h.2.1))) :=
      (MeasureTheory.lintegral_map hF hproj).symm
    _ = ∫⁻ ha, F ha ∂((observableProcess P hm c eta heta hs U).law t ⊗ₘ P.kernel t) := by
      rw [observable_law_succ_map_historyAction]
    _ = (∫⁻ ha, ENNReal.ofReal (cappedCount c i t ha.1 : ℝ)
        ∂((observableProcess P hm c eta heta hs U).law t ⊗ₘ P.kernel t)) +
        ∫⁻ ha, activeSelectedENN c i t ha
          ∂((observableProcess P hm c eta heta hs U).law t ⊗ₘ P.kernel t) :=
      lintegral_add_left
        ((measurable_cast_cappedCount c i t).ennreal_ofReal.comp measurable_fst) _
    _ = _ := by
      congr 1
      calc
        _ = ∫⁻ h, ∫⁻ _a, ENNReal.ofReal (cappedCount c i t h : ℝ)
            ∂P.kernel t h ∂(observableProcess P hm c eta heta hs U).law t :=
          Measure.lintegral_compProd
            ((measurable_cast_cappedCount c i t).ennreal_ofReal.comp measurable_fst)
        _ = _ := by simp

theorem lintegral_cappedCount_eq_sum {d m : ℕ} (P : Policy d m) (hm : 0 < m) (c : ℕ)
    {eta : ℝ} (heta : 0 ≤ eta) (hs : eta ≤ 1 / 16) (U : Bits d) (i : Fin d) :
    ∀ T, (∫⁻ h, ENNReal.ofReal (cappedCount c i T h : ℝ)
      ∂(observableProcess P hm c eta heta hs U).law T) =
      ∑ t ∈ Finset.range T, ∫⁻ ha, activeSelectedENN c i t ha
        ∂((observableProcess P hm c eta heta hs U).law t ⊗ₘ P.kernel t) := by
  intro T
  induction T with
  | zero => simp [cappedCount]
  | succ T ih => rw [lintegral_cappedCount_succ P hm c heta hs U i T, ih, Finset.sum_range_succ]

/-- Exact conditional KL chain followed by the expected capped selection count. -/
theorem observable_bit_KL_le_expectedCappedCount {d m T : ℕ}
    (P : Policy d m) (hm : 0 < m) (hmd : m ≤ d) (c : ℕ)
    {eta : ℝ} (heta : 0 ≤ eta) (hs : eta ≤ 1 / 16) (U : Bits d) (i : Fin d) :
    klDiv ((observableProcess P hm c eta heta hs (Function.update U i false)).law T)
      ((observableProcess P hm c eta heta hs (Function.update U i true)).law T) ≤
      ENNReal.ofReal (128 * (eta / m) ^ 2) *
        ENNReal.ofReal (∫ h, (cappedCount c i T h : ℝ)
          ∂(observableProcess P hm c eta heta hs (Function.update U i false)).law T) := by
  let K := observableProcess P hm c eta heta hs (Function.update U i false)
  let L := observableProcess P hm c eta heta hs (Function.update U i true)
  let coeff := ENNReal.ofReal (128 * (eta / m) ^ 2)
  have hr (t : ℕ) : K.roundKL L t ≤
      coeff * ∫⁻ ha, activeSelectedENN c i t ha ∂(K.law t ⊗ₘ P.kernel t) := by
    apply (observable_roundKL_bit_le_indicator P hm c heta hs U i t).trans_eq
    calc
      _ = ∫⁻ ha, coeff * activeSelectedENN c i t ha ∂(K.law t ⊗ₘ P.kernel t) := by
        apply lintegral_congr
        intro ha
        rw [show 128 * (eta / m) ^ 2 * activeIndicator c t ha.1 i * selectedIndicator i ha.2 =
          (128 * (eta / m) ^ 2) * (activeIndicator c t ha.1 i * selectedIndicator i ha.2) by ring]
        exact ENNReal.ofReal_mul (by positivity)
      _ = _ := lintegral_const_mul coeff (measurable_activeSelectedENN c i t)
  change klDiv (K.law T) (L.law T) ≤ _
  rw [K.klDiv_law_eq_sum_roundKL L T]
  calc
    _ ≤ ∑ t ∈ Finset.range T, coeff * ∫⁻ ha, activeSelectedENN c i t ha
        ∂(K.law t ⊗ₘ P.kernel t) := Finset.sum_le_sum fun t _ => hr t
    _ = coeff * ∫⁻ h, ENNReal.ofReal (cappedCount c i T h : ℝ) ∂K.law T := by
      rw [← Finset.mul_sum]
      congr 1
      exact (lintegral_cappedCount_eq_sum P hm c heta hs _ i T).symm
    _ = _ := by
      congr 1
      symm
      apply ofReal_integral_eq_lintegral_ofReal
      · exact Integrable.of_mem_Icc 0 (c : ℝ) (measurable_cast_cappedCount c i T).aemeasurable
          (ae_of_all _ fun h => ⟨Nat.cast_nonneg _, by
            exact_mod_cast cappedCount_le_cap hmd c i T h⟩)
      · exact ae_of_all _ fun h => Nat.cast_nonneg _

theorem observable_bit_KL_le_cap {d m T : ℕ}
    (P : Policy d m) (hm : 0 < m) (hmd : m ≤ d) (c : ℕ)
    {eta : ℝ} (heta : 0 ≤ eta) (hs : eta ≤ 1 / 16) (U : Bits d) (i : Fin d) :
    klDiv ((observableProcess P hm c eta heta hs (Function.update U i false)).law T)
      ((observableProcess P hm c eta heta hs (Function.update U i true)).law T) ≤
      ENNReal.ofReal (128 * (eta / m) ^ 2 * c) := by
  apply (observable_bit_KL_le_expectedCappedCount P hm hmd c heta hs U i).trans
  rw [ENNReal.ofReal_mul (by positivity : (0 : ℝ) ≤ 128 * (eta / m) ^ 2)]
  apply mul_le_mul_right
  apply ENNReal.ofReal_le_ofReal
  calc
    _ ≤ ∫ _h : History d m T, (c : ℝ)
        ∂(observableProcess P hm c eta heta hs (Function.update U i false)).law T := by
      apply integral_mono
      · exact Integrable.of_mem_Icc 0 (c : ℝ) (measurable_cast_cappedCount c i T).aemeasurable
          (ae_of_all _ fun h => ⟨Nat.cast_nonneg _, by
            exact_mod_cast cappedCount_le_cap hmd c i T h⟩)
      · exact integrable_const _
      · intro h
        dsimp only
        exact_mod_cast cappedCount_le_cap hmd c i T h
    _ = (c : ℝ) := by simp

end

end MsetsPaper.Lower.SparseCapped
