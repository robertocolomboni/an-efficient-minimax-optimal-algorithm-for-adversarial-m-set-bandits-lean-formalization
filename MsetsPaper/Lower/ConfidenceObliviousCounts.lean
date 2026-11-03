import MsetsPaper.Lower.ConfidenceObliviousProcess
import MsetsPaper.Lower.DenseCommonNoiseCounts

/-! # The exact expected-selection-count KL budget for the confidence laws -/

namespace MsetsPaper.Lower.ConfidenceOblivious

open MsetsLower MsetsLower.Feedback MsetsLower.Lower MsetsLower.Lower.Confidence
open MeasureTheory ProbabilityTheory InformationTheory Set
open scoped ENNReal ProbabilityTheory BigOperators

noncomputable section

theorem law_succ_map_historyAction {d m : ℕ} (P : Policy d m) (K : HistoryKernelProcess d m)
    (hfst : ∀ t, Kernel.fst (K.kernel t) = P.kernel t) (t : ℕ) :
    (K.law (t + 1)).map (fun h : History d m (t + 1) => (h.1, h.2.1)) =
      K.law t ⊗ₘ P.kernel t := by
  rw [HistoryKernelProcess.law_succ]
  change ((K.law t ⊗ₘ K.kernel t).map (Prod.map id Prod.fst)) = _
  rw [← Measure.compProd_map measurable_fst, ← Kernel.fst_eq, hfst t]

theorem lintegral_selectedCount_succ_general {d m : ℕ}
    (P : Policy d m) (K : HistoryKernelProcess d m)
    (hfst : ∀ t, Kernel.fst (K.kernel t) = P.kernel t) (i : Fin d) (t : ℕ) :
    (∫⁻ h, ENNReal.ofReal (History.selectedCount i (t + 1) h) ∂K.law (t + 1)) =
      (∫⁻ h, ENNReal.ofReal (History.selectedCount i t h) ∂K.law t) +
      ∫⁻ ha, DenseCommonNoise.selectedENN i ha.2 ∂(K.law t ⊗ₘ P.kernel t) := by
  let F : History d m t × MSetAction d m → ℝ≥0∞ := fun ha =>
    ENNReal.ofReal (History.selectedCount i t ha.1) + DenseCommonNoise.selectedENN i ha.2
  have hF : Measurable F :=
    ((History.measurable_selectedCount (m := m) i t).ennreal_ofReal.comp measurable_fst).add
      ((measurable_of_finite (DenseCommonNoise.selectedENN i)).comp measurable_snd)
  have hproj : Measurable (fun h : History d m (t + 1) => (h.1, h.2.1)) := by fun_prop
  calc
    _ = ∫⁻ h, F (h.1, h.2.1) ∂K.law (t + 1) := by
      apply lintegral_congr
      intro h
      exact ENNReal.ofReal_add (History.selectedCount_mem_Icc i t h.1).1
        (History.selectedIndicator_mem_Icc i h.2.1).1
    _ = ∫⁻ ha, F ha ∂((K.law (t + 1)).map (fun h : History d m (t + 1) => (h.1, h.2.1))) :=
      (MeasureTheory.lintegral_map hF hproj).symm
    _ = ∫⁻ ha, F ha ∂(K.law t ⊗ₘ P.kernel t) := by rw [law_succ_map_historyAction P K hfst]
    _ = (∫⁻ ha, ENNReal.ofReal (History.selectedCount i t ha.1) ∂(K.law t ⊗ₘ P.kernel t)) +
        ∫⁻ ha, DenseCommonNoise.selectedENN i ha.2 ∂(K.law t ⊗ₘ P.kernel t) :=
      lintegral_add_left
        ((History.measurable_selectedCount (m := m) i t).ennreal_ofReal.comp measurable_fst) _
    _ = _ := by
      congr 1
      calc
        _ = ∫⁻ h, ∫⁻ _a, ENNReal.ofReal (History.selectedCount i t h)
            ∂P.kernel t h ∂K.law t := by
          exact Measure.lintegral_compProd
            ((History.measurable_selectedCount (m := m) i t).ennreal_ofReal.comp measurable_fst)
        _ = _ := by simp

theorem lintegral_selectedCount_eq_sum_general {d m : ℕ}
    (P : Policy d m) (K : HistoryKernelProcess d m)
    (hfst : ∀ t, Kernel.fst (K.kernel t) = P.kernel t) (i : Fin d) :
    ∀ T : ℕ, (∫⁻ h, ENNReal.ofReal (History.selectedCount i T h) ∂K.law T) =
      ∑ t ∈ Finset.range T, ∫⁻ ha, DenseCommonNoise.selectedENN i ha.2 ∂(K.law t ⊗ₘ P.kernel t) := by
  intro T
  induction T with
  | zero => simp [History.selectedCount, History.actionSum]
  | succ T ih =>
      rw [lintegral_selectedCount_succ_general P K hfst i T, ih, Finset.sum_range_succ]

theorem reference_planted_KL_le_expectedCount {d m T : ℕ}
    (P : Policy d m) (hm : 1 ≤ m) (hmd : m ≤ d)
    (Delta : ℝ) (hDelta : 0 ≤ Delta) (hsmall : (m : ℝ) * Delta ≤ 1 / 2 ^ 13) (i : Fin d) :
    klDiv ((referenceProcess P hm hmd Delta hDelta hsmall).law T)
      ((plantedProcess P hm hmd Delta hDelta hsmall i).law T) ≤
      ENNReal.ofReal (128 * (4 * Delta) ^ 2) *
        ENNReal.ofReal (∫ h, History.selectedCount i T h
          ∂(referenceProcess P hm hmd Delta hDelta hsmall).law T) := by
  let K := referenceProcess P hm hmd Delta hDelta hsmall
  let L := plantedProcess P hm hmd Delta hDelta hsmall i
  let c := ENNReal.ofReal (128 * (4 * Delta) ^ 2)
  have hfst (t : ℕ) : Kernel.fst (K.kernel t) = P.kernel t :=
    freshRoundKernel_fst P hm hmd (feedback_scale_admissible hDelta hsmall).1
      (feedback_scale_admissible hDelta hsmall).2 (fun _ => 0) (by intro j; norm_num) t
  have hr (t : ℕ) : K.roundKL L t ≤
      c * ∫⁻ ha, DenseCommonNoise.selectedENN i ha.2 ∂(K.law t ⊗ₘ P.kernel t) := by
    apply (reference_planted_roundKL_le_indicator P hm hmd Delta hDelta hsmall i t).trans_eq
    calc
      _ = ∫⁻ ha, c * DenseCommonNoise.selectedENN i ha.2 ∂(K.law t ⊗ₘ P.kernel t) := by
        apply lintegral_congr
        intro ha
        simp only [DenseCommonNoise.selectedENN, History.selectedIndicator,
          ENNReal.ofReal_mul (by positivity : (0 : ℝ) ≤ 128 * (4 * Delta) ^ 2)]
        rfl
      _ = _ := lintegral_const_mul c
        ((measurable_of_finite (DenseCommonNoise.selectedENN i)).comp measurable_snd)
  change klDiv (K.law T) (L.law T) ≤ _
  rw [K.klDiv_law_eq_sum_roundKL L T]
  calc
    _ ≤ ∑ t ∈ Finset.range T, c * ∫⁻ ha, DenseCommonNoise.selectedENN i ha.2
        ∂(K.law t ⊗ₘ P.kernel t) := Finset.sum_le_sum fun t _ => hr t
    _ = c * ∫⁻ h, ENNReal.ofReal (History.selectedCount i T h) ∂K.law T := by
      rw [← Finset.mul_sum]
      congr 1
      exact (lintegral_selectedCount_eq_sum_general P K hfst i T).symm
    _ = _ := by
      congr 1
      symm
      apply ofReal_integral_eq_lintegral_ofReal
      · exact Integrable.of_mem_Icc 0 (T : ℝ)
          (History.measurable_selectedCount (m := m) i T).aemeasurable
          (ae_of_all _ (History.selectedCount_mem_Icc i T))
      · exact ae_of_all _ fun h => (History.selectedCount_mem_Icc i T h).1

theorem sum_selectedIndicator_candidates {d m : ℕ} (hmd : m ≤ d) (a : MSetAction d m) :
    (∑ i ∈ confidenceCandidates d m hmd, History.selectedIndicator i a) =
      (candidateCount hmd a : ℝ) := by
  classical
  simp only [History.selectedIndicator, Finset.sum_boole]
  congr 1
  unfold candidateCount
  congr 1
  ext i
  simp [and_comm]

theorem sum_selectedCount_candidates {d m : ℕ} (hmd : m ≤ d) :
    ∀ t (h : History d m t), (∑ i ∈ confidenceCandidates d m hmd, History.selectedCount i t h) =
      History.actionSum (fun a => (candidateCount hmd a : ℝ)) t h := by
  intro t
  induction t with
  | zero => intro h; simp [History.selectedCount, History.actionSum]
  | succ t ih =>
      intro h
      simp only [History.selectedCount, History.actionSum_succ, Finset.sum_add_distrib]
      rw [show (∑ i ∈ confidenceCandidates d m hmd,
        History.actionSum (History.selectedIndicator i) t h.1) =
        History.actionSum (fun a => (candidateCount hmd a : ℝ)) t h.1 from ih h.1,
        sum_selectedIndicator_candidates]

theorem reference_planted_KL_finite {d m T : ℕ}
    (P : Policy d m) (hm : 1 ≤ m) (hmd : m ≤ d)
    (Delta : ℝ) (hDelta : 0 ≤ Delta) (hsmall : (m : ℝ) * Delta ≤ 1 / 2 ^ 13) (i : Fin d) :
    klDiv ((referenceProcess P hm hmd Delta hDelta hsmall).law T)
      ((plantedProcess P hm hmd Delta hDelta hsmall i).law T) ≠ ∞ := by
  exact ne_of_lt (lt_of_le_of_lt (reference_planted_KL_le_expectedCount P hm hmd Delta hDelta hsmall i)
    (ENNReal.mul_lt_top ENNReal.ofReal_lt_top ENNReal.ofReal_lt_top))

theorem reference_planted_KL_toReal_le {d m T : ℕ}
    (P : Policy d m) (hm : 1 ≤ m) (hmd : m ≤ d)
    (Delta : ℝ) (hDelta : 0 ≤ Delta) (hsmall : (m : ℝ) * Delta ≤ 1 / 2 ^ 13) (i : Fin d) :
    (klDiv ((referenceProcess P hm hmd Delta hDelta hsmall).law T)
      ((plantedProcess P hm hmd Delta hDelta hsmall i).law T)).toReal ≤
      128 * (4 * Delta) ^ 2 * (∫ h, History.selectedCount i T h
        ∂(referenceProcess P hm hmd Delta hDelta hsmall).law T) := by
  have h := ENNReal.toReal_mono
    (ENNReal.mul_ne_top ENNReal.ofReal_ne_top ENNReal.ofReal_ne_top)
    (reference_planted_KL_le_expectedCount (T := T) P hm hmd Delta hDelta hsmall i)
  have hnonneg : 0 ≤ ∫ h, History.selectedCount i T h
      ∂(referenceProcess P hm hmd Delta hDelta hsmall).law T :=
    integral_nonneg fun h => (History.selectedCount_mem_Icc i T h).1
  simpa only [ENNReal.toReal_mul, ENNReal.toReal_ofReal (by positivity : (0 : ℝ) ≤ 128 * (4 * Delta) ^ 2),
    ENNReal.toReal_ofReal hnonneg] using h

end

end MsetsPaper.Lower.ConfidenceOblivious
