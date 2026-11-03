import MsetsPaper.Lower.ConfidenceObliviousSeeded
import MsetsLower.Lower.Confidence.AverageScore
import Mathlib.Probability.Kernel.Composition.IntegralCompProd
import Mathlib.MeasureTheory.Function.ConditionalExpectation.Basic

/-! # P4: average scores for the unstopped oblivious environments

The auxiliary learner stops; the noise and losses do not. The score
average below has no activity indicator and holds on every history.
-/

namespace MsetsPaper.Lower.ConfidenceOblivious

open MsetsLower MsetsLower.Feedback MsetsLower.Lower MsetsLower.Lower.Confidence
open MeasureTheory ProbabilityTheory Set
open scoped ENNReal ProbabilityTheory BigOperators
noncomputable section

def shapeSum {T : ℕ} (Z : Table T) (t : ℕ) : ℝ :=
  ∑ s ∈ Finset.range t, shape (tableNoise Z s)

def averageScoreRemainder {d m T : ℕ} (hmd : m ≤ d) (Z : Table T) (Delta : ℝ) :
    (t : ℕ) → History d m t → ℝ
  | 0, _ => 0
  | t + 1, h => averageScoreRemainder hmd Z Delta t h.1 +
      ((candidateCount hmd h.2.1 : ℝ) - 1) *
        (((confidenceCandidates d m hmd).card : ℝ) / (8 * m) - Delta * shape (tableNoise Z t))

theorem sum_score_succ {d m T : ℕ} (hmd : m ≤ d) (Z : Table T) (Delta : ℝ)
    (t : ℕ) (h : History d m (t + 1)) :
    ∑ i ∈ confidenceCandidates d m hmd, score hmd Z Delta i (t + 1) h =
      (∑ i ∈ confidenceCandidates d m hmd, score hmd Z Delta i t h.1) +
      ((confidenceCandidates d m hmd).card : ℝ) * candidatePenalty hmd h.2.1 +
      Delta * shape (tableNoise Z t) *
        (((confidenceCandidates d m hmd).card : ℝ) - candidateCount hmd h.2.1) := by
  classical
  have hs (i : Fin d) : score hmd Z Delta i (t + 1) h =
      score hmd Z Delta i t h.1 + candidatePenalty hmd h.2.1 +
        Delta * shape (tableNoise Z t) * missedIndicator i h.2.1 := by
    simp only [score, cumulativePenalty_succ, missedShapeSum]
    ring
  simp_rw [hs]
  rw [Finset.sum_add_distrib, Finset.sum_add_distrib]
  simp only [Finset.sum_const, nsmul_eq_mul]
  rw [← Finset.mul_sum, sum_missedIndicator]

/-- The exact algebraic equality preceding the pointwise lower bound. -/
theorem sum_score_identity {d m T : ℕ} (hmd : m ≤ d) (Z : Table T) (Delta : ℝ) :
    ∀ t (h : History d m t),
      ∑ i ∈ confidenceCandidates d m hmd, score hmd Z Delta i t h =
        Delta * (((confidenceCandidates d m hmd).card : ℝ) - 1) * shapeSum Z t +
          averageScoreRemainder hmd Z Delta t h := by
  intro t
  induction t with
  | zero => intro h; simp [score, cumulativePenalty_zero, missedShapeSum, shapeSum, averageScoreRemainder]
  | succ t ih =>
    intro h
    rw [sum_score_succ, ih]
    simp only [shapeSum, Finset.sum_range_succ, averageScoreRemainder, candidatePenalty]
    ring

theorem shapeSum_nonneg {T : ℕ} (Z : Table T) (t : ℕ) : 0 ≤ shapeSum Z t :=
  Finset.sum_nonneg (fun s _ ↦ (shape_mem_Icc (tableNoise_mem_Icc Z s)).1)

theorem averageScoreRemainder_nonneg {d m T : ℕ} (hm : 1 ≤ m) (hmd : m ≤ d)
    (Z : Table T) (Delta : ℝ) (hDelta : 0 ≤ Delta)
    (hscale : Delta ≤ ((confidenceCandidates d m hmd).card : ℝ) / (8 * m)) :
    ∀ t (h : History d m t), 0 ≤ averageScoreRemainder hmd Z Delta t h := by
  intro t
  induction t with
  | zero => intro h; rfl
  | succ t ih =>
    intro h
    have hn : (1 : ℝ) ≤ candidateCount hmd h.2.1 := by
      exact_mod_cast candidateCount_pos hm hmd h.2.1
    have hg := mul_le_mul_of_nonneg_left (shape_mem_Icc (tableNoise_mem_Icc Z t)).2 hDelta
    change 0 ≤ averageScoreRemainder hmd Z Delta t h.1 + _
    exact add_nonneg (ih h.1) (mul_nonneg (by linarith) (by linarith))

theorem sum_score_lower {d m T : ℕ} (hm : 1 ≤ m) (hmd : m ≤ d)
    (hN : 2 ≤ (confidenceCandidates d m hmd).card)
    (Z : Table T) (Delta : ℝ) (hDelta : 0 ≤ Delta)
    (hscale : Delta ≤ ((confidenceCandidates d m hmd).card : ℝ) / (8 * m))
    (t : ℕ) (h : History d m t) :
    Delta * (((confidenceCandidates d m hmd).card : ℝ) / 2) * shapeSum Z t ≤
      ∑ i ∈ confidenceCandidates d m hmd, score hmd Z Delta i t h := by
  rw [sum_score_identity]
  have hNr : (2 : ℝ) ≤ (confidenceCandidates d m hmd).card := by exact_mod_cast hN
  have hr := averageScoreRemainder_nonneg hm hmd Z Delta hDelta hscale t h
  have hmul := mul_le_mul_of_nonneg_right
    (mul_le_mul_of_nonneg_left (show ((confidenceCandidates d m hmd).card : ℝ) / 2 ≤
      (confidenceCandidates d m hmd).card - 1 by linarith) hDelta) (shapeSum_nonneg Z t)
  linarith

theorem score_le_nine_eighths {d m T : ℕ} (hmd : m ≤ d) (Z : Table T)
    (Delta : ℝ) (hDelta : 0 ≤ Delta) (i : Fin d) (h : History d m T)
    (hpenalty : cumulativePenalty hmd T h ≤ Delta * T / 8) :
    score hmd Z Delta i T h ≤ 9 * Delta * T / 8 := by
  have hmiss := mul_le_mul_of_nonneg_left (missedShapeSum_mem_Icc Z i T h).2 hDelta
  unfold score
  linarith

/-- The literal two-level split from the manuscript. -/
theorem integral_le_threshold_add_tail {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ] (f : Ω → ℝ) (hf : Measurable f)
    (hfi : Integrable f μ) (B : ℝ) (hB : 0 ≤ B)
    (hu : ∀ᵐ x ∂μ, f x ≤ 9 * B / 8) :
    ∫ x, f x ∂μ ≤ B / 8 + B * μ.real {x | B / 8 ≤ f x} := by
  let E := {x | B / 8 ≤ f x}
  have hE : MeasurableSet E := measurableSet_le measurable_const hf
  have hI : Integrable (E.indicator (fun _ : Ω ↦ (1 : ℝ))) μ := (integrable_const 1).indicator hE
  have hmajor : ∀ᵐ x ∂μ, f x ≤ B / 8 + B * E.indicator (fun _ : Ω ↦ (1 : ℝ)) x := by
    filter_upwards [hu] with x hx
    by_cases h : x ∈ E
    · simp only [Set.indicator_of_mem h]
      linarith
    · have hh : f x < B / 8 := lt_of_not_ge h
      simp only [Set.indicator_of_notMem h, mul_zero, add_zero]
      exact hh.le
  have hi := integral_mono_ae hfi ((integrable_const (B / 8)).add (hI.const_mul B)) hmajor
  change (∫ x, f x ∂μ) ≤ ∫ x, B / 8 + B * E.indicator (fun _ : Ω ↦ (1 : ℝ)) x ∂μ at hi
  have hiI : (∫ x, E.indicator (fun _ : Ω ↦ (1 : ℝ)) x ∂μ) = μ.real E :=
    integral_indicator_one hE
  rw [integral_add (integrable_const (B / 8)) (hI.const_mul B), integral_const,
    integral_const_mul, hiI] at hi
  simpa only [probReal_univ, one_smul] using hi

def referenceJointLaw {d m : ℕ} (P : Policy d m) (hm : 1 ≤ m) (hmd : m ≤ d)
    (T : ℕ) : Measure (Table T × History d m T) :=
  DenseCommonNoise.noiseTableMeasure T ⊗ₘ parametricRunKernel P (referenceTableLossProcess hm hmd T) T

instance referenceJointLaw_isProbabilityMeasure {d m : ℕ}
    (P : Policy d m) (hm : 1 ≤ m) (hmd : m ≤ d) (T : ℕ) :
    IsProbabilityMeasure (referenceJointLaw P hm hmd T) := by
  letI := parametricRunKernel_isMarkov P (referenceTableLossProcess hm hmd T) T
  unfold referenceJointLaw
  infer_instance

theorem referenceJointLaw_map_table {d m : ℕ}
    (P : Policy d m) (hm : 1 ≤ m) (hmd : m ≤ d) (T : ℕ) :
    (referenceJointLaw P hm hmd T).map Prod.fst = DenseCommonNoise.noiseTableMeasure T := by
  letI := parametricRunKernel_isMarkov P (referenceTableLossProcess hm hmd T) T
  exact Measure.fst_compProd _ _

theorem referenceJointLaw_map_history {d m : ℕ}
    (P : Policy d m) (hm : 1 ≤ m) (hmd : m ≤ d) (T : ℕ) :
    (referenceJointLaw P hm hmd T).map Prod.snd =
      parametricRunKernel P (referenceTableLossProcess hm hmd T) T ∘ₘ DenseCommonNoise.noiseTableMeasure T := by
  letI := parametricRunKernel_isMarkov P (referenceTableLossProcess hm hmd T) T
  exact Measure.snd_compProd _ _

theorem measurable_shapeSum {T : ℕ} (t : ℕ) : Measurable (fun Z : Table T ↦ shapeSum Z t) :=
  Finset.measurable_sum _ (fun s _ ↦ measurable_shape.comp (measurable_tableNoise s))

theorem integral_shapeSum_noise (T : ℕ) :
    ∫ Z : Table T, shapeSum Z T ∂DenseCommonNoise.noiseTableMeasure T = (2 / 3 : ℝ) * T := by
  unfold shapeSum
  rw [integral_finsetSum]
  · have hterm : ∀ s ∈ Finset.range T,
        (∫ Z : Table T, shape (tableNoise Z s) ∂DenseCommonNoise.noiseTableMeasure T) = (2 / 3 : ℝ) := by
      intro s hs
      have hst := Finset.mem_range.mp hs
      simp only [tableNoise, dif_pos hst]
      rw [← DenseCommonNoise.integral_shape_noiseMeasure,
        ← DenseCommonNoise.map_noise_coordinate (⟨s, hst⟩ : Fin T)]
      exact (integral_map (μ := DenseCommonNoise.noiseTableMeasure T)
        (φ := fun Z : Table T ↦ Z (⟨s, hst⟩ : Fin T))
        (f := fun z : Noise ↦ shape z.val) (measurable_pi_apply _).aemeasurable
        (measurable_shape.comp measurable_subtype_coe).aestronglyMeasurable).symm
    rw [Finset.sum_congr rfl hterm]
    simp
    ring
  · intro s _
    exact Integrable.of_mem_Icc (0 : ℝ) 1
      (measurable_shape.comp (measurable_tableNoise s)).aemeasurable
      (ae_of_all _ fun Z ↦ shape_mem_Icc (tableNoise_mem_Icc Z s))

theorem integral_shapeSum_joint {d m : ℕ}
    (P : Policy d m) (hm : 1 ≤ m) (hmd : m ≤ d) (T : ℕ) :
    ∫ x, shapeSum x.1 T ∂referenceJointLaw P hm hmd T = (2 / 3 : ℝ) * T := by
  rw [← integral_shapeSum_noise T, ← referenceJointLaw_map_table P hm hmd T]
  exact (integral_map measurable_fst.aemeasurable (measurable_shapeSum T).aestronglyMeasurable).symm

theorem measurable_missedShapeSum {d m T : ℕ} (i : Fin d) :
    ∀ t, Measurable (fun x : Table T × History d m t ↦ missedShapeSum x.1 i t x.2) := by
  intro t
  induction t with
  | zero => exact measurable_const
  | succ t ih =>
    exact (ih.comp (measurable_fst.prodMk measurable_snd.fst)).add
      (((measurable_shape.comp (measurable_tableNoise t)).comp measurable_fst).mul
        ((measurable_of_finite (missedIndicator i)).comp measurable_snd.snd.fst))

theorem measurable_score {d m T : ℕ} (hmd : m ≤ d) (Delta : ℝ) (i : Fin d) (t : ℕ) :
    Measurable (fun x : Table T × History d m t ↦ score hmd x.1 Delta i t x.2) :=
  ((measurable_cumulativePenalty hmd t).comp measurable_snd).add
    ((measurable_missedShapeSum i t).const_mul Delta)

theorem cumulativePenalty_le {d m : ℕ} (hm : 1 ≤ m) (hmd : m ≤ d) :
    ∀ t (h : History d m t), cumulativePenalty hmd t h ≤ (t : ℝ) / 8 := by
  intro t
  induction t with
  | zero => intro h; simp [cumulativePenalty_zero]
  | succ t ih =>
    intro h
    have hp := (candidatePenalty_mem_Ico hm hmd h.2.1).2
    rw [cumulativePenalty_succ]
    push_cast
    linarith [ih h.1]

theorem integrable_score {d m T t : ℕ} (hm : 1 ≤ m) (hmd : m ≤ d)
    (Delta : ℝ) (hDelta : 0 ≤ Delta) (i : Fin d)
    (μ : Measure (Table T × History d m t)) [IsFiniteMeasure μ] :
    Integrable (fun x ↦ score hmd x.1 Delta i t x.2) μ := by
  apply Integrable.of_mem_Icc (0 : ℝ) ((t : ℝ) / 8 + Delta * t)
    (measurable_score hmd Delta i t).aemeasurable
  apply ae_of_all
  intro x
  have hmiss := missedShapeSum_mem_Icc x.1 i t x.2
  have hp := cumulativePenalty_nonneg hm hmd t x.2
  have hpu := cumulativePenalty_le hm hmd t x.2
  change 0 ≤ cumulativePenalty hmd t x.2 + Delta * missedShapeSum x.1 i t x.2 ∧ _
  constructor
  · exact add_nonneg hp (mul_nonneg hDelta hmiss.1)
  · unfold score
    exact add_le_add hpu (mul_le_mul_of_nonneg_left hmiss.2 hDelta)

theorem observableScore_eq_reference_joint_ae {d m T : ℕ}
    (P : Policy d m) (hm : 1 ≤ m) (hmd : m ≤ d) (Delta : ℝ) (i : Fin d) :
    ∀ᵐ x ∂referenceJointLaw P hm hmd T,
      observableScore hmd Delta i T x.2 = score hmd x.1 Delta i T x.2 := by
  letI := parametricRunKernel_isMarkov P (referenceTableLossProcess hm hmd T) T
  apply Measure.ae_compProd_of_ae_ae
    (measurableSet_eq_fun ((measurable_observableScore hmd Delta i T).comp measurable_snd)
      (measurable_score hmd Delta i T))
  apply ae_of_all
  intro Z
  rw [parametricRunKernel_apply]
  exact observableScore_eq_reference_ae P hm hmd Delta Z i T

/-- The sigma-algebra generated by the complete observed history on the
joint space of the noise table and the interaction history. -/
def referenceHistorySigma (d m T : ℕ) : MeasurableSpace (Table T × History d m T) :=
  MeasurableSpace.comap Prod.snd inferInstance

theorem referenceHistorySigma_le (d m T : ℕ) :
    referenceHistorySigma d m T ≤
      (inferInstance : MeasurableSpace (Table T × History d m T)) :=
  measurable_snd.comap_le

/-- The manuscript's conditioning step: under the reference law the score
is determined by the observed history, because its noises can be recovered.
This is an equality of the actual conditional expectation, not only an
identity after taking an unconditional integral. -/
theorem conditional_score_eq_reference {d m T : ℕ}
    (P : Policy d m) (hm : 1 ≤ m) (hmd : m ≤ d)
    (Delta : ℝ) (hDelta : 0 ≤ Delta) (i : Fin d) :
    (referenceJointLaw P hm hmd T)[
      (fun x => score hmd x.1 Delta i T x.2) | referenceHistorySigma d m T] =ᵐ[
        referenceJointLaw P hm hmd T] fun x => score hmd x.1 Delta i T x.2 := by
  let μ := referenceJointLaw P hm hmd T
  have hobs := observableScore_eq_reference_joint_ae (T := T) P hm hmd Delta i
  have hrev : (fun x => score hmd x.1 Delta i T x.2) =ᵐ[μ]
      (fun x => observableScore hmd Delta i T x.2) := hobs.mono fun _ hx => hx.symm
  have hmeas : StronglyMeasurable[referenceHistorySigma d m T]
      (fun x : Table T × History d m T => observableScore hmd Delta i T x.2) := by
    apply Measurable.stronglyMeasurable
    exact (measurable_observableScore hmd Delta i T).comp
      (Measurable.of_comap_le le_rfl)
  have hobsint : Integrable
      (fun x : Table T × History d m T => observableScore hmd Delta i T x.2) μ :=
    (integrable_score hm hmd Delta hDelta i μ).congr hrev
  have heq := condExp_congr_ae (m := referenceHistorySigma d m T) hrev
  rw [condExp_of_stronglyMeasurable (referenceHistorySigma_le d m T) hmeas hobsint] at heq
  exact heq.trans hobs

/-- The displayed conditional average-score identity, before division by
the positive cardinality of V. The remainder is the same finite sum as in
the manuscript's second line. -/
theorem conditional_sum_score_identity {d m T : ℕ}
    (P : Policy d m) (hm : 1 ≤ m) (hmd : m ≤ d)
    (Delta : ℝ) (hDelta : 0 ≤ Delta) :
    ∀ᵐ x ∂referenceJointLaw P hm hmd T,
      (∑ i ∈ confidenceCandidates d m hmd,
        ((referenceJointLaw P hm hmd T)[
          (fun y => score hmd y.1 Delta i T y.2) | referenceHistorySigma d m T]) x) =
        Delta * (((confidenceCandidates d m hmd).card : ℝ) - 1) * shapeSum x.1 T +
          averageScoreRemainder hmd x.1 Delta T x.2 := by
  have hall : ∀ᵐ x ∂referenceJointLaw P hm hmd T, ∀ i : Fin d,
      ((referenceJointLaw P hm hmd T)[
        (fun y => score hmd y.1 Delta i T y.2) | referenceHistorySigma d m T]) x =
          score hmd x.1 Delta i T x.2 :=
    (ae_all_iff).2 fun i => conditional_score_eq_reference P hm hmd Delta hDelta i
  filter_upwards [hall] with x hx
  simp_rw [hx]
  exact sum_score_identity hmd x.1 Delta T x.2

theorem conditional_sum_score_lower {d m T : ℕ}
    (P : Policy d m) (hm : 1 ≤ m) (hmd : m ≤ d)
    (hN : 2 ≤ (confidenceCandidates d m hmd).card)
    (Delta : ℝ) (hDelta : 0 ≤ Delta)
    (hscale : Delta ≤ ((confidenceCandidates d m hmd).card : ℝ) / (8 * m)) :
    ∀ᵐ x ∂referenceJointLaw P hm hmd T,
      Delta * (((confidenceCandidates d m hmd).card : ℝ) / 2) * shapeSum x.1 T ≤
        ∑ i ∈ confidenceCandidates d m hmd,
          ((referenceJointLaw P hm hmd T)[
            (fun y => score hmd y.1 Delta i T y.2) | referenceHistorySigma d m T]) x := by
  filter_upwards [conditional_sum_score_identity P hm hmd Delta hDelta] with x hx
  rw [hx, ← sum_score_identity hmd x.1 Delta T x.2]
  exact sum_score_lower hm hmd hN x.1 Delta hDelta hscale T x.2

theorem integral_sum_score_lower {d m T : ℕ}
    (P : Policy d m) (hm : 1 ≤ m) (hmd : m ≤ d)
    (hN : 2 ≤ (confidenceCandidates d m hmd).card)
    (Delta : ℝ) (hDelta : 0 ≤ Delta)
    (hscale : Delta ≤ ((confidenceCandidates d m hmd).card : ℝ) / (8 * m)) :
    Delta * ((confidenceCandidates d m hmd).card : ℝ) * T / 3 ≤
      ∑ i ∈ confidenceCandidates d m hmd,
        ∫ x, score hmd x.1 Delta i T x.2 ∂referenceJointLaw P hm hmd T := by
  have hg : Integrable (fun x : Table T × History d m T ↦ shapeSum x.1 T)
      (referenceJointLaw P hm hmd T) := by
    apply Integrable.of_mem_Icc (0 : ℝ) T ((measurable_shapeSum T).comp measurable_fst).aemeasurable
    apply ae_of_all
    intro x
    refine ⟨shapeSum_nonneg x.1 T, ?_⟩
    calc
      shapeSum x.1 T ≤ ∑ s ∈ Finset.range T, (1 : ℝ) :=
        Finset.sum_le_sum (fun s _ ↦ (shape_mem_Icc (tableNoise_mem_Icc x.1 s)).2)
      _ = T := by simp
  have hsum := integrable_finset_sum (confidenceCandidates d m hmd)
    (fun i _ ↦ integrable_condExp (μ := referenceJointLaw P hm hmd T)
      (m := referenceHistorySigma d m T) (f := fun x => score hmd x.1 Delta i T x.2))
  have hmono := integral_mono_ae (hg.const_mul _) hsum
    (conditional_sum_score_lower P hm hmd hN Delta hDelta hscale)
  rw [integral_const_mul, integral_shapeSum_joint, integral_finsetSum _
    (fun i _ ↦ integrable_condExp)] at hmono
  simp_rw [integral_condExp (referenceHistorySigma_le d m T)] at hmono
  nlinarith

theorem reference_scoreEvent_probability {d m T : ℕ}
    (P : Policy d m) (hm : 1 ≤ m) (hmd : m ≤ d) (Delta : ℝ) (i : Fin d) :
    (referenceJointLaw P hm hmd T).real
        {x | Delta * T / 8 ≤ score hmd x.1 Delta i T x.2} =
      (parametricRunKernel P (referenceTableLossProcess hm hmd T) T ∘ₘ
        DenseCommonNoise.noiseTableMeasure T).real (scoreEvent hmd Delta i T) := by
  rw [← referenceJointLaw_map_history P hm hmd T]
  rw [measureReal_def, measureReal_def,
    Measure.map_apply measurable_snd (measurableSet_scoreEvent hmd Delta i T)]
  congr 1
  apply measure_congr
  filter_upwards [observableScore_eq_reference_joint_ae P hm hmd Delta i] with x hx
  apply propext
  change (Delta * T / 8 ≤ score hmd x.1 Delta i T x.2) ↔
    (Delta * T / 8 ≤ observableScore hmd Delta i T x.2)
  rw [hx]

theorem reference_average_event_ge_five_twentyfourths {d m T : ℕ}
    (P : Policy d m) (hm : 1 ≤ m) (hmd : m ≤ d)
    (hN : 2 ≤ (confidenceCandidates d m hmd).card) (hT : 0 < T)
    (Delta : ℝ) (hDelta : 0 < Delta)
    (hscale : Delta ≤ ((confidenceCandidates d m hmd).card : ℝ) / (8 * m))
    (hpenalty : ∀ᵐ x ∂referenceJointLaw P hm hmd T,
      cumulativePenalty hmd T x.2 ≤ Delta * T / 8) :
    (5 : ℝ) / 24 ≤
      (∑ i ∈ confidenceCandidates d m hmd,
        (parametricRunKernel P (referenceTableLossProcess hm hmd T) T ∘ₘ
          DenseCommonNoise.noiseTableMeasure T).real (scoreEvent hmd Delta i T)) /
        (confidenceCandidates d m hmd).card := by
  have hB : 0 < Delta * T := mul_pos hDelta (by exact_mod_cast hT)
  have hNr : (0 : ℝ) < (confidenceCandidates d m hmd).card := by exact_mod_cast (show 0 < _ by omega)
  have hlower := integral_sum_score_lower (T := T) P hm hmd hN Delta hDelta.le hscale
  have hupper (i : Fin d) :
      (∫ x, score hmd x.1 Delta i T x.2 ∂referenceJointLaw P hm hmd T) ≤
        Delta * T / 8 + Delta * T *
          (parametricRunKernel P (referenceTableLossProcess hm hmd T) T ∘ₘ
            DenseCommonNoise.noiseTableMeasure T).real (scoreEvent hmd Delta i T) := by
    have hu : ∀ᵐ x ∂referenceJointLaw P hm hmd T,
        score hmd x.1 Delta i T x.2 ≤ 9 * (Delta * T) / 8 := by
      filter_upwards [hpenalty] with x hx
      simpa only [mul_assoc] using score_le_nine_eighths hmd x.1 Delta hDelta.le i x.2 hx
    have hh := integral_le_threshold_add_tail (referenceJointLaw P hm hmd T)
      (fun x ↦ score hmd x.1 Delta i T x.2) (measurable_score hmd Delta i T)
      (integrable_score hm hmd Delta hDelta.le i _) (Delta * T) hB.le hu
    rw [reference_scoreEvent_probability] at hh
    exact hh
  have hsum := Finset.sum_le_sum (s := confidenceCandidates d m hmd) (fun i _ ↦ hupper i)
  simp only [Finset.sum_add_distrib, Finset.sum_const, nsmul_eq_mul, ← Finset.mul_sum] at hsum
  apply (le_div_iff₀ hNr).mpr
  have htotal := hlower.trans hsum
  nlinarith

theorem auxiliary_reference_average_event {d m T : ℕ}
    (P : Policy d m) (hm : 1 ≤ m) (hmd : m ≤ d)
    (hN : 2 ≤ (confidenceCandidates d m hmd).card) (hT : 0 < T)
    (Delta : ℝ) (hDelta : 0 < Delta)
    (hscale : Delta ≤ ((confidenceCandidates d m hmd).card : ℝ) / (8 * m))
    (r : MsetsPaper.Probability.PolicySeed.Seeds T)
    (j : Fin d) (hj : j ∈ confidenceCandidates d m hmd) :
    let A := auxiliaryPolicy P hmd r (Delta * T / 8) (coreComparator hm hmd j hj)
    (5 : ℝ) / 24 ≤
      (∑ i ∈ confidenceCandidates d m hmd,
        (parametricRunKernel A (referenceTableLossProcess hm hmd T) T ∘ₘ
          DenseCommonNoise.noiseTableMeasure T).real (scoreEvent hmd Delta i T)) /
        (confidenceCandidates d m hmd).card := by
  dsimp only
  apply reference_average_event_ge_five_twentyfourths _ hm hmd hN hT Delta hDelta hscale
  let A := auxiliaryPolicy P hmd r (Delta * T / 8) (coreComparator hm hmd j hj)
  letI := parametricRunKernel_isMarkov A (referenceTableLossProcess hm hmd T) T
  apply Measure.ae_compProd_of_ae_ae
    (measurableSet_le ((measurable_cumulativePenalty hmd T).comp measurable_snd) measurable_const)
  apply ae_of_all
  intro Z
  rw [parametricRunKernel_apply]
  filter_upwards [auxiliaryPolicy_penalty_ae P hm hmd r (Delta * T / 8)
    (by positivity) j hj ((referenceTableLossProcess hm hmd T).at Z) T] with h hh
  exact hh.le

end
end MsetsPaper.Lower.ConfidenceOblivious
