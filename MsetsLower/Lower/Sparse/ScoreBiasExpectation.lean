import MsetsLower.Lower.Sparse.ScoreBiasFullTable
import MsetsLower.Lower.Sparse.PositiveDriftExpectation
import MsetsLower.Lower.Sparse.Gamma

set_option linter.style.header false

/-!
# Expected sparse score bias on the full hidden table

This file supplies the chronological `2/3` feedback identity for an
arbitrary bounded predictable weight.  It is then specialized to the
coordinate and learner scores and combined with the genuine full-table
cell sign estimate from `ScoreBiasFullTable`.
-/

namespace MsetsLower.Lower.Sparse

open MsetsLower Feedback MeasureTheory ProbabilityTheory Set
open scoped BigOperators ENNReal ProbabilityTheory

noncomputable section

/-! ## A generic chronological feedback-score identity -/

/-- A predictable real weight: at round `t` it may depend on the past and
the action, but not on the fresh feedback. -/
abbrev SparsePredictableWeight (n k : Nat) :=
  (t : Nat) -> History n k t -> MSetAction n k -> Real

/-- The realized score obtained by multiplying a predictable weight by the
observable feedback score. -/
def sparseObservableWeightedScore {n k : Nat}
    (V : SparseAdaptiveParameters n k) (W : SparsePredictableWeight n k) :
    (T : Nat) -> History n k T -> Real
  | 0, _ => 0
  | t + 1, h =>
      sparseObservableWeightedScore V W t h.1 +
        W t h.1 h.2.1 *
          feedbackScoreShape (V.value t h.1 h.2.1) h.2.2

/-- The corresponding chronological sum before the fresh feedback score is
inserted. -/
def sparsePredictableWeightTotal {n k : Nat}
    (W : SparsePredictableWeight n k) :
    (T : Nat) -> History n k T -> Real
  | 0, _ => 0
  | t + 1, h => sparsePredictableWeightTotal W t h.1 + W t h.1 h.2.1

@[simp] theorem sparseObservableWeightedScore_zero
    {n k : Nat} (V : SparseAdaptiveParameters n k)
    (W : SparsePredictableWeight n k) (h : History n k 0) :
    sparseObservableWeightedScore V W 0 h = 0 := rfl

@[simp] theorem sparseObservableWeightedScore_succ
    {n k t : Nat} (V : SparseAdaptiveParameters n k)
    (W : SparsePredictableWeight n k) (h : History n k (t + 1)) :
    sparseObservableWeightedScore V W (t + 1) h =
      sparseObservableWeightedScore V W t h.1 +
        W t h.1 h.2.1 *
          feedbackScoreShape (V.value t h.1 h.2.1) h.2.2 := rfl

@[simp] theorem sparsePredictableWeightTotal_zero
    {n k : Nat} (W : SparsePredictableWeight n k) (h : History n k 0) :
    sparsePredictableWeightTotal W 0 h = 0 := rfl

@[simp] theorem sparsePredictableWeightTotal_succ
    {n k t : Nat} (W : SparsePredictableWeight n k)
    (h : History n k (t + 1)) :
    sparsePredictableWeightTotal W (t + 1) h =
      sparsePredictableWeightTotal W t h.1 + W t h.1 h.2.1 := rfl

set_option maxHeartbeats 2000000 in
-- Dependent histories make this recursive measurability proof elaboration-heavy.
theorem measurable_sparseObservableWeightedScore
    {n k : Nat} (V : SparseAdaptiveParameters n k)
    (W : SparsePredictableWeight n k)
    (hW : forall t, Measurable (fun hA : History n k t × MSetAction n k =>
      W t hA.1 hA.2)) :
    forall T, Measurable (sparseObservableWeightedScore V W T) := by
  intro T
  induction T with
  | zero => exact measurable_const
  | succ t ih =>
      have hparameter : Measurable (fun h : History n k (t + 1) =>
          V.value t h.1 h.2.1) :=
        (V.measurable_value t).comp
          (measurable_fst.prodMk (measurable_fst.comp measurable_snd))
      have hfeedback : Measurable (fun h : History n k (t + 1) => h.2.2) :=
        measurable_snd.comp measurable_snd
      have hweight : Measurable (fun h : History n k (t + 1) =>
          W t h.1 h.2.1) :=
        (hW t).comp
          (measurable_fst.prodMk (measurable_fst.comp measurable_snd))
      have hscore :=
        measurable_feedbackScoreShape_uncurry.comp (hparameter.prodMk hfeedback)
      change Measurable (fun h : History n k (t + 1) =>
        sparseObservableWeightedScore V W t h.1 +
          W t h.1 h.2.1 * feedbackScoreShape (V.value t h.1 h.2.1) h.2.2)
      exact (ih.comp measurable_fst).add (hweight.mul hscore)

set_option maxHeartbeats 1000000 in
-- Dependent histories make this recursive measurability proof elaboration-heavy.
theorem measurable_sparsePredictableWeightTotal
    {n k : Nat} (W : SparsePredictableWeight n k)
    (hW : forall t, Measurable (fun hA : History n k t × MSetAction n k =>
      W t hA.1 hA.2)) :
    forall T, Measurable (sparsePredictableWeightTotal W T) := by
  intro T
  induction T with
  | zero => exact measurable_const
  | succ t ih =>
      exact (ih.comp measurable_fst).add <|
        (hW t).comp
          (measurable_fst.prodMk (measurable_fst.comp measurable_snd))

theorem sparseObservableWeightedScore_abs_le
    {n k : Nat} (V : SparseAdaptiveParameters n k)
    (W : SparsePredictableWeight n k) {C : Real} (hC : 0 <= C)
    (hWabs : forall t h A, |W t h A| <= C) :
    forall T (h : History n k T), sparseHistoryInFeedbackSupport T h ->
      |sparseObservableWeightedScore V W T h| <= C * T := by
  intro T
  induction T with
  | zero => intro h _; simp
  | succ t ih =>
      intro h hsupp
      have hprev := ih h.1 hsupp.1
      have hG := feedbackScoreShape_mem_Icc
        (V.abs_le t h.1 h.2.1) hsupp.2
      have hGabs : |feedbackScoreShape
          (V.value t h.1 h.2.1) h.2.2| <= 1 := by
        rw [abs_of_nonneg hG.1]
        exact hG.2
      rw [sparseObservableWeightedScore_succ]
      calc
        |sparseObservableWeightedScore V W t h.1 +
            W t h.1 h.2.1 *
              feedbackScoreShape (V.value t h.1 h.2.1) h.2.2| <=
            |sparseObservableWeightedScore V W t h.1| +
              |W t h.1 h.2.1 *
                feedbackScoreShape (V.value t h.1 h.2.1) h.2.2| :=
          abs_add_le _ _
        _ <= C * t + C * 1 := by
          rw [abs_mul]
          exact add_le_add hprev <|
            mul_le_mul (hWabs t h.1 h.2.1) hGabs (abs_nonneg _) hC
        _ = C * (t + 1 : Nat) := by push_cast; ring

theorem sparsePredictableWeightTotal_abs_le
    {n k : Nat} (W : SparsePredictableWeight n k) {C : Real}
    (_hC : 0 <= C) (hWabs : forall t h A, |W t h A| <= C) :
    forall T (h : History n k T),
      |sparsePredictableWeightTotal W T h| <= C * T := by
  intro T
  induction T with
  | zero => intro h; simp
  | succ t ih =>
      intro h
      rw [sparsePredictableWeightTotal_succ]
      calc
        |sparsePredictableWeightTotal W t h.1 + W t h.1 h.2.1| <=
            |sparsePredictableWeightTotal W t h.1| + |W t h.1 h.2.1| :=
          abs_add_le _ _
        _ <= C * t + C := add_le_add (ih h.1) (hWabs t h.1 h.2.1)
        _ = C * (t + 1 : Nat) := by push_cast; ring

/-- One realized weighted increment. -/
def sparseWeightedRound {n k t : Nat}
    (V : SparseAdaptiveParameters n k) (W : SparsePredictableWeight n k)
    (h : History n k t) (Ay : MSetAction n k × Real) : Real :=
  W t h Ay.1 * feedbackScoreShape (V.value t h Ay.1) Ay.2

set_option maxHeartbeats 1000000 in
-- The dependent predictable weight is specialized at a fixed history.
theorem measurable_sparseWeightedRound
    {n k t : Nat} (V : SparseAdaptiveParameters n k)
    (W : SparsePredictableWeight n k)
    (hW : forall t, Measurable (fun hA : History n k t × MSetAction n k =>
      W t hA.1 hA.2)) (h : History n k t) :
    Measurable (sparseWeightedRound V W h) := by
  have hw : Measurable (fun Ay : MSetAction n k × Real => W t h Ay.1) :=
    (hW t).comp (measurable_const.prodMk measurable_fst)
  have hp : Measurable (fun Ay : MSetAction n k × Real =>
      V.value t h Ay.1) :=
    (V.measurable_value t).comp (measurable_const.prodMk measurable_fst)
  exact hw.mul <| measurable_feedbackScoreShape_uncurry.comp
    (hp.prodMk measurable_snd)

theorem integrable_sparseWeightedRound
    {n k t : Nat} (P : Policy n k) (V : SparseAdaptiveParameters n k)
    (W : SparsePredictableWeight n k)
    (hW : forall t, Measurable (fun hA : History n k t × MSetAction n k =>
      W t hA.1 hA.2)) {C : Real} (hC : 0 <= C)
    (hWabs : forall t h A, |W t h A| <= C) (h : History n k t) :
    Integrable (sparseWeightedRound V W h)
      (sparseAdaptiveRoundKernel P V t h) := by
  letI : IsMarkovKernel (sparseAdaptiveRoundKernel P V t) :=
    sparseAdaptiveRoundKernel_isMarkov P V t
  apply Integrable.of_bound
    (measurable_sparseWeightedRound V W hW h).aestronglyMeasurable C
  filter_upwards [ae_sparseAdaptiveRoundKernel_feedback_mem_support
    P V t h] with Ay hy
  rw [Real.norm_eq_abs, sparseWeightedRound, abs_mul]
  have hG := feedbackScoreShape_mem_Icc (V.abs_le t h Ay.1) hy
  have hGabs : |feedbackScoreShape (V.value t h Ay.1) Ay.2| <= 1 := by
    rw [abs_of_nonneg hG.1]
    exact hG.2
  exact (mul_le_mul (hWabs t h Ay.1) hGabs (abs_nonneg _) hC).trans
    (by simp)

/-- The fresh feedback contributes exactly `2/3`, conditionally on the past
and the action. -/
theorem integral_sparseWeightedRound
    {n k t : Nat} (P : Policy n k) (V : SparseAdaptiveParameters n k)
    (W : SparsePredictableWeight n k)
    (hW : forall t, Measurable (fun hA : History n k t × MSetAction n k =>
      W t hA.1 hA.2)) {C : Real} (hC : 0 <= C)
    (hWabs : forall t h A, |W t h A| <= C) (h : History n k t) :
    (∫ Ay, sparseWeightedRound V W h Ay
        ∂sparseAdaptiveRoundKernel P V t h) =
      (2 / 3 : Real) * ∫ A, W t h A ∂P.kernel t h := by
  letI : IsMarkovKernel (sparseAdaptiveRoundKernel P V t) :=
    sparseAdaptiveRoundKernel_isMarkov P V t
  have hint := integrable_sparseWeightedRound P V W hW hC hWabs h
  let feedbackK := sparseParamFeedbackKernel
    (fun hA : History n k t × MSetAction n k => V.value t hA.1 hA.2)
  letI : IsMarkovKernel feedbackK := by
    dsimp [feedbackK]
    exact sparseParamFeedbackKernel_isMarkov _ (V.measurable_value t)
      (fun hA => V.abs_le t hA.1 hA.2)
  change (∫ Ay, sparseWeightedRound V W h Ay
      ∂(P.kernel t ⊗ₖ feedbackK) h) = _
  rw [ProbabilityTheory.integral_compProd hint]
  calc
    (∫ A, ∫ y, sparseWeightedRound V W h (A, y)
        ∂feedbackK (h, A) ∂P.kernel t h) =
        ∫ A, (2 / 3 : Real) * W t h A ∂P.kernel t h := by
      apply integral_congr_ae
      apply ae_of_all
      intro A
      change (∫ y, W t h A * feedbackScoreShape (V.value t h A) y
          ∂feedbackK (h, A)) = (2 / 3 : Real) * W t h A
      rw [show feedbackK (h, A) = feedbackDensityMeasure (V.value t h A) by
        exact sparseParamFeedbackKernel_apply _ (V.measurable_value t) _
          (V.abs_le t h A)]
      rw [integral_const_mul,
        integral_feedbackScoreShape_feedbackDensityMeasure (V.abs_le t h A)]
      ring
    _ = (2 / 3 : Real) * ∫ A, W t h A ∂P.kernel t h := by
      rw [integral_const_mul]

theorem integrable_sparseObservableWeightedScore_adaptiveLaw
    {n k T : Nat} (P : Policy n k) (V : SparseAdaptiveParameters n k)
    (W : SparsePredictableWeight n k)
    (hW : forall t, Measurable (fun hA : History n k t × MSetAction n k =>
      W t hA.1 hA.2)) {C : Real} (hC : 0 <= C)
    (hWabs : forall t h A, |W t h A| <= C) :
    Integrable (sparseObservableWeightedScore V W T)
      ((sparseAdaptiveProcess P V).law T) := by
  letI : IsProbabilityMeasure ((sparseAdaptiveProcess P V).law T) :=
    inferInstance
  apply Integrable.of_bound
    (measurable_sparseObservableWeightedScore V W hW T).aestronglyMeasurable
    (C * T)
  filter_upwards [ae_sparseAdaptiveProcess_history_support P V T] with h hsupp
  rw [Real.norm_eq_abs]
  exact sparseObservableWeightedScore_abs_le V W hC hWabs T h hsupp

theorem integrable_sparsePredictableWeightTotal_adaptiveLaw
    {n k T : Nat} (P : Policy n k) (V : SparseAdaptiveParameters n k)
    (W : SparsePredictableWeight n k)
    (hW : forall t, Measurable (fun hA : History n k t × MSetAction n k =>
      W t hA.1 hA.2)) {C : Real} (hC : 0 <= C)
    (hWabs : forall t h A, |W t h A| <= C) :
    Integrable (sparsePredictableWeightTotal W T)
      ((sparseAdaptiveProcess P V).law T) := by
  letI : IsProbabilityMeasure ((sparseAdaptiveProcess P V).law T) :=
    inferInstance
  apply Integrable.of_bound
    (measurable_sparsePredictableWeightTotal W hW T).aestronglyMeasurable
    (C * T)
  exact ae_of_all _ fun h => by
    rw [Real.norm_eq_abs]
    exact sparsePredictableWeightTotal_abs_le W hC hWabs T h

theorem integral_sparseObservableWeightedScore_succ_round
    {n k t : Nat} (P : Policy n k) (V : SparseAdaptiveParameters n k)
    (W : SparsePredictableWeight n k)
    (hW : forall t, Measurable (fun hA : History n k t × MSetAction n k =>
      W t hA.1 hA.2)) {C : Real} (hC : 0 <= C)
    (hWabs : forall t h A, |W t h A| <= C) (h : History n k t) :
    (∫ Ay, sparseObservableWeightedScore V W (t + 1) (h, Ay)
        ∂sparseAdaptiveRoundKernel P V t h) =
      sparseObservableWeightedScore V W t h +
        (2 / 3 : Real) * ∫ A, W t h A ∂P.kernel t h := by
  letI : IsMarkovKernel (sparseAdaptiveRoundKernel P V t) :=
    sparseAdaptiveRoundKernel_isMarkov P V t
  have hround := integrable_sparseWeightedRound P V W hW hC hWabs h
  simp_rw [sparseObservableWeightedScore_succ]
  change (∫ Ay, sparseObservableWeightedScore V W t h +
      sparseWeightedRound V W h Ay
      ∂sparseAdaptiveRoundKernel P V t h) = _
  rw [integral_add (integrable_const _) hround,
    integral_sparseWeightedRound P V W hW hC hWabs h]
  simp

theorem integral_sparsePredictableWeightTotal_succ_round
    {n k t : Nat} (P : Policy n k) (V : SparseAdaptiveParameters n k)
    (W : SparsePredictableWeight n k)
    (hW : forall t, Measurable (fun hA : History n k t × MSetAction n k =>
      W t hA.1 hA.2)) {C : Real} (hC : 0 <= C)
    (hWabs : forall t h A, |W t h A| <= C) (h : History n k t) :
    (∫ Ay, sparsePredictableWeightTotal W (t + 1) (h, Ay)
        ∂sparseAdaptiveRoundKernel P V t h) =
      sparsePredictableWeightTotal W t h +
        ∫ A, W t h A ∂P.kernel t h := by
  letI : IsMarkovKernel (sparseAdaptiveRoundKernel P V t) :=
    sparseAdaptiveRoundKernel_isMarkov P V t
  let feedbackK := sparseParamFeedbackKernel
    (fun hA : History n k t × MSetAction n k => V.value t hA.1 hA.2)
  letI : IsMarkovKernel feedbackK := by
    dsimp [feedbackK]
    exact sparseParamFeedbackKernel_isMarkov _ (V.measurable_value t)
      (fun hA => V.abs_le t hA.1 hA.2)
  have hfinal : Integrable
      (fun Ay : MSetAction n k × Real =>
        sparsePredictableWeightTotal W t h + W t h Ay.1)
      ((P.kernel t ⊗ₖ feedbackK) h) := by
    apply Integrable.of_bound
      (((measurable_const.add <|
        (hW t).comp (measurable_const.prodMk measurable_fst))).aestronglyMeasurable)
      (C * (t + 1 : Nat))
    exact ae_of_all _ fun Ay => by
      rw [Real.norm_eq_abs]
      exact sparsePredictableWeightTotal_abs_le W hC hWabs
        (t + 1) (h, Ay)
  simp_rw [sparsePredictableWeightTotal_succ]
  change (∫ Ay, sparsePredictableWeightTotal W t h + W t h Ay.1
      ∂(P.kernel t ⊗ₖ feedbackK) h) = _
  rw [ProbabilityTheory.integral_compProd hfinal]
  calc
    (∫ A, ∫ _y, sparsePredictableWeightTotal W t h + W t h A
        ∂feedbackK (h, A) ∂P.kernel t h) =
        ∫ A, sparsePredictableWeightTotal W t h + W t h A
          ∂P.kernel t h := by
      apply integral_congr_ae
      exact ae_of_all _ fun A => by simp
    _ = sparsePredictableWeightTotal W t h +
        ∫ A, W t h A ∂P.kernel t h := by
      have hw : Integrable (fun A => W t h A) (P.kernel t h) := by
        apply Integrable.of_bound
          ((hW t).comp (measurable_const.prodMk measurable_id)).aestronglyMeasurable C
        exact ae_of_all _ fun A => by
          rw [Real.norm_eq_abs]
          exact hWabs t h A
      rw [integral_add (integrable_const _) hw]
      simp

set_option maxHeartbeats 4000000 in
-- The dependent chronological induction expands several nested kernel integrals.
/-- Chronological averaging: every fresh feedback score is replaced by its
exact conditional mean `2/3`, with no independence assumption on actions. -/
theorem integral_sparseObservableWeightedScore_adaptiveLaw
    {n k : Nat} (P : Policy n k) (V : SparseAdaptiveParameters n k)
    (W : SparsePredictableWeight n k)
    (hW : forall t, Measurable (fun hA : History n k t × MSetAction n k =>
      W t hA.1 hA.2)) {C : Real} (hC : 0 <= C)
    (hWabs : forall t h A, |W t h A| <= C) : forall T,
    (∫ h, sparseObservableWeightedScore V W T h
        ∂(sparseAdaptiveProcess P V).law T) =
      (2 / 3 : Real) *
        ∫ h, sparsePredictableWeightTotal W T h
          ∂(sparseAdaptiveProcess P V).law T := by
  intro T
  induction T with
  | zero => simp
  | succ t ih =>
      let mu := (sparseAdaptiveProcess P V).law t
      let kappa := sparseAdaptiveRoundKernel P V t
      letI : IsProbabilityMeasure mu := by dsimp [mu]; infer_instance
      letI : IsFiniteMeasure mu := ⟨by simp⟩
      let hsf : SFinite mu := by infer_instance
      letI : IsMarkovKernel kappa := by
        dsimp [kappa]
        exact sparseAdaptiveRoundKernel_isMarkov P V t
      let hsk : IsSFiniteKernel kappa := by infer_instance
      letI : IsMarkovKernel (P.kernel t) := P.isMarkov t
      have hscoreFinal := integrable_sparseObservableWeightedScore_adaptiveLaw
        (T := t + 1) P V W hW hC hWabs
      have hpredFinal := integrable_sparsePredictableWeightTotal_adaptiveLaw
        (T := t + 1) P V W hW hC hWabs
      have hscorePrev := integrable_sparseObservableWeightedScore_adaptiveLaw
        (T := t) P V W hW hC hWabs
      have hpredPrev := integrable_sparsePredictableWeightTotal_adaptiveLaw
        (T := t) P V W hW hC hWabs
      have hinnerMeas : StronglyMeasurable (fun h : History n k t =>
          ∫ A, W t h A ∂P.kernel t h) :=
        (hW t).stronglyMeasurable.integral_kernel_prod_right'
      have hinnerInt : Integrable (fun h : History n k t =>
          ∫ A, W t h A ∂P.kernel t h) mu := by
        change Integrable (fun h : History n k t =>
          ∫ A, W t h A ∂P.kernel t h)
            ((sparseAdaptiveProcess P V).law t)
        letI : IsProbabilityMeasure
            ((sparseAdaptiveProcess P V).law t) := inferInstance
        apply Integrable.of_bound hinnerMeas.aestronglyMeasurable C
        exact ae_of_all _ fun h => by
          have hb := norm_integral_le_of_norm_le_const
            (μ := P.kernel t h) (f := fun A => W t h A) (C := C)
            (ae_of_all _ fun A => hWabs t h A)
          simpa using hb
      have hscoreFinal' := hscoreFinal
      change Integrable (fun z : History n k t × (MSetAction n k × Real) =>
        sparseObservableWeightedScore V W (t + 1) z) (mu ⊗ₘ kappa)
        at hscoreFinal'
      have hpredFinal' := hpredFinal
      change Integrable (fun z : History n k t × (MSetAction n k × Real) =>
        sparsePredictableWeightTotal W (t + 1) z) (mu ⊗ₘ kappa)
        at hpredFinal'
      have hscoreFubini :
          (∫ z : History n k t × (MSetAction n k × Real),
              sparseObservableWeightedScore V W (t + 1) z ∂mu ⊗ₘ kappa) =
            ∫ h, ∫ Ay, sparseObservableWeightedScore V W (t + 1) (h, Ay)
              ∂kappa h ∂mu :=
        @Measure.integral_compProd
          (History n k t) (MSetAction n k × Real)
          (inferInstanceAs (MeasurableSpace (History n k t)))
          (inferInstanceAs (MeasurableSpace (MSetAction n k × Real)))
          kappa mu hsf hsk Real inferInstance inferInstance _ hscoreFinal'
      have hpredFubini :
          (∫ z : History n k t × (MSetAction n k × Real),
              sparsePredictableWeightTotal W (t + 1) z ∂mu ⊗ₘ kappa) =
            ∫ h, ∫ Ay, sparsePredictableWeightTotal W (t + 1) (h, Ay)
              ∂kappa h ∂mu :=
        @Measure.integral_compProd
          (History n k t) (MSetAction n k × Real)
          (inferInstanceAs (MeasurableSpace (History n k t)))
          (inferInstanceAs (MeasurableSpace (MSetAction n k × Real)))
          kappa mu hsf hsk Real inferInstance inferInstance _ hpredFinal'
      change (∫ z, sparseObservableWeightedScore V W (t + 1) z
          ∂mu ⊗ₘ kappa) =
        (2 / 3 : Real) *
          ∫ z, sparsePredictableWeightTotal W (t + 1) z ∂mu ⊗ₘ kappa
      calc
        (∫ z, sparseObservableWeightedScore V W (t + 1) z
            ∂mu ⊗ₘ kappa) =
            ∫ h, ∫ Ay, sparseObservableWeightedScore V W (t + 1) (h, Ay)
              ∂kappa h ∂mu := hscoreFubini
        _ = ∫ h, (sparseObservableWeightedScore V W t h +
              (2 / 3 : Real) * ∫ A, W t h A ∂P.kernel t h) ∂mu := by
          apply integral_congr_ae
          exact ae_of_all _ fun h =>
            integral_sparseObservableWeightedScore_succ_round
              P V W hW hC hWabs h
        _ = (∫ h, sparseObservableWeightedScore V W t h ∂mu) +
              (2 / 3 : Real) *
                ∫ h, ∫ A, W t h A ∂P.kernel t h ∂mu := by
          rw [integral_add hscorePrev (hinnerInt.const_mul (2 / 3 : Real)),
            integral_const_mul]
        _ = (2 / 3 : Real) *
            ((∫ h, sparsePredictableWeightTotal W t h ∂mu) +
              ∫ h, ∫ A, W t h A ∂P.kernel t h ∂mu) := by
          rw [ih]
          ring
        _ = (2 / 3 : Real) *
            ∫ h, ∫ Ay, sparsePredictableWeightTotal W (t + 1) (h, Ay)
              ∂kappa h ∂mu := by
          congr 1
          rw [← integral_add hpredPrev hinnerInt]
          apply integral_congr_ae
          exact ae_of_all _ fun h =>
            (integral_sparsePredictableWeightTotal_succ_round
              P V W hW hC hWabs h).symm
        _ = (2 / 3 : Real) *
            ∫ z, sparsePredictableWeightTotal W (t + 1) z
              ∂mu ⊗ₘ kappa := by rw [hpredFubini]

/-! ## Coordinate and learner specializations -/

def sparseCoordinatePredictableWeight {n n' k : Nat}
    (hn' : n' <= n) (q c0 : Nat) (U : Nat -> Fin n -> Real)
    (j : Fin n') : SparsePredictableWeight n k := fun t h _A =>
  U (t / q) (sparseSignalCoordinate hn' j) *
    sparseActive q c0 (sparseSignalCoordinate hn' j) t h

def sparseLearnerPredictableWeight {n k : Nat}
    (n' q c0 : Nat) (U : Nat -> Fin n -> Real) :
    SparsePredictableWeight n k := fun t h A =>
  sparseActionScore n' q c0 U t h A

theorem measurable_sparseCoordinatePredictableWeight
    {n n' k q c0 : Nat} (hn' : n' <= n)
    (U : Nat -> Fin n -> Real) (j : Fin n') : forall t,
    Measurable (fun hA : History n k t × MSetAction n k =>
      sparseCoordinatePredictableWeight hn' q c0 U j t hA.1 hA.2) := by
  intro t
  exact measurable_const.mul <|
    (measurable_sparseActive
      (q := q) (c0 := c0) (sparseSignalCoordinate hn' j) t).comp
        measurable_fst

theorem measurable_sparseLearnerPredictableWeight
    {n k n' q c0 : Nat} (U : Nat -> Fin n -> Real) : forall t,
    Measurable (fun hA : History n k t × MSetAction n k =>
      sparseLearnerPredictableWeight n' q c0 U t hA.1 hA.2) := by
  intro t
  have hitem : Measurable (fun h : History n k t => fun i : Fin n =>
      sparseActive q c0 i t h * sparseSignalWeight n' q U t i) := by
    refine Measurable.of_eval fun i => ?_
    exact (measurable_sparseActive i t).mul measurable_const
  exact measurable_actionLoss_joint hitem

theorem sparseCoordinatePredictableWeight_abs_le
    {n n' k q c0 : Nat} (hn' : n' <= n)
    (U : Nat -> Fin n -> Real) (hU : forall b i, |U b i| <= 1)
    (j : Fin n') : forall t (h : History n k t) A,
    |sparseCoordinatePredictableWeight hn' q c0 U j t h A| <= 1 := by
  intro t h A
  unfold sparseCoordinatePredictableWeight
  rw [abs_mul]
  have ha := sparseActive_mem_Icc
    (q := q) (c0 := c0) (sparseSignalCoordinate hn' j) h
  have haabs : |sparseActive q c0 (sparseSignalCoordinate hn' j) t h| <= 1 := by
    rw [abs_of_nonneg ha.1]
    exact ha.2
  exact (mul_le_mul (hU (t / q) (sparseSignalCoordinate hn' j)) haabs
    (abs_nonneg _) (by norm_num)).trans (by norm_num)

theorem sparseLearnerPredictableWeight_abs_le
    {n k n' q c0 : Nat} (U : Nat -> Fin n -> Real)
    (hU : forall b i, |U b i| <= 1) : forall t (h : History n k t) A,
    |sparseLearnerPredictableWeight n' q c0 U t h A| <= (k : Real) := by
  intro t h A
  exact sparseActionScore_abs_le hU t h A

theorem sparseObservableWeightedScore_coordinate_eq
    {n n' k q c0 : Nat} (V : SparseAdaptiveParameters n k)
    (hn' : n' <= n) (U : Nat -> Fin n -> Real) (j : Fin n') :
    forall T (h : History n k T),
      sparseObservableWeightedScore V
          (sparseCoordinatePredictableWeight hn' q c0 U j) T h =
        sparseObservableCoordinateScore V hn' q c0 U j T h := by
  intro T
  induction T with
  | zero => intro h; rfl
  | succ t ih =>
      intro h
      rw [sparseObservableWeightedScore_succ,
        sparseObservableCoordinateScore_succ, ih]
      rfl

theorem sparseObservableWeightedScore_learner_eq
    {n k n' q c0 : Nat} (V : SparseAdaptiveParameters n k)
    (U : Nat -> Fin n -> Real) : forall T (h : History n k T),
      sparseObservableWeightedScore V
          (sparseLearnerPredictableWeight n' q c0 U) T h =
        sparseObservableLearnerScore V n' q c0 U T h := by
  intro T
  induction T with
  | zero => intro h; rfl
  | succ t ih =>
      intro h
      rw [sparseObservableWeightedScore_succ,
        sparseObservableLearnerScore_succ, ih]
      unfold sparseLearnerPredictableWeight
      ring

/-- Conditional chronological identity for one coordinate score. -/
theorem integral_sparseObservableCoordinateScore_adaptiveLaw
    {n n' k q c0 : Nat} (P : Policy n k)
    (V : SparseAdaptiveParameters n k) (hn' : n' <= n)
    (U : Nat -> Fin n -> Real) (hU : forall b i, |U b i| <= 1)
    (j : Fin n') (T : Nat) :
    (∫ h, sparseObservableCoordinateScore V hn' q c0 U j T h
        ∂(sparseAdaptiveProcess P V).law T) =
      (2 / 3 : Real) *
        ∫ h, sparsePredictableWeightTotal
            (sparseCoordinatePredictableWeight hn' q c0 U j) T h
          ∂(sparseAdaptiveProcess P V).law T := by
  rw [← integral_sparseObservableWeightedScore_adaptiveLaw
    P V (sparseCoordinatePredictableWeight hn' q c0 U j)
      (measurable_sparseCoordinatePredictableWeight hn' U j)
      (by norm_num : (0 : Real) <= 1)
      (sparseCoordinatePredictableWeight_abs_le hn' U hU j) T]
  apply integral_congr_ae
  exact ae_of_all _ fun h =>
    (sparseObservableWeightedScore_coordinate_eq V hn' U j T h).symm

/-- Conditional chronological identity for the learner score. -/
theorem integral_sparseObservableLearnerScore_adaptiveLaw
    {n k n' q c0 : Nat} (P : Policy n k)
    (V : SparseAdaptiveParameters n k) (U : Nat -> Fin n -> Real)
    (hU : forall b i, |U b i| <= 1) (T : Nat) :
    (∫ h, sparseObservableLearnerScore V n' q c0 U T h
        ∂(sparseAdaptiveProcess P V).law T) =
      (2 / 3 : Real) *
        ∫ h, sparsePredictableWeightTotal
            (sparseLearnerPredictableWeight n' q c0 U) T h
          ∂(sparseAdaptiveProcess P V).law T := by
  rw [← integral_sparseObservableWeightedScore_adaptiveLaw
    P V (sparseLearnerPredictableWeight n' q c0 U)
      (measurable_sparseLearnerPredictableWeight U)
      (Nat.cast_nonneg k) (sparseLearnerPredictableWeight_abs_le U hU) T]
  apply integral_congr_ae
  exact ae_of_all _ fun h =>
    (sparseObservableWeightedScore_learner_eq V U T h).symm

/-! ## Fixed-block predictable counts -/

/-- Number of rounds in a fixed block during which one signal coordinate is
active.  Unlike the learner pull count, this does not require selection by
the learner. -/
def sparseObservableCellActiveCount {n n' k : Nat}
    (hn' : n' <= n) (q c0 b : Nat) (j : Fin n') :
    (T : Nat) -> History n k T -> Real
  | 0, _ => 0
  | t + 1, h =>
      sparseObservableCellActiveCount hn' q c0 b j t h.1 +
        if t / q = b then
          sparseActive q c0 (sparseSignalCoordinate hn' j) t h.1
        else 0

@[simp] theorem sparseObservableCellActiveCount_zero
    {n n' k q c0 b : Nat} (hn' : n' <= n) (j : Fin n')
    (h : History n k 0) :
    sparseObservableCellActiveCount hn' q c0 b j 0 h = 0 := rfl

@[simp] theorem sparseObservableCellActiveCount_succ
    {n n' k q c0 b t : Nat} (hn' : n' <= n) (j : Fin n')
    (h : History n k (t + 1)) :
    sparseObservableCellActiveCount hn' q c0 b j (t + 1) h =
      sparseObservableCellActiveCount hn' q c0 b j t h.1 +
        if t / q = b then
          sparseActive q c0 (sparseSignalCoordinate hn' j) t h.1
        else 0 := rfl

theorem measurable_sparseObservableCellActiveCount
    {n n' k q c0 b : Nat} (hn' : n' <= n) (j : Fin n') : forall T,
    Measurable (sparseObservableCellActiveCount
      (k := k) hn' q c0 b j T) := by
  intro T
  induction T with
  | zero => exact measurable_const
  | succ t ih =>
      rw [show sparseObservableCellActiveCount hn' q c0 b j (t + 1) =
          fun h => sparseObservableCellActiveCount hn' q c0 b j t h.1 +
            if t / q = b then
              sparseActive q c0 (sparseSignalCoordinate hn' j) t h.1
            else 0 by rfl]
      apply (ih.comp measurable_fst).add
      by_cases htb : t / q = b
      · simp only [if_pos htb]
        exact (measurable_sparseActive
          (q := q) (c0 := c0) (sparseSignalCoordinate hn' j) t).comp
            measurable_fst
      · simp only [if_neg htb]
        exact measurable_const

theorem sparseObservableCellActiveCount_nonneg
    {n n' k q c0 : Nat} (hn' : n' <= n) (b : Nat) (j : Fin n') :
    forall T (h : History n k T),
      0 <= sparseObservableCellActiveCount hn' q c0 b j T h := by
  intro T
  induction T with
  | zero => intro h; simp
  | succ t ih =>
      intro h
      rw [sparseObservableCellActiveCount_succ]
      apply add_nonneg (ih h.1)
      split_ifs
      · exact (sparseActive_mem_Icc
          (q := q) (c0 := c0) (sparseSignalCoordinate hn' j) h.1).1
      · norm_num

/-- A block contains at most `q` active rounds.  The strengthened invariant
also records the number of elapsed rounds while the block is current. -/
theorem sparseObservableCellActiveCount_invariant
    {n n' k q c0 : Nat} (hq : 0 < q) (hn' : n' <= n)
    (b : Nat) (j : Fin n') : forall T (h : History n k T),
    sparseObservableCellActiveCount hn' q c0 b j T h <= (q : Real) ∧
      (T / q = b ->
        sparseObservableCellActiveCount hn' q c0 b j T h <=
          (T % q : Nat)) ∧
      (T / q < b ->
        sparseObservableCellActiveCount hn' q c0 b j T h = 0) := by
  intro T
  induction T with
  | zero =>
      intro h
      constructor
      · simp
      constructor
      · intro _; simp
      · intro _; simp
  | succ t ih =>
      intro h
      have hp := ih h.1
      have ha := sparseActive_mem_Icc
        (q := q) (c0 := c0) (sparseSignalCoordinate hn' j) h.1
      have hmono : t / q <= (t + 1) / q :=
        Nat.div_le_div_right (by omega)
      by_cases htb : t / q = b
      · rw [sparseObservableCellActiveCount_succ, if_pos htb]
        have htmod : t % q < q := Nat.mod_lt t hq
        have htmodR : (((t % q : Nat) : Real) + 1) <= (q : Real) := by
          exact_mod_cast (Nat.succ_le_iff.mpr htmod)
        constructor
        · have hpcur := hp.2.1 htb
          linarith [hpcur, ha.2, htmodR]
        constructor
        · intro hnext
          have htEq := Nat.mod_add_div t q
          have hsEq := Nat.mod_add_div (t + 1) q
          rw [htb] at htEq
          rw [hnext] at hsEq
          have hmodSucc : (t + 1) % q = t % q + 1 := by omega
          have hmodSuccR : (((t + 1) % q : Nat) : Real) =
              ((t % q : Nat) : Real) + 1 := by exact_mod_cast hmodSucc
          rw [hmodSuccR]
          have hpcur := hp.2.1 htb
          linarith [hpcur, ha.2]
        · intro hless
          omega
      · rw [sparseObservableCellActiveCount_succ, if_neg htb, add_zero]
        constructor
        · exact hp.1
        constructor
        · intro hnext
          have hprevLess : t / q < b := by omega
          rw [hp.2.2 hprevLess]
          exact Nat.cast_nonneg _
        · intro hless
          exact hp.2.2 (by omega)

theorem sparseObservableCellActiveCount_mem_Icc
    {n n' k q c0 T : Nat} (hq : 0 < q) (hn' : n' <= n)
    (b : Nat) (j : Fin n') (h : History n k T) :
    sparseObservableCellActiveCount hn' q c0 b j T h ∈
      Icc (0 : Real) q :=
  ⟨sparseObservableCellActiveCount_nonneg hn' b j T h,
    (sparseObservableCellActiveCount_invariant hq hn' b j T h).1⟩

/-- The predictable coordinate weight is the sum of the hidden cell value
times its fixed-block active count. -/
theorem sparsePredictableWeightTotal_coordinate_eq_cellSum
    {B n n' k q c0 : Nat} (hq : 0 < q) (hn' : n' <= n)
    (U : Nat -> Fin n -> Real) (j : Fin n') : forall T,
    T <= B * q -> forall h : History n k T,
    sparsePredictableWeightTotal
        (sparseCoordinatePredictableWeight hn' q c0 U j) T h =
      ∑ b : Fin B,
        U b.1 (sparseSignalCoordinate hn' j) *
          sparseObservableCellActiveCount hn' q c0 b.1 j T h := by
  intro T
  induction T with
  | zero => intro hT h; simp
  | succ t ih =>
      intro hT h
      have ht : t < B * q := lt_of_lt_of_le (by omega) hT
      have hb : t / q < B := (Nat.div_lt_iff_lt_mul hq).2 ht
      let bt : Fin B := ⟨t / q, hb⟩
      rw [sparsePredictableWeightTotal_succ,
        ih (by omega : t <= B * q) h.1]
      simp_rw [sparseObservableCellActiveCount_succ, mul_add,
        Finset.sum_add_distrib]
      congr 1
      unfold sparseCoordinatePredictableWeight
      symm
      refine (Fintype.sum_eq_single bt ?_).trans ?_
      · intro b hne
        have hneq : t / q ≠ b.1 := by
          intro heq
          apply hne
          apply Fin.ext
          exact heq.symm
        simp [hneq]
      · simp [bt]

/-- The learner's one-round predictable score is exactly the sum of hidden
signal weights times the active pull indicators. -/
theorem sparseActionScore_eq_sum_signalPull
    {n n' k q c0 : Nat} (hn' : n' <= n)
    (U : Nat -> Fin n -> Real) (t : Nat) (h : History n k t)
    (A : MSetAction n k) :
    sparseActionScore n' q c0 U t h A =
      ∑ j : Fin n',
        U (t / q) (sparseSignalCoordinate hn' j) *
          sparsePullIndicator hn' q c0 j t h A := by
  classical
  let S : Finset (Fin n) := Finset.univ.filter fun i => i.1 < n'
  have hS : S = Finset.univ.map
      ⟨sparseSignalCoordinate hn', sparseSignalCoordinate_injective hn'⟩ := by
    ext i
    constructor
    · intro hi
      have hi' : i.1 < n' := (Finset.mem_filter.mp hi).2
      have heq : sparseSignalCoordinate hn' (⟨i.1, hi'⟩ : Fin n') = i :=
        Fin.ext rfl
      rw [Finset.mem_map]
      exact ⟨⟨i.1, hi'⟩, Finset.mem_univ _, heq⟩
    · intro hi
      rw [Finset.mem_map] at hi
      rcases hi with ⟨j, _hj, rfl⟩
      simp [S, sparseSignalCoordinate]
  rw [sparseActionScore, actionLoss_eq_finset_sum]
  calc
    (∑ i ∈ A.1,
        sparseActive q c0 i t h * sparseSignalWeight n' q U t i) =
        ∑ i ∈ S,
          U (t / q) i * sparseActive q c0 i t h *
            History.selectedIndicator i A := by
      calc
        (∑ i ∈ A.1,
            sparseActive q c0 i t h * sparseSignalWeight n' q U t i) =
            ∑ i ∈ A.1.filter (fun i => i.1 < n'),
              sparseActive q c0 i t h * U (t / q) i := by
          rw [Finset.sum_filter]
          apply Finset.sum_congr rfl
          intro i hi
          by_cases hip : i.1 < n'
          · simp [sparseSignalWeight, hip]
          · simp [sparseSignalWeight, hip]
        _ = ∑ i ∈ S.filter (fun i => i ∈ A.1),
              U (t / q) i * sparseActive q c0 i t h := by
          have hfilter : A.1.filter (fun i => i.1 < n') =
              S.filter (fun i => i ∈ A.1) := by
            ext i
            simp [S, and_comm]
          rw [hfilter]
          apply Finset.sum_congr rfl
          intro i hi
          ring
        _ = ∑ i ∈ S,
              U (t / q) i * sparseActive q c0 i t h *
                History.selectedIndicator i A := by
          rw [Finset.sum_filter]
          apply Finset.sum_congr rfl
          intro i hi
          by_cases hia : i ∈ A.1
          · simp [History.selectedIndicator, hia]
          · simp [History.selectedIndicator, hia]
    _ = ∑ j : Fin n',
          U (t / q) (sparseSignalCoordinate hn' j) *
            sparseActive q c0 (sparseSignalCoordinate hn' j) t h *
              History.selectedIndicator (sparseSignalCoordinate hn' j) A := by
      rw [hS, Finset.sum_map]
      rfl
    _ = ∑ j : Fin n',
        U (t / q) (sparseSignalCoordinate hn' j) *
          sparsePullIndicator hn' q c0 j t h A := by
      apply Finset.sum_congr rfl
      intro j _hj
      unfold sparsePullIndicator
      ring

/-- The learner predictable total decomposes over all block--signal cells,
with the literal capped pull count from `ScoreBiasFullTable`. -/
theorem sparsePredictableWeightTotal_learner_eq_cellSum
    {B n n' k q c0 : Nat} (hq : 0 < q) (hn' : n' <= n)
    (U : Nat -> Fin n -> Real) : forall T,
    T <= B * q -> forall h : History n k T,
    sparsePredictableWeightTotal
        (sparseLearnerPredictableWeight n' q c0 U) T h =
      ∑ b : Fin B, ∑ j : Fin n',
        U b.1 (sparseSignalCoordinate hn' j) *
          sparseObservableCellPullCount hn' q c0 b.1 j T h := by
  intro T
  induction T with
  | zero => intro hT h; simp
  | succ t ih =>
      intro hT h
      have ht : t < B * q := lt_of_lt_of_le (by omega) hT
      have hb : t / q < B := (Nat.div_lt_iff_lt_mul hq).2 ht
      let bt : Fin B := ⟨t / q, hb⟩
      rw [sparsePredictableWeightTotal_succ,
        ih (by omega : t <= B * q) h.1]
      unfold sparseLearnerPredictableWeight
      rw [sparseActionScore_eq_sum_signalPull hn' U t h.1 h.2.1]
      simp_rw [sparseObservableCellPullCount_succ, mul_add,
        Finset.sum_add_distrib]
      congr 1
      symm
      refine (Fintype.sum_eq_single bt ?_).trans ?_
      · intro b hne
        have hneq : t / q ≠ b.1 := by
          intro heq
          apply hne
          apply Fin.ext
          exact heq.symm
        simp [hneq]
      · simp [bt]

/-! ## Full-table cell sums and chronological identities -/

def sparseHiddenTableCoordinateCellSum
    {B n n' k : Nat} (hn' : n' <= n) (q c0 : Nat) (j : Fin n')
    (T : Nat) (z : SparseHiddenTable B n × History n k T) : Real :=
  ∑ b : Fin B,
    sparseHiddenTableU z.1 b.1 (sparseSignalCoordinate hn' j) *
      sparseObservableCellActiveCount hn' q c0 b.1 j T z.2

def sparseHiddenTableLearnerCellSum
    {B n n' k : Nat} (hn' : n' <= n) (q c0 : Nat)
    (T : Nat) (z : SparseHiddenTable B n × History n k T) : Real :=
  ∑ b : Fin B, ∑ j : Fin n',
    sparseHiddenTableU z.1 b.1 (sparseSignalCoordinate hn' j) *
      sparseObservableCellPullCount hn' q c0 b.1 j T z.2

theorem measurable_sparseHiddenTableCoordinateCellSum
    {B n n' k q c0 T : Nat} (hn' : n' <= n) (j : Fin n') :
    Measurable (sparseHiddenTableCoordinateCellSum
      (B := B) (k := k) hn' q c0 j T) := by
  unfold sparseHiddenTableCoordinateCellSum
  exact Finset.measurable_sum _ fun b _ =>
    ((measurable_sparseHiddenTableU B n b.1
      (sparseSignalCoordinate hn' j)).comp measurable_fst).mul <|
        (measurable_sparseObservableCellActiveCount
          (q := q) (c0 := c0) hn' j T).comp measurable_snd

theorem measurable_sparseHiddenTableLearnerCellSum
    {B n n' k q c0 T : Nat} (hn' : n' <= n) :
    Measurable (sparseHiddenTableLearnerCellSum
      (B := B) (k := k) hn' q c0 T) := by
  unfold sparseHiddenTableLearnerCellSum
  exact Finset.measurable_sum _ fun b _ =>
    Finset.measurable_sum _ fun j _ =>
      ((measurable_sparseHiddenTableU B n b.1
        (sparseSignalCoordinate hn' j)).comp measurable_fst).mul <|
          (measurable_sparseObservableCellPullCount
            (q := q) (c0 := c0) hn' j T).comp measurable_snd

theorem sparseHiddenTableCoordinateCellSum_abs_le
    {B n n' k q c0 T : Nat} (hq : 0 < q) (hn' : n' <= n)
    (j : Fin n') (z : SparseHiddenTable B n × History n k T) :
    |sparseHiddenTableCoordinateCellSum hn' q c0 j T z| <=
      (B : Real) * q := by
  unfold sparseHiddenTableCoordinateCellSum
  calc
    |∑ b : Fin B,
        sparseHiddenTableU z.1 b.1 (sparseSignalCoordinate hn' j) *
          sparseObservableCellActiveCount hn' q c0 b.1 j T z.2| <=
        ∑ b : Fin B,
          |sparseHiddenTableU z.1 b.1 (sparseSignalCoordinate hn' j) *
            sparseObservableCellActiveCount hn' q c0 b.1 j T z.2| :=
      Finset.abs_sum_le_sum_abs _ _
    _ <= ∑ _b : Fin B, (q : Real) := by
      apply Finset.sum_le_sum
      intro b _hb
      rw [abs_mul, abs_of_nonneg
        (sparseObservableCellActiveCount_nonneg hn' b.1 j T z.2)]
      exact (mul_le_mul
        (sparseHiddenTableU_abs_le_one z.1 b.1
          (sparseSignalCoordinate hn' j))
        (sparseObservableCellActiveCount_invariant hq hn' b.1 j T z.2).1
        (sparseObservableCellActiveCount_nonneg hn' b.1 j T z.2)
        (by norm_num)).trans (by simp)
    _ = (B : Real) * q := by simp

theorem sparseHiddenTableLearnerCellSum_abs_le
    {B n n' k q c0 T : Nat} (hn' : n' <= n)
    (z : SparseHiddenTable B n × History n k T) :
    |sparseHiddenTableLearnerCellSum hn' q c0 T z| <=
      (B : Real) * (n' : Real) * c0 := by
  unfold sparseHiddenTableLearnerCellSum
  calc
    |∑ b : Fin B, ∑ j : Fin n',
        sparseHiddenTableU z.1 b.1 (sparseSignalCoordinate hn' j) *
          sparseObservableCellPullCount hn' q c0 b.1 j T z.2| <=
        ∑ b : Fin B, |∑ j : Fin n',
          sparseHiddenTableU z.1 b.1 (sparseSignalCoordinate hn' j) *
            sparseObservableCellPullCount hn' q c0 b.1 j T z.2| :=
      Finset.abs_sum_le_sum_abs _ _
    _ <= ∑ b : Fin B, ∑ j : Fin n',
        |sparseHiddenTableU z.1 b.1 (sparseSignalCoordinate hn' j) *
          sparseObservableCellPullCount hn' q c0 b.1 j T z.2| := by
      apply Finset.sum_le_sum
      intro b _hb
      exact Finset.abs_sum_le_sum_abs _ _
    _ <= ∑ _b : Fin B, ∑ _j : Fin n', (c0 : Real) := by
      apply Finset.sum_le_sum
      intro b _hb
      apply Finset.sum_le_sum
      intro j _hj
      rw [abs_mul, abs_of_nonneg
        (sparseObservableCellPullCount_nonneg hn' j T z.2)]
      exact (mul_le_mul
        (sparseHiddenTableU_abs_le_one z.1 b.1
          (sparseSignalCoordinate hn' j))
        (sparseObservableCellPullCount_le hn' b.1 j T z.2)
        (sparseObservableCellPullCount_nonneg hn' j T z.2)
        (by norm_num)).trans (by simp)
    _ = (B : Real) * (n' : Real) * c0 := by simp; ring

theorem integrable_sparseHiddenTableCoordinateScore_jointLaw
    {B n n' k q c0 T : Nat} (P : Policy n k) (hk : 1 <= k)
    (eta : Real) (heta0 : 0 <= eta) (heta : eta <= (1 : Real) / 16)
    (hn' : n' <= n) (j : Fin n') :
    let F := sparseHiddenTableParameterFamily (n := n) hk eta heta0 heta n' q c0 B
    Integrable (fun z : SparseHiddenTable B n × History n k T =>
      sparseObservableCoordinateScore (F.at z.1) hn' q c0
        (sparseHiddenTableU z.1) j T z.2)
      (sparseJointLaw (sparseHiddenTableMeasure B n) P F T) := by
  dsimp only
  let F := sparseHiddenTableParameterFamily (n := n) hk eta heta0 heta n' q c0 B
  let joint := sparseJointLaw (sparseHiddenTableMeasure B n) P F T
  letI : IsProbabilityMeasure joint := by
    dsimp [joint]
    unfold sparseJointLaw
    infer_instance
  apply Integrable.of_bound
    (measurable_sparseFamilyObservableCoordinateScore F sparseHiddenTableU
      (fun b i => measurable_sparseHiddenTableU B n b i)
      hn' q c0 j T).aestronglyMeasurable (T : Real)
  filter_upwards [ae_sparseJointLaw_history_support
    (sparseHiddenTableMeasure B n) P F T] with z hsupp
  simpa only [Real.norm_eq_abs, joint] using
    sparseObservableCoordinateScore_abs_le (F.at z.1) hn'
      (sparseHiddenTableU z.1) (sparseHiddenTableU_abs_le_one z.1)
      j T z.2 hsupp

theorem integrable_sparseHiddenTableLearnerScore_jointLaw
    {B n n' k q c0 T : Nat} (P : Policy n k) (hk : 1 <= k)
    (eta : Real) (heta0 : 0 <= eta) (heta : eta <= (1 : Real) / 16) :
    let F := sparseHiddenTableParameterFamily (n := n) hk eta heta0 heta n' q c0 B
    Integrable (fun z : SparseHiddenTable B n × History n k T =>
      sparseObservableLearnerScore (F.at z.1) n' q c0
        (sparseHiddenTableU z.1) T z.2)
      (sparseJointLaw (sparseHiddenTableMeasure B n) P F T) := by
  dsimp only
  let F := sparseHiddenTableParameterFamily (n := n) hk eta heta0 heta n' q c0 B
  let joint := sparseJointLaw (sparseHiddenTableMeasure B n) P F T
  letI : IsProbabilityMeasure joint := by
    dsimp [joint]
    unfold sparseJointLaw
    infer_instance
  apply Integrable.of_bound
    (measurable_sparseFamilyObservableLearnerScore F sparseHiddenTableU
      (fun b i => measurable_sparseHiddenTableU B n b i)
      n' q c0 T).aestronglyMeasurable ((k : Real) * T)
  filter_upwards [ae_sparseJointLaw_history_support
    (sparseHiddenTableMeasure B n) P F T] with z hsupp
  simpa only [Real.norm_eq_abs, joint] using
    sparseObservableLearnerScore_abs_le hk (F.at z.1)
      (sparseHiddenTableU z.1) (sparseHiddenTableU_abs_le_one z.1)
      T z.2 hsupp

theorem integrable_sparseHiddenTableCoordinateCellSum_jointLaw
    {B n n' k q c0 T : Nat} (P : Policy n k) (hk : 1 <= k)
    (eta : Real) (heta0 : 0 <= eta) (heta : eta <= (1 : Real) / 16)
    (hq : 0 < q) (hn' : n' <= n) (j : Fin n') :
    let F := sparseHiddenTableParameterFamily (n := n) hk eta heta0 heta n' q c0 B
    Integrable (sparseHiddenTableCoordinateCellSum
      (B := B) (k := k) hn' q c0 j T)
      (sparseJointLaw (sparseHiddenTableMeasure B n) P F T) := by
  dsimp only
  let joint := sparseJointLaw (sparseHiddenTableMeasure B n) P
    (sparseHiddenTableParameterFamily hk eta heta0 heta n' q c0 B) T
  letI : IsProbabilityMeasure joint := by
    dsimp [joint]
    unfold sparseJointLaw
    infer_instance
  apply Integrable.of_bound
    (measurable_sparseHiddenTableCoordinateCellSum
      (B := B) (k := k) hn' j).aestronglyMeasurable ((B : Real) * q)
  exact ae_of_all _ fun z => by
    rw [Real.norm_eq_abs]
    exact sparseHiddenTableCoordinateCellSum_abs_le hq hn' j z

theorem integrable_sparseHiddenTableLearnerCellSum_jointLaw
    {B n n' k q c0 T : Nat} (P : Policy n k) (hk : 1 <= k)
    (eta : Real) (heta0 : 0 <= eta) (heta : eta <= (1 : Real) / 16)
    (hn' : n' <= n) :
    let F := sparseHiddenTableParameterFamily (n := n) hk eta heta0 heta n' q c0 B
    Integrable (sparseHiddenTableLearnerCellSum
      (B := B) (k := k) hn' q c0 T)
      (sparseJointLaw (sparseHiddenTableMeasure B n) P F T) := by
  dsimp only
  let joint := sparseJointLaw (sparseHiddenTableMeasure B n) P
    (sparseHiddenTableParameterFamily hk eta heta0 heta n' q c0 B) T
  letI : IsProbabilityMeasure joint := by
    dsimp [joint]
    unfold sparseJointLaw
    infer_instance
  apply Integrable.of_bound
    (measurable_sparseHiddenTableLearnerCellSum
      (B := B) (k := k) hn').aestronglyMeasurable
      ((B : Real) * (n' : Real) * c0)
  exact ae_of_all _ fun z => by
    rw [Real.norm_eq_abs]
    exact sparseHiddenTableLearnerCellSum_abs_le hn' z

/-- Joint-law chronological identity for one coordinate, already rewritten
as its literal sum of fixed-block cell counts. -/
theorem integral_sparseHiddenTableCoordinateScore_eq_cellSum
    {B n n' k q c0 T : Nat} (P : Policy n k) (hk : 1 <= k)
    (eta : Real) (heta0 : 0 <= eta) (heta : eta <= (1 : Real) / 16)
    (hq : 0 < q) (hn' : n' <= n) (hT : T <= B * q) (j : Fin n') :
    let F := sparseHiddenTableParameterFamily (n := n) hk eta heta0 heta n' q c0 B
    (∫ z, sparseObservableCoordinateScore (F.at z.1) hn' q c0
        (sparseHiddenTableU z.1) j T z.2
      ∂sparseJointLaw (sparseHiddenTableMeasure B n) P F T) =
      (2 / 3 : Real) *
        ∫ z, sparseHiddenTableCoordinateCellSum hn' q c0 j T z
          ∂sparseJointLaw (sparseHiddenTableMeasure B n) P F T := by
  dsimp only
  let F := sparseHiddenTableParameterFamily (n := n) hk eta heta0 heta n' q c0 B
  have hscore := integrable_sparseHiddenTableCoordinateScore_jointLaw
    (B := B) (q := q) (c0 := c0) (T := T)
      P hk eta heta0 heta hn' j
  have hcell := integrable_sparseHiddenTableCoordinateCellSum_jointLaw
    (B := B) (q := q) (c0 := c0) (T := T)
      P hk eta heta0 heta hq hn' j
  unfold sparseJointLaw at hscore hcell ⊢
  rw [Measure.integral_compProd hscore, Measure.integral_compProd hcell]
  calc
    (∫ table, ∫ h,
        sparseObservableCoordinateScore (F.at table) hn' q c0
          (sparseHiddenTableU table) j T h
        ∂sparseFamilyLawKernel P F T table
      ∂sparseHiddenTableMeasure B n) =
      ∫ table, (2 / 3 : Real) *
        ∫ h, sparseHiddenTableCoordinateCellSum hn' q c0 j T (table, h)
          ∂sparseFamilyLawKernel P F T table
        ∂sparseHiddenTableMeasure B n := by
      apply integral_congr_ae
      exact ae_of_all _ fun table => by
        simp only [sparseFamilyLawKernel_apply]
        rw [integral_sparseObservableCoordinateScore_adaptiveLaw
          P (F.at table) hn' (sparseHiddenTableU table)
            (sparseHiddenTableU_abs_le_one table) j T]
        congr 1
        apply integral_congr_ae
        exact ae_of_all _ fun h => by
          unfold sparseHiddenTableCoordinateCellSum
          exact sparsePredictableWeightTotal_coordinate_eq_cellSum
            hq hn' (sparseHiddenTableU table) j T hT h
    _ = (2 / 3 : Real) *
        ∫ table, ∫ h,
          sparseHiddenTableCoordinateCellSum hn' q c0 j T (table, h)
            ∂sparseFamilyLawKernel P F T table
          ∂sparseHiddenTableMeasure B n := integral_const_mul _ _

/-- Joint-law chronological identity for the learner score, rewritten as
the double sum of capped cell pull counts. -/
theorem integral_sparseHiddenTableLearnerScore_eq_cellSum
    {B n n' k q c0 T : Nat} (P : Policy n k) (hk : 1 <= k)
    (eta : Real) (heta0 : 0 <= eta) (heta : eta <= (1 : Real) / 16)
    (hq : 0 < q) (hn' : n' <= n) (hT : T <= B * q) :
    let F := sparseHiddenTableParameterFamily (n := n) hk eta heta0 heta n' q c0 B
    (∫ z, sparseObservableLearnerScore (F.at z.1) n' q c0
        (sparseHiddenTableU z.1) T z.2
      ∂sparseJointLaw (sparseHiddenTableMeasure B n) P F T) =
      (2 / 3 : Real) *
        ∫ z, sparseHiddenTableLearnerCellSum hn' q c0 T z
          ∂sparseJointLaw (sparseHiddenTableMeasure B n) P F T := by
  dsimp only
  let F := sparseHiddenTableParameterFamily (n := n) hk eta heta0 heta n' q c0 B
  have hscore := integrable_sparseHiddenTableLearnerScore_jointLaw
    (B := B) (T := T) (n' := n') (q := q) (c0 := c0)
      P hk eta heta0 heta
  have hcell := integrable_sparseHiddenTableLearnerCellSum_jointLaw
    (B := B) (q := q) (c0 := c0) (T := T)
      P hk eta heta0 heta hn'
  unfold sparseJointLaw at hscore hcell ⊢
  rw [Measure.integral_compProd hscore, Measure.integral_compProd hcell]
  calc
    (∫ table, ∫ h,
        sparseObservableLearnerScore (F.at table) n' q c0
          (sparseHiddenTableU table) T h
        ∂sparseFamilyLawKernel P F T table
      ∂sparseHiddenTableMeasure B n) =
      ∫ table, (2 / 3 : Real) *
        ∫ h, sparseHiddenTableLearnerCellSum hn' q c0 T (table, h)
          ∂sparseFamilyLawKernel P F T table
        ∂sparseHiddenTableMeasure B n := by
      apply integral_congr_ae
      exact ae_of_all _ fun table => by
        simp only [sparseFamilyLawKernel_apply]
        rw [integral_sparseObservableLearnerScore_adaptiveLaw
          P (F.at table) (sparseHiddenTableU table)
            (sparseHiddenTableU_abs_le_one table) T]
        congr 1
        apply integral_congr_ae
        exact ae_of_all _ fun h => by
          unfold sparseHiddenTableLearnerCellSum
          exact sparsePredictableWeightTotal_learner_eq_cellSum
            hq hn' (sparseHiddenTableU table) T hT h
    _ = (2 / 3 : Real) *
        ∫ table, ∫ h,
          sparseHiddenTableLearnerCellSum hn' q c0 T (table, h)
            ∂sparseFamilyLawKernel P F T table
          ∂sparseHiddenTableMeasure B n := integral_const_mul _ _

/-! ## Cellwise integral bounds -/

theorem integrable_sparseHiddenTableCellActiveTerm_jointLaw
    {B n n' k q c0 T : Nat} (P : Policy n k) (hk : 1 <= k)
    (eta : Real) (heta0 : 0 <= eta) (heta : eta <= (1 : Real) / 16)
    (hq : 0 < q) (hn' : n' <= n) (b : Fin B) (j : Fin n') :
    let F := sparseHiddenTableParameterFamily (n := n)
      hk eta heta0 heta n' q c0 B
    Integrable (fun z : SparseHiddenTable B n × History n k T =>
      sparseHiddenTableU z.1 b.1 (sparseSignalCoordinate hn' j) *
        sparseObservableCellActiveCount hn' q c0 b.1 j T z.2)
      (sparseJointLaw (sparseHiddenTableMeasure B n) P F T) := by
  dsimp only
  let joint := sparseJointLaw (sparseHiddenTableMeasure B n) P
    (sparseHiddenTableParameterFamily (n := n)
      hk eta heta0 heta n' q c0 B) T
  letI : IsProbabilityMeasure joint := by
    dsimp [joint]
    unfold sparseJointLaw
    infer_instance
  apply Integrable.of_bound
    ((((measurable_sparseHiddenTableU B n b.1
      (sparseSignalCoordinate hn' j)).comp measurable_fst).mul <|
        (measurable_sparseObservableCellActiveCount
          (q := q) (c0 := c0) hn' j T).comp measurable_snd).aestronglyMeasurable)
      (q : Real)
  exact ae_of_all _ fun z => by
    change |sparseHiddenTableU z.1 b.1 (sparseSignalCoordinate hn' j) *
      sparseObservableCellActiveCount hn' q c0 b.1 j T z.2| <= (q : Real)
    rw [abs_mul, abs_of_nonneg
      (sparseObservableCellActiveCount_nonneg hn' b.1 j T z.2)]
    exact (mul_le_mul
      (sparseHiddenTableU_abs_le_one z.1 b.1
        (sparseSignalCoordinate hn' j))
      (sparseObservableCellActiveCount_invariant hq hn' b.1 j T z.2).1
      (sparseObservableCellActiveCount_nonneg hn' b.1 j T z.2)
      (by norm_num)).trans (by simp)

theorem integrable_sparseHiddenTableCellPullTerm_jointLaw
    {B n n' k q c0 T : Nat} (P : Policy n k) (hk : 1 <= k)
    (eta : Real) (heta0 : 0 <= eta) (heta : eta <= (1 : Real) / 16)
    (hn' : n' <= n) (b : Fin B) (j : Fin n') :
    let F := sparseHiddenTableParameterFamily (n := n)
      hk eta heta0 heta n' q c0 B
    Integrable (fun z : SparseHiddenTable B n × History n k T =>
      sparseHiddenTableU z.1 b.1 (sparseSignalCoordinate hn' j) *
        sparseObservableCellPullCount hn' q c0 b.1 j T z.2)
      (sparseJointLaw (sparseHiddenTableMeasure B n) P F T) := by
  dsimp only
  let joint := sparseJointLaw (sparseHiddenTableMeasure B n) P
    (sparseHiddenTableParameterFamily (n := n)
      hk eta heta0 heta n' q c0 B) T
  letI : IsProbabilityMeasure joint := by
    dsimp [joint]
    unfold sparseJointLaw
    infer_instance
  apply Integrable.of_bound
    ((((measurable_sparseHiddenTableU B n b.1
      (sparseSignalCoordinate hn' j)).comp measurable_fst).mul <|
        (measurable_sparseObservableCellPullCount
          (q := q) (c0 := c0) hn' j T).comp measurable_snd).aestronglyMeasurable)
      (c0 : Real)
  exact ae_of_all _ fun z => by
    change |sparseHiddenTableU z.1 b.1 (sparseSignalCoordinate hn' j) *
      sparseObservableCellPullCount hn' q c0 b.1 j T z.2| <= (c0 : Real)
    rw [abs_mul, abs_of_nonneg
      (sparseObservableCellPullCount_nonneg hn' j T z.2)]
    exact (mul_le_mul
      (sparseHiddenTableU_abs_le_one z.1 b.1
        (sparseSignalCoordinate hn' j))
      (sparseObservableCellPullCount_le hn' b.1 j T z.2)
      (sparseObservableCellPullCount_nonneg hn' j T z.2)
      (by norm_num)).trans (by simp)

/-- Absolute integral bound for the coordinate cell sum, obtained from the
literal full-table sign pairing independently in every block. -/
theorem integral_sparseHiddenTableCoordinateCellSum_abs_le
    {B n n' k q c0 T : Nat} (P : Policy n k) (hk : 1 <= k)
    (eta : Real) (heta0 : 0 <= eta) (heta : eta <= (1 : Real) / 16)
    (hq : 0 < q) (hn' : n' <= n) (_hT : T <= B * q)
    (j : Fin n') {rho : Real} (hrho : 0 <= rho)
    (hrhoeq : rho = eta ^ 2 * (c0 : Real) / (k : Real) ^ 2) :
    let F := sparseHiddenTableParameterFamily (n := n)
      hk eta heta0 heta n' q c0 B
    |∫ z, sparseHiddenTableCoordinateCellSum hn' q c0 j T z
        ∂sparseJointLaw (sparseHiddenTableMeasure B n) P F T| <=
      8 * (B : Real) * q * Real.sqrt rho := by
  classical
  dsimp only
  let F := sparseHiddenTableParameterFamily (n := n)
    hk eta heta0 heta n' q c0 B
  let joint := sparseJointLaw (sparseHiddenTableMeasure B n) P F T
  have hterm : forall b : Fin B, Integrable
      (fun z : SparseHiddenTable B n × History n k T =>
        sparseHiddenTableU z.1 b.1 (sparseSignalCoordinate hn' j) *
          sparseObservableCellActiveCount hn' q c0 b.1 j T z.2) joint := by
    intro b
    exact integrable_sparseHiddenTableCellActiveTerm_jointLaw
      (T := T) P hk eta heta0 heta hq hn' b j
  have hcell (b : Fin B) :
      |∫ z, sparseHiddenTableU z.1 b.1 (sparseSignalCoordinate hn' j) *
          sparseObservableCellActiveCount hn' q c0 b.1 j T z.2 ∂joint| <=
        8 * (q : Real) * Real.sqrt rho := by
    simpa [F, joint] using lower_score_bias_hiddenTableCell_jointLaw
      (B := B) (T := T) P hk eta heta0 heta hn' b j hrho hrhoeq
      (Nat.cast_nonneg q)
      (sparseObservableCellActiveCount hn' q c0 b.1 j T)
      (measurable_sparseObservableCellActiveCount hn' j T)
      (fun h => sparseObservableCellActiveCount_mem_Icc hq hn' b.1 j h)
  unfold sparseHiddenTableCoordinateCellSum
  rw [integral_finsetSum Finset.univ (fun b _hb => hterm b)]
  calc
    |∑ b : Fin B, ∫ z,
        sparseHiddenTableU z.1 b.1 (sparseSignalCoordinate hn' j) *
          sparseObservableCellActiveCount hn' q c0 b.1 j T z.2 ∂joint| <=
      ∑ b : Fin B, |∫ z,
        sparseHiddenTableU z.1 b.1 (sparseSignalCoordinate hn' j) *
          sparseObservableCellActiveCount hn' q c0 b.1 j T z.2 ∂joint| :=
        Finset.abs_sum_le_sum_abs _ _
    _ <= ∑ _b : Fin B, 8 * (q : Real) * Real.sqrt rho :=
      Finset.sum_le_sum fun b _hb => hcell b
    _ = 8 * (B : Real) * q * Real.sqrt rho := by simp; ring

/-- Absolute integral bound for the learner cell sum. -/
theorem integral_sparseHiddenTableLearnerCellSum_abs_le
    {B n n' k q c0 T : Nat} (P : Policy n k) (hk : 1 <= k)
    (eta : Real) (heta0 : 0 <= eta) (heta : eta <= (1 : Real) / 16)
    (hn' : n' <= n) {rho : Real} (hrho : 0 <= rho)
    (hrhoeq : rho = eta ^ 2 * (c0 : Real) / (k : Real) ^ 2) :
    let F := sparseHiddenTableParameterFamily (n := n)
      hk eta heta0 heta n' q c0 B
    |∫ z, sparseHiddenTableLearnerCellSum hn' q c0 T z
        ∂sparseJointLaw (sparseHiddenTableMeasure B n) P F T| <=
      8 * (B : Real) * (n' : Real) * c0 * Real.sqrt rho := by
  classical
  dsimp only
  let F := sparseHiddenTableParameterFamily (n := n)
    hk eta heta0 heta n' q c0 B
  let joint := sparseJointLaw (sparseHiddenTableMeasure B n) P F T
  have hterm : forall b : Fin B, forall j : Fin n', Integrable
      (fun z : SparseHiddenTable B n × History n k T =>
        sparseHiddenTableU z.1 b.1 (sparseSignalCoordinate hn' j) *
          sparseObservableCellPullCount hn' q c0 b.1 j T z.2) joint := by
    intro b j
    exact integrable_sparseHiddenTableCellPullTerm_jointLaw
      (T := T) P hk eta heta0 heta hn' b j
  have hinner (b : Fin B) : Integrable
      (fun z : SparseHiddenTable B n × History n k T =>
        ∑ j : Fin n',
          sparseHiddenTableU z.1 b.1 (sparseSignalCoordinate hn' j) *
            sparseObservableCellPullCount hn' q c0 b.1 j T z.2) joint :=
    integrable_finsetSum _ fun j _hj => hterm b j
  have hcell (b : Fin B) (j : Fin n') :
      |∫ z, sparseHiddenTableU z.1 b.1 (sparseSignalCoordinate hn' j) *
          sparseObservableCellPullCount hn' q c0 b.1 j T z.2 ∂joint| <=
        8 * (c0 : Real) * Real.sqrt rho := by
    simpa [F, joint] using lower_score_bias_hiddenTableCell_jointLaw
      (B := B) (T := T) P hk eta heta0 heta hn' b j hrho hrhoeq
      (Nat.cast_nonneg c0)
      (sparseObservableCellPullCount hn' q c0 b.1 j T)
      (measurable_sparseObservableCellPullCount hn' j T)
      (fun h => ⟨sparseObservableCellPullCount_nonneg hn' j T h,
        sparseObservableCellPullCount_le hn' b.1 j T h⟩)
  unfold sparseHiddenTableLearnerCellSum
  rw [integral_finsetSum Finset.univ (fun b _hb => hinner b)]
  simp_rw [integral_finsetSum Finset.univ (fun j _hj => hterm _ j)]
  calc
    |∑ b : Fin B, ∑ j : Fin n', ∫ z,
        sparseHiddenTableU z.1 b.1 (sparseSignalCoordinate hn' j) *
          sparseObservableCellPullCount hn' q c0 b.1 j T z.2 ∂joint| <=
      ∑ b : Fin B, |∑ j : Fin n', ∫ z,
        sparseHiddenTableU z.1 b.1 (sparseSignalCoordinate hn' j) *
          sparseObservableCellPullCount hn' q c0 b.1 j T z.2 ∂joint| :=
        Finset.abs_sum_le_sum_abs _ _
    _ <= ∑ b : Fin B, ∑ j : Fin n', |∫ z,
        sparseHiddenTableU z.1 b.1 (sparseSignalCoordinate hn' j) *
          sparseObservableCellPullCount hn' q c0 b.1 j T z.2 ∂joint| := by
      apply Finset.sum_le_sum
      intro b _hb
      exact Finset.abs_sum_le_sum_abs _ _
    _ <= ∑ _b : Fin B, ∑ _j : Fin n',
        8 * (c0 : Real) * Real.sqrt rho := by
      apply Finset.sum_le_sum
      intro b _hb
      exact Finset.sum_le_sum fun j _hj => hcell b j
    _ = 8 * (B : Real) * (n' : Real) * c0 * Real.sqrt rho := by
      simp
      ring

/-! ## Score-mean bounds and the global manuscript inequality -/

theorem integral_sparseHiddenTableCoordinateScore_lower
    {B n n' k q c0 T : Nat} (P : Policy n k) (hk : 1 <= k)
    (eta : Real) (heta0 : 0 <= eta) (heta : eta <= (1 : Real) / 16)
    (hq : 0 < q) (hn' : n' <= n) (hT : T <= B * q)
    (j : Fin n') {rho : Real} (hrho : 0 <= rho)
    (hrhoeq : rho = eta ^ 2 * (c0 : Real) / (k : Real) ^ 2) :
    let F := sparseHiddenTableParameterFamily (n := n)
      hk eta heta0 heta n' q c0 B
    (-(16 / (3 : Real)) * (B : Real) * q * Real.sqrt rho <=
      (∫ z, sparseObservableCoordinateScore (F.at z.1) hn' q c0
          (sparseHiddenTableU z.1) j T z.2
        ∂sparseJointLaw (sparseHiddenTableMeasure B n) P F T)) := by
  dsimp only
  let F := sparseHiddenTableParameterFamily (n := n)
    hk eta heta0 heta n' q c0 B
  have heq := integral_sparseHiddenTableCoordinateScore_eq_cellSum
    (B := B) (c0 := c0) (T := T) P hk eta heta0 heta hq hn' hT j
  have hcell := integral_sparseHiddenTableCoordinateCellSum_abs_le
    (B := B) (T := T) P hk eta heta0 heta hq hn' hT j hrho hrhoeq
  rw [heq]
  calc
    -(16 / (3 : Real)) * (B : Real) * q * Real.sqrt rho =
        (2 / 3 : Real) * (-(8 * (B : Real) * q * Real.sqrt rho)) := by ring
    _ <= (2 / 3 : Real) *
        ∫ z, sparseHiddenTableCoordinateCellSum hn' q c0 j T z
          ∂sparseJointLaw (sparseHiddenTableMeasure B n) P F T :=
      mul_le_mul_of_nonneg_left (abs_le.mp hcell).1 (by norm_num)

theorem integral_sparseHiddenTableLearnerScore_upper
    {B n n' k q c0 T : Nat} (P : Policy n k) (hk : 1 <= k)
    (eta : Real) (heta0 : 0 <= eta) (heta : eta <= (1 : Real) / 16)
    (hq : 0 < q) (hn' : n' <= n) (hT : T <= B * q)
    {rho : Real} (hrho : 0 <= rho)
    (hrhoeq : rho = eta ^ 2 * (c0 : Real) / (k : Real) ^ 2) :
    let F := sparseHiddenTableParameterFamily (n := n)
      hk eta heta0 heta n' q c0 B
    (∫ z, sparseObservableLearnerScore (F.at z.1) n' q c0
        (sparseHiddenTableU z.1) T z.2
      ∂sparseJointLaw (sparseHiddenTableMeasure B n) P F T) <=
      (16 / (3 : Real)) * (B : Real) * (n' : Real) * c0 *
        Real.sqrt rho := by
  dsimp only
  let F := sparseHiddenTableParameterFamily (n := n)
    hk eta heta0 heta n' q c0 B
  have heq := integral_sparseHiddenTableLearnerScore_eq_cellSum
    (B := B) (c0 := c0) (T := T) P hk eta heta0 heta hq hn' hT
  have hcell := integral_sparseHiddenTableLearnerCellSum_abs_le
    (B := B) (q := q) (c0 := c0) (T := T) P hk eta heta0 heta hn' hrho hrhoeq
  rw [heq]
  calc
    (2 / 3 : Real) *
        ∫ z, sparseHiddenTableLearnerCellSum hn' q c0 T z
          ∂sparseJointLaw (sparseHiddenTableMeasure B n) P F T <=
      (2 / 3 : Real) *
        (8 * (B : Real) * (n' : Real) * c0 * Real.sqrt rho) :=
      mul_le_mul_of_nonneg_left (abs_le.mp hcell).2 (by norm_num)
    _ = (16 / (3 : Real)) * (B : Real) * (n' : Real) * c0 *
        Real.sqrt rho := by ring

/-- `eq:lower-score-bias` on the genuine iid full hidden table.  All
sequential KL/Pinsker, sign pairing, chronological feedback averaging, and
cell counting are internal; the only hypotheses are the construction's
literal parameter and counting identities. -/
theorem lower_score_bias_fullTable
    {B n n' k r q c0 T0 : Nat} (P : Policy n k) (hk : 1 <= k)
    (eta : Real) (heta0 : 0 <= eta) (heta : eta <= (1 : Real) / 16)
    (hq : 0 < q) (hn' : n' <= n) (hr : 1 <= r)
    {rho : Real} (hrho : 0 <= rho)
    (hrhoeq : rho = eta ^ 2 * (c0 : Real) / (k : Real) ^ 2)
    (hT0 : B * q = T0) (hnr : n' = k * r)
    (hc : B * n' * c0 = 8 * k * T0) :
    let F := sparseHiddenTableParameterFamily (n := n)
      hk eta heta0 heta n' q c0 B
    (-(48 * Real.sqrt rho * (k : Real) * (T0 : Real)) <=
      (r : Real)⁻¹ * (∑ j : Fin n',
            (∫ z, sparseObservableCoordinateScore (F.at z.1) hn' q c0
                (sparseHiddenTableU z.1) j T0 z.2
              ∂sparseJointLaw (sparseHiddenTableMeasure B n) P F T0)) -
        (∫ z, sparseObservableLearnerScore (F.at z.1) n' q c0
            (sparseHiddenTableU z.1) T0 z.2
          ∂sparseJointLaw (sparseHiddenTableMeasure B n) P F T0)) := by
  classical
  dsimp only
  let F := sparseHiddenTableParameterFamily (n := n)
    hk eta heta0 heta n' q c0 B
  let joint := sparseJointLaw (sparseHiddenTableMeasure B n) P F T0
  have hT : T0 <= B * q := by omega
  have hcoordEach (j : Fin n') :
      -(16 / (3 : Real)) * (B : Real) * q * Real.sqrt rho <=
        ∫ z, sparseObservableCoordinateScore (F.at z.1) hn' q c0
            (sparseHiddenTableU z.1) j T0 z.2 ∂joint := by
    simpa [F, joint] using integral_sparseHiddenTableCoordinateScore_lower
      (B := B) (T := T0) P hk eta heta0 heta hq hn' hT j hrho hrhoeq
  have hsum :
      -(16 / (3 : Real)) * (B : Real) * (n' : Real) * q *
          Real.sqrt rho <=
        ∑ j : Fin n',
          ∫ z, sparseObservableCoordinateScore (F.at z.1) hn' q c0
              (sparseHiddenTableU z.1) j T0 z.2 ∂joint := by
    calc
      -(16 / (3 : Real)) * (B : Real) * (n' : Real) * q *
          Real.sqrt rho =
        ∑ _j : Fin n',
          (-(16 / (3 : Real)) * (B : Real) * q * Real.sqrt rho) := by
            simp
            ring
      _ <= ∑ j : Fin n',
          ∫ z, sparseObservableCoordinateScore (F.at z.1) hn' q c0
              (sparseHiddenTableU z.1) j T0 z.2 ∂joint :=
        Finset.sum_le_sum fun j _hj => hcoordEach j
  have hrR : 0 <= (r : Real) := Nat.cast_nonneg r
  have hcoordinate :
      -(16 / (3 : Real)) * (B : Real) * (n' : Real) * q *
          Real.sqrt rho / (r : Real) <=
        (r : Real)⁻¹ *
          ∑ j : Fin n',
            ∫ z, sparseObservableCoordinateScore (F.at z.1) hn' q c0
                (sparseHiddenTableU z.1) j T0 z.2 ∂joint := by
    calc
      -(16 / (3 : Real)) * (B : Real) * (n' : Real) * q *
          Real.sqrt rho / (r : Real) =
        (r : Real)⁻¹ *
          (-(16 / (3 : Real)) * (B : Real) * (n' : Real) * q *
            Real.sqrt rho) := by ring
      _ <= (r : Real)⁻¹ *
          ∑ j : Fin n',
            ∫ z, sparseObservableCoordinateScore (F.at z.1) hn' q c0
                (sparseHiddenTableU z.1) j T0 z.2 ∂joint :=
        mul_le_mul_of_nonneg_left hsum (inv_nonneg.mpr hrR)
  have hlearner :
      (∫ z, sparseObservableLearnerScore (F.at z.1) n' q c0
          (sparseHiddenTableU z.1) T0 z.2 ∂joint) <=
        (16 / (3 : Real)) * (B : Real) * (n' : Real) * c0 *
          Real.sqrt rho := by
    simpa [F, joint] using integral_sparseHiddenTableLearnerScore_upper
      (B := B) (T := T0) P hk eta heta0 heta hq hn' hT hrho hrhoeq
  have hglobal := lower_score_bias_aggregate hr hT0 hnr hc
    hcoordinate hlearner
  simpa [F, joint, mul_assoc, mul_left_comm, mul_comm] using hglobal

#print axioms integral_sparseObservableWeightedScore_adaptiveLaw
#print axioms integral_sparseObservableCoordinateScore_adaptiveLaw
#print axioms integral_sparseObservableLearnerScore_adaptiveLaw
#print axioms sparseObservableCellActiveCount_invariant
#print axioms sparsePredictableWeightTotal_coordinate_eq_cellSum
#print axioms sparseActionScore_eq_sum_signalPull
#print axioms sparsePredictableWeightTotal_learner_eq_cellSum
#print axioms sparseHiddenTableCoordinateCellSum_abs_le
#print axioms sparseHiddenTableLearnerCellSum_abs_le
#print axioms integral_sparseHiddenTableCoordinateScore_eq_cellSum
#print axioms integral_sparseHiddenTableLearnerScore_eq_cellSum
#print axioms integral_sparseHiddenTableCoordinateCellSum_abs_le
#print axioms integral_sparseHiddenTableLearnerCellSum_abs_le
#print axioms integral_sparseHiddenTableCoordinateScore_lower
#print axioms integral_sparseHiddenTableLearnerScore_upper
#print axioms lower_score_bias_fullTable

end

end MsetsLower.Lower.Sparse
