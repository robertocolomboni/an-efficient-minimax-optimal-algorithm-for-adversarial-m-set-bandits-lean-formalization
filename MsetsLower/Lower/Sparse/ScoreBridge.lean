import MsetsLower.Lower.Sparse.Fixing
import MsetsLower.Lower.Sparse.PositiveDrift
import MsetsLower.Probability.ChangedLawMaximum

/-!
# Observable scores and fixed-table scores

The stochastic likelihood argument sees centered feedback.  A deterministic
protocol section records the actual action loss.  This file proves, on the
full-measure set of protocol-compatible histories, that undoing the affine
shift reconstructs exactly the source-table scores used in the pathwise
regret identity.
-/

set_option linter.style.header false

namespace MsetsLower.Lower.Sparse

open MsetsLower Feedback MeasureTheory ProbabilityTheory Set
open scoped BigOperators ENNReal ProbabilityTheory

noncomputable section

/-! ## Support of deterministic protocol sections -/

def SparseProtocolHistoryCompatible {n k : Nat} (L : LossProcess n k) :
    (t : Nat) → History n k t → Prop
  | 0, _ => True
  | t + 1, h =>
      SparseProtocolHistoryCompatible L t h.1 ∧
        h.2.2 = actionLoss h.2.1 (L.itemLoss t h.1)

theorem measurableSet_sparseProtocolHistoryCompatible
    {n k : Nat} (L : LossProcess n k) : ∀ t : Nat,
    MeasurableSet {h : History n k t |
      SparseProtocolHistoryCompatible L t h} := by
  intro t
  induction t with
  | zero => simp [SparseProtocolHistoryCompatible]
  | succ t ih =>
      have hinput : Measurable (fun h : History n k (t + 1) =>
          (h.1, h.2.1)) :=
        measurable_fst.prodMk (measurable_fst.comp measurable_snd)
      have hloss : Measurable (fun h : History n k (t + 1) =>
          actionLoss h.2.1 (L.itemLoss t h.1)) :=
        (measurable_actionLoss_joint (L.measurable_itemLoss t)).comp hinput
      change MeasurableSet {h : History n k (t + 1) |
        SparseProtocolHistoryCompatible L t h.1 ∧
          h.2.2 = actionLoss h.2.1 (L.itemLoss t h.1)}
      exact (ih.preimage measurable_fst).inter
        (measurableSet_eq_fun (measurable_snd.comp measurable_snd) hloss)

theorem ae_roundKernel_sparseProtocolHistoryCompatible
    {n k t : Nat} (P : Policy n k) (L : LossProcess n k)
    (h : History n k t)
    (hcompat : SparseProtocolHistoryCompatible L t h) :
    ∀ᵐ h' ∂roundKernel P L t h,
      SparseProtocolHistoryCompatible L (t + 1) h' := by
  unfold roundKernel
  rw [Kernel.map_apply _ (measurable_extendRun L t) h]
  change ∀ᵐ h' ∂(actionHistoryKernel P t h).map (extendRun L t),
    h' ∈ {h' : History n k (t + 1) |
      SparseProtocolHistoryCompatible L (t + 1) h'}
  apply (ae_map_iff (measurable_extendRun L t).aemeasurable
    (measurableSet_sparseProtocolHistoryCompatible L (t + 1))).2
  rw [actionHistoryKernel_apply]
  apply (ae_map_iff measurable_prodMk_left.aemeasurable
    ((measurableSet_sparseProtocolHistoryCompatible L (t + 1)).preimage
      (measurable_extendRun L t))).2
  apply ae_of_all
  intro A
  exact ⟨hcompat, rfl⟩

theorem ae_runLaw_sparseProtocolHistoryCompatible
    {n k : Nat} (P : Policy n k) (L : LossProcess n k) : ∀ t : Nat,
    ∀ᵐ h ∂runLaw P L t, SparseProtocolHistoryCompatible L t h := by
  intro t
  induction t with
  | zero => simp [runLaw, SparseProtocolHistoryCompatible]
  | succ t ih =>
      rw [runLaw_succ]
      apply Measure.ae_comp_of_ae_ae
        (measurableSet_sparseProtocolHistoryCompatible L (t + 1))
      filter_upwards [ih] with h hcompat
      exact ae_roundKernel_sparseProtocolHistoryCompatible P L h hcompat

/-! ## Observable learner score -/

def sparseObservableLearnerScore {n k : Nat}
    (V : SparseAdaptiveParameters n k) (n' q c0 : Nat)
    (U : Nat → Fin n → Real) :
    (T : Nat) → History n k T → Real
  | 0, _ => 0
  | t + 1, h =>
      sparseObservableLearnerScore V n' q c0 U t h.1 +
        feedbackScoreShape (V.value t h.1 h.2.1) h.2.2 *
          sparseActionScore n' q c0 U t h.1 h.2.1

@[simp] theorem sparseObservableLearnerScore_zero
    {n k n' q c0 : Nat} (V : SparseAdaptiveParameters n k)
    (U : Nat → Fin n → Real) (h : History n k 0) :
    sparseObservableLearnerScore V n' q c0 U 0 h = 0 := rfl

@[simp] theorem sparseObservableLearnerScore_succ
    {n k n' q c0 t : Nat} (V : SparseAdaptiveParameters n k)
    (U : Nat → Fin n → Real) (h : History n k (t + 1)) :
    sparseObservableLearnerScore V n' q c0 U (t + 1) h =
      sparseObservableLearnerScore V n' q c0 U t h.1 +
        feedbackScoreShape (V.value t h.1 h.2.1) h.2.2 *
          sparseActionScore n' q c0 U t h.1 h.2.1 := rfl

set_option maxHeartbeats 1000000 in
-- Elaborating measurability through the dependent recursive history type is expensive.
theorem measurable_sparseObservableLearnerScore
    {n k n' q c0 : Nat} (V : SparseAdaptiveParameters n k)
    (U : Nat → Fin n → Real) : ∀ T,
    Measurable (sparseObservableLearnerScore V n' q c0 U T) := by
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
      have hscore : Measurable (fun h : History n k (t + 1) =>
          sparseActionScore n' q c0 U t h.1 h.2.1) := by
        have hitem : Measurable (fun h : History n k t => fun i : Fin n =>
            sparseActive q c0 i t h * sparseSignalWeight n' q U t i) := by
          refine Measurable.of_eval fun i => ?_
          exact (measurable_sparseActive i t).mul measurable_const
        exact (measurable_actionLoss_joint hitem).comp
          (measurable_fst.prodMk (measurable_fst.comp measurable_snd))
      exact (ih.comp measurable_fst).add <|
        (measurable_feedbackScoreShape_uncurry.comp
          (hparameter.prodMk hfeedback)).mul hscore

/-! ## Exact score reconstruction on compatible actual histories -/

private theorem sparse_centered_feedbackScoreShape_eq_shape
    {n k t : Nat} (hk : 1 ≤ k)
    (eta : Real) (heta0 : 0 ≤ eta) (heta : eta ≤ (1 : Real) / 16)
    (n' q c0 : Nat) (U : Nat → Fin n → Real)
    (hU : ∀ b i, |U b i| ≤ 1) (Z : Nat → Real)
    (hZ : ∀ t, Z t ∈ Icc (-1 : Real) 1)
    (h : History n k t) (A : MSetAction n k) (y : Real)
    (hy : y = (1 : Real) / 2 +
      feedbackMap (sparseFeedbackParameter eta n' q c0 U t h A) (Z t)) :
    feedbackScoreShape
        ((sparseAdaptiveParametersOfTable hk eta heta0 heta
          n' q c0 U hU).value t
            ((sparseActualHistoryEquiv n k t).symm h) A)
        (y - (1 : Real) / 2) = shape (Z t) := by
  have hparam :
      (sparseAdaptiveParametersOfTable hk eta heta0 heta
        n' q c0 U hU).value t
          ((sparseActualHistoryEquiv n k t).symm h) A =
        sparseFeedbackParameter eta n' q c0 U t h A := by
    change sparseFeedbackParameter eta n' q c0 U t
        ((sparseActualHistoryEquiv n k t).symm h) A =
      sparseFeedbackParameter eta n' q c0 U t h A
    simpa using
      (sparseFeedbackParameter_actualHistory eta U
        ((sparseActualHistoryEquiv n k t).symm h) A).symm
  rw [hparam, hy]
  have hshift : (1 : Real) / 2 +
      feedbackMap (sparseFeedbackParameter eta n' q c0 U t h A) (Z t) -
        (1 : Real) / 2 =
      feedbackMap (sparseFeedbackParameter eta n' q c0 U t h A) (Z t) := by
    ring
  rw [hshift]
  unfold feedbackScoreShape
  rw [feedbackInverse_feedbackMap
    ((sparseFeedbackParameter_abs_le hk heta0 hU t h A).trans heta)
    (hZ t)]

theorem sparseObservableCoordinateScore_centered_eq_table
    {n n' k q c0 T0 : Nat} (hk : 1 ≤ k) (hn' : n' ≤ n)
    (eta : Real) (heta0 : 0 ≤ eta) (heta : eta ≤ (1 : Real) / 16)
    (U : Nat → Fin n → Real) (hU : ∀ b i, |U b i| ≤ 1)
    (Z : Nat → Real) (hZ : ∀ t, Z t ∈ Icc (-1 : Real) 1)
    (j : Fin n') : ∀ t (h : History n k t), t ≤ T0 →
    SparseProtocolHistoryCompatible
        (sparseLossProcess hk eta heta0 heta n' q c0 T0 U hU Z hZ) t h →
    sparseObservableCoordinateScore
        (sparseAdaptiveParametersOfTable hk eta heta0 heta
          n' q c0 U hU) hn' q c0 U j t
          ((sparseActualHistoryEquiv n k t).symm h) =
      sparseCoordinateScore n' q c0 U Z (sparseSignalCoordinate hn' j) t h := by
  intro t
  induction t with
  | zero => intro h ht hcompat; rfl
  | succ t ih =>
      rintro ⟨h, A, y⟩ ht hcompat
      have ht0 : t < T0 := by omega
      have hloss := lower_sparse_action_loss hk eta n' q c0 T0 U Z
        ht0 h A
      have hy : y = (1 : Real) / 2 +
          feedbackMap (sparseFeedbackParameter eta n' q c0 U t h A) (Z t) :=
        hcompat.2.trans hloss
      have hshape := sparse_centered_feedbackScoreShape_eq_shape
        hk eta heta0 heta n' q c0 U hU Z hZ h A y hy
      have hactive :
          sparseActive q c0 (sparseSignalCoordinate hn' j) t
              ((sparseActualHistoryEquiv n k t).symm h) =
            sparseActive q c0 (sparseSignalCoordinate hn' j) t h := by
        simpa using
          (sparseActive_actualHistory
            (q := q) (c0 := c0) (sparseSignalCoordinate hn' j)
            ((sparseActualHistoryEquiv n k t).symm h)).symm
      rw [sparseActualHistoryEquiv_symm_succ,
        sparseObservableCoordinateScore_succ,
        sparseCoordinateScore_succ,
        ih h (by omega) hcompat.1, hshape, hactive]
      have hi : (sparseSignalCoordinate hn' j).1 < n' := by
        simpa [sparseSignalCoordinate] using j.2
      simp [sparseSignalWeight, hi]

theorem sparseObservableLearnerScore_centered_eq_table
    {n k n' q c0 T0 : Nat} (hk : 1 ≤ k)
    (eta : Real) (heta0 : 0 ≤ eta) (heta : eta ≤ (1 : Real) / 16)
    (U : Nat → Fin n → Real) (hU : ∀ b i, |U b i| ≤ 1)
    (Z : Nat → Real) (hZ : ∀ t, Z t ∈ Icc (-1 : Real) 1) :
    ∀ t (h : History n k t), t ≤ T0 →
    SparseProtocolHistoryCompatible
        (sparseLossProcess hk eta heta0 heta n' q c0 T0 U hU Z hZ) t h →
    sparseObservableLearnerScore
        (sparseAdaptiveParametersOfTable hk eta heta0 heta
          n' q c0 U hU) n' q c0 U t
          ((sparseActualHistoryEquiv n k t).symm h) =
      sparseLearnerScore n' q c0 U Z t h := by
  intro t
  induction t with
  | zero => intro h ht hcompat; rfl
  | succ t ih =>
      rintro ⟨h, A, y⟩ ht hcompat
      have ht0 : t < T0 := by omega
      have hloss := lower_sparse_action_loss hk eta n' q c0 T0 U Z
        ht0 h A
      have hy : y = (1 : Real) / 2 +
          feedbackMap (sparseFeedbackParameter eta n' q c0 U t h A) (Z t) :=
        hcompat.2.trans hloss
      have hshape := sparse_centered_feedbackScoreShape_eq_shape
        hk eta heta0 heta n' q c0 U hU Z hZ h A y hy
      have haction :
          sparseActionScore n' q c0 U t
              ((sparseActualHistoryEquiv n k t).symm h) A =
            sparseActionScore n' q c0 U t h A := by
        simpa using
          (sparseActionScore_actualHistory U
            ((sparseActualHistoryEquiv n k t).symm h) A).symm
      rw [sparseActualHistoryEquiv_symm_succ,
        sparseObservableLearnerScore_succ, sparseLearnerScore_succ,
        ih h (by omega) hcompat.1, hshape, haction]

/-! ## Uniform score bounds on the genuine feedback support -/

theorem sparseObservableCoordinateScore_abs_le
    {n n' k q c0 : Nat} (V : SparseAdaptiveParameters n k)
    (hn' : n' ≤ n) (U : Nat → Fin n → Real)
    (hU : ∀ b i, |U b i| ≤ 1) (j : Fin n') :
    ∀ T (h : History n k T), sparseHistoryInFeedbackSupport T h →
      |sparseObservableCoordinateScore V hn' q c0 U j T h| ≤ (T : Real) := by
  intro T
  induction T with
  | zero => intro h hsupp; simp
  | succ t ih =>
      intro h hsupp
      have hG := feedbackScoreShape_mem_Icc
        (V.abs_le t h.1 h.2.1) hsupp.2
      have ha := sparseActive_mem_Icc
        (q := q) (c0 := c0) (sparseSignalCoordinate hn' j) h.1
      have hinc :
          |U (t / q) (sparseSignalCoordinate hn' j) *
            sparseActive q c0 (sparseSignalCoordinate hn' j) t h.1 *
              feedbackScoreShape (V.value t h.1 h.2.1) h.2.2| ≤ 1 := by
        rw [abs_mul, abs_mul, abs_of_nonneg ha.1, abs_of_nonneg hG.1]
        have hua := hU (t / q) (sparseSignalCoordinate hn' j)
        have hAG :
            sparseActive q c0 (sparseSignalCoordinate hn' j) t h.1 *
                feedbackScoreShape (V.value t h.1 h.2.1) h.2.2 ≤ 1 := by
          calc
            _ ≤ 1 * 1 := mul_le_mul ha.2 hG.2 hG.1 (by norm_num)
            _ = 1 := by norm_num
        calc
          |U (t / q) (sparseSignalCoordinate hn' j)| *
              sparseActive q c0 (sparseSignalCoordinate hn' j) t h.1 *
                feedbackScoreShape (V.value t h.1 h.2.1) h.2.2 ≤
              1 * (sparseActive q c0 (sparseSignalCoordinate hn' j) t h.1 *
                feedbackScoreShape (V.value t h.1 h.2.1) h.2.2) := by
            rw [mul_assoc]
            exact mul_le_mul_of_nonneg_right hua (mul_nonneg ha.1 hG.1)
          _ ≤ 1 := by simpa only [one_mul] using hAG
      rw [sparseObservableCoordinateScore_succ]
      calc
        |_ + _| ≤
            |sparseObservableCoordinateScore V hn' q c0 U j t h.1| +
              |U (t / q) (sparseSignalCoordinate hn' j) *
                sparseActive q c0 (sparseSignalCoordinate hn' j) t h.1 *
                  feedbackScoreShape (V.value t h.1 h.2.1) h.2.2| :=
          abs_add_le _ _
        _ ≤ (t : Real) + 1 := add_le_add (ih h.1 hsupp.1) hinc
        _ = (t + 1 : Nat) := by push_cast; ring

theorem sparseObservableLearnerScore_abs_le
    {n k n' q c0 : Nat} (hk : 1 ≤ k)
    (V : SparseAdaptiveParameters n k) (U : Nat → Fin n → Real)
    (hU : ∀ b i, |U b i| ≤ 1) :
    ∀ T (h : History n k T), sparseHistoryInFeedbackSupport T h →
      |sparseObservableLearnerScore V n' q c0 U T h| ≤
        (k : Real) * (T : Real) := by
  intro T
  induction T with
  | zero => intro h hsupp; simp
  | succ t ih =>
      intro h hsupp
      have hG := feedbackScoreShape_mem_Icc
        (V.abs_le t h.1 h.2.1) hsupp.2
      have hscore := sparseActionScore_abs_le
        (n' := n') (q := q) (c0 := c0) hU t h.1 h.2.1
      have hinc :
          |feedbackScoreShape (V.value t h.1 h.2.1) h.2.2 *
            sparseActionScore n' q c0 U t h.1 h.2.1| ≤ (k : Real) := by
        rw [abs_mul, abs_of_nonneg hG.1]
        calc
          feedbackScoreShape (V.value t h.1 h.2.1) h.2.2 *
              |sparseActionScore n' q c0 U t h.1 h.2.1| ≤
              1 * (k : Real) :=
            mul_le_mul hG.2 hscore (abs_nonneg _) (by norm_num)
          _ = (k : Real) := one_mul _
      rw [sparseObservableLearnerScore_succ]
      calc
        |_ + _| ≤
            |sparseObservableLearnerScore V n' q c0 U t h.1| +
              |feedbackScoreShape (V.value t h.1 h.2.1) h.2.2 *
                sparseActionScore n' q c0 U t h.1 h.2.1| := abs_add_le _ _
        _ ≤ (k : Real) * (t : Real) + (k : Real) :=
          add_le_add (ih h.1 hsupp.1) hinc
        _ = (k : Real) * (t + 1 : Nat) := by push_cast; ring

#print axioms ae_runLaw_sparseProtocolHistoryCompatible
#print axioms sparseObservableCoordinateScore_centered_eq_table
#print axioms sparseObservableLearnerScore_centered_eq_table
#print axioms sparseObservableCoordinateScore_abs_le
#print axioms sparseObservableLearnerScore_abs_le

end

end MsetsLower.Lower.Sparse
