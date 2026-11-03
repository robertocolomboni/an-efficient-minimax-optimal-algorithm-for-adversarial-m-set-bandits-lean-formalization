import MsetsLower.Lower.Sparse.Table
import MsetsLower.Lower.Sparse.PositiveDrift

/-!
# Expected positive core for the sparse construction

This file carries out the two independent `2/3` averages used in the
positive-drift argument: the feedback score has conditional mean `2/3`, and
each hidden table score has mean `2/3`.  The remaining loss is exactly the
pathwise inactive-coordinate count from `PositiveDrift`.
-/

namespace MsetsLower.Lower.Sparse

open MsetsLower Feedback Set
open MeasureTheory ProbabilityTheory
open scoped BigOperators ENNReal ProbabilityTheory

noncomputable section

/-- Under its own feedback law, the observable score reconstructs the
source score and hence has mean `2/3`. -/
theorem integral_feedbackScoreShape_feedbackDensityMeasure
    {u : Real} (hu : |u| <= (1 : Real) / 16) :
    (∫ y, feedbackScoreShape u y ∂feedbackDensityMeasure u) =
      (2 / 3 : Real) := by
  rw [<- feedbackPushforwardMeasure_eq_densityMeasure hu]
  unfold feedbackPushforwardMeasure
  rw [integral_map]
  · rw [<- integral_shape_sourceUniformMeasure]
    apply integral_congr_ae
    filter_upwards [ae_sourceUniformMeasure_mem_Icc] with z hz
    rw [feedbackScoreShape, feedbackInverse_feedbackMap hu hz]
  · exact (continuous_feedbackMap u).measurable.aemeasurable
  · exact (measurable_feedbackScoreShape_uncurry.comp
      (measurable_const.prodMk measurable_id)).aestronglyMeasurable


/-- Every in-range coordinate of a recursively represented hidden column is
still exactly uniform on `[-1,1]`; the total clipping is invisible on the
support. -/
theorem map_sparseHiddenColumnAt_measure :
    forall (B b : Nat), b < B ->
      Measure.map (fun column : SparseHiddenColumn B =>
          sparseHiddenColumnAt column b)
        (sparseHiddenColumnMeasure B) = sourceUniformMeasure := by
  intro B
  induction B with
  | zero =>
      intro b hb
      omega
  | succ B ih =>
      intro b hb
      by_cases hlast : b = B
      · subst b
        have hfun :
            (fun column : SparseHiddenColumn (B + 1) =>
              sparseHiddenColumnAt column B) =
            (fun column : SparseHiddenColumn B × Real =>
              sparseClampUnit column.2) := by
          funext column
          have hB : B < B + 1 := by omega
          rw [sparseHiddenColumnAt, dif_pos hB]
          have hfin : (⟨B, hB⟩ : Fin (B + 1)) = Fin.last B := Fin.ext rfl
          rw [hfin]
          simp [sparseHiddenColumnRawAt]
        rw [hfun, sparseHiddenColumnMeasure]
        change Measure.map (sparseClampUnit ∘ Prod.snd)
            ((sparseHiddenColumnMeasure B).prod sourceUniformMeasure) = _
        rw [<- Measure.map_map measurable_sparseClampUnit measurable_snd,
          Measure.map_snd_prod, measure_univ, one_smul,
          sourceUniformMeasure_map_sparseClampUnit]
      · have hb' : b < B := by omega
        have hfun :
            (fun column : SparseHiddenColumn (B + 1) =>
              sparseHiddenColumnAt column b) =
            (fun column : SparseHiddenColumn B × Real =>
              sparseHiddenColumnAt column.1 b) := by
          funext column
          have hbSucc : b < B + 1 := hb
          rw [sparseHiddenColumnAt, dif_pos hbSucc,
            sparseHiddenColumnAt, dif_pos hb']
          have hfin : (⟨b, hbSucc⟩ : Fin (B + 1)) =
              (⟨b, hb'⟩ : Fin B).castSucc := Fin.ext rfl
          congr 1
          change Fin.lastCases column.2
              (fun q => sparseHiddenColumnRawAt column.1 q) ⟨b, hbSucc⟩ =
            sparseHiddenColumnRawAt column.1 ⟨b, hb'⟩
          rw [hfin]
          exact Fin.lastCases_castSucc ⟨b, hb'⟩
        rw [hfun, sparseHiddenColumnMeasure]
        change Measure.map
            ((fun column : SparseHiddenColumn B =>
              sparseHiddenColumnAt column b) ∘ Prod.fst)
            ((sparseHiddenColumnMeasure B).prod sourceUniformMeasure) = _
        rw [<- Measure.map_map (measurable_sparseHiddenColumnAt B b)
            measurable_fst,
          Measure.map_fst_prod, measure_univ, one_smul, ih b hb']

/-- A coordinate of the full hidden table has the same source-uniform
marginal. -/
theorem map_sparseHiddenTableU_measure
    {B n : Nat} (tableCoordinate : Fin n) {b : Nat} (hb : b < B) :
    Measure.map (fun table : SparseHiddenTable B n =>
        sparseHiddenTableU table b tableCoordinate)
      (sparseHiddenTableMeasure B n) = sourceUniformMeasure := by
  let readColumn : SparseHiddenColumn B -> Real := fun column =>
    sparseHiddenColumnAt column b
  have heval :
      Measure.map (Function.eval tableCoordinate)
          (sparseHiddenTableMeasure B n) =
        sparseHiddenColumnMeasure B := by
    exact (measurePreserving_eval
      (fun _ : Fin n => sparseHiddenColumnMeasure B) tableCoordinate).map_eq
  change Measure.map (readColumn ∘ Function.eval tableCoordinate)
      (sparseHiddenTableMeasure B n) = sourceUniformMeasure
  rw [<- Measure.map_map (measurable_sparseHiddenColumnAt B b)
      (measurable_pi_apply tableCoordinate),
    heval]
  exact map_sparseHiddenColumnAt_measure B b hb

/-- Consequently every in-range hidden table score has mean `2/3`. -/
theorem integral_shape_sparseHiddenTableU
    {B n : Nat} (tableCoordinate : Fin n) {b : Nat} (hb : b < B) :
    (∫ table, shape (sparseHiddenTableU table b tableCoordinate)
        ∂sparseHiddenTableMeasure B n) = (2 / 3 : Real) := by
  rw [<- integral_shape_sourceUniformMeasure,
    <- map_sparseHiddenTableU_measure tableCoordinate hb]
  rw [integral_map
    (measurable_sparseHiddenTableU B n b tableCoordinate).aemeasurable
    measurable_shape.aestronglyMeasurable]

/-! ## Conditional expectation of one positive-core increment -/

/-- The part of one positive-core increment known before sampling the action
and the fresh feedback. -/
def sparsePositiveCorePredictableSum {n n' k : Nat}
    (hn' : n' <= n) (q c0 t : Nat) (U : Nat -> Fin n -> Real)
    (h : History n k t) : Real :=
  ∑ j : Fin n',
    shape (U (t / q) (sparseSignalCoordinate hn' j)) *
      sparseActive q c0 (sparseSignalCoordinate hn' j) t h

/-- The realized sum of all positive-core increments at one round. -/
def sparsePositiveCoreRoundSum {n n' k : Nat}
    (V : SparseAdaptiveParameters n k) (hn' : n' <= n)
    (q c0 t : Nat) (U : Nat -> Fin n -> Real) (h : History n k t)
    (Ay : MSetAction n k × Real) : Real :=
  sparsePositiveCorePredictableSum hn' q c0 t U h *
    feedbackScoreShape (V.value t h Ay.1) Ay.2

set_option maxHeartbeats 1000000 in
theorem measurable_sparsePositiveCoreRoundSum
    {n n' k q c0 t : Nat} (V : SparseAdaptiveParameters n k)
    (hn' : n' <= n) (U : Nat -> Fin n -> Real)
    (h : History n k t) :
    Measurable (sparsePositiveCoreRoundSum V hn' q c0 t U h) := by
  unfold sparsePositiveCoreRoundSum
  have hparameter : Measurable (fun Ay : MSetAction n k × Real =>
      V.value t h Ay.1) :=
    (V.measurable_value t).comp (measurable_const.prodMk measurable_fst)
  exact measurable_const.mul <|
    measurable_feedbackScoreShape_uncurry.comp
      (hparameter.prodMk measurable_snd)

theorem sparsePositiveCorePredictableSum_mem_Icc
    {n n' k q c0 t : Nat} (hn' : n' <= n)
    (U : Nat -> Fin n -> Real)
    (hU : forall b i, U b i ∈ Icc (-1 : Real) 1)
    (h : History n k t) :
    sparsePositiveCorePredictableSum hn' q c0 t U h ∈
      Icc (0 : Real) n' := by
  have hterm : forall j : Fin n',
      shape (U (t / q) (sparseSignalCoordinate hn' j)) *
          sparseActive q c0 (sparseSignalCoordinate hn' j) t h ∈
        Icc (0 : Real) 1 := by
    intro j
    have hs := shape_mem_Icc
      (hU (t / q) (sparseSignalCoordinate hn' j))
    have ha := sparseActive_mem_Icc
      (q := q) (c0 := c0) (sparseSignalCoordinate hn' j) h
    constructor
    · exact mul_nonneg hs.1 ha.1
    · calc
        shape (U (t / q) (sparseSignalCoordinate hn' j)) *
            sparseActive q c0 (sparseSignalCoordinate hn' j) t h <=
          1 * sparseActive q c0 (sparseSignalCoordinate hn' j) t h :=
            mul_le_mul_of_nonneg_right hs.2 ha.1
        _ <= 1 := by simpa using ha.2
  constructor
  · unfold sparsePositiveCorePredictableSum
    exact Finset.sum_nonneg fun j _ => (hterm j).1
  · unfold sparsePositiveCorePredictableSum
    calc
      (∑ j : Fin n',
          shape (U (t / q) (sparseSignalCoordinate hn' j)) *
            sparseActive q c0 (sparseSignalCoordinate hn' j) t h) <=
          ∑ _j : Fin n', (1 : Real) :=
        Finset.sum_le_sum fun j _ => (hterm j).2
      _ = n' := by simp

theorem sparsePositiveCoreRoundSum_mem_Icc
    {n n' k q c0 t : Nat} (V : SparseAdaptiveParameters n k)
    (hn' : n' <= n) (U : Nat -> Fin n -> Real)
    (hU : forall b i, U b i ∈ Icc (-1 : Real) 1)
    (h : History n k t) (Ay : MSetAction n k × Real)
    (hy : Ay.2 ∈ Icc (-1 / 2 : Real) (1 / 2 : Real)) :
    sparsePositiveCoreRoundSum V hn' q c0 t U h Ay ∈
      Icc (0 : Real) n' := by
  have hp := sparsePositiveCorePredictableSum_mem_Icc
    (q := q) (c0 := c0) hn' U hU h
  have hG := feedbackScoreShape_mem_Icc (V.abs_le t h Ay.1) hy
  unfold sparsePositiveCoreRoundSum
  constructor
  · exact mul_nonneg hp.1 hG.1
  · calc
      sparsePositiveCorePredictableSum hn' q c0 t U h *
          feedbackScoreShape (V.value t h Ay.1) Ay.2 <=
        sparsePositiveCorePredictableSum hn' q c0 t U h * 1 :=
          mul_le_mul_of_nonneg_left hG.2 hp.1
      _ <= n' := by simpa using hp.2

theorem integrable_sparsePositiveCoreRoundSum
    {n n' k q c0 t : Nat} (P : Policy n k)
    (V : SparseAdaptiveParameters n k) (hn' : n' <= n)
    (U : Nat -> Fin n -> Real)
    (hU : forall b i, U b i ∈ Icc (-1 : Real) 1)
    (h : History n k t) :
    Integrable (sparsePositiveCoreRoundSum V hn' q c0 t U h)
      (sparseAdaptiveRoundKernel P V t h) := by
  letI : IsMarkovKernel (sparseAdaptiveRoundKernel P V t) :=
    sparseAdaptiveRoundKernel_isMarkov P V t
  apply Integrable.of_mem_Icc 0 n'
    (measurable_sparsePositiveCoreRoundSum V hn' U h).aemeasurable
  filter_upwards [ae_sparseAdaptiveRoundKernel_feedback_mem_support
    P V t h] with Ay hy
  exact sparsePositiveCoreRoundSum_mem_Icc V hn' U hU h Ay hy

/-- The fresh feedback contributes the first exact `2/3`, independently of
the learner's adaptive action. -/
theorem integral_sparsePositiveCoreRoundSum
    {n n' k q c0 t : Nat} (P : Policy n k)
    (V : SparseAdaptiveParameters n k) (hn' : n' <= n)
    (U : Nat -> Fin n -> Real)
    (hU : forall b i, U b i ∈ Icc (-1 : Real) 1)
    (h : History n k t) :
    (∫ Ay, sparsePositiveCoreRoundSum V hn' q c0 t U h Ay
        ∂sparseAdaptiveRoundKernel P V t h) =
      (2 / 3 : Real) * sparsePositiveCorePredictableSum hn' q c0 t U h := by
  letI : IsMarkovKernel (sparseAdaptiveRoundKernel P V t) :=
    sparseAdaptiveRoundKernel_isMarkov P V t
  have hint := integrable_sparsePositiveCoreRoundSum
    (q := q) (c0 := c0) P V hn' U hU h
  let feedbackK := sparseParamFeedbackKernel
    (fun hA : History n k t × MSetAction n k =>
      V.value t hA.1 hA.2)
  letI : IsMarkovKernel feedbackK := by
    dsimp [feedbackK]
    exact sparseParamFeedbackKernel_isMarkov _ (V.measurable_value t)
      (fun hA => V.abs_le t hA.1 hA.2)
  change (∫ Ay, sparsePositiveCoreRoundSum V hn' q c0 t U h Ay
      ∂(P.kernel t ⊗ₖ feedbackK) h) = _
  rw [ProbabilityTheory.integral_compProd hint]
  calc
    (∫ A, ∫ y,
        sparsePositiveCoreRoundSum V hn' q c0 t U h (A, y)
          ∂feedbackK (h, A) ∂P.kernel t h) =
        ∫ _A, (2 / 3 : Real) *
          sparsePositiveCorePredictableSum hn' q c0 t U h
          ∂P.kernel t h := by
      apply integral_congr_ae
      apply ae_of_all
      intro A
      change (∫ y, sparsePositiveCoreRoundSum V hn' q c0 t U h (A, y)
          ∂feedbackK (h, A)) =
        (2 / 3 : Real) * sparsePositiveCorePredictableSum hn' q c0 t U h
      rw [show feedbackK (h, A) =
          feedbackDensityMeasure (V.value t h A) by
        exact sparseParamFeedbackKernel_apply _ (V.measurable_value t) _
          (V.abs_le t h A)]
      unfold sparsePositiveCoreRoundSum
      rw [integral_const_mul,
        integral_feedbackScoreShape_feedbackDensityMeasure
          (V.abs_le t h A)]
      ring
    _ = (2 / 3 : Real) *
        sparsePositiveCorePredictableSum hn' q c0 t U h := by simp

/-! ## Chronological summation under the adaptive law -/

set_option maxHeartbeats 2000000 in
theorem measurable_sparseObservablePositiveCore
    {n n' k q c0 : Nat} (V : SparseAdaptiveParameters n k)
    (hn' : n' <= n) (U : Nat -> Fin n -> Real) (j : Fin n') :
    forall T, Measurable
      (sparseObservablePositiveCore V hn' q c0 U j T) := by
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
      exact (ih.comp measurable_fst).add <|
        (measurable_const.mul
          ((measurable_sparseActive
            (q := q) (c0 := c0) (sparseSignalCoordinate hn' j) t).comp
              measurable_fst)).mul
          (measurable_feedbackScoreShape_uncurry.comp
            (hparameter.prodMk hfeedback))

/-- Sum of the positive cores over all signal coordinates. -/
def sparseObservableTotalPositiveCore {n n' k : Nat}
    (V : SparseAdaptiveParameters n k) (hn' : n' <= n) (q c0 : Nat)
    (U : Nat -> Fin n -> Real) (T : Nat) (h : History n k T) : Real :=
  ∑ j : Fin n', sparseObservablePositiveCore V hn' q c0 U j T h

/-- Chronological sum of the predictable factors preceding fresh feedback. -/
def sparsePositiveCorePredictableTotal {n n' k : Nat}
    (hn' : n' <= n) (q c0 : Nat) (U : Nat -> Fin n -> Real) :
    (T : Nat) -> History n k T -> Real
  | 0, _ => 0
  | t + 1, h =>
      sparsePositiveCorePredictableTotal hn' q c0 U t h.1 +
        sparsePositiveCorePredictableSum hn' q c0 t U h.1

@[simp] theorem sparseObservableTotalPositiveCore_zero
    {n n' k q c0 : Nat} (V : SparseAdaptiveParameters n k)
    (hn' : n' <= n) (U : Nat -> Fin n -> Real)
    (h : History n k 0) :
    sparseObservableTotalPositiveCore V hn' q c0 U 0 h = 0 := by
  simp [sparseObservableTotalPositiveCore, sparseObservablePositiveCore]

@[simp] theorem sparseObservableTotalPositiveCore_succ
    {n n' k q c0 t : Nat} (V : SparseAdaptiveParameters n k)
    (hn' : n' <= n) (U : Nat -> Fin n -> Real)
    (h : History n k (t + 1)) :
    sparseObservableTotalPositiveCore V hn' q c0 U (t + 1) h =
      sparseObservableTotalPositiveCore V hn' q c0 U t h.1 +
        sparsePositiveCoreRoundSum V hn' q c0 t U h.1 h.2 := by
  simp only [sparseObservableTotalPositiveCore,
    sparseObservablePositiveCore_succ, Finset.sum_add_distrib]
  unfold sparsePositiveCoreRoundSum sparsePositiveCorePredictableSum
  rw [Finset.sum_mul]

@[simp] theorem sparsePositiveCorePredictableTotal_succ
    {n n' k q c0 t : Nat} (hn' : n' <= n)
    (U : Nat -> Fin n -> Real) (h : History n k (t + 1)) :
    sparsePositiveCorePredictableTotal hn' q c0 U (t + 1) h =
      sparsePositiveCorePredictableTotal hn' q c0 U t h.1 +
        sparsePositiveCorePredictableSum hn' q c0 t U h.1 := rfl

theorem measurable_sparseObservableTotalPositiveCore
    {n n' k q c0 : Nat} (V : SparseAdaptiveParameters n k)
    (hn' : n' <= n) (U : Nat -> Fin n -> Real) (T : Nat) :
    Measurable (sparseObservableTotalPositiveCore V hn' q c0 U T) := by
  unfold sparseObservableTotalPositiveCore
  exact Finset.measurable_sum _ fun j _ =>
    measurable_sparseObservablePositiveCore V hn' U j T

set_option maxHeartbeats 1000000 in
theorem measurable_sparsePositiveCorePredictableTotal
    {n n' k q c0 : Nat} (hn' : n' <= n)
    (U : Nat -> Fin n -> Real) :
    forall T, Measurable
      (sparsePositiveCorePredictableTotal (k := k) hn' q c0 U T) := by
  intro T
  induction T with
  | zero => exact measurable_const
  | succ t ih =>
      apply (ih.comp measurable_fst).add
      unfold sparsePositiveCorePredictableSum
      exact Finset.measurable_sum _ fun j _ =>
        measurable_const.mul <|
          (measurable_sparseActive
            (q := q) (c0 := c0) (sparseSignalCoordinate hn' j) t).comp
              measurable_fst

theorem measurable_sparsePositiveCorePredictableSum
    {n n' k q c0 t : Nat} (hn' : n' <= n)
    (U : Nat -> Fin n -> Real) :
    Measurable (sparsePositiveCorePredictableSum
      (k := k) hn' q c0 t U) := by
  unfold sparsePositiveCorePredictableSum
  exact Finset.measurable_sum _ fun j _ =>
    measurable_const.mul <|
      measurable_sparseActive
        (q := q) (c0 := c0) (sparseSignalCoordinate hn' j) t

theorem sparseObservablePositiveCore_mem_Icc
    {n n' k q c0 : Nat} (V : SparseAdaptiveParameters n k)
    (hn' : n' <= n) (U : Nat -> Fin n -> Real)
    (hU : forall b i, U b i ∈ Icc (-1 : Real) 1) (j : Fin n') :
    forall T (h : History n k T), sparseHistoryInFeedbackSupport T h ->
      sparseObservablePositiveCore V hn' q c0 U j T h ∈
        Icc (0 : Real) T := by
  intro T
  induction T with
  | zero => intro h _; simp [sparseObservablePositiveCore]
  | succ t ih =>
      intro h hsupp
      have hprev := ih h.1 hsupp.1
      have hs := shape_mem_Icc
        (hU (t / q) (sparseSignalCoordinate hn' j))
      have ha := sparseActive_mem_Icc
        (q := q) (c0 := c0) (sparseSignalCoordinate hn' j) h.1
      have hG := feedbackScoreShape_mem_Icc
        (V.abs_le t h.1 h.2.1) hsupp.2
      have hsa :
          shape (U (t / q) (sparseSignalCoordinate hn' j)) *
              sparseActive q c0 (sparseSignalCoordinate hn' j) t h.1 ∈
            Icc (0 : Real) 1 := by
        constructor
        · exact mul_nonneg hs.1 ha.1
        · calc
            shape (U (t / q) (sparseSignalCoordinate hn' j)) *
                sparseActive q c0 (sparseSignalCoordinate hn' j) t h.1 <=
              1 * sparseActive q c0 (sparseSignalCoordinate hn' j) t h.1 :=
                mul_le_mul_of_nonneg_right hs.2 ha.1
            _ <= 1 := by simpa using ha.2
      have hinc :
          shape (U (t / q) (sparseSignalCoordinate hn' j)) *
              sparseActive q c0 (sparseSignalCoordinate hn' j) t h.1 *
                feedbackScoreShape (V.value t h.1 h.2.1) h.2.2 ∈
            Icc (0 : Real) 1 := by
        constructor
        · exact mul_nonneg hsa.1 hG.1
        · calc
            (shape (U (t / q) (sparseSignalCoordinate hn' j)) *
                sparseActive q c0 (sparseSignalCoordinate hn' j) t h.1) *
                  feedbackScoreShape (V.value t h.1 h.2.1) h.2.2 <=
              1 * feedbackScoreShape (V.value t h.1 h.2.1) h.2.2 :=
                mul_le_mul_of_nonneg_right hsa.2 hG.1
            _ <= 1 := by simpa using hG.2
      rw [sparseObservablePositiveCore_succ]
      constructor
      · exact add_nonneg hprev.1 hinc.1
      · calc
          sparseObservablePositiveCore V hn' q c0 U j t h.1 +
              shape (U (t / q) (sparseSignalCoordinate hn' j)) *
                sparseActive q c0 (sparseSignalCoordinate hn' j) t h.1 *
                  feedbackScoreShape (V.value t h.1 h.2.1) h.2.2 <=
            (t : Real) + 1 := add_le_add hprev.2 hinc.2
          _ = ((t + 1 : Nat) : Real) := by push_cast; ring

theorem sparseObservableTotalPositiveCore_mem_Icc
    {n n' k q c0 T : Nat} (V : SparseAdaptiveParameters n k)
    (hn' : n' <= n) (U : Nat -> Fin n -> Real)
    (hU : forall b i, U b i ∈ Icc (-1 : Real) 1)
    (h : History n k T) (hsupp : sparseHistoryInFeedbackSupport T h) :
    sparseObservableTotalPositiveCore V hn' q c0 U T h ∈
      Icc (0 : Real) ((n' : Real) * T) := by
  have hj := fun j : Fin n' =>
    sparseObservablePositiveCore_mem_Icc
      (q := q) (c0 := c0) V hn' U hU j T h hsupp
  constructor
  · unfold sparseObservableTotalPositiveCore
    exact Finset.sum_nonneg fun j _ => (hj j).1
  · unfold sparseObservableTotalPositiveCore
    calc
      (∑ j : Fin n',
          sparseObservablePositiveCore V hn' q c0 U j T h) <=
        ∑ _j : Fin n', (T : Real) :=
          Finset.sum_le_sum fun j _ => (hj j).2
      _ = (n' : Real) * T := by simp

theorem sparsePositiveCorePredictableTotal_mem_Icc
    {n n' k q c0 : Nat} (hn' : n' <= n)
    (U : Nat -> Fin n -> Real)
    (hU : forall b i, U b i ∈ Icc (-1 : Real) 1) :
    forall T (h : History n k T),
      sparsePositiveCorePredictableTotal hn' q c0 U T h ∈
        Icc (0 : Real) ((n' : Real) * T) := by
  intro T
  induction T with
  | zero => intro h; simp [sparsePositiveCorePredictableTotal]
  | succ t ih =>
      intro h
      have hprev := ih h.1
      have hround := sparsePositiveCorePredictableSum_mem_Icc
        (q := q) (c0 := c0) hn' U hU h.1
      rw [sparsePositiveCorePredictableTotal_succ]
      constructor
      · exact add_nonneg hprev.1 hround.1
      · calc
          sparsePositiveCorePredictableTotal hn' q c0 U t h.1 +
              sparsePositiveCorePredictableSum hn' q c0 t U h.1 <=
            (n' : Real) * t + n' := add_le_add hprev.2 hround.2
          _ = (n' : Real) * (t + 1 : Nat) := by push_cast; ring

theorem integrable_sparseObservableTotalPositiveCore_adaptiveLaw
    {n n' k q c0 T : Nat} (P : Policy n k)
    (V : SparseAdaptiveParameters n k) (hn' : n' <= n)
    (U : Nat -> Fin n -> Real)
    (hU : forall b i, U b i ∈ Icc (-1 : Real) 1) :
    Integrable (sparseObservableTotalPositiveCore V hn' q c0 U T)
      ((sparseAdaptiveProcess P V).law T) := by
  letI : IsProbabilityMeasure ((sparseAdaptiveProcess P V).law T) :=
    inferInstance
  apply Integrable.of_mem_Icc 0 ((n' : Real) * T)
    (measurable_sparseObservableTotalPositiveCore V hn' U T).aemeasurable
  filter_upwards [ae_sparseAdaptiveProcess_history_support P V T] with h hsupp
  exact sparseObservableTotalPositiveCore_mem_Icc V hn' U hU h hsupp

theorem integrable_sparsePositiveCorePredictableTotal_adaptiveLaw
    {n n' k q c0 T : Nat} (P : Policy n k)
    (V : SparseAdaptiveParameters n k) (hn' : n' <= n)
    (U : Nat -> Fin n -> Real)
    (hU : forall b i, U b i ∈ Icc (-1 : Real) 1) :
    Integrable (sparsePositiveCorePredictableTotal hn' q c0 U T)
      ((sparseAdaptiveProcess P V).law T) := by
  letI : IsProbabilityMeasure ((sparseAdaptiveProcess P V).law T) :=
    inferInstance
  apply Integrable.of_mem_Icc 0 ((n' : Real) * T)
    (measurable_sparsePositiveCorePredictableTotal hn' U T).aemeasurable
  exact ae_of_all _ fun h =>
    sparsePositiveCorePredictableTotal_mem_Icc hn' U hU T h

theorem integrable_sparsePositiveCorePredictableSum_adaptiveLaw
    {n n' k q c0 t : Nat} (P : Policy n k)
    (V : SparseAdaptiveParameters n k) (hn' : n' <= n)
    (U : Nat -> Fin n -> Real)
    (hU : forall b i, U b i ∈ Icc (-1 : Real) 1) :
    Integrable (sparsePositiveCorePredictableSum hn' q c0 t U)
      ((sparseAdaptiveProcess P V).law t) := by
  letI : IsProbabilityMeasure ((sparseAdaptiveProcess P V).law t) :=
    inferInstance
  apply Integrable.of_mem_Icc 0 n'
    (measurable_sparsePositiveCorePredictableSum hn' U).aemeasurable
  exact ae_of_all _ fun h =>
    sparsePositiveCorePredictableSum_mem_Icc hn' U hU h

theorem integral_sparseObservableTotalPositiveCore_succ_round
    {n n' k q c0 t : Nat} (P : Policy n k)
    (V : SparseAdaptiveParameters n k) (hn' : n' <= n)
    (U : Nat -> Fin n -> Real)
    (hU : forall b i, U b i ∈ Icc (-1 : Real) 1)
    (h : History n k t) :
    (∫ Ay,
        sparseObservableTotalPositiveCore V hn' q c0 U (t + 1) (h, Ay)
          ∂sparseAdaptiveRoundKernel P V t h) =
      sparseObservableTotalPositiveCore V hn' q c0 U t h +
        (2 / 3 : Real) *
          sparsePositiveCorePredictableSum hn' q c0 t U h := by
  letI : IsMarkovKernel (sparseAdaptiveRoundKernel P V t) :=
    sparseAdaptiveRoundKernel_isMarkov P V t
  have hround := integrable_sparsePositiveCoreRoundSum
    (q := q) (c0 := c0) P V hn' U hU h
  simp_rw [sparseObservableTotalPositiveCore_succ]
  rw [integral_add (integrable_const _) hround]
  rw [integral_sparsePositiveCoreRoundSum
    (q := q) (c0 := c0) P V hn' U hU h]
  simp

theorem integral_sparsePositiveCorePredictableTotal_succ_round
    {n n' k q c0 t : Nat} (P : Policy n k)
    (V : SparseAdaptiveParameters n k) (hn' : n' <= n)
    (U : Nat -> Fin n -> Real) (h : History n k t) :
    (∫ Ay,
        sparsePositiveCorePredictableTotal hn' q c0 U (t + 1) (h, Ay)
          ∂sparseAdaptiveRoundKernel P V t h) =
      sparsePositiveCorePredictableTotal hn' q c0 U t h +
        sparsePositiveCorePredictableSum hn' q c0 t U h := by
  letI : IsMarkovKernel (sparseAdaptiveRoundKernel P V t) :=
    sparseAdaptiveRoundKernel_isMarkov P V t
  simp [sparsePositiveCorePredictableTotal_succ]

/-- Chronologically averaging the fresh feedback replaces every realized
positive-core score by exactly `2/3` times its predictable factor. -/
theorem integral_sparseObservableTotalPositiveCore_adaptiveLaw
    {n n' k q c0 : Nat} (P : Policy n k)
    (V : SparseAdaptiveParameters n k) (hn' : n' <= n)
    (U : Nat -> Fin n -> Real)
    (hU : forall b i, U b i ∈ Icc (-1 : Real) 1) :
    forall T,
      (∫ h, sparseObservableTotalPositiveCore V hn' q c0 U T h
          ∂(sparseAdaptiveProcess P V).law T) =
        (2 / 3 : Real) *
          ∫ h, sparsePositiveCorePredictableTotal hn' q c0 U T h
            ∂(sparseAdaptiveProcess P V).law T := by
  intro T
  induction T with
  | zero =>
      simp [sparseObservableTotalPositiveCore,
        sparseObservablePositiveCore, sparsePositiveCorePredictableTotal]
  | succ t ih =>
      let mu := (sparseAdaptiveProcess P V).law t
      let kappa := sparseAdaptiveRoundKernel P V t
      letI : IsProbabilityMeasure mu := by
        dsimp [mu]
        infer_instance
      let hsf : SFinite mu := by infer_instance
      letI : IsMarkovKernel kappa := by
        dsimp [kappa]
        exact sparseAdaptiveRoundKernel_isMarkov P V t
      have hcoreFinal :=
        integrable_sparseObservableTotalPositiveCore_adaptiveLaw
          (q := q) (c0 := c0) (T := t + 1) P V hn' U hU
      have hpredFinal :=
        integrable_sparsePositiveCorePredictableTotal_adaptiveLaw
          (q := q) (c0 := c0) (T := t + 1) P V hn' U hU
      have hcorePrev :=
        integrable_sparseObservableTotalPositiveCore_adaptiveLaw
          (q := q) (c0 := c0) (T := t) P V hn' U hU
      have hpredPrev :=
        integrable_sparsePositiveCorePredictableTotal_adaptiveLaw
          (q := q) (c0 := c0) (T := t) P V hn' U hU
      have hroundPred :=
        integrable_sparsePositiveCorePredictableSum_adaptiveLaw
          (q := q) (c0 := c0) (t := t) P V hn' U hU
      let hsk : IsSFiniteKernel kappa := by infer_instance
      have hcoreFinal' := hcoreFinal
      change Integrable
        (fun z : History n k t × (MSetAction n k × Real) =>
          sparseObservableTotalPositiveCore V hn' q c0 U (t + 1) z)
        (mu ⊗ₘ kappa) at hcoreFinal'
      have hpredFinal' := hpredFinal
      change Integrable
        (fun z : History n k t × (MSetAction n k × Real) =>
          sparsePositiveCorePredictableTotal hn' q c0 U (t + 1) z)
        (mu ⊗ₘ kappa) at hpredFinal'
      have hcoreFubini :
          (∫ z : History n k t × (MSetAction n k × Real),
            sparseObservableTotalPositiveCore V hn' q c0 U (t + 1) z
              ∂mu ⊗ₘ kappa) =
            ∫ h, ∫ Ay,
              sparseObservableTotalPositiveCore V hn' q c0 U (t + 1)
                (h, Ay) ∂kappa h ∂mu :=
        @Measure.integral_compProd
          (History n k t) (MSetAction n k × Real)
          (inferInstanceAs (MeasurableSpace (History n k t)))
          (inferInstanceAs (MeasurableSpace (MSetAction n k × Real)))
          kappa mu hsf hsk Real inferInstance inferInstance _ hcoreFinal'
      have hpredFubini :
          (∫ z : History n k t × (MSetAction n k × Real),
            sparsePositiveCorePredictableTotal hn' q c0 U (t + 1) z
              ∂mu ⊗ₘ kappa) =
            ∫ h, ∫ Ay,
              sparsePositiveCorePredictableTotal hn' q c0 U (t + 1)
                (h, Ay) ∂kappa h ∂mu :=
        @Measure.integral_compProd
          (History n k t) (MSetAction n k × Real)
          (inferInstanceAs (MeasurableSpace (History n k t)))
          (inferInstanceAs (MeasurableSpace (MSetAction n k × Real)))
          kappa mu hsf hsk Real inferInstance inferInstance _ hpredFinal'
      change (∫ z,
          sparseObservableTotalPositiveCore V hn' q c0 U (t + 1) z
            ∂mu ⊗ₘ kappa) =
        (2 / 3 : Real) *
          ∫ z, sparsePositiveCorePredictableTotal hn' q c0 U (t + 1) z
            ∂mu ⊗ₘ kappa
      calc
        (∫ z,
            sparseObservableTotalPositiveCore V hn' q c0 U (t + 1) z
              ∂mu ⊗ₘ kappa) =
            ∫ h, ∫ Ay,
              sparseObservableTotalPositiveCore V hn' q c0 U (t + 1)
                (h, Ay) ∂kappa h ∂mu :=
          hcoreFubini
        _ = ∫ h,
            (sparseObservableTotalPositiveCore V hn' q c0 U t h +
              (2 / 3 : Real) *
                sparsePositiveCorePredictableSum hn' q c0 t U h) ∂mu := by
          apply integral_congr_ae
          apply ae_of_all
          intro h
          exact integral_sparseObservableTotalPositiveCore_succ_round
            (q := q) (c0 := c0) P V hn' U hU h
        _ = (∫ h, sparseObservableTotalPositiveCore V hn' q c0 U t h ∂mu) +
            (2 / 3 : Real) *
              ∫ h, sparsePositiveCorePredictableSum hn' q c0 t U h ∂mu := by
          rw [integral_add hcorePrev (hroundPred.const_mul (2 / 3 : Real)),
            integral_const_mul]
        _ = (2 / 3 : Real) *
            ((∫ h, sparsePositiveCorePredictableTotal hn' q c0 U t h ∂mu) +
              ∫ h, sparsePositiveCorePredictableSum hn' q c0 t U h ∂mu) := by
          rw [ih]
          ring
        _ = (2 / 3 : Real) *
            ∫ h, (sparsePositiveCorePredictableTotal hn' q c0 U t h +
              sparsePositiveCorePredictableSum hn' q c0 t U h) ∂mu := by
          rw [integral_add hpredPrev hroundPred]
        _ = (2 / 3 : Real) *
            ∫ z, sparsePositiveCorePredictableTotal hn' q c0 U (t + 1) z
              ∂mu ⊗ₘ kappa := by
          congr 1
          rw [hpredFubini]
          apply integral_congr_ae
          apply ae_of_all
          intro h
          exact (integral_sparsePositiveCorePredictableTotal_succ_round
            (q := q) (c0 := c0) P V hn' U h).symm

/-! ## Removing activity without an independence assumption -/

/-- Chronological sum of the unmasked hidden scores. -/
def sparseHiddenShapeTotal {n n' : Nat} (hn' : n' <= n) (q : Nat)
    (U : Nat -> Fin n -> Real) : Nat -> Real
  | 0 => 0
  | t + 1 => sparseHiddenShapeTotal hn' q U t +
      ∑ j : Fin n', shape (U (t / q) (sparseSignalCoordinate hn' j))

@[simp] theorem sparseHiddenShapeTotal_succ
    {n n' q t : Nat} (hn' : n' <= n) (U : Nat -> Fin n -> Real) :
    sparseHiddenShapeTotal hn' q U (t + 1) =
      sparseHiddenShapeTotal hn' q U t +
        ∑ j : Fin n',
          shape (U (t / q) (sparseSignalCoordinate hn' j)) := rfl

/-- At one round, masking hidden scores by activity loses at most one for
each inactive signal coordinate.  No independence between the table and the
learner's past is used. -/
theorem sparsePositiveCorePredictableSum_lower
    {n n' k q c0 t : Nat} (hn' : n' <= n)
    (U : Nat -> Fin n -> Real)
    (hU : forall b i, U b i ∈ Icc (-1 : Real) 1)
    (h : History n k t) :
    (∑ j : Fin n', shape (U (t / q) (sparseSignalCoordinate hn' j))) -
        ((sparseInactiveSignals hn' q c0 t h).card : Real) <=
      sparsePositiveCorePredictableSum hn' q c0 t U h := by
  classical
  let S := sparseInactiveSignals hn' q c0 t h
  have hj : forall j : Fin n',
      shape (U (t / q) (sparseSignalCoordinate hn' j)) -
          (if j ∈ S then (1 : Real) else 0) <=
        shape (U (t / q) (sparseSignalCoordinate hn' j)) *
          sparseActive q c0 (sparseSignalCoordinate hn' j) t h := by
    intro j
    have hs := shape_mem_Icc
      (hU (t / q) (sparseSignalCoordinate hn' j))
    by_cases hactive :
        sparseBlockSelectedCount q (sparseSignalCoordinate hn' j) t h <
          (c0 : Real)
    · have hjnot : j ∉ S := by
        simp [S, sparseInactiveSignals, hactive]
      simp [hjnot, sparseActive, hactive]
    · have hjmem : j ∈ S := by
        simpa [S, sparseInactiveSignals] using (le_of_not_gt hactive)
      simp only [if_pos hjmem, sparseActive, if_neg hactive, mul_zero]
      linarith [hs.2]
  unfold sparsePositiveCorePredictableSum
  calc
    (∑ j : Fin n', shape (U (t / q) (sparseSignalCoordinate hn' j))) -
        (S.card : Real) =
      ∑ j : Fin n',
        (shape (U (t / q) (sparseSignalCoordinate hn' j)) -
          if j ∈ S then (1 : Real) else 0) := by
        rw [Finset.sum_sub_distrib]
        congr 1
        simpa using
          (Finset.sum_boole (R := Real) (fun j : Fin n' => j ∈ S)
            Finset.univ).symm
    _ <= ∑ j : Fin n',
        shape (U (t / q) (sparseSignalCoordinate hn' j)) *
          sparseActive q c0 (sparseSignalCoordinate hn' j) t h :=
      Finset.sum_le_sum fun j _ => hj j

/-- Summed version of the preceding masking estimate. -/
theorem sparsePositiveCorePredictableTotal_lower
    {n n' k q c0 : Nat} (hn' : n' <= n)
    (U : Nat -> Fin n -> Real)
    (hU : forall b i, U b i ∈ Icc (-1 : Real) 1) :
    forall T (h : History n k T),
      sparseHiddenShapeTotal hn' q U T -
          sparseInactiveTime hn' q c0 T h <=
        sparsePositiveCorePredictableTotal hn' q c0 U T h := by
  intro T
  induction T with
  | zero => intro h; simp [sparseHiddenShapeTotal,
      sparseInactiveTime, sparsePositiveCorePredictableTotal]
  | succ t ih =>
      intro h
      have hround := sparsePositiveCorePredictableSum_lower
        (q := q) (c0 := c0) hn' U hU h.1
      rw [sparseHiddenShapeTotal_succ,
        sparsePositiveCorePredictableTotal_succ]
      change sparseHiddenShapeTotal hn' q U t +
          (∑ j : Fin n',
            shape (U (t / q) (sparseSignalCoordinate hn' j))) -
            (sparseInactiveTime hn' q c0 t h.1 +
              ((sparseInactiveSignals hn' q c0 t h.1).card : Real)) <= _
      linarith [ih h.1]

theorem measurable_sparseHiddenShapeTotal_hiddenTable
    {B n n' q : Nat} (hn' : n' <= n) :
    forall T, Measurable (fun table : SparseHiddenTable B n =>
      sparseHiddenShapeTotal hn' q (sparseHiddenTableU table) T) := by
  intro T
  induction T with
  | zero => exact measurable_const
  | succ t ih =>
      apply ih.add
      exact Finset.measurable_sum _ fun j _ =>
        measurable_shape.comp
          (measurable_sparseHiddenTableU B n (t / q)
            (sparseSignalCoordinate hn' j))

theorem sparseHiddenShapeTotal_hiddenTable_mem_Icc
    {B n n' q T : Nat} (hn' : n' <= n)
    (table : SparseHiddenTable B n) :
    sparseHiddenShapeTotal hn' q (sparseHiddenTableU table) T ∈
      Icc (0 : Real) ((n' : Real) * T) := by
  induction T with
  | zero => simp [sparseHiddenShapeTotal]
  | succ t ih =>
      have hj : forall j : Fin n',
          shape (sparseHiddenTableU table (t / q)
            (sparseSignalCoordinate hn' j)) ∈ Icc (0 : Real) 1 :=
        fun j => shape_mem_Icc <| (abs_le).1 <|
          sparseHiddenTableU_abs_le_one table (t / q)
            (sparseSignalCoordinate hn' j)
      have hsum :
          (∑ j : Fin n', shape (sparseHiddenTableU table (t / q)
            (sparseSignalCoordinate hn' j))) ∈ Icc (0 : Real) n' := by
        constructor
        · exact Finset.sum_nonneg fun j _ => (hj j).1
        · calc
            (∑ j : Fin n', shape (sparseHiddenTableU table (t / q)
                (sparseSignalCoordinate hn' j))) <=
              ∑ _j : Fin n', (1 : Real) :=
                Finset.sum_le_sum fun j _ => (hj j).2
            _ = n' := by simp
      rw [sparseHiddenShapeTotal_succ]
      constructor
      · exact add_nonneg ih.1 hsum.1
      · calc
          sparseHiddenShapeTotal hn' q (sparseHiddenTableU table) t +
              (∑ j : Fin n', shape (sparseHiddenTableU table (t / q)
                (sparseSignalCoordinate hn' j))) <=
            (n' : Real) * t + n' := add_le_add ih.2 hsum.2
          _ = (n' : Real) * (t + 1 : Nat) := by push_cast; ring

theorem integrable_sparseHiddenShapeTotal_hiddenTable
    {B n n' q T : Nat} (hn' : n' <= n) :
    Integrable (fun table : SparseHiddenTable B n =>
      sparseHiddenShapeTotal hn' q (sparseHiddenTableU table) T)
      (sparseHiddenTableMeasure B n) := by
  apply Integrable.of_mem_Icc 0 ((n' : Real) * T)
    (measurable_sparseHiddenShapeTotal_hiddenTable hn' T).aemeasurable
  exact ae_of_all _ fun table =>
    sparseHiddenShapeTotal_hiddenTable_mem_Icc hn' table

/-- The second exact `2/3`: averaged over the full hidden table, the
unmasked chronological score is `2n'T/3`. -/
theorem integral_sparseHiddenShapeTotal_hiddenTable
    {B n n' q T : Nat} (hq : 0 < q) (hn' : n' <= n)
    (hT : T <= B * q) :
    (∫ table, sparseHiddenShapeTotal hn' q (sparseHiddenTableU table) T
        ∂sparseHiddenTableMeasure B n) =
      (2 / 3 : Real) * (n' : Real) * T := by
  induction T with
  | zero => simp [sparseHiddenShapeTotal]
  | succ t ih =>
      have ht : t < B * q := lt_of_lt_of_le (by omega) hT
      have hb : t / q < B := (Nat.div_lt_iff_lt_mul hq).2 ht
      have hTprev : t <= B * q := by omega
      have hprev := integrable_sparseHiddenShapeTotal_hiddenTable
        (B := B) (q := q) (T := t) hn'
      have hj : forall j : Fin n', Integrable
          (fun table : SparseHiddenTable B n =>
            shape (sparseHiddenTableU table (t / q)
              (sparseSignalCoordinate hn' j)))
          (sparseHiddenTableMeasure B n) := by
        intro j
        apply Integrable.of_mem_Icc 0 1
          (measurable_shape.comp
            (measurable_sparseHiddenTableU B n (t / q)
              (sparseSignalCoordinate hn' j))).aemeasurable
        exact ae_of_all _ fun table => shape_mem_Icc <| (abs_le).1 <|
          sparseHiddenTableU_abs_le_one table (t / q)
            (sparseSignalCoordinate hn' j)
      have heach (j : Fin n') :
          (∫ table, shape (sparseHiddenTableU table (t / q)
              (sparseSignalCoordinate hn' j))
              ∂sparseHiddenTableMeasure B n) = (2 / 3 : Real) :=
        integral_shape_sparseHiddenTableU
          (B := B) (n := n) (b := t / q)
          (sparseSignalCoordinate hn' j) hb
      have hsum :
          (∑ j : Fin n',
            ∫ table, shape (sparseHiddenTableU table (t / q)
              (sparseSignalCoordinate hn' j))
              ∂sparseHiddenTableMeasure B n) =
            (n' : Real) * (2 / 3 : Real) := by
        simp_rw [heach]
        simp
      simp_rw [sparseHiddenShapeTotal_succ]
      rw [integral_add hprev (integrable_finsetSum _ fun j _ => hj j),
        integral_finsetSum Finset.univ (fun j _ => hj j), ih hTprev,
        hsum]
      push_cast
      ring

/-! ## Joint hidden-state/history expectation -/

def sparseFamilyTotalPositiveCore
    {Omega : Type*} [MeasurableSpace Omega] {n n' k : Nat}
    (F : SparseAdaptiveParameterFamily Omega n k) (hn' : n' <= n)
    (q c0 : Nat) (U : Omega -> Nat -> Fin n -> Real) (T : Nat)
    (z : Omega × History n k T) : Real :=
  sparseObservableTotalPositiveCore (F.at z.1) hn' q c0 (U z.1) T z.2

def sparseFamilyPredictableTotal
    {Omega : Type*} [MeasurableSpace Omega] {n n' k : Nat}
    (hn' : n' <= n) (q c0 : Nat)
    (U : Omega -> Nat -> Fin n -> Real) (T : Nat)
    (z : Omega × History n k T) : Real :=
  sparsePositiveCorePredictableTotal hn' q c0 (U z.1) T z.2

set_option maxHeartbeats 2000000 in
theorem measurable_sparseFamilyTotalPositiveCore
    {Omega : Type*} [MeasurableSpace Omega] {n n' k q c0 : Nat}
    (F : SparseAdaptiveParameterFamily Omega n k) (hn' : n' <= n)
    (U : Omega -> Nat -> Fin n -> Real)
    (hUmeas : forall b i, Measurable (fun omega => U omega b i)) :
    forall T, Measurable (sparseFamilyTotalPositiveCore F hn' q c0 U T) := by
  intro T
  induction T with
  | zero =>
      have hzero : sparseFamilyTotalPositiveCore F hn' q c0 U 0 =
          fun _ => (0 : Real) := by
        funext z
        simp [sparseFamilyTotalPositiveCore]
      rw [hzero]
      exact measurable_const
  | succ t ih =>
      have hprefix : Measurable (fun z : Omega × History n k (t + 1) =>
          (z.1, z.2.1)) :=
        measurable_fst.prodMk (measurable_fst.comp measurable_snd)
      have hpredict : Measurable (fun z : Omega × History n k (t + 1) =>
          sparsePositiveCorePredictableSum hn' q c0 t (U z.1) z.2.1) := by
        unfold sparsePositiveCorePredictableSum
        exact Finset.measurable_sum _ fun j _ =>
          (measurable_shape.comp
            ((hUmeas (t / q) (sparseSignalCoordinate hn' j)).comp
              measurable_fst)).mul <|
            (measurable_sparseActive
              (q := q) (c0 := c0) (sparseSignalCoordinate hn' j) t).comp
                (measurable_fst.comp measurable_snd)
      have hparameter : Measurable (fun z : Omega × History n k (t + 1) =>
          F.value t z.1 z.2.1 z.2.2.1) :=
        (F.measurable_value t).comp <|
          hprefix.prodMk
            (measurable_fst.comp (measurable_snd.comp measurable_snd))
      have hfeedback : Measurable (fun z : Omega × History n k (t + 1) =>
          z.2.2.2) := measurable_snd.comp (measurable_snd.comp measurable_snd)
      have hsucc : sparseFamilyTotalPositiveCore F hn' q c0 U (t + 1) =
          fun z : Omega × History n k (t + 1) =>
            sparseFamilyTotalPositiveCore F hn' q c0 U t (z.1, z.2.1) +
              sparsePositiveCorePredictableSum hn' q c0 t (U z.1) z.2.1 *
                feedbackScoreShape (F.value t z.1 z.2.1 z.2.2.1)
                  z.2.2.2 := by
        funext z
        rw [sparseFamilyTotalPositiveCore,
          sparseObservableTotalPositiveCore_succ]
        rfl
      rw [hsucc]
      exact (ih.comp hprefix).add <| hpredict.mul <|
        measurable_feedbackScoreShape_uncurry.comp
          (hparameter.prodMk hfeedback)

set_option maxHeartbeats 1000000 in
theorem measurable_sparseFamilyPredictableTotal
    {Omega : Type*} [MeasurableSpace Omega] {n n' k q c0 : Nat}
    (hn' : n' <= n) (U : Omega -> Nat -> Fin n -> Real)
    (hUmeas : forall b i, Measurable (fun omega => U omega b i)) :
    forall T, Measurable (sparseFamilyPredictableTotal
      (k := k) hn' q c0 U T) := by
  intro T
  induction T with
  | zero => exact measurable_const
  | succ t ih =>
      have hprefix : Measurable (fun z : Omega × History n k (t + 1) =>
          (z.1, z.2.1)) :=
        measurable_fst.prodMk (measurable_fst.comp measurable_snd)
      change Measurable (fun z : Omega × History n k (t + 1) =>
        sparseFamilyPredictableTotal hn' q c0 U t (z.1, z.2.1) +
          sparsePositiveCorePredictableSum hn' q c0 t (U z.1) z.2.1)
      apply (ih.comp hprefix).add
      unfold sparsePositiveCorePredictableSum
      exact Finset.measurable_sum _ fun j _ =>
        (measurable_shape.comp
          ((hUmeas (t / q) (sparseSignalCoordinate hn' j)).comp
            measurable_fst)).mul <|
          (measurable_sparseActive
            (q := q) (c0 := c0) (sparseSignalCoordinate hn' j) t).comp
              (measurable_fst.comp measurable_snd)

theorem integrable_sparseFamilyTotalPositiveCore_jointLaw
    {Omega : Type*} [MeasurableSpace Omega] {n n' k q c0 T : Nat}
    (mu : Measure Omega) [IsProbabilityMeasure mu] (P : Policy n k)
    (F : SparseAdaptiveParameterFamily Omega n k) (hn' : n' <= n)
    (U : Omega -> Nat -> Fin n -> Real)
    (hUmeas : forall b i, Measurable (fun omega => U omega b i))
    (hU : forall omega b i, U omega b i ∈ Icc (-1 : Real) 1) :
    Integrable (sparseFamilyTotalPositiveCore F hn' q c0 U T)
      (sparseJointLaw mu P F T) := by
  letI : IsProbabilityMeasure (sparseJointLaw mu P F T) := by
    unfold sparseJointLaw
    infer_instance
  apply Integrable.of_mem_Icc 0 ((n' : Real) * T)
    (measurable_sparseFamilyTotalPositiveCore F hn' U hUmeas T).aemeasurable
  filter_upwards [ae_sparseJointLaw_history_support mu P F T] with z hsupp
  exact sparseObservableTotalPositiveCore_mem_Icc
    (q := q) (c0 := c0) (F.at z.1) hn' (U z.1) (hU z.1) z.2 hsupp

theorem integrable_sparseFamilyPredictableTotal_jointLaw
    {Omega : Type*} [MeasurableSpace Omega] {n n' k q c0 T : Nat}
    (mu : Measure Omega) [IsProbabilityMeasure mu] (P : Policy n k)
    (F : SparseAdaptiveParameterFamily Omega n k) (hn' : n' <= n)
    (U : Omega -> Nat -> Fin n -> Real)
    (hUmeas : forall b i, Measurable (fun omega => U omega b i))
    (hU : forall omega b i, U omega b i ∈ Icc (-1 : Real) 1) :
    Integrable (sparseFamilyPredictableTotal (k := k) hn' q c0 U T)
      (sparseJointLaw mu P F T) := by
  letI : IsProbabilityMeasure (sparseJointLaw mu P F T) := by
    unfold sparseJointLaw
    infer_instance
  apply Integrable.of_mem_Icc 0 ((n' : Real) * T)
    (measurable_sparseFamilyPredictableTotal hn' U hUmeas T).aemeasurable
  exact ae_of_all _ fun z =>
    sparsePositiveCorePredictableTotal_mem_Icc hn' (U z.1) (hU z.1) T z.2

/-- Joint-law version of the chronological `2/3` feedback identity. -/
theorem integral_sparseFamilyTotalPositiveCore_jointLaw
    {Omega : Type*} [MeasurableSpace Omega] {n n' k q c0 T : Nat}
    (mu : Measure Omega) [IsProbabilityMeasure mu] (P : Policy n k)
    (F : SparseAdaptiveParameterFamily Omega n k) (hn' : n' <= n)
    (U : Omega -> Nat -> Fin n -> Real)
    (hUmeas : forall b i, Measurable (fun omega => U omega b i))
    (hU : forall omega b i, U omega b i ∈ Icc (-1 : Real) 1) :
    (∫ z, sparseFamilyTotalPositiveCore F hn' q c0 U T z
        ∂sparseJointLaw mu P F T) =
      (2 / 3 : Real) *
        ∫ z, sparseFamilyPredictableTotal (k := k) hn' q c0 U T z
          ∂sparseJointLaw mu P F T := by
  have hcore := integrable_sparseFamilyTotalPositiveCore_jointLaw
    (q := q) (c0 := c0) (T := T) mu P F hn' U hUmeas hU
  have hpred := integrable_sparseFamilyPredictableTotal_jointLaw
    (q := q) (c0 := c0) (T := T) mu P F hn' U hUmeas hU
  unfold sparseJointLaw at hcore hpred ⊢
  rw [Measure.integral_compProd hcore, Measure.integral_compProd hpred]
  calc
    (∫ omega, ∫ h,
        sparseFamilyTotalPositiveCore F hn' q c0 U T (omega, h)
          ∂sparseFamilyLawKernel P F T omega ∂mu) =
      ∫ omega, (2 / 3 : Real) *
        (∫ h, sparseFamilyPredictableTotal hn' q c0 U T (omega, h)
          ∂sparseFamilyLawKernel P F T omega) ∂mu := by
      apply integral_congr_ae
      apply ae_of_all
      intro omega
      change (∫ h,
          sparseFamilyTotalPositiveCore F hn' q c0 U T (omega, h)
            ∂sparseFamilyLawKernel P F T omega) =
        (2 / 3 : Real) *
          ∫ h, sparseFamilyPredictableTotal hn' q c0 U T (omega, h)
            ∂sparseFamilyLawKernel P F T omega
      rw [sparseFamilyLawKernel_apply]
      exact integral_sparseObservableTotalPositiveCore_adaptiveLaw
        P (F.at omega) hn' (U omega) (hU omega) T
    _ = (2 / 3 : Real) *
        ∫ omega, ∫ h,
          sparseFamilyPredictableTotal hn' q c0 U T (omega, h)
            ∂sparseFamilyLawKernel P F T omega ∂mu :=
      integral_const_mul _ _

/-! ## Concrete full-table capstones -/

/-- After the pathwise inactive-time estimate, the predictable core retains
`13/24` of `n'T`.  This statement is already on the genuine full hidden-table
joint law and has no abstract energy or KL premise. -/
theorem integral_sparseHiddenTablePredictableTotal_lower
    {B n n' k q c0 r ell T : Nat}
    (P : Policy n k) (hk : 1 <= k)
    (eta : Real) (heta0 : 0 <= eta) (heta : eta <= (1 : Real) / 16)
    (hn' : n' <= n) (hr : 0 < r) (hell : 0 < ell)
    (hnprod : n' = k * r) (hqeq : q = r * ell)
    (hc0eq : c0 = 8 * ell) (hT : T <= B * q) :
    (13 / 24 : Real) * (n' : Real) * T <=
      ∫ z, sparseFamilyPredictableTotal hn' q c0
          (fun table : SparseHiddenTable B n => sparseHiddenTableU table) T z
        ∂sparseJointLaw (sparseHiddenTableMeasure B n) P
          (sparseHiddenTableParameterFamily hk eta heta0 heta n' q c0 B) T := by
  let F : SparseAdaptiveParameterFamily (SparseHiddenTable B n) n k :=
    sparseHiddenTableParameterFamily hk eta heta0 heta n' q c0 B
  let U : SparseHiddenTable B n -> Nat -> Fin n -> Real :=
    fun table => sparseHiddenTableU table
  let joint := sparseJointLaw (sparseHiddenTableMeasure B n) P F T
  letI : IsProbabilityMeasure joint := by
    dsimp [joint, sparseJointLaw]
    infer_instance
  have hUmeas : forall b i, Measurable (fun table => U table b i) := by
    intro b i
    exact measurable_sparseHiddenTableU B n b i
  have hU : forall table b i, U table b i ∈ Icc (-1 : Real) 1 := by
    intro table b i
    exact (abs_le).1 (sparseHiddenTableU_abs_le_one table b i)
  have hpred : Integrable
      (sparseFamilyPredictableTotal (k := k) hn' q c0 U T) joint := by
    dsimp [joint]
    exact integrable_sparseFamilyPredictableTotal_jointLaw
      (sparseHiddenTableMeasure B n) P F hn' U hUmeas hU
  have hhidden : Integrable (fun z : SparseHiddenTable B n × History n k T =>
      sparseHiddenShapeTotal hn' q (U z.1) T) joint := by
    apply Integrable.of_mem_Icc 0 ((n' : Real) * T)
      ((measurable_sparseHiddenShapeTotal_hiddenTable
        (B := B) (q := q) hn' T).comp measurable_fst).aemeasurable
    exact ae_of_all _ fun z =>
      sparseHiddenShapeTotal_hiddenTable_mem_Icc hn' z.1
  have hbase : Integrable (fun z : SparseHiddenTable B n × History n k T =>
      sparseHiddenShapeTotal hn' q (U z.1) T -
        (n' : Real) * T / 8) joint :=
    hhidden.sub (integrable_const _)
  have hpoint : forall z : SparseHiddenTable B n × History n k T,
      sparseHiddenShapeTotal hn' q (U z.1) T - (n' : Real) * T / 8 <=
        sparseFamilyPredictableTotal hn' q c0 U T z := by
    intro z
    have hmask := sparsePositiveCorePredictableTotal_lower
      (q := q) (c0 := c0) hn' (U z.1) (hU z.1) T z.2
    have hinactive := sparseInactiveTime_le_eighth
      hr hell hn' hnprod hqeq hc0eq z.2
    dsimp [sparseFamilyPredictableTotal]
    linarith
  have hlower :
      (∫ z, sparseHiddenShapeTotal hn' q (U z.1) T -
          (n' : Real) * T / 8 ∂joint) <=
        ∫ z, sparseFamilyPredictableTotal hn' q c0 U T z ∂joint :=
    integral_mono hbase hpred hpoint
  have hhiddenEq :
      (∫ z, sparseHiddenShapeTotal hn' q (U z.1) T ∂joint) =
        ∫ table, sparseHiddenShapeTotal hn' q (U table) T
          ∂sparseHiddenTableMeasure B n := by
    dsimp [joint, sparseJointLaw] at hhidden ⊢
    rw [Measure.integral_compProd hhidden]
    simp
  have hq : 0 < q := by
    rw [hqeq]
    exact Nat.mul_pos hr hell
  have htable := integral_sparseHiddenShapeTotal_hiddenTable hq hn' hT
  have hjoint :
      (∫ z, sparseHiddenShapeTotal hn' q (U z.1) T ∂joint) =
        (2 / 3 : Real) * (n' : Real) * T := by
    rw [hhiddenEq]
    exact htable
  rw [integral_sub hhidden (integrable_const _), hjoint] at hlower
  simp only [integral_const, probReal_univ, one_smul] at hlower
  dsimp [joint, F, U] at hlower ⊢
  nlinarith

/-- Concrete expectation form of the manuscript's positive-core lower bound:
the two exact `2/3` averages and the inactive-time loss give `13n'T/36`. -/
theorem integral_sparseHiddenTableTotalPositiveCore_lower
    {B n n' k q c0 r ell T : Nat}
    (P : Policy n k) (hk : 1 <= k)
    (eta : Real) (heta0 : 0 <= eta) (heta : eta <= (1 : Real) / 16)
    (hn' : n' <= n) (hr : 0 < r) (hell : 0 < ell)
    (hnprod : n' = k * r) (hqeq : q = r * ell)
    (hc0eq : c0 = 8 * ell) (hT : T <= B * q) :
    (13 / 36 : Real) * (n' : Real) * T <=
      ∫ z, sparseFamilyTotalPositiveCore
          (sparseHiddenTableParameterFamily hk eta heta0 heta n' q c0 B)
          hn' q c0
          (fun table : SparseHiddenTable B n => sparseHiddenTableU table) T z
        ∂sparseJointLaw (sparseHiddenTableMeasure B n) P
          (sparseHiddenTableParameterFamily hk eta heta0 heta n' q c0 B) T := by
  let F : SparseAdaptiveParameterFamily (SparseHiddenTable B n) n k :=
    sparseHiddenTableParameterFamily hk eta heta0 heta n' q c0 B
  let U : SparseHiddenTable B n -> Nat -> Fin n -> Real :=
    fun table => sparseHiddenTableU table
  have hUmeas : forall b i, Measurable (fun table => U table b i) := by
    intro b i
    exact measurable_sparseHiddenTableU B n b i
  have hU : forall table b i, U table b i ∈ Icc (-1 : Real) 1 := by
    intro table b i
    exact (abs_le).1 (sparseHiddenTableU_abs_le_one table b i)
  have heq := integral_sparseFamilyTotalPositiveCore_jointLaw
    (q := q) (c0 := c0) (T := T)
    (sparseHiddenTableMeasure B n) P F hn' U hUmeas hU
  have hpred := integral_sparseHiddenTablePredictableTotal_lower
    P hk eta heta0 heta hn' hr hell hnprod hqeq hc0eq hT
  dsimp [F, U] at heq hpred ⊢
  rw [heq]
  nlinarith

/-- The normalized form used as `hcore` after averaging the `n'=kr`
coordinate transformations. -/
theorem integral_sparseHiddenTableTotalPositiveCore_div_r_lower
    {B n n' k q c0 r ell T : Nat}
    (P : Policy n k) (hk : 1 <= k)
    (eta : Real) (heta0 : 0 <= eta) (heta : eta <= (1 : Real) / 16)
    (hn' : n' <= n) (hr : 0 < r) (hell : 0 < ell)
    (hnprod : n' = k * r) (hqeq : q = r * ell)
    (hc0eq : c0 = 8 * ell) (hT : T <= B * q) :
    (13 / 36 : Real) * (k : Real) * T <=
      (1 / (r : Real)) *
        ∫ z, sparseFamilyTotalPositiveCore
            (sparseHiddenTableParameterFamily hk eta heta0 heta n' q c0 B)
            hn' q c0
            (fun table : SparseHiddenTable B n => sparseHiddenTableU table) T z
          ∂sparseJointLaw (sparseHiddenTableMeasure B n) P
            (sparseHiddenTableParameterFamily hk eta heta0 heta n' q c0 B) T := by
  have hcore := integral_sparseHiddenTableTotalPositiveCore_lower
    P hk eta heta0 heta hn' hr hell hnprod hqeq hc0eq hT
  have hrReal : 0 < (r : Real) := by exact_mod_cast hr
  have hnprodReal : (n' : Real) = (k : Real) * (r : Real) := by
    exact_mod_cast hnprod
  have hscale := mul_le_mul_of_nonneg_left hcore
    (by positivity : (0 : Real) <= 1 / (r : Real))
  calc
    (13 / 36 : Real) * (k : Real) * T =
        (1 / (r : Real)) * ((13 / 36 : Real) * (n' : Real) * T) := by
      rw [hnprodReal]
      field_simp
    _ <= (1 / (r : Real)) *
        ∫ z, sparseFamilyTotalPositiveCore
            (sparseHiddenTableParameterFamily hk eta heta0 heta n' q c0 B)
            hn' q c0
            (fun table : SparseHiddenTable B n => sparseHiddenTableU table) T z
          ∂sparseJointLaw (sparseHiddenTableMeasure B n) P
            (sparseHiddenTableParameterFamily hk eta heta0 heta n' q c0 B) T :=
      hscale

#print axioms integral_feedbackScoreShape_feedbackDensityMeasure

end

end MsetsLower.Lower.Sparse
