import MsetsLower.Core.ParametricRun
import MsetsLower.Feedback.Moments
import MsetsLower.Lower.ParametricRegret
import MsetsLower.Lower.Sparse.FeedbackBridge
import MsetsLower.Lower.Sparse.JointLikelihood
import Mathlib.MeasureTheory.Constructions.Pi

/-!
# Finite auxiliary tables for the sparse construction

This file realizes the manuscript's finite iid table `(U,Z)` as a measurable
parameter.  Every parameter is clipped to `[-1,1]`, so every table section is
an admissible deterministic non-anticipating loss process, including tables
outside the support of the product-uniform law.
-/

set_option linter.style.header false

namespace MsetsLower.Lower.Sparse

open MsetsLower Feedback MeasureTheory ProbabilityTheory Set
open scoped ENNReal ProbabilityTheory

noncomputable section

/-! ## A total support-safe clipping map -/

def sparseClampUnit (z : Real) : Real := max (-1) (min 1 z)

theorem measurable_sparseClampUnit : Measurable sparseClampUnit := by
  exact measurable_const.max (measurable_const.min measurable_id)

theorem sparseClampUnit_mem_Icc (z : Real) :
    sparseClampUnit z ∈ Icc (-1 : Real) 1 := by
  constructor
  · exact le_max_left _ _
  · rw [sparseClampUnit]
    exact max_le (by norm_num) (min_le_left _ _)

@[simp] theorem sparseClampUnit_eq_self {z : Real}
    (hz : z ∈ Icc (-1 : Real) 1) : sparseClampUnit z = z := by
  rw [sparseClampUnit, min_eq_right hz.2, max_eq_right hz.1]

theorem sourceUniformMeasure_map_sparseClampUnit :
    sourceUniformMeasure.map sparseClampUnit = sourceUniformMeasure := by
  calc
    sourceUniformMeasure.map sparseClampUnit = sourceUniformMeasure.map id := by
      apply Measure.map_congr
      filter_upwards [ae_sourceUniformMeasure_mem_Icc] with z hz
      exact sparseClampUnit_eq_self hz
    _ = sourceUniformMeasure := Measure.map_id

/-! ## Reading recursively represented hidden columns -/

def sparseHiddenColumnRawAt :
    {B : Nat} → SparseHiddenColumn B → Fin B → Real
  | 0, _, r => Fin.elim0 r
  | B + 1, column, r =>
      Fin.lastCases column.2
        (fun q => sparseHiddenColumnRawAt column.1 q) r

theorem measurable_sparseHiddenColumnRawAt (B : Nat) (r : Fin B) :
    Measurable (fun column : SparseHiddenColumn B =>
      sparseHiddenColumnRawAt column r) := by
  induction B with
  | zero => exact Fin.elim0 r
  | succ B ih =>
      have hspace : instMeasurableSpaceSparseHiddenColumn (B + 1) =
          @Prod.instMeasurableSpace (SparseHiddenColumn B) Real
            (instMeasurableSpaceSparseHiddenColumn B) Real.measurableSpace := rfl
      rw [hspace]
      refine Fin.lastCases ?_ (fun q => ?_) r
      · change Measurable
          (fun column : SparseHiddenColumn B × Real =>
            sparseHiddenColumnRawAt (B := B + 1) column (Fin.last B))
        simpa [sparseHiddenColumnRawAt] using
          (measurable_snd : Measurable
            (fun column : SparseHiddenColumn B × Real => column.2))
      · change Measurable
          (fun column : SparseHiddenColumn B × Real =>
            sparseHiddenColumnRawAt (B := B + 1) column q.castSucc)
        simpa [sparseHiddenColumnRawAt, Function.comp_def] using
          (ih q).comp (measurable_fst : Measurable
            (fun column : SparseHiddenColumn B × Real => column.1))

def sparseHiddenColumnAt {B : Nat}
    (column : SparseHiddenColumn B) (b : Nat) : Real :=
  if hb : b < B then
    sparseClampUnit (sparseHiddenColumnRawAt column ⟨b, hb⟩)
  else 0

theorem measurable_sparseHiddenColumnAt (B b : Nat) :
    Measurable (fun column : SparseHiddenColumn B =>
      sparseHiddenColumnAt column b) := by
  by_cases hb : b < B
  · simp only [sparseHiddenColumnAt, dif_pos hb]
    exact measurable_sparseClampUnit.comp
      (measurable_sparseHiddenColumnRawAt B ⟨b, hb⟩)
  · simp only [sparseHiddenColumnAt, dif_neg hb]
    exact measurable_const

theorem sparseHiddenColumnAt_mem_Icc {B : Nat}
    (column : SparseHiddenColumn B) (b : Nat) :
    sparseHiddenColumnAt column b ∈ Icc (-1 : Real) 1 := by
  by_cases hb : b < B
  · rw [sparseHiddenColumnAt, dif_pos hb]
    exact sparseClampUnit_mem_Icc _
  · rw [sparseHiddenColumnAt, dif_neg hb]
    norm_num

/-! ## Full hidden and feedback tables -/

abbrev SparseHiddenTable (B n : Nat) := Fin n → SparseHiddenColumn B

def sparseHiddenTableMeasure (B n : Nat) :
    Measure (SparseHiddenTable B n) :=
  Measure.pi (fun _ : Fin n => sparseHiddenColumnMeasure B)

theorem sparseHiddenColumnMeasure_isProbability :
    (B : Nat) → IsProbabilityMeasure (sparseHiddenColumnMeasure B)
  | 0 => by
      rw [isProbabilityMeasure_iff, sparseHiddenColumnMeasure]
      simp
  | B + 1 => by
      letI : IsProbabilityMeasure (sparseHiddenColumnMeasure B) :=
        sparseHiddenColumnMeasure_isProbability B
      letI : IsProbabilityMeasure sourceUniformMeasure := inferInstance
      exact Measure.prod.instIsProbabilityMeasure _ _

instance (B : Nat) :
    IsProbabilityMeasure (sparseHiddenColumnMeasure B) :=
  sparseHiddenColumnMeasure_isProbability B

instance (B n : Nat) :
    IsProbabilityMeasure (sparseHiddenTableMeasure B n) := by
  unfold sparseHiddenTableMeasure
  infer_instance

@[reducible] def SparseNoiseTable : Nat → Type
  | 0 => PUnit
  | T + 1 => SparseNoiseTable T × Real

@[reducible] instance sparseNoiseTableMeasurableSpace :
    (T : Nat) → MeasurableSpace (SparseNoiseTable T)
  | 0 => inferInstanceAs (MeasurableSpace PUnit)
  | T + 1 => @Prod.instMeasurableSpace (SparseNoiseTable T) Real
      (sparseNoiseTableMeasurableSpace T) Real.measurableSpace

def sparseNoiseTableMeasure :
    (T : Nat) → Measure (SparseNoiseTable T)
  | 0 => Measure.dirac PUnit.unit
  | T + 1 => (sparseNoiseTableMeasure T).prod sourceUniformMeasure

theorem sparseNoiseTableMeasure_isProbability :
    (T : Nat) → IsProbabilityMeasure (sparseNoiseTableMeasure T)
  | 0 => by
      rw [isProbabilityMeasure_iff, sparseNoiseTableMeasure]
      simp
  | T + 1 => by
      letI : IsProbabilityMeasure (sparseNoiseTableMeasure T) :=
        sparseNoiseTableMeasure_isProbability T
      letI : IsProbabilityMeasure sourceUniformMeasure := inferInstance
      exact Measure.prod.instIsProbabilityMeasure _ _

instance (T : Nat) : IsProbabilityMeasure (sparseNoiseTableMeasure T) :=
  sparseNoiseTableMeasure_isProbability T

def sparseNoiseTableRawAt :
    {T : Nat} → SparseNoiseTable T → Fin T → Real
  | 0, _, r => Fin.elim0 r
  | T + 1, table, r =>
      Fin.lastCases table.2 (fun q => sparseNoiseTableRawAt table.1 q) r

theorem measurable_sparseNoiseTableRawAt (T : Nat) (r : Fin T) :
    Measurable (fun table : SparseNoiseTable T =>
      sparseNoiseTableRawAt table r) := by
  induction T with
  | zero => exact Fin.elim0 r
  | succ T ih =>
      have hspace : sparseNoiseTableMeasurableSpace (T + 1) =
          @Prod.instMeasurableSpace (SparseNoiseTable T) Real
            (sparseNoiseTableMeasurableSpace T) Real.measurableSpace := rfl
      rw [hspace]
      refine Fin.lastCases ?_ (fun q => ?_) r
      · change Measurable
          (fun table : SparseNoiseTable T × Real =>
            sparseNoiseTableRawAt (T := T + 1) table (Fin.last T))
        simpa [sparseNoiseTableRawAt] using
          (measurable_snd : Measurable
            (fun table : SparseNoiseTable T × Real => table.2))
      · change Measurable
          (fun table : SparseNoiseTable T × Real =>
            sparseNoiseTableRawAt (T := T + 1) table q.castSucc)
        simpa [sparseNoiseTableRawAt, Function.comp_def] using
          (ih q).comp (measurable_fst : Measurable
            (fun table : SparseNoiseTable T × Real => table.1))

def sparseNoiseTableAt {T : Nat}
    (table : SparseNoiseTable T) (t : Nat) : Real :=
  if ht : t < T then
    sparseClampUnit (sparseNoiseTableRawAt table ⟨t, ht⟩)
  else 0

theorem measurable_sparseNoiseTableAt (T t : Nat) :
    Measurable (fun table : SparseNoiseTable T => sparseNoiseTableAt table t) := by
  by_cases ht : t < T
  · simp only [sparseNoiseTableAt, dif_pos ht]
    exact measurable_sparseClampUnit.comp
      (measurable_sparseNoiseTableRawAt T ⟨t, ht⟩)
  · simp only [sparseNoiseTableAt, dif_neg ht]
    exact measurable_const

theorem sparseNoiseTableAt_mem_Icc {T : Nat}
    (table : SparseNoiseTable T) (t : Nat) :
    sparseNoiseTableAt table t ∈ Icc (-1 : Real) 1 := by
  by_cases ht : t < T
  · rw [sparseNoiseTableAt, dif_pos ht]
    exact sparseClampUnit_mem_Icc _
  · rw [sparseNoiseTableAt, dif_neg ht]
    norm_num

@[simp] theorem sparseNoiseTableAt_snoc_last {T : Nat}
    (table : SparseNoiseTable T) (z : Real) :
    sparseNoiseTableAt (T := T + 1) (table, z) T = sparseClampUnit z := by
  have ht : T < T + 1 := by omega
  rw [sparseNoiseTableAt, dif_pos ht]
  have hfin : (⟨T, ht⟩ : Fin (T + 1)) = Fin.last T := Fin.ext rfl
  rw [hfin]
  simp [sparseNoiseTableRawAt]

@[simp] theorem sparseNoiseTableAt_snoc_prefix {T r : Nat}
    (table : SparseNoiseTable T) (z : Real) (hr : r < T) :
    sparseNoiseTableAt (T := T + 1) (table, z) r =
      sparseNoiseTableAt table r := by
  have hr' : r < T + 1 := hr.trans (by omega)
  rw [sparseNoiseTableAt, dif_pos hr', sparseNoiseTableAt, dif_pos hr]
  have hfin : (⟨r, hr'⟩ : Fin (T + 1)) =
      (⟨r, hr⟩ : Fin T).castSucc := Fin.ext rfl
  congr 1
  change Fin.lastCases z (fun q => sparseNoiseTableRawAt table q)
      ⟨r, hr'⟩ = sparseNoiseTableRawAt table ⟨r, hr⟩
  rw [hfin]
  exact Fin.lastCases_castSucc ⟨r, hr⟩

abbrev SparseAuxTable (B n T : Nat) :=
  SparseHiddenTable B n × SparseNoiseTable T

def sparseAuxTableMeasure (B n T : Nat) :
    Measure (SparseAuxTable B n T) :=
  (sparseHiddenTableMeasure B n).prod (sparseNoiseTableMeasure T)

instance (B n T : Nat) :
    IsProbabilityMeasure (sparseAuxTableMeasure B n T) := by
  unfold sparseAuxTableMeasure
  infer_instance

def sparseTableU {B n T : Nat} (table : SparseAuxTable B n T) :
    Nat → Fin n → Real :=
  fun b i => sparseHiddenColumnAt (table.1 i) b

def sparseHiddenTableU {B n : Nat} (table : SparseHiddenTable B n) :
    Nat → Fin n → Real :=
  fun b i => sparseHiddenColumnAt (table i) b

def sparseTableZ {B n T : Nat} (table : SparseAuxTable B n T) :
    Nat → Real :=
  fun t => sparseNoiseTableAt table.2 t

theorem sparseTableU_abs_le_one {B n T : Nat}
    (table : SparseAuxTable B n T) (b : Nat) (i : Fin n) :
    |sparseTableU table b i| ≤ 1 := by
  exact (abs_le).2 (sparseHiddenColumnAt_mem_Icc (table.1 i) b)

theorem sparseTableZ_mem_Icc {B n T : Nat}
    (table : SparseAuxTable B n T) (t : Nat) :
    sparseTableZ table t ∈ Icc (-1 : Real) 1 :=
  sparseNoiseTableAt_mem_Icc table.2 t

theorem measurable_sparseTableU (B n T b : Nat) (i : Fin n) :
    Measurable (fun table : SparseAuxTable B n T => sparseTableU table b i) := by
  exact (measurable_sparseHiddenColumnAt B b).comp
    ((measurable_pi_apply i).comp measurable_fst)

theorem measurable_sparseHiddenTableU (B n b : Nat) (i : Fin n) :
    Measurable (fun table : SparseHiddenTable B n =>
      sparseHiddenTableU table b i) := by
  exact (measurable_sparseHiddenColumnAt B b).comp (measurable_pi_apply i)

theorem sparseHiddenTableU_abs_le_one {B n : Nat}
    (table : SparseHiddenTable B n) (b : Nat) (i : Fin n) :
    |sparseHiddenTableU table b i| ≤ 1 := by
  exact (abs_le).2 (sparseHiddenColumnAt_mem_Icc (table i) b)

theorem measurable_sparseTableZ (B n T t : Nat) :
    Measurable (fun table : SparseAuxTable B n T => sparseTableZ table t) := by
  exact (measurable_sparseNoiseTableAt T t).comp measurable_snd

/-! ## The base adaptive feedback family indexed by the complete hidden table -/

def sparseHiddenTableParameterFamily
    {n k : Nat} (hk : 1 ≤ k) (eta : Real) (heta0 : 0 ≤ eta)
    (heta : eta ≤ (1 : Real) / 16) (n' q c0 B : Nat) :
    SparseAdaptiveParameterFamily (SparseHiddenTable B n) n k where
  value t table h A :=
    sparseFeedbackParameter eta n' q c0
      (sparseHiddenTableU table) t h A
  measurable_value t := by
    have hitem : Measurable
        (fun input : SparseHiddenTable B n × History n k t =>
          fun i : Fin n =>
            sparseActive q c0 i t input.2 *
              sparseSignalWeight n' q
                (sparseHiddenTableU input.1) t i) := by
      refine Measurable.of_eval fun i => ?_
      have ha : Measurable
          (fun input : SparseHiddenTable B n × History n k t =>
            sparseActive q c0 i t input.2) :=
        (measurable_sparseActive i t).comp measurable_snd
      have hw : Measurable
          (fun input : SparseHiddenTable B n × History n k t =>
            sparseSignalWeight n' q
              (sparseHiddenTableU input.1) t i) := by
        by_cases hi : i.1 < n'
        · simp only [sparseSignalWeight, hi, if_true]
          exact (measurable_sparseHiddenTableU B n (t / q) i).comp
            measurable_fst
        · simp only [sparseSignalWeight, hi, if_false]
          exact measurable_const
      exact ha.mul hw
    unfold sparseFeedbackParameter sparseActionScore
    exact measurable_const.mul (measurable_actionLoss_joint hitem)
  abs_le t table h A :=
    (sparseFeedbackParameter_abs_le hk heta0
      (sparseHiddenTableU_abs_le_one table) t h A).trans heta

/-! ## Noise-only table family at a fixed hidden table -/

def sparseNoiseTableLossProcess
    {n k : Nat} (hk : 1 ≤ k) (eta : Real) (heta0 : 0 ≤ eta)
    (heta : eta ≤ (1 : Real) / 16) (n' q c0 T0 : Nat)
    (U : Nat → Fin n → Real) (hU : ∀ b i, |U b i| ≤ 1) :
    ParametricLossProcess (SparseNoiseTable T0) n k where
  itemLoss t table h :=
    sparseItemLoss eta n' q c0 T0 U (sparseNoiseTableAt table) t h
  measurable_itemLoss t := by
    refine Measurable.of_eval fun i => ?_
    by_cases ht : t < T0
    · simp only [sparseItemLoss, ht, if_true]
      have hz : Measurable
          (fun input : SparseNoiseTable T0 × History n k t =>
            sparseNoiseTableAt input.1 t) :=
        (measurable_sparseNoiseTableAt T0 t).comp measurable_fst
      have ha : Measurable
          (fun input : SparseNoiseTable T0 × History n k t =>
            sparseActive q c0 i t input.2) :=
        (measurable_sparseActive i t).comp measurable_snd
      exact ((measurable_const.add hz).div_const _).sub
        ((((measurable_const.mul (measurable_shape.comp hz)).mul ha).mul
          measurable_const))
    · simp only [sparseItemLoss, ht, if_false]
      exact measurable_const
  action_nonneg table t h A :=
    (lower_sparse_action_loss_mem_Icc hk heta0 heta n' q c0 T0 hU
      (sparseNoiseTableAt_mem_Icc table) t h A).1
  action_le_one table t h A :=
    (lower_sparse_action_loss_mem_Icc hk heta0 heta n' q c0 T0 hU
      (sparseNoiseTableAt_mem_Icc table) t h A).2

/-! ## The table-indexed deterministic sparse adversary -/

def sparseTableLossProcess
    {n k : Nat} (hk : 1 ≤ k) (eta : Real) (heta0 : 0 ≤ eta)
    (heta : eta ≤ (1 : Real) / 16) (n' q c0 T0 B : Nat) :
    ParametricLossProcess (SparseAuxTable B n T0) n k where
  itemLoss t table h :=
    sparseItemLoss eta n' q c0 T0
      (sparseTableU table) (sparseTableZ table) t h
  measurable_itemLoss t := by
    refine Measurable.of_eval fun i => ?_
    by_cases ht : t < T0
    · simp only [sparseItemLoss, ht, if_true]
      change Measurable (fun input : SparseAuxTable B n T0 × History n k t =>
        (1 + sparseTableZ input.1 t) / (2 * (k : Real)) -
          eta / (k : Real) * shape (sparseTableZ input.1 t) *
            sparseActive q c0 i t input.2 *
              sparseSignalWeight n' q (sparseTableU input.1) t i)
      have hz : Measurable (fun input : SparseAuxTable B n T0 × History n k t =>
          sparseTableZ input.1 t) :=
        (measurable_sparseTableZ B n T0 t).comp measurable_fst
      have ha : Measurable (fun input : SparseAuxTable B n T0 × History n k t =>
          sparseActive q c0 i t input.2) :=
        (measurable_sparseActive i t).comp measurable_snd
      have hw : Measurable (fun input : SparseAuxTable B n T0 × History n k t =>
          sparseSignalWeight n' q (sparseTableU input.1) t i) := by
        by_cases hi : i.1 < n'
        · simp only [sparseSignalWeight, hi, if_true]
          exact (measurable_sparseTableU B n T0 (t / q) i).comp measurable_fst
        · simp only [sparseSignalWeight, hi, if_false]
          exact measurable_const
      exact ((measurable_const.add hz).div_const _).sub
        ((((measurable_const.mul (measurable_shape.comp hz)).mul ha).mul hw))
    · simp only [sparseItemLoss, ht, if_false]
      change Measurable (fun _input : SparseAuxTable B n T0 × History n k t =>
        (0 : Real))
      exact measurable_const
  action_nonneg table t h A :=
    (lower_sparse_action_loss_mem_Icc hk heta0 heta n' q c0 T0
      (sparseTableU_abs_le_one table) (sparseTableZ_mem_Icc table) t h A).1
  action_le_one table t h A :=
    (lower_sparse_action_loss_mem_Icc hk heta0 heta n' q c0 T0
      (sparseTableU_abs_le_one table) (sparseTableZ_mem_Icc table) t h A).2

private theorem lossProcess_eq_of_itemLoss_eq
    {n k : Nat} (L K : LossProcess n k)
    (hitem : L.itemLoss = K.itemLoss) : L = K := by
  cases L
  cases K
  dsimp at hitem
  cases hitem
  rfl

theorem sparseTableLossProcess_at
    {n k : Nat} (hk : 1 ≤ k) (eta : Real) (heta0 : 0 ≤ eta)
    (heta : eta ≤ (1 : Real) / 16) (n' q c0 T0 B : Nat)
    (table : SparseAuxTable B n T0) :
    (sparseTableLossProcess hk eta heta0 heta n' q c0 T0 B).at table =
      sparseLossProcess hk eta heta0 heta n' q c0 T0
        (sparseTableU table) (sparseTableU_abs_le_one table)
        (sparseTableZ table) (sparseTableZ_mem_Icc table) := by
  apply lossProcess_eq_of_itemLoss_eq
  rfl

theorem sparseParametricRunKernel_apply
    {n k : Nat} (hk : 1 ≤ k) (eta : Real) (heta0 : 0 ≤ eta)
    (heta : eta ≤ (1 : Real) / 16) (n' q c0 T0 B : Nat)
    (P : Policy n k) (table : SparseAuxTable B n T0) :
    parametricRunKernel P
        (sparseTableLossProcess hk eta heta0 heta n' q c0 T0 B) T0 table =
      runLaw P
        ((sparseTableLossProcess hk eta heta0 heta n' q c0 T0 B).at table) T0 :=
  parametricRunKernel_apply P
    (sparseTableLossProcess hk eta heta0 heta n' q c0 T0 B) table T0

#print axioms sourceUniformMeasure_map_sparseClampUnit
#print axioms sparseHiddenColumnMeasure_isProbability
#print axioms sparseNoiseTableMeasure_isProbability
#print axioms sparseTableLossProcess_at
#print axioms sparseParametricRunKernel_apply

end

end MsetsLower.Lower.Sparse
