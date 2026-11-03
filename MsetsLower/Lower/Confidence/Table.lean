import MsetsLower.Feedback.Moments
import MsetsLower.Lower.Confidence.ObservableScore
import MsetsLower.Lower.ParametricRegret
import Mathlib.MeasureTheory.Integral.Prod

/-!
# Finite noise tables for the confidence construction

The auxiliary table is a genuinely finite product, represented recursively
as a snoc-list.  Its entries are real-valued and are clipped to `[-1,1]`
before they are used.  Consequently every fixed table, including parameters
outside the support of the product measure, defines an admissible deterministic
loss process.  On the product measure the clipping is almost surely the
identity.
-/

namespace MsetsLower.Lower.Confidence

open MsetsLower Feedback MeasureTheory ProbabilityTheory Set
open scoped ENNReal ProbabilityTheory

noncomputable section

/-- A length-`T` real table, stored in prefix--last-coordinate form. -/
@[reducible] def ConfidenceNoiseTable : Nat → Type
  | 0 => PUnit
  | T + 1 => ConfidenceNoiseTable T × Real

@[reducible] instance confidenceNoiseTableMeasurableSpace :
    (T : Nat) → MeasurableSpace (ConfidenceNoiseTable T)
  | 0 => inferInstanceAs (MeasurableSpace PUnit)
  | T + 1 => @Prod.instMeasurableSpace (ConfidenceNoiseTable T) Real
      (confidenceNoiseTableMeasurableSpace T) Real.measurableSpace

/-- Product-uniform law on the finite table. -/
def confidenceNoiseTableMeasure :
    (T : Nat) → Measure (ConfidenceNoiseTable T)
  | 0 => Measure.dirac PUnit.unit
  | T + 1 =>
      (confidenceNoiseTableMeasure T).prod sourceUniformMeasure

theorem confidenceNoiseTableMeasure_isProbability :
    (T : Nat) → IsProbabilityMeasure (confidenceNoiseTableMeasure T)
  | 0 => by
      rw [isProbabilityMeasure_iff, confidenceNoiseTableMeasure]
      simp
  | T + 1 => by
      letI : IsProbabilityMeasure (confidenceNoiseTableMeasure T) :=
        confidenceNoiseTableMeasure_isProbability T
      letI : IsProbabilityMeasure sourceUniformMeasure := inferInstance
      exact Measure.prod.instIsProbabilityMeasure _ _

instance (T : Nat) :
    IsProbabilityMeasure (confidenceNoiseTableMeasure T) :=
  confidenceNoiseTableMeasure_isProbability T

/-- Total clipping used to make every parameter admissible. -/
def clampConfidenceNoise (z : Real) : Real :=
  max (-1) (min 1 z)

theorem measurable_clampConfidenceNoise :
    Measurable clampConfidenceNoise := by
  exact measurable_const.max (measurable_const.min measurable_id)

theorem clampConfidenceNoise_mem_Icc (z : Real) :
    clampConfidenceNoise z ∈ Icc (-1 : Real) 1 := by
  constructor
  · exact le_max_left _ _
  · rw [clampConfidenceNoise]
    exact max_le (by norm_num) (min_le_left _ _)

@[simp] theorem clampConfidenceNoise_eq_self
    {z : Real} (hz : z ∈ Icc (-1 : Real) 1) :
    clampConfidenceNoise z = z := by
  rw [clampConfidenceNoise, min_eq_right hz.2, max_eq_right hz.1]

theorem sourceUniformMeasure_map_clampConfidenceNoise :
    sourceUniformMeasure.map clampConfidenceNoise = sourceUniformMeasure := by
  calc
    sourceUniformMeasure.map clampConfidenceNoise =
        sourceUniformMeasure.map id := by
      apply Measure.map_congr
      filter_upwards [ae_sourceUniformMeasure_mem_Icc] with z hz
      exact clampConfidenceNoise_eq_self hz
    _ = sourceUniformMeasure := Measure.map_id

/-- The un-clipped coordinate of a finite table. -/
def confidenceNoiseTableRawAt :
    {T : Nat} → ConfidenceNoiseTable T → Fin T → Real
  | 0, _, r => Fin.elim0 r
  | T + 1, table, r =>
      Fin.lastCases table.2
        (fun q => confidenceNoiseTableRawAt table.1 q) r

theorem measurable_confidenceNoiseTableRawAt
    (T : Nat) (r : Fin T) :
    Measurable
      (fun table : ConfidenceNoiseTable T =>
        confidenceNoiseTableRawAt table r) := by
  induction T with
  | zero => exact Fin.elim0 r
  | succ T ih =>
      have hspace : confidenceNoiseTableMeasurableSpace (T + 1) =
          @Prod.instMeasurableSpace (ConfidenceNoiseTable T) Real
            (confidenceNoiseTableMeasurableSpace T) Real.measurableSpace := rfl
      rw [hspace]
      refine Fin.lastCases ?_ (fun q => ?_) r
      · change Measurable
          (fun table : ConfidenceNoiseTable T × Real =>
            confidenceNoiseTableRawAt (T := T + 1) table (Fin.last T))
        simpa [confidenceNoiseTableRawAt] using
          (measurable_snd : Measurable
            (fun table : ConfidenceNoiseTable T × Real => table.2))
      · change Measurable
          (fun table : ConfidenceNoiseTable T × Real =>
            confidenceNoiseTableRawAt (T := T + 1) table q.castSucc)
        simpa [confidenceNoiseTableRawAt, Function.comp_def] using
          (ih q).comp (measurable_fst : Measurable
            (fun table : ConfidenceNoiseTable T × Real => table.1))

/-- Noise stream read from a length-`T` table, with zero padding after `T`. -/
def confidenceTableNoise {T : Nat}
    (table : ConfidenceNoiseTable T) (t : Nat) : Real :=
  if ht : t < T then
    clampConfidenceNoise
      (confidenceNoiseTableRawAt table ⟨t, ht⟩)
  else 0

theorem measurable_confidenceTableNoise (T t : Nat) :
    Measurable
      (fun table : ConfidenceNoiseTable T => confidenceTableNoise table t) := by
  by_cases ht : t < T
  · simp only [confidenceTableNoise, dif_pos ht]
    exact measurable_clampConfidenceNoise.comp
      (measurable_confidenceNoiseTableRawAt T ⟨t, ht⟩)
  · simp only [confidenceTableNoise, dif_neg ht]
    exact measurable_const

theorem confidenceTableNoise_mem_Icc {T : Nat}
    (table : ConfidenceNoiseTable T) (t : Nat) :
    confidenceTableNoise table t ∈ Icc (-1 : Real) 1 := by
  by_cases ht : t < T
  · rw [confidenceTableNoise, dif_pos ht]
    exact clampConfidenceNoise_mem_Icc _
  · rw [confidenceTableNoise, dif_neg ht]
    norm_num

@[simp] theorem confidenceTableNoise_snoc_last {T : Nat}
    (table : ConfidenceNoiseTable T) (z : Real) :
    confidenceTableNoise (T := T + 1) (table, z) T =
      clampConfidenceNoise z := by
  have ht : T < T + 1 := by omega
  rw [confidenceTableNoise, dif_pos ht]
  have hfin : (⟨T, ht⟩ : Fin (T + 1)) = Fin.last T := Fin.ext rfl
  rw [hfin]
  simp [confidenceNoiseTableRawAt]

@[simp] theorem confidenceTableNoise_snoc_prefix {T r : Nat}
    (table : ConfidenceNoiseTable T) (z : Real) (hr : r < T) :
    confidenceTableNoise (T := T + 1) (table, z) r =
      confidenceTableNoise table r := by
  have hr' : r < T + 1 := hr.trans (by omega)
  rw [confidenceTableNoise, dif_pos hr', confidenceTableNoise, dif_pos hr]
  have hfin : (⟨r, hr'⟩ : Fin (T + 1)) =
      (⟨r, hr⟩ : Fin T).castSucc := Fin.ext rfl
  congr 1
  change Fin.lastCases z (fun q => confidenceNoiseTableRawAt table q)
      ⟨r, hr'⟩ = confidenceNoiseTableRawAt table ⟨r, hr⟩
  rw [hfin]
  exact Fin.lastCases_castSucc ⟨r, hr⟩

/-- Jointly measurable reference family indexed by a clipped finite table. -/
def confidenceReferenceTableLossProcess
    {n k : Nat} (hk : 1 ≤ k) (hkn : k ≤ n) (T : Nat) :
    ParametricLossProcess (ConfidenceNoiseTable T) n k where
  itemLoss t table _ :=
    referenceItemLoss hkn (confidenceTableNoise table t)
  measurable_itemLoss t := by
    refine Measurable.of_eval fun j => ?_
    change Measurable (fun input : ConfidenceNoiseTable T × History n k t =>
      ((1 : Real) / 4 + confidenceTableNoise input.1 t / 8) / (k : Real) +
        (1 / (8 * (k : Real))) * candidateIndicator hkn j)
    have hz : Measurable
        (fun input : ConfidenceNoiseTable T × History n k t =>
          confidenceTableNoise input.1 t) :=
      (measurable_confidenceTableNoise T t).comp measurable_fst
    exact ((measurable_const.add (hz.div_const 8)).div_const _).add
      measurable_const
  action_nonneg table t h A := by
    exact (actionLoss_referenceItemLoss_mem_Icc hk hkn
      (confidenceTableNoise_mem_Icc table t) A).1.trans' (by positivity)
  action_le_one table t h A :=
    (actionLoss_referenceItemLoss_mem_Icc hk hkn
      (confidenceTableNoise_mem_Icc table t) A).2.trans (by norm_num)

/-- Jointly measurable planted family indexed by a clipped finite table. -/
def confidencePlantedTableLossProcess
    {n k : Nat} (hk : 1 ≤ k) (hkn : k ≤ n) (T : Nat)
    (Delta : Real) (hDelta : 0 ≤ Delta)
    (hsmall : (k : Real) * Delta ≤ 1 / (2 : Real) ^ 13)
    (B : Real) (i : Fin n) :
    ParametricLossProcess (ConfidenceNoiseTable T) n k where
  itemLoss t table h :=
    plantedItemLoss hkn (confidenceTableNoise table t) Delta
      (activeIndicator hkn B t h) i
  measurable_itemLoss t := by
    refine Measurable.of_eval fun j => ?_
    change Measurable (fun input : ConfidenceNoiseTable T × History n k t =>
      referenceItemLoss hkn (confidenceTableNoise input.1 t) j -
        Delta * shape (confidenceTableNoise input.1 t) *
          activeIndicator hkn B t input.2 * (if j = i then 1 else 0))
    have hz : Measurable
        (fun input : ConfidenceNoiseTable T × History n k t =>
          confidenceTableNoise input.1 t) :=
      (measurable_confidenceTableNoise T t).comp measurable_fst
    have ha : Measurable
        (fun input : ConfidenceNoiseTable T × History n k t =>
          activeIndicator hkn B t input.2) :=
      (measurable_activeIndicator hkn B t).comp measurable_snd
    exact ((measurable_const.add (hz.div_const 8)).div_const _ |>.add
      measurable_const).sub
        (((measurable_const.mul (measurable_shape.comp hz)).mul ha).mul
          measurable_const)
  action_nonneg table t h A :=
    (actionLoss_plantedItemLoss_mem_Icc hk hkn
      (confidenceTableNoise_mem_Icc table t) hDelta hsmall
      (activeIndicator_mem_Icc hkn B t h) i A).1
  action_le_one table t h A :=
    (actionLoss_plantedItemLoss_mem_Icc hk hkn
      (confidenceTableNoise_mem_Icc table t) hDelta hsmall
      (activeIndicator_mem_Icc hkn B t h) i A).2

private theorem lossProcess_eq_of_itemLoss_eq
    {n k : Nat} (L K : LossProcess n k)
    (hitem : L.itemLoss = K.itemLoss) : L = K := by
  cases L with
  | mk leftItem leftMeas leftNonneg leftLe =>
      cases K with
      | mk rightItem rightMeas rightNonneg rightLe =>
          dsimp at hitem
          cases hitem
          rfl

theorem confidenceReferenceTableLossProcess_at
    {n k T : Nat} (hk : 1 ≤ k) (hkn : k ≤ n)
    (table : ConfidenceNoiseTable T) :
    (confidenceReferenceTableLossProcess hk hkn T).at table =
      referenceLossProcess hk hkn (confidenceTableNoise table)
        (confidenceTableNoise_mem_Icc table) := by
  apply lossProcess_eq_of_itemLoss_eq
  rfl

theorem confidencePlantedTableLossProcess_at
    {n k T : Nat} (hk : 1 ≤ k) (hkn : k ≤ n)
    (table : ConfidenceNoiseTable T)
    (Delta : Real) (hDelta : 0 ≤ Delta)
    (hsmall : (k : Real) * Delta ≤ 1 / (2 : Real) ^ 13)
    (B : Real) (i : Fin n) :
    (confidencePlantedTableLossProcess hk hkn T Delta hDelta hsmall B i).at table =
      plantedLossProcess hk hkn (confidenceTableNoise table)
        (confidenceTableNoise_mem_Icc table) Delta hDelta hsmall B i := by
  apply lossProcess_eq_of_itemLoss_eq
  rfl

#print axioms confidenceNoiseTableMeasure_isProbability
#print axioms sourceUniformMeasure_map_clampConfidenceNoise
#print axioms confidenceReferenceTableLossProcess_at
#print axioms confidencePlantedTableLossProcess_at

end

end MsetsLower.Lower.Confidence
