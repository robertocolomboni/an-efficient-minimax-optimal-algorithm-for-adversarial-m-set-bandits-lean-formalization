import MsetsLower.Core.ParametricRun
import MsetsLower.Lower.Dense.PairedConstruction
import MsetsLower.Lower.Dense.Moment
import MsetsLower.Lower.RegretMeasurability
import Mathlib.MeasureTheory.Constructions.Pi

/-!
# Auxiliary tables for the dense construction

The iid paired items are a proof device.  This file realizes a complete item
table as a measurable parameter and shows that fixing it gives a deterministic
loss sequence fixed in advance, while retaining the exact loss formula of the
manuscript.
-/

set_option linter.style.header false

namespace MsetsLower.Lower.Dense

open MsetsLower MeasureTheory ProbabilityTheory
open scoped ENNReal ProbabilityTheory

noncomputable section

/-- A complete table of paired items.  Only its first `T` coordinates are used
at horizon `T`; using `Nat` makes the same family reusable at every horizon. -/
abbrev DenseItemTable (k T : Nat) := Fin T → PairItem k

/-- Read the `t`-th entry inside the table horizon and use a harmless default
paired item afterward. -/
def denseTableItem {k T : Nat} (hk : 1 ≤ k)
    (table : DenseItemTable k T) (t : Nat) : PairItem k :=
  if ht : t < T then table ⟨t, ht⟩ else (⟨0, hk⟩, false)

/-- The table-indexed paired losses form a jointly measurable parametric loss
process.  They do not depend on history, so each fixed section is a loss
sequence fixed in advance. -/
def denseTableLossProcess {n k : Nat} (hk : 1 ≤ k) (hD : 2 * k ≤ n)
    (T : Nat) : ParametricLossProcess (DenseItemTable k T) n k where
  itemLoss t table history := pairedLoss hD (denseTableItem hk table t)
  measurable_itemLoss t := by
    apply measurable_pi_lambda
    intro i
    have htable : Measurable (fun table : DenseItemTable k T =>
        pairedLoss hD (denseTableItem hk table t) i) :=
      measurable_of_finite _
    exact htable.comp measurable_fst
  action_nonneg table t history action :=
    (lower_dense_action_loss_mem_Icc hk hD action
      (denseTableItem hk table t)).1
  action_le_one table t history action :=
    (lower_dense_action_loss_mem_Icc hk hD action
      (denseTableItem hk table t)).2

@[simp] theorem denseTableLossProcess_itemLoss
    {n k : Nat} (hk : 1 ≤ k) (hD : 2 * k ≤ n)
    (T : Nat) (table : DenseItemTable k T) (t : Nat)
    (history : History n k t) :
    (denseTableLossProcess hk hD T).itemLoss t table history =
      pairedLoss hD (denseTableItem hk table t) := rfl

@[simp] theorem denseTableLossProcess_at_itemLoss
    {n k : Nat} (hk : 1 ≤ k) (hD : 2 * k ≤ n)
    (T : Nat) (table : DenseItemTable k T) (t : Nat)
    (history : History n k t) :
    ((denseTableLossProcess hk hD T).at table).itemLoss t history =
      pairedLoss hD (denseTableItem hk table t) := rfl

@[simp] theorem denseTableItem_of_lt {k T : Nat} (hk : 1 ≤ k)
    (table : DenseItemTable k T) {t : Nat} (ht : t < T) :
    denseTableItem hk table t = table ⟨t, ht⟩ := by
  simp [denseTableItem, ht]

/-- Every fixed table section is history-independent, which is the formal
meaning of "fixed in advance" in `prop:lower-bounded-action`. -/
theorem denseTableLossProcess_fixedInAdvance
    {n k : Nat} (hk : 1 ≤ k) (hD : 2 * k ≤ n)
    (T : Nat) (table : DenseItemTable k T) (t : Nat)
    (history history' : History n k t) :
    ((denseTableLossProcess hk hD T).at table).itemLoss t history =
      ((denseTableLossProcess hk hD T).at table).itemLoss t history' := by
  rfl

/-- Reconstruct the latent action/item history from an observable history and
a fixed table.  The stored scalar feedback is deliberately ignored; regret is
recomputed from the loss table in both semantics. -/
def denseLatentHistory {n k T : Nat} (hk : 1 ≤ k)
    (table : DenseItemTable k T) :
    (t : Nat) → History n k t → PairedJointHistory n k t
  | 0, _ => ()
  | t + 1, history =>
      (denseLatentHistory hk table t history.1,
        (history.2.1, denseTableItem hk table t))

theorem measurable_denseLatentHistory {n k T : Nat} (hk : 1 ≤ k)
    (table : DenseItemTable k T) : ∀ t,
    Measurable (denseLatentHistory (n := n) hk table t) := by
  intro t
  induction t with
  | zero => exact measurable_const
  | succ t ih =>
      exact (ih.comp measurable_fst).prodMk
        ((measurable_fst.comp measurable_snd).prodMk measurable_const)

theorem realizedCumulativeLoss_denseTable
    {n k T : Nat} (hk : 1 ≤ k) (hD : 2 * k ≤ n)
    (table : DenseItemTable k T) : ∀ t (history : History n k t),
    realizedCumulativeLoss ((denseTableLossProcess hk hD T).at table) t history =
      pairedLearnerCumulativeLoss hD t (denseLatentHistory hk table t history) := by
  intro t
  induction t with
  | zero => intro history; rfl
  | succ t ih =>
      intro history
      rw [realizedCumulativeLoss, pairedLearnerCumulativeLoss, ih history.1]
      rfl

theorem comparatorCumulativeLoss_denseTable
    {n k T : Nat} (hk : 1 ≤ k) (hD : 2 * k ≤ n)
    (table : DenseItemTable k T) : ∀ t (history : History n k t)
      (action : MSetAction n k),
    comparatorCumulativeLoss ((denseTableLossProcess hk hD T).at table)
        t history action =
      pairedFixedCumulativeLoss hD t
        (denseLatentHistory hk table t history) action := by
  intro t
  induction t with
  | zero => intro history action; rfl
  | succ t ih =>
      intro history action
      rw [comparatorCumulativeLoss, pairedFixedCumulativeLoss,
        ih history.1 action]
      rfl

theorem bestComparatorCumulativeLoss_denseTable
    {n k T : Nat} (hk : 1 ≤ k) (hD : 2 * k ≤ n)
    (table : DenseItemTable k T) (t : Nat) (history : History n k t) :
    bestComparatorCumulativeLoss
        ((denseTableLossProcess hk hD T).at table) t history =
      pairedBestCumulativeLoss hD t
        (denseLatentHistory hk table t history) := by
  unfold bestComparatorCumulativeLoss pairedBestCumulativeLoss
  have hfunctions :
      comparatorCumulativeLoss ((denseTableLossProcess hk hD T).at table)
          t history =
        pairedFixedCumulativeLoss hD t
          (denseLatentHistory hk table t history) := by
    funext action
    exact comparatorCumulativeLoss_denseTable hk hD table t history action
  rw [hfunctions]

/-- The latent external regret used in the moment proof is exactly the
protocol's external regret for every fixed table section. -/
theorem pathRegret_denseTable
    {n k T : Nat} (hk : 1 ≤ k) (hD : 2 * k ≤ n)
    (table : DenseItemTable k T) (t : Nat) (history : History n k t) :
    pathRegret ((denseTableLossProcess hk hD T).at table) t history =
      pairedExternalRegret hD t (denseLatentHistory hk table t history) := by
  unfold pathRegret pairedExternalRegret
  rw [realizedCumulativeLoss_denseTable hk hD table t history,
    bestComparatorCumulativeLoss_denseTable hk hD table t history]

/-- Product law of the iid item table under a paired hypothesis. -/
def denseItemTableMeasure {k T : Nat} (hk : 1 ≤ k)
    (theta : Fin k → PairSign) (epsilon : Real)
    (hepsilon_nonneg : 0 ≤ epsilon) (hepsilon_le_one : epsilon ≤ 1) :
    Measure (DenseItemTable k T) :=
  Measure.pi (fun _ => (pairedPMF hk theta epsilon
    hepsilon_nonneg hepsilon_le_one).toMeasure)

instance denseItemTableMeasure.instIsProbabilityMeasure
    {k T : Nat} (hk : 1 ≤ k) (theta : Fin k → PairSign)
    (epsilon : Real) (hepsilon_nonneg : 0 ≤ epsilon)
    (hepsilon_le_one : epsilon ≤ 1) :
    IsProbabilityMeasure
      (denseItemTableMeasure (T := T) hk theta epsilon
        hepsilon_nonneg hepsilon_le_one) := by
  unfold denseItemTableMeasure
  infer_instance

/-- A coordinate of the iid table has exactly the displayed paired law. -/
theorem denseItemTableMeasure_map_apply
    {k T : Nat} (hk : 1 ≤ k) (theta : Fin k → PairSign)
    (epsilon : Real) (hepsilon_nonneg : 0 ≤ epsilon)
    (hepsilon_le_one : epsilon ≤ 1) (t : Fin T) :
    (denseItemTableMeasure hk theta epsilon hepsilon_nonneg
      hepsilon_le_one).map (fun table => table t) =
      (pairedPMF hk theta epsilon hepsilon_nonneg
        hepsilon_le_one).toMeasure := by
  exact (measurePreserving_eval
    (fun _ : Fin T => (pairedPMF hk theta epsilon hepsilon_nonneg
      hepsilon_le_one).toMeasure) t).map_eq

/-- Every section of the table-indexed kernel is the actual protocol law for
the corresponding deterministic fixed-in-advance loss sequence. -/
theorem denseParametricRunKernel_apply
    {n k : Nat} (hk : 1 ≤ k) (hD : 2 * k ≤ n)
    (P : Policy n k) (T : Nat) (table : DenseItemTable k T) :
    parametricRunKernel P (denseTableLossProcess hk hD T) T table =
      runLaw P ((denseTableLossProcess hk hD T).at table) T :=
  parametricRunKernel_apply P (denseTableLossProcess hk hD T) table T

#print axioms denseTableLossProcess_fixedInAdvance
#print axioms pathRegret_denseTable
#print axioms denseItemTableMeasure_map_apply
#print axioms denseParametricRunKernel_apply

end

end MsetsLower.Lower.Dense
