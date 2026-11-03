import MsetsLower.Lower.Complement
import Mathlib.MeasureTheory.Constructions.BorelSpace.Order

/-!
# Measurability of finite-horizon regret

The fixing-table and probability arguments use events of the form
`{R_T ≥ r}`.  This file proves that the pathwise regret defined from the
observable history is measurable; no measurability of a best-action selector
is assumed.
-/

namespace MsetsLower.Lower

open MsetsLower MeasureTheory Set

noncomputable section

theorem measurable_realizedCumulativeLoss {d m : Nat}
    (L : LossProcess d m) :
    ∀ t, Measurable (realizedCumulativeLoss L t) := by
  intro t
  induction t with
  | zero => exact measurable_const
  | succ t ih =>
      change Measurable (fun h : History d m (t + 1) ↦
        realizedCumulativeLoss L t h.1 +
          actionLoss h.2.1 (L.itemLoss t h.1))
      have hpair : Measurable (fun h : History d m (t + 1) ↦ (h.1, h.2.1)) :=
        measurable_fst.prodMk (measurable_fst.comp measurable_snd)
      exact (ih.comp measurable_fst).add
        ((measurable_actionLoss_joint (L.measurable_itemLoss t)).comp hpair)

theorem measurable_comparatorCumulativeLoss {d m : Nat}
    (L : LossProcess d m) (a : MSetAction d m) :
    ∀ t, Measurable (fun h : History d m t ↦
      comparatorCumulativeLoss L t h a) := by
  intro t
  induction t with
  | zero => exact measurable_const
  | succ t ih =>
      change Measurable (fun h : History d m (t + 1) ↦
        comparatorCumulativeLoss L t h.1 a +
          actionLoss a (L.itemLoss t h.1))
      exact (ih.comp measurable_fst).add
        ((measurable_actionLoss a (L.measurable_itemLoss t)).comp measurable_fst)

/-- The best fixed-comparator value is measurable as a finite infimum. -/
theorem measurable_bestComparatorCumulativeLoss {d m : Nat}
    [Nonempty (MSetAction d m)] (L : LossProcess d m) (t : Nat) :
    Measurable (bestComparatorCumulativeLoss L t) := by
  unfold bestComparatorCumulativeLoss
  change Measurable (fun h : History d m t ↦
    ⨅ a : MSetAction d m, comparatorCumulativeLoss L t h a)
  exact Measurable.iInf fun a ↦ measurable_comparatorCumulativeLoss L a t

theorem measurable_pathRegret {d m : Nat}
    [Nonempty (MSetAction d m)] (L : LossProcess d m) (t : Nat) :
    Measurable (pathRegret L t) := by
  unfold pathRegret
  exact (measurable_realizedCumulativeLoss L t).sub
    (measurable_bestComparatorCumulativeLoss L t)

/-- In particular, every regret lower-tail event used in the manuscript is a
measurable event under the run law. -/
theorem measurableSet_pathRegret_ge {d m : Nat}
    [Nonempty (MSetAction d m)] (L : LossProcess d m) (t : Nat) (r : Real) :
    MeasurableSet {h : History d m t | r ≤ pathRegret L t h} := by
  exact measurableSet_le measurable_const (measurable_pathRegret L t)

theorem measurableSet_pathRegret_ge_of_le {d m : Nat} (hmd : m ≤ d)
    (L : LossProcess d m) (t : Nat) (r : Real) :
    MeasurableSet {h : History d m t | r ≤ pathRegret L t h} := by
  letI : Nonempty (MSetAction d m) := nonempty_MSetAction hmd
  exact measurableSet_pathRegret_ge L t r

end

end MsetsLower.Lower
