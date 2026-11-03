import MsetsLower.Core.HistoryPrefix
import MsetsLower.Lower.RegretMeasurability

/-!
# Regret after an inactive suffix

Sparse lower-bound environments are active for `T0` rounds and identically
zero afterwards.  These lemmas prove, pathwise and at the level of the run
law, that extending such an experiment does not change external regret.
-/

namespace MsetsLower.Lower

open MsetsLower MeasureTheory Set

noncomputable section

/-- From round `s` onward every action has zero aggregate loss. -/
def ZeroActionLossFrom {d m : Nat} (L : LossProcess d m)
    (s : Nat) : Prop :=
  ∀ t, s ≤ t → ∀ (h : History d m t) (a : MSetAction d m),
    actionLoss a (L.itemLoss t h) = 0

theorem realizedCumulativeLoss_add_of_zeroFrom
    {d m s : Nat} {L : LossProcess d m}
    (hzero : ZeroActionLossFrom L s) :
    ∀ r (h : History d m (s + r)),
      realizedCumulativeLoss L (s + r) h =
        realizedCumulativeLoss L s (History.dropSuffix s r h) := by
  intro r
  induction r with
  | zero => intro h; rfl
  | succ r ih =>
      intro h
      change realizedCumulativeLoss L (s + r) h.1 +
          actionLoss h.2.1 (L.itemLoss (s + r) h.1) =
        realizedCumulativeLoss L s (History.dropSuffix s r h.1)
      rw [hzero (s + r) (by omega) h.1 h.2.1, add_zero]
      exact ih h.1

theorem comparatorCumulativeLoss_add_of_zeroFrom
    {d m s : Nat} {L : LossProcess d m}
    (hzero : ZeroActionLossFrom L s) :
    ∀ r (h : History d m (s + r)) (a : MSetAction d m),
      comparatorCumulativeLoss L (s + r) h a =
        comparatorCumulativeLoss L s (History.dropSuffix s r h) a := by
  intro r
  induction r with
  | zero => intro h a; rfl
  | succ r ih =>
      intro h a
      change comparatorCumulativeLoss L (s + r) h.1 a +
          actionLoss a (L.itemLoss (s + r) h.1) =
        comparatorCumulativeLoss L s (History.dropSuffix s r h.1) a
      rw [hzero (s + r) (by omega) h.1 a, add_zero]
      exact ih h.1 a

theorem bestComparatorCumulativeLoss_add_of_zeroFrom
    {d m s r : Nat} {L : LossProcess d m}
    (hzero : ZeroActionLossFrom L s) (h : History d m (s + r)) :
    bestComparatorCumulativeLoss L (s + r) h =
      bestComparatorCumulativeLoss L s (History.dropSuffix s r h) := by
  unfold bestComparatorCumulativeLoss
  rw [show comparatorCumulativeLoss L (s + r) h =
      comparatorCumulativeLoss L s (History.dropSuffix s r h) by
    funext a
    exact comparatorCumulativeLoss_add_of_zeroFrom hzero r h a]

theorem pathRegret_add_of_zeroFrom
    {d m s r : Nat} {L : LossProcess d m}
    (hzero : ZeroActionLossFrom L s) (h : History d m (s + r)) :
    pathRegret L (s + r) h =
      pathRegret L s (History.dropSuffix s r h) := by
  unfold pathRegret
  rw [realizedCumulativeLoss_add_of_zeroFrom hzero r h,
    bestComparatorCumulativeLoss_add_of_zeroFrom hzero h]

/-- The regret lower-tail probability is invariant under a suffix of
zero-loss rounds. -/
theorem runLaw_add_regretTailProbability_of_zeroFrom
    {d m s r : Nat} (hmd : m ≤ d) (P : Policy d m)
    (L : LossProcess d m) (hzero : ZeroActionLossFrom L s)
    (threshold : Real) :
    (runLaw P L (s + r)).real
        {h | threshold ≤ pathRegret L (s + r) h} =
      (runLaw P L s).real
        {h | threshold ≤ pathRegret L s h} := by
  letI : Nonempty (MSetAction d m) := nonempty_MSetAction hmd
  let E : Set (History d m s) := {h | threshold ≤ pathRegret L s h}
  have hE : MeasurableSet E := measurableSet_pathRegret_ge L s threshold
  have hpre :
      History.dropSuffix s r ⁻¹' E =
        {h | threshold ≤ pathRegret L (s + r) h} := by
    ext h
    change (threshold ≤ pathRegret L s (History.dropSuffix s r h)) ↔
      threshold ≤ pathRegret L (s + r) h
    rw [pathRegret_add_of_zeroFrom hzero h]
  have hmap := runLaw_add_map_dropSuffix P L s r
  have happly := congrArg (fun μ : Measure (History d m s) => μ E) hmap
  rw [Measure.map_apply (History.measurable_dropSuffix s r) hE] at happly
  have hreal := congrArg ENNReal.toReal happly
  simpa [Measure.real, hpre] using hreal

#print axioms realizedCumulativeLoss_add_of_zeroFrom
#print axioms comparatorCumulativeLoss_add_of_zeroFrom
#print axioms pathRegret_add_of_zeroFrom
#print axioms runLaw_add_regretTailProbability_of_zeroFrom

end

end MsetsLower.Lower
