import MsetsLower.Core.Protocol

/-!
# Measurable statistics of the observable history

Adaptive constructions in the lower-bound proof repeatedly accumulate a
function of the learner's past actions.  This fold follows the nested history
type literally and establishes measurability once, rather than reproving it in
each construction.
-/

namespace MsetsLower.History

noncomputable section

/-- Sum a real statistic over all actions stored in a length-`t` history. -/
def actionSum {d m : Nat} (stat : MSetAction d m → Real) :
    (t : Nat) → History d m t → Real
  | 0, _ => 0
  | t + 1, h => actionSum stat t h.1 + stat h.2.1

@[simp] theorem actionSum_zero
    {d m : Nat} (stat : MSetAction d m → Real) (h : History d m 0) :
    actionSum stat 0 h = 0 := rfl

@[simp] theorem actionSum_succ
    {d m t : Nat} (stat : MSetAction d m → Real)
    (h : History d m (t + 1)) :
    actionSum stat (t + 1) h = actionSum stat t h.1 + stat h.2.1 := rfl

theorem measurable_actionSum
    {d m : Nat} {stat : MSetAction d m → Real} (hstat : Measurable stat) :
    ∀ t, Measurable (actionSum stat t) := by
  intro t
  induction t with
  | zero => exact measurable_const
  | succ t ih =>
      exact (ih.comp measurable_fst).add
        (hstat.comp (measurable_fst.comp measurable_snd))

/-- On the finite action space, every action statistic is measurable. -/
theorem measurable_actionSum_of_finite
    {d m : Nat} (stat : MSetAction d m → Real) (t : Nat) :
    Measurable (actionSum stat t) :=
  measurable_actionSum (measurable_of_finite stat) t

theorem actionSum_nonneg
    {d m : Nat} {stat : MSetAction d m → Real}
    (hstat : ∀ a, 0 ≤ stat a) :
    ∀ (t : Nat) (h : History d m t), 0 ≤ actionSum stat t h := by
  intro t
  induction t with
  | zero => intro h; simp
  | succ t ih =>
      intro h
      rw [actionSum_succ]
      exact add_nonneg (ih h.1) (hstat h.2.1)

/-- A pointwise bound on the per-action statistic yields the corresponding
linear bound on its history sum. -/
theorem actionSum_le
    {d m : Nat} {stat : MSetAction d m → Real} {c : Real}
    (hstat : ∀ a, stat a ≤ c) :
    ∀ (t : Nat) (h : History d m t), actionSum stat t h ≤ t * c := by
  intro t
  induction t with
  | zero => intro h; simp
  | succ t ih =>
      intro h
      rw [actionSum_succ]
      have hprev := ih h.1
      have hlast := hstat h.2.1
      push_cast
      nlinarith

/-- Indicator that an item belongs to an action. -/
def selectedIndicator {d m : Nat} (i : Fin d) (a : MSetAction d m) : Real :=
  if i ∈ a.1 then 1 else 0

theorem selectedIndicator_mem
    {d m : Nat} (i : Fin d) (a : MSetAction d m) (hi : i ∈ a.1) :
    selectedIndicator i a = 1 := by simp [selectedIndicator, hi]

theorem selectedIndicator_not_mem
    {d m : Nat} (i : Fin d) (a : MSetAction d m) (hi : i ∉ a.1) :
    selectedIndicator i a = 0 := by simp [selectedIndicator, hi]

theorem selectedIndicator_mem_Icc
    {d m : Nat} (i : Fin d) (a : MSetAction d m) :
    selectedIndicator i a ∈ Set.Icc (0 : Real) 1 := by
  by_cases hi : i ∈ a.1 <;> simp [selectedIndicator, hi]

/-- Number of prior selections of coordinate `i`, represented as a real
history statistic. -/
def selectedCount {d m : Nat} (i : Fin d) (t : Nat) (h : History d m t) : Real :=
  actionSum (selectedIndicator i) t h

theorem measurable_selectedCount
    {d m : Nat} (i : Fin d) (t : Nat) :
    Measurable (selectedCount (m := m) i t) :=
  measurable_actionSum_of_finite _ _

theorem selectedCount_mem_Icc
    {d m : Nat} (i : Fin d) (t : Nat) (h : History d m t) :
    selectedCount i t h ∈ Set.Icc (0 : Real) t := by
  constructor
  · exact actionSum_nonneg (fun a => (selectedIndicator_mem_Icc i a).1) t h
  · simpa [selectedCount] using
      (actionSum_le (fun a => (selectedIndicator_mem_Icc i a).2) t h)

end

end MsetsLower.History
