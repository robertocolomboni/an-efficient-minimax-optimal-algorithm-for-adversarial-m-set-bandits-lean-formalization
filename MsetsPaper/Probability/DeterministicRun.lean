import MsetsLower.Core.Protocol

/-! # Literal deterministic interaction and its exact Dirac run law -/

noncomputable section
open MeasureTheory ProbabilityTheory MsetsLower MsetsLower.History

namespace MsetsPaper.Probability

variable {d m : ℕ}

def deterministicRun (choose : (t : ℕ) → History d m t → MSetAction d m)
    (L : LossProcess d m) : (t : ℕ) → History d m t
  | 0 => ()
  | t + 1 =>
      let h := deterministicRun choose L t
      let a := choose t h
      h.snoc a (actionLoss a (L.itemLoss t h))

theorem deterministic_roundKernel
    (choose : (t : ℕ) → History d m t → MSetAction d m)
    (hc : ∀ t, Measurable (choose t)) (L : LossProcess d m)
    (t : ℕ) (h : History d m t) :
    roundKernel (Policy.deterministic choose hc) L t h =
      Measure.dirac (h.snoc (choose t h) (actionLoss (choose t h) (L.itemLoss t h))) := by
  ext s hs
  rw [roundKernel_apply _ _ _ _ hs]
  change (Measure.dirac (choose t h)) {a | h.snoc a (actionLoss a (L.itemLoss t h)) ∈ s} = _
  rw [Measure.dirac_apply, Measure.dirac_apply]
  rfl

theorem runLaw_deterministic_eq_dirac
    (choose : (t : ℕ) → History d m t → MSetAction d m)
    (hc : ∀ t, Measurable (choose t)) (L : LossProcess d m) :
    ∀ t, runLaw (Policy.deterministic choose hc) L t = Measure.dirac (deterministicRun choose L t) := by
  intro t
  induction t with
  | zero => rfl
  | succ t ih =>
    ext s hs
    rw [runLaw_succ_apply _ _ _ hs, ih,
      lintegral_dirac' _ ((roundKernel (Policy.deterministic choose hc) L t).measurable_coe hs),
      deterministic_roundKernel]
    rfl

theorem measurable_deterministicRun {Ξ : Type*} [MeasurableSpace Ξ]
    (choose : (t : ℕ) → Ξ → History d m t → MSetAction d m)
    (hc : ∀ t, Measurable (Function.uncurry (choose t)))
    (L : Ξ → LossProcess d m)
    (hL : ∀ t, Measurable (fun x : Ξ × History d m t ↦ (L x.1).itemLoss t x.2)) :
    ∀ t, Measurable (fun x ↦ deterministicRun (fun t h ↦ choose t x h) (L x) t) := by
  intro t
  induction t with
  | zero => exact measurable_const
  | succ t ih =>
    have ha := (hc t).comp (measurable_id.prodMk ih)
    have hl := (hL t).comp (measurable_id.prodMk ih)
    exact ih.prodMk (ha.prodMk
      ((measurable_actionLoss_joint hl).comp (measurable_id.prodMk ha)))

end MsetsPaper.Probability
