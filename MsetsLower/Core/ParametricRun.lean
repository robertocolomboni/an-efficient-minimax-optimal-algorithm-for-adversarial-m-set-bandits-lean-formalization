import MsetsLower.Core.Protocol
import MsetsLower.Probability.KernelFixing
import Mathlib.Probability.Kernel.Composition.KernelLemmas

set_option linter.style.header false

/-!
# Measurable families of deterministic loss processes

The lower-bound constructions randomize an auxiliary table and then fix it.
This file constructs the table-indexed run as a genuine Markov kernel and
proves that every section is definitionally the ordinary protocol `runLaw`
for the corresponding deterministic adaptive loss process.
-/

namespace MsetsLower

open MeasureTheory ProbabilityTheory
open scoped ENNReal ProbabilityTheory

noncomputable section

/-- A jointly measurable family of deterministic non-anticipating loss
processes, indexed by an auxiliary parameter `Xi`. -/
structure ParametricLossProcess
    (Xi : Type*) [MeasurableSpace Xi] (d m : Nat) where
  itemLoss : (t : Nat) → Xi → History d m t → Fin d → Real
  measurable_itemLoss : ∀ t,
    Measurable (fun x : Xi × History d m t => itemLoss t x.1 x.2)
  action_nonneg : ∀ xi t h (a : MSetAction d m),
    0 ≤ actionLoss a (itemLoss t xi h)
  action_le_one : ∀ xi t h (a : MSetAction d m),
    actionLoss a (itemLoss t xi h) ≤ 1

/-- Fixing the parameter gives an ordinary deterministic adaptive loss
process. -/
def ParametricLossProcess.at
    {Xi : Type*} [MeasurableSpace Xi] {d m : Nat}
    (L : ParametricLossProcess Xi d m) (xi : Xi) : LossProcess d m where
  itemLoss t h := L.itemLoss t xi h
  measurable_itemLoss t :=
    (L.measurable_itemLoss t).comp (measurable_const.prodMk measurable_id)
  action_nonneg t h a := L.action_nonneg xi t h a
  action_le_one t h a := L.action_le_one xi t h a

/-- Append the literal aggregate feedback while retaining the table
parameter in the input. -/
def parametricExtendRun
    {Xi : Type*} [MeasurableSpace Xi] {d m : Nat}
    (L : ParametricLossProcess Xi d m) (t : Nat) :
    (Xi × History d m t) × MSetAction d m → History d m (t + 1)
  | ((xi, h), a) => (h, (a, actionLoss a (L.itemLoss t xi h)))

theorem measurable_parametricExtendRun
    {Xi : Type*} [MeasurableSpace Xi] {d m : Nat}
    (L : ParametricLossProcess Xi d m) (t : Nat) :
    Measurable (parametricExtendRun L t) := by
  change Measurable (fun p : (Xi × History d m t) × MSetAction d m =>
    (p.1.2, (p.2, actionLoss p.2 (L.itemLoss t p.1.1 p.1.2))))
  exact (measurable_snd.comp measurable_fst).prodMk
    (measurable_snd.prodMk
      (measurable_actionLoss_joint (L.measurable_itemLoss t)))

/-- Sample the policy action while retaining both parameter and history. -/
def parametricActionHistoryKernel
    {Xi : Type*} [MeasurableSpace Xi] {d m : Nat}
    (P : Policy d m) (t : Nat) :
    Kernel (Xi × History d m t) ((Xi × History d m t) × MSetAction d m) :=
  Kernel.compProd Kernel.id
    (Kernel.prodMkLeft (Xi × History d m t)
      ((P.kernel t).comap Prod.snd measurable_snd))

instance parametricActionHistoryKernel.instIsMarkovKernel
    {Xi : Type*} [MeasurableSpace Xi] {d m : Nat}
    (P : Policy d m) (t : Nat) :
    IsMarkovKernel (parametricActionHistoryKernel (Xi := Xi) P t) := by
  unfold parametricActionHistoryKernel
  infer_instance

theorem parametricActionHistoryKernel_apply
    {Xi : Type*} [MeasurableSpace Xi] {d m : Nat}
    (P : Policy d m) (t : Nat) (xi : Xi) (h : History d m t) :
    parametricActionHistoryKernel (Xi := Xi) P t (xi, h) =
      (P.kernel t h).map (fun a => ((xi, h), a)) := by
  ext s hs
  rw [parametricActionHistoryKernel, Kernel.compProd_apply hs,
    Kernel.id_apply]
  simp only [Kernel.prodMkLeft_apply, Kernel.comap_apply]
  have hsection : Measurable (fun b : Xi × History d m t =>
      P.kernel t b.2 (Prod.mk b ⁻¹' s)) := by
    simpa only [Kernel.comap_apply] using
      (Kernel.measurable_kernel_prodMk_left
        (κ := (P.kernel t).comap Prod.snd measurable_snd) hs)
  rw [lintegral_dirac' _ hsection]
  rw [Measure.map_apply measurable_prodMk_left hs]

/-- One interaction round for a measurable table-indexed family. -/
def parametricRoundKernel
    {Xi : Type*} [MeasurableSpace Xi] {d m : Nat}
    (P : Policy d m) (L : ParametricLossProcess Xi d m) (t : Nat) :
    Kernel (Xi × History d m t) (History d m (t + 1)) :=
  (parametricActionHistoryKernel (Xi := Xi) P t).map
    (parametricExtendRun L t)

instance parametricRoundKernel.instIsMarkovKernel
    {Xi : Type*} [MeasurableSpace Xi] {d m : Nat}
    (P : Policy d m) (L : ParametricLossProcess Xi d m) (t : Nat) :
    IsMarkovKernel (parametricRoundKernel P L t) := by
  unfold parametricRoundKernel
  exact Kernel.IsMarkovKernel.map _ (measurable_parametricExtendRun L t)

/-- At a fixed parameter the parametric round kernel is exactly the ordinary
round kernel for the fixed deterministic loss process. -/
theorem parametricRoundKernel_apply
    {Xi : Type*} [MeasurableSpace Xi] {d m : Nat}
    (P : Policy d m) (L : ParametricLossProcess Xi d m)
    (t : Nat) (xi : Xi) (h : History d m t) :
    parametricRoundKernel P L t (xi, h) =
      roundKernel P (L.at xi) t h := by
  ext s hs
  rw [parametricRoundKernel,
    Kernel.map_apply' _ (measurable_parametricExtendRun L t) _ hs,
    parametricActionHistoryKernel_apply]
  rw [Measure.map_apply measurable_prodMk_left
    ((measurable_parametricExtendRun L t) hs)]
  rw [roundKernel_apply P (L.at xi) t h hs]
  rfl

/-- The history law through `t` rounds, as a Markov kernel from the table
parameter to observable histories. -/
def parametricRunKernel
    {Xi : Type*} [MeasurableSpace Xi] {d m : Nat}
    (P : Policy d m) (L : ParametricLossProcess Xi d m) :
    (t : Nat) → Kernel Xi (History d m t)
  | 0 => Kernel.deterministic (fun _ => ()) measurable_const
  | t + 1 => Kernel.snd
      (parametricRunKernel P L t ⊗ₖ parametricRoundKernel P L t)

theorem parametricRunKernel_isMarkov
    {Xi : Type*} [MeasurableSpace Xi] {d m : Nat}
    (P : Policy d m) (L : ParametricLossProcess Xi d m) : ∀ t,
    IsMarkovKernel (parametricRunKernel P L t) := by
  intro t
  induction t with
  | zero =>
      unfold parametricRunKernel
      exact Kernel.isMarkovKernel_deterministic _
  | succ t ih =>
      unfold parametricRunKernel
      letI : IsMarkovKernel (parametricRunKernel P L t) := ih
      letI : IsMarkovKernel (parametricRoundKernel P L t) :=
        parametricRoundKernel.instIsMarkovKernel P L t
      infer_instance

/-- The section at a fixed table is precisely the existing recursive
`runLaw`; no representation of the learner by a master random tape is used. -/
theorem parametricRunKernel_apply
    {Xi : Type*} [MeasurableSpace Xi] {d m : Nat}
    (P : Policy d m) (L : ParametricLossProcess Xi d m) (xi : Xi) : ∀ t,
    parametricRunKernel P L t xi = runLaw P (L.at xi) t := by
  intro t
  induction t with
  | zero =>
      exact Kernel.deterministic_apply _ _
  | succ t ih =>
      letI : IsMarkovKernel (parametricRunKernel P L t) :=
        parametricRunKernel_isMarkov P L t
      letI : IsMarkovKernel (parametricRoundKernel P L t) :=
        parametricRoundKernel.instIsMarkovKernel P L t
      ext s hs
      rw [parametricRunKernel, Kernel.snd_apply' _ _ hs,
        Kernel.compProd_apply (measurable_snd hs)]
      simp only [Set.preimage, Set.mem_setOf_eq]
      rw [runLaw_succ, Measure.bind_apply hs (Kernel.aemeasurable _)]
      rw [ih]
      apply lintegral_congr
      intro h
      exact congrArg (fun mu : Measure (History d m (t + 1)) => mu s)
        (parametricRoundKernel_apply P L t xi h)

end

end MsetsLower

#print axioms MsetsLower.ParametricLossProcess.at
#print axioms MsetsLower.parametricRoundKernel_apply
#print axioms MsetsLower.parametricRunKernel_isMarkov
#print axioms MsetsLower.parametricRunKernel_apply
