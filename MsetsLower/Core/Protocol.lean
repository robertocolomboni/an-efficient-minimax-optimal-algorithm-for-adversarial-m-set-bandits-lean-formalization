import MsetsLower.Prelude
import Mathlib.Data.Fintype.Powerset
import Mathlib.Probability.Kernel.Composition.MeasureComp

/-!
# Operational semantics of the adaptive m-set protocol

This file gives the protocol used in the lower-bound appendix a literal
measure-theoretic semantics.  An action is an `m`-element finset, a history is
the right-nested sequence of action/aggregate-loss observations, a randomized
policy is a family of Markov kernels, and an adaptive non-anticipating
adversary is a measurable deterministic function of the preceding history.

The law of a run is generated recursively by a Markov kernel.  In particular,
the adversary is evaluated before the current action is sampled; its input is
only the history through the preceding round.
-/

namespace MsetsLower

open MeasureTheory ProbabilityTheory
open scoped BigOperators ProbabilityTheory

noncomputable section

/-- The action space `X_{d,m}`: subsets of `Fin d` having exactly `m` items. -/
@[reducible] def MSetAction (d m : Nat) :=
  {s : Finset (Fin d) // s.card = m}

/-- The finite action space carries its discrete sigma-algebra. -/
instance (d m : Nat) : MeasurableSpace (MSetAction d m) := ⊤

instance (d m : Nat) : DiscreteMeasurableSpace (MSetAction d m) := inferInstance

@[simp] theorem MSetAction.card_val {d m : Nat} (a : MSetAction d m) :
    a.1.card = m :=
  a.2

/-- The number of `m`-set actions is the binomial coefficient from the paper. -/
theorem card_MSetAction (d m : Nat) :
    Fintype.card (MSetAction d m) = Nat.choose d m := by
  simp [MSetAction, Fintype.card_finset_len]

/-- Exact-cardinality actions exist whenever `m ≤ d`. -/
theorem nonempty_MSetAction {d m : Nat} (hmd : m ≤ d) :
    Nonempty (MSetAction d m) := by
  rw [← Fintype.card_pos_iff, card_MSetAction]
  exact Nat.choose_pos hmd

/-- The aggregate loss observed after playing an action. -/
def actionLoss {d m : Nat} (a : MSetAction d m) (itemLoss : Fin d → Real) : Real :=
  ∑ i : Fin d, if i ∈ a.1 then itemLoss i else 0

theorem actionLoss_eq_finset_sum {d m : Nat} (a : MSetAction d m)
    (itemLoss : Fin d → Real) :
    actionLoss a itemLoss = ∑ i ∈ a.1, itemLoss i := by
  classical
  simp [actionLoss]

@[simp] theorem actionLoss_zero {d m : Nat} (a : MSetAction d m) :
    actionLoss a (fun _ ↦ 0) = 0 := by
  simp [actionLoss]

theorem actionLoss_add {d m : Nat} (a : MSetAction d m)
    (f g : Fin d → Real) :
    actionLoss a (fun i ↦ f i + g i) = actionLoss a f + actionLoss a g := by
  classical
  simp only [actionLoss]
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro i _
  by_cases hi : i ∈ a.1 <;> simp [hi]

/-- Measurability of aggregate loss for a fixed action. -/
theorem measurable_actionLoss {d m : Nat} {Ω : Type*} [MeasurableSpace Ω]
    (a : MSetAction d m) {ℓ : Ω → Fin d → Real} (hℓ : Measurable ℓ) :
    Measurable (fun ω ↦ actionLoss a (ℓ ω)) := by
  classical
  unfold actionLoss
  refine Finset.measurable_sum _ ?_
  intro i _
  by_cases hi : i ∈ a.1
  · simpa [hi] using hℓ.eval (a := i)
  · simp only [hi, if_false]
    exact measurable_const

/-- Joint measurability when both the history and the finite action vary. -/
theorem measurable_actionLoss_joint {d m : Nat} {Ω : Type*} [MeasurableSpace Ω]
    {ℓ : Ω → Fin d → Real} (hℓ : Measurable ℓ) :
    Measurable (fun p : Ω × MSetAction d m ↦ actionLoss p.2 (ℓ p.1)) := by
  classical
  unfold actionLoss
  refine Finset.measurable_sum _ ?_
  intro i _
  have hmem : MeasurableSet {p : Ω × MSetAction d m | i ∈ p.2.1} := by
    exact measurable_snd
      (show MeasurableSet {a : MSetAction d m | i ∈ a.1} from
        MeasurableSet.of_discrete)
  exact Measurable.ite hmem
    ((hℓ.comp measurable_fst).eval (a := i)) measurable_const

/-- Histories are appended on the right: `H 0 = Unit` and
`H (t+1) = H t × (Action × Real)`. -/
@[reducible] def History (d m : Nat) : Nat → Type
  | 0 => Unit
  | t + 1 => History d m t × (MSetAction d m × Real)

@[reducible] private def historyMeasurableSpace (d m : Nat) :
    (t : Nat) → MeasurableSpace (History d m t)
  | 0 => inferInstanceAs (MeasurableSpace Unit)
  | t + 1 => by
      letI := historyMeasurableSpace d m t
      change MeasurableSpace (History d m t × (MSetAction d m × Real))
      infer_instance

@[reducible] instance (d m t : Nat) : MeasurableSpace (History d m t) :=
  historyMeasurableSpace d m t

private theorem historyMeasurableSingletonClass (d m : Nat) :
    ∀ t, MeasurableSingletonClass (History d m t) := by
  intro t
  induction t with
  | zero => exact inferInstanceAs (MeasurableSingletonClass Unit)
  | succ t ih =>
      letI : MeasurableSingletonClass (History d m t) := ih
      change MeasurableSingletonClass
        (History d m t × (MSetAction d m × Real))
      infer_instance

instance (d m t : Nat) : MeasurableSingletonClass (History d m t) :=
  historyMeasurableSingletonClass d m t

/-- Append the action and its scalar feedback to a history. -/
def History.snoc {d m t : Nat} (h : History d m t) (a : MSetAction d m)
    (feedback : Real) : History d m (t + 1) :=
  (h, (a, feedback))

/-- A randomized learner: at each time, a Markov kernel from the observable
history to the next `m`-set action. -/
structure Policy (d m : Nat) where
  kernel : (t : Nat) → Kernel (History d m t) (MSetAction d m)
  isMarkov : ∀ t, IsMarkovKernel (kernel t)

instance Policy.instIsMarkovKernel {d m : Nat} (P : Policy d m) (t : Nat) :
    IsMarkovKernel (P.kernel t) :=
  P.isMarkov t

/-- A history-measurable choice rule gives a deterministic policy. -/
def Policy.deterministic {d m : Nat}
    (choose : (t : Nat) → History d m t → MSetAction d m)
    (hchoose : ∀ t, Measurable (choose t)) : Policy d m where
  kernel t := Kernel.deterministic (choose t) (hchoose t)
  isMarkov t := by infer_instance

/-- A deterministic adaptive non-anticipating loss process.  Item losses may
be arbitrary real numbers; the paper's normalization is imposed at action
level, exactly where feedback and regret use them. -/
structure LossProcess (d m : Nat) where
  itemLoss : (t : Nat) → History d m t → Fin d → Real
  measurable_itemLoss : ∀ t, Measurable (itemLoss t)
  action_nonneg : ∀ t h (a : MSetAction d m), 0 ≤ actionLoss a (itemLoss t h)
  action_le_one : ∀ t h (a : MSetAction d m), actionLoss a (itemLoss t h) ≤ 1

theorem LossProcess.action_mem_Icc {d m : Nat} (L : LossProcess d m)
    (t : Nat) (h : History d m t) (a : MSetAction d m) :
    actionLoss a (L.itemLoss t h) ∈ Set.Icc (0 : Real) 1 :=
  ⟨L.action_nonneg t h a, L.action_le_one t h a⟩

/-- The identically-zero adaptive adversary. -/
def LossProcess.zero (d m : Nat) : LossProcess d m where
  itemLoss _ _ _ := 0
  measurable_itemLoss _ := measurable_const
  action_nonneg _ _ a := by simp
  action_le_one _ _ a := by simp

/-- Deterministically add the feedback generated from a history/action pair. -/
def extendRun {d m : Nat} (L : LossProcess d m) (t : Nat) :
    History d m t × MSetAction d m → History d m (t + 1)
  | (h, a) => h.snoc a (actionLoss a (L.itemLoss t h))

theorem measurable_extendRun {d m : Nat} (L : LossProcess d m) (t : Nat) :
    Measurable (extendRun L t) := by
  change Measurable (fun p : History d m t × MSetAction d m ↦
    (p.1, (p.2, actionLoss p.2 (L.itemLoss t p.1))))
  exact measurable_fst.prodMk
    (measurable_snd.prodMk
      (measurable_actionLoss_joint (L.measurable_itemLoss t)))

/-- First sample an action from the policy, while retaining the history. -/
def actionHistoryKernel {d m : Nat} (P : Policy d m) (t : Nat) :
    Kernel (History d m t) (History d m t × MSetAction d m) :=
  Kernel.compProd Kernel.id
    (Kernel.prodMkLeft (History d m t) (P.kernel t))

instance actionHistoryKernel.instIsMarkovKernel {d m : Nat}
    (P : Policy d m) (t : Nat) :
    IsMarkovKernel (actionHistoryKernel P t) := by
  unfold actionHistoryKernel
  infer_instance

/-- Pointwise, retaining the history does not alter the learner's action law. -/
theorem actionHistoryKernel_apply {d m : Nat} (P : Policy d m) (t : Nat)
    (h : History d m t) :
    actionHistoryKernel P t h =
      (P.kernel t h).map (fun a ↦ (h, a)) := by
  ext s hs
  rw [actionHistoryKernel, Kernel.compProd_apply hs, Kernel.id_apply]
  simp only [Kernel.prodMkLeft_apply]
  rw [lintegral_dirac]
  rw [Measure.map_apply measurable_prodMk_left hs]

/-- One full interaction round: sample the learner action and append the
aggregate loss chosen from the preceding history. -/
def roundKernel {d m : Nat} (P : Policy d m) (L : LossProcess d m) (t : Nat) :
    Kernel (History d m t) (History d m (t + 1)) :=
  Kernel.map (actionHistoryKernel P t) (extendRun L t)

instance roundKernel.instIsMarkovKernel {d m : Nat}
    (P : Policy d m) (L : LossProcess d m) (t : Nat) :
    IsMarkovKernel (roundKernel P L t) := by
  unfold roundKernel
  exact Kernel.IsMarkovKernel.map _ (measurable_extendRun L t)

/-- Conditional on a preceding history, the round law is precisely the
policy's action law pushed forward by the aggregate-feedback update. -/
theorem roundKernel_apply {d m : Nat} (P : Policy d m) (L : LossProcess d m)
    (t : Nat) (h : History d m t) {s : Set (History d m (t + 1))}
    (hs : MeasurableSet s) :
    roundKernel P L t h s =
      P.kernel t h {a | h.snoc a (actionLoss a (L.itemLoss t h)) ∈ s} := by
  rw [roundKernel, Kernel.map_apply' _ (measurable_extendRun L t) h hs,
    actionHistoryKernel_apply]
  rw [Measure.map_apply measurable_prodMk_left ((measurable_extendRun L t) hs)]
  rfl

/-- Recursive law of the observable run. -/
@[reducible] def runLaw {d m : Nat} (P : Policy d m) (L : LossProcess d m) :
    (t : Nat) → Measure (History d m t)
  | 0 => Measure.dirac ()
  | t + 1 => roundKernel P L t ∘ₘ runLaw P L t

@[simp] theorem runLaw_zero {d m : Nat} (P : Policy d m) (L : LossProcess d m) :
    runLaw P L 0 = Measure.dirac () :=
  rfl

@[simp] theorem runLaw_succ {d m : Nat} (P : Policy d m) (L : LossProcess d m)
    (t : Nat) :
    runLaw P L (t + 1) = roundKernel P L t ∘ₘ runLaw P L t :=
  rfl

theorem runLaw_isProbabilityMeasure {d m : Nat} (P : Policy d m)
    (L : LossProcess d m) :
    ∀ t, IsProbabilityMeasure (runLaw P L t) := by
  intro t
  induction t with
  | zero =>
      unfold runLaw
      exact Measure.dirac.isProbabilityMeasure
  | succ t ih =>
      unfold runLaw
      letI : IsProbabilityMeasure (runLaw P L t) := ih
      infer_instance

instance {d m : Nat} (P : Policy d m) (L : LossProcess d m) (t : Nat) :
    IsProbabilityMeasure (runLaw P L t) :=
  runLaw_isProbabilityMeasure P L t

/-- Integral form of the recursive law, useful for conditional arguments. -/
theorem runLaw_succ_apply {d m : Nat} (P : Policy d m) (L : LossProcess d m)
    (t : Nat) {s : Set (History d m (t + 1))} (hs : MeasurableSet s) :
    runLaw P L (t + 1) s =
      ∫⁻ h, roundKernel P L t h s ∂runLaw P L t := by
  rw [runLaw_succ, Measure.bind_apply hs (Kernel.aemeasurable _)]

end

end MsetsLower
