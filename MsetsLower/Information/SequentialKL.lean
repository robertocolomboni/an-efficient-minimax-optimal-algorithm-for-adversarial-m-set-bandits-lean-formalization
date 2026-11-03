import MsetsLower.Core.Protocol
import Mathlib.InformationTheory.KullbackLeibler.ChainRule

/-!
# Sequential Kullback--Leibler chain rule

This file turns Mathlib's exact composition-product chain rule into the
round-by-round identity needed by the lower-bound argument.  The conditional
term is deliberately kept as a KL divergence between two joint
composition-products: this is the fully general form of the chain rule and
does not require an unproved measurability assertion for
`h ↦ klDiv (κ h) (η h)`.
-/

namespace MsetsLower

open MeasureTheory ProbabilityTheory InformationTheory
open scoped BigOperators ProbabilityTheory ENNReal

noncomputable section

section Generic

variable {α β : Type*} [MeasurableSpace α] [MeasurableSpace β]

/-- One exact sequential KL step.  The last summand is the conditional
divergence, averaged with respect to the first history law, in Mathlib's
composition-product formulation. -/
theorem sequentialKL_oneStep (P Q : Measure α) (K L : Kernel α β)
    [IsFiniteMeasure P] [IsFiniteMeasure Q]
    [IsMarkovKernel K] [IsMarkovKernel L] :
    klDiv (P ⊗ₘ K) (Q ⊗ₘ L) =
      klDiv P Q + klDiv (P ⊗ₘ K) (P ⊗ₘ L) :=
  klDiv_compProd_eq_add P Q K L

/-- If the conditional laws coincide, adjoining the next observation does
not change KL divergence. -/
theorem sequentialKL_oneStep_sameKernel (P Q : Measure α) (K : Kernel α β)
    [IsFiniteMeasure P] [IsFiniteMeasure Q] [IsMarkovKernel K] :
    klDiv (P ⊗ₘ K) (Q ⊗ₘ K) = klDiv P Q :=
  klDiv_compProd_left P Q K

variable {γ : Type*} [MeasurableSpace γ]

/-- Two-stage form used when the learner has the same conditional action law
in both environments.  The action stage contributes exactly zero, leaving
only the conditional observation cost after the common action kernel. -/
theorem sequentialKL_twoStage_sameAction (P Q : Measure α) (A : Kernel α β)
    (K L : Kernel (α × β) γ)
    [IsFiniteMeasure P] [IsFiniteMeasure Q] [IsMarkovKernel A]
    [IsMarkovKernel K] [IsMarkovKernel L] :
    klDiv ((P ⊗ₘ A) ⊗ₘ K) ((Q ⊗ₘ A) ⊗ₘ L) =
      klDiv P Q + klDiv ((P ⊗ₘ A) ⊗ₘ K) ((P ⊗ₘ A) ⊗ₘ L) := by
  rw [sequentialKL_oneStep, sequentialKL_oneStep_sameKernel]

end Generic

section KernelHistory

/-- A fully stochastic action/feedback process on the paper's recursively
defined history spaces.  This is the model used before the random loss table
is fixed: each kernel may jointly randomize the next action and scalar
feedback as a function of the observable past. -/
structure HistoryKernelProcess (d m : Nat) where
  kernel : (t : Nat) → Kernel (History d m t) (MSetAction d m × Real)
  isMarkov : ∀ t, IsMarkovKernel (kernel t)

instance HistoryKernelProcess.instIsMarkovKernel {d m : Nat}
    (K : HistoryKernelProcess d m) (t : Nat) : IsMarkovKernel (K.kernel t) :=
  K.isMarkov t

/-- Law of a stochastic process through `T` rounds. -/
@[reducible] def HistoryKernelProcess.law {d m : Nat} (K : HistoryKernelProcess d m) :
    (T : Nat) → Measure (History d m T)
  | 0 => Measure.dirac ()
  | t + 1 => K.law t ⊗ₘ K.kernel t

@[simp] theorem HistoryKernelProcess.law_zero {d m : Nat}
    (K : HistoryKernelProcess d m) : K.law 0 = Measure.dirac () :=
  rfl

@[simp] theorem HistoryKernelProcess.law_succ {d m : Nat}
    (K : HistoryKernelProcess d m) (t : Nat) :
    K.law (t + 1) = K.law t ⊗ₘ K.kernel t :=
  rfl

theorem HistoryKernelProcess.law_isProbabilityMeasure {d m : Nat}
    (K : HistoryKernelProcess d m) : ∀ t, IsProbabilityMeasure (K.law t) := by
  intro t
  induction t with
  | zero =>
      unfold HistoryKernelProcess.law
      exact Measure.dirac.isProbabilityMeasure
  | succ t ih =>
      unfold HistoryKernelProcess.law
      letI : IsProbabilityMeasure (K.law t) := ih
      constructor
      exact Measure.compProd_apply_univ.trans measure_univ

instance {d m : Nat} (K : HistoryKernelProcess d m) (t : Nat) :
    IsProbabilityMeasure (K.law t) :=
  K.law_isProbabilityMeasure t

/-- Conditional KL cost of one stochastic process relative to another. -/
def HistoryKernelProcess.roundKL {d m : Nat} (K L : HistoryKernelProcess d m)
    (t : Nat) : ℝ≥0∞ :=
  klDiv (K.law t ⊗ₘ K.kernel t) (K.law t ⊗ₘ L.kernel t)

/-- Exact one-round KL recursion for fully stochastic history kernels. -/
theorem HistoryKernelProcess.klDiv_law_succ_eq_add {d m : Nat}
    (K L : HistoryKernelProcess d m) (t : Nat) :
    klDiv (K.law (t + 1)) (L.law (t + 1)) =
      klDiv (K.law t) (L.law t) + K.roundKL L t := by
  rw [K.law_succ, L.law_succ]
  exact sequentialKL_oneStep _ _ _ _

/-- Exact telescoping chain rule for a stochastic action/feedback history. -/
theorem HistoryKernelProcess.klDiv_law_eq_sum_roundKL {d m : Nat}
    (K L : HistoryKernelProcess d m) : ∀ T : Nat,
    klDiv (K.law T) (L.law T) = ∑ t ∈ Finset.range T, K.roundKL L t := by
  intro T
  induction T with
  | zero =>
      rw [Finset.sum_range_zero]
      change klDiv (K.law 0) (K.law 0) = 0
      exact klDiv_self _
  | succ T ih =>
      rw [K.klDiv_law_succ_eq_add L, ih, Finset.sum_range_succ]

/-- Accumulation of arbitrary valid one-round KL budgets for stochastic
history laws. -/
theorem HistoryKernelProcess.klDiv_law_le_sum {d m : Nat}
    (K L : HistoryKernelProcess d m) (T : Nat) (budget : Nat → ℝ≥0∞)
    (hbudget : ∀ t < T, K.roundKL L t ≤ budget t) :
    klDiv (K.law T) (L.law T) ≤ ∑ t ∈ Finset.range T, budget t := by
  rw [K.klDiv_law_eq_sum_roundKL L]
  exact Finset.sum_le_sum fun t ht ↦ hbudget t (Finset.mem_range.mp ht)

end KernelHistory

section Protocol

/-- The newly recorded action/feedback pair, as a measurable function of a
preceding history and sampled action. -/
def recordedObservation {d m : Nat} (L : LossProcess d m) (t : Nat) :
    History d m t × MSetAction d m → MSetAction d m × Real
  | (h, a) => (a, actionLoss a (L.itemLoss t h))

theorem measurable_recordedObservation {d m : Nat} (L : LossProcess d m) (t : Nat) :
    Measurable (recordedObservation L t) := by
  change Measurable (fun p : History d m t × MSetAction d m ↦
    (p.2, actionLoss p.2 (L.itemLoss t p.1)))
  exact measurable_snd.prodMk
    (measurable_actionLoss_joint (L.measurable_itemLoss t))

/-- Conditional law of the action/feedback pair appended in one round. -/
def observationKernel {d m : Nat} (P : Policy d m) (L : LossProcess d m) (t : Nat) :
    Kernel (History d m t) (MSetAction d m × Real) :=
  Kernel.map (actionHistoryKernel P t) (recordedObservation L t)

instance observationKernel.instIsMarkovKernel {d m : Nat}
    (P : Policy d m) (L : LossProcess d m) (t : Nat) :
    IsMarkovKernel (observationKernel P L t) := by
  unfold observationKernel
  exact Kernel.IsMarkovKernel.map _ (measurable_recordedObservation L t)

/-- Pointwise description of the one-round observation law. -/
theorem observationKernel_apply {d m : Nat} (P : Policy d m) (L : LossProcess d m)
    (t : Nat) (h : History d m t) {s : Set (MSetAction d m × Real)}
    (hs : MeasurableSet s) :
    observationKernel P L t h s =
      P.kernel t h {a | (a, actionLoss a (L.itemLoss t h)) ∈ s} := by
  rw [observationKernel, Kernel.map_apply' _ (measurable_recordedObservation L t) h hs,
    actionHistoryKernel_apply]
  rw [Measure.map_apply measurable_prodMk_left
    ((measurable_recordedObservation L t) hs)]
  rfl

/-- The recursive run law is literally a composition-product of its prefix
law and the conditional law of the newly recorded observation. -/
theorem runLaw_succ_eq_compProd {d m : Nat} (P : Policy d m) (L : LossProcess d m)
    (t : Nat) :
    runLaw P L (t + 1) = runLaw P L t ⊗ₘ observationKernel P L t := by
  ext s hs
  rw [runLaw_succ_apply P L t hs]
  calc
    ∫⁻ h, roundKernel P L t h s ∂runLaw P L t =
        ∫⁻ h, observationKernel P L t h (Prod.mk h ⁻¹' s) ∂runLaw P L t := by
      apply lintegral_congr
      intro h
      rw [roundKernel_apply P L t h hs]
      rw [observationKernel_apply P L t h (measurable_prodMk_left hs)]
      rfl
    _ = (runLaw P L t ⊗ₘ observationKernel P L t) s :=
      (Measure.compProd_apply hs).symm

/-- The deterministic protocol, including the learner's randomization, as a
special case of `HistoryKernelProcess`. -/
def protocolHistoryKernelProcess {d m : Nat} (P : Policy d m) (L : LossProcess d m) :
    HistoryKernelProcess d m where
  kernel t := observationKernel P L t
  isMarkov t := by infer_instance

/-- The stochastic-history construction specializes exactly to `runLaw`. -/
theorem protocolHistoryKernelProcess_law_eq_runLaw {d m : Nat}
    (P : Policy d m) (L : LossProcess d m) : ∀ T : Nat,
    (protocolHistoryKernelProcess P L).law T = runLaw P L T := by
  intro T
  induction T with
  | zero => rfl
  | succ T ih =>
      rw [HistoryKernelProcess.law_succ, runLaw_succ_eq_compProd, ih]
      rfl

/-- The conditional KL cost of round `t`, averaged under the first run law.
This is the exact conditional term delivered by the chain rule. -/
def roundConditionalKL {d m : Nat} (P₀ P₁ : Policy d m)
    (L₀ L₁ : LossProcess d m) (t : Nat) : ℝ≥0∞ :=
  klDiv
    (runLaw P₀ L₀ t ⊗ₘ observationKernel P₀ L₀ t)
    (runLaw P₀ L₀ t ⊗ₘ observationKernel P₁ L₁ t)

/-- Exact one-round chain rule for the observable protocol laws. -/
theorem runLaw_klDiv_succ_eq_add {d m : Nat} (P₀ P₁ : Policy d m)
    (L₀ L₁ : LossProcess d m) (t : Nat) :
    klDiv (runLaw P₀ L₀ (t + 1)) (runLaw P₁ L₁ (t + 1)) =
      klDiv (runLaw P₀ L₀ t) (runLaw P₁ L₁ t) +
        roundConditionalKL P₀ P₁ L₀ L₁ t := by
  rw [runLaw_succ_eq_compProd P₀ L₀ t, runLaw_succ_eq_compProd P₁ L₁ t]
  exact sequentialKL_oneStep _ _ _ _

/-- The KL divergence of the full history is exactly the sum of its
round-conditional KL costs. -/
theorem runLaw_klDiv_eq_sum_roundConditionalKL {d m : Nat} (P₀ P₁ : Policy d m)
    (L₀ L₁ : LossProcess d m) : ∀ T : Nat,
    klDiv (runLaw P₀ L₀ T) (runLaw P₁ L₁ T) =
      ∑ t ∈ Finset.range T, roundConditionalKL P₀ P₁ L₀ L₁ t := by
  intro T
  induction T with
  | zero =>
      rw [Finset.sum_range_zero]
      change klDiv (runLaw P₀ L₀ 0) (runLaw P₀ L₀ 0) = 0
      exact klDiv_self _
  | succ T ih =>
      rw [runLaw_klDiv_succ_eq_add, ih, Finset.sum_range_succ]

/-- Sequential KL upper bound obtained by bounding every conditional cost.
The hypothesis is local in time and the conclusion is the accumulated
information budget used by the lower-bound proof. -/
theorem runLaw_klDiv_le_sum {d m : Nat} (P₀ P₁ : Policy d m)
    (L₀ L₁ : LossProcess d m) (T : Nat) (budget : Nat → ℝ≥0∞)
    (hbudget : ∀ t < T, roundConditionalKL P₀ P₁ L₀ L₁ t ≤ budget t) :
    klDiv (runLaw P₀ L₀ T) (runLaw P₁ L₁ T) ≤
      ∑ t ∈ Finset.range T, budget t := by
  rw [runLaw_klDiv_eq_sum_roundConditionalKL]
  exact Finset.sum_le_sum fun t ht ↦ hbudget t (Finset.mem_range.mp ht)

/-- Constant per-round specialization of `runLaw_klDiv_le_sum`. -/
theorem runLaw_klDiv_le_nat_mul {d m : Nat} (P₀ P₁ : Policy d m)
    (L₀ L₁ : LossProcess d m) (T : Nat) (c : ℝ≥0∞)
    (hc : ∀ t < T, roundConditionalKL P₀ P₁ L₀ L₁ t ≤ c) :
    klDiv (runLaw P₀ L₀ T) (runLaw P₁ L₁ T) ≤ T * c := by
  simpa using runLaw_klDiv_le_sum P₀ P₁ L₀ L₁ T (fun _ ↦ c) hc

/-- A round whose conditional observation kernels agree has zero
conditional KL cost. -/
theorem roundConditionalKL_eq_zero_of_observationKernel_eq {d m : Nat}
    (P₀ P₁ : Policy d m) (L₀ L₁ : LossProcess d m) (t : Nat)
    (h : observationKernel P₀ L₀ t = observationKernel P₁ L₁ t) :
    roundConditionalKL P₀ P₁ L₀ L₁ t = 0 := by
  simp [roundConditionalKL, h, klDiv_self]

/-- Almost-everywhere equality under the first history law is sufficient for
zero conditional cost. -/
theorem roundConditionalKL_eq_zero_of_observationKernel_ae_eq {d m : Nat}
    (P₀ P₁ : Policy d m) (L₀ L₁ : LossProcess d m) (t : Nat)
    (h : observationKernel P₀ L₀ t =ᵐ[runLaw P₀ L₀ t]
      observationKernel P₁ L₁ t) :
    roundConditionalKL P₀ P₁ L₀ L₁ t = 0 := by
  rw [roundConditionalKL, Measure.compProd_congr h, klDiv_self]

/-- Indicator/cost specialization.  Off the active rounds the two
conditional kernels really coincide; on active rounds only the stated local
cost estimate is used.  Thus no KL cost is charged where the perturbation is
absent. -/
theorem runLaw_klDiv_le_sum_indicator {d m : Nat} (P₀ P₁ : Policy d m)
    (L₀ L₁ : LossProcess d m) (T : Nat) (active : Nat → Prop)
    [DecidablePred active] (cost : Nat → ℝ≥0∞)
    (hmatch : ∀ t < T, ¬ active t →
      observationKernel P₀ L₀ t = observationKernel P₁ L₁ t)
    (hcost : ∀ t < T, active t →
      roundConditionalKL P₀ P₁ L₀ L₁ t ≤ cost t) :
    klDiv (runLaw P₀ L₀ T) (runLaw P₁ L₁ T) ≤
      ∑ t ∈ Finset.range T, if active t then cost t else 0 := by
  apply runLaw_klDiv_le_sum P₀ P₁ L₀ L₁
  intro t ht
  by_cases ha : active t
  · simpa [ha] using hcost t ht ha
  · simp [ha, roundConditionalKL_eq_zero_of_observationKernel_eq
      P₀ P₁ L₀ L₁ t (hmatch t ht ha)]

end Protocol

end

end MsetsLower
