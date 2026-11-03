import MsetsLower.Core.Protocol
import Mathlib.MeasureTheory.Measure.Typeclasses.Probability

/-! # The ordinary finite-armed bandit protocol

Actions are literally elements of `Fin K`.  Histories record the chosen arm
and its scalar feedback.  Loss processes are deterministic measurable
functions of the preceding observable history, with every coordinate in [0,1].
-/

namespace MsetsPaper.Lower.Ordinary

open MeasureTheory ProbabilityTheory

noncomputable section

@[reducible] def History (K : ℕ) : ℕ → Type
  | 0 => Unit
  | t + 1 => History K t × (Fin K × ℝ)

@[reducible] def historyMeasurableSpace (K : ℕ) : (t : ℕ) → MeasurableSpace (History K t)
  | 0 => inferInstanceAs (MeasurableSpace Unit)
  | t + 1 =>
      letI := historyMeasurableSpace K t
      inferInstanceAs (MeasurableSpace (History K t × (Fin K × ℝ)))

@[reducible] instance (K t : ℕ) : MeasurableSpace (History K t) := historyMeasurableSpace K t

theorem historyMeasurableSingletonClass (K : ℕ) :
    ∀ t, MeasurableSingletonClass (History K t) := by
  intro t
  induction t with
  | zero => exact inferInstanceAs (MeasurableSingletonClass Unit)
  | succ t ih =>
      letI : MeasurableSingletonClass (History K t) := ih
      change MeasurableSingletonClass (History K t × (Fin K × ℝ))
      infer_instance

instance (K t : ℕ) : MeasurableSingletonClass (History K t) :=
  historyMeasurableSingletonClass K t

def History.snoc {K t : ℕ} (h : History K t) (i : Fin K) (z : ℝ) :
    History K (t + 1) := (h, (i, z))

structure Policy (K : ℕ) where
  kernel : (t : ℕ) → Kernel (History K t) (Fin K)
  isMarkov : ∀ t, IsMarkovKernel (kernel t)

instance {K : ℕ} (P : Policy K) (t : ℕ) : IsMarkovKernel (P.kernel t) :=
  P.isMarkov t

structure LossProcess (K : ℕ) where
  loss : (t : ℕ) → History K t → Fin K → ℝ
  measurable_loss : ∀ t, Measurable (loss t)
  loss_mem_Icc : ∀ t h i, loss t h i ∈ Set.Icc (0 : ℝ) 1

def extendRun {K : ℕ} (L : LossProcess K) (t : ℕ) :
    History K t × Fin K → History K (t + 1) :=
  fun p ↦ p.1.snoc p.2 (L.loss t p.1 p.2)

theorem measurable_extendRun {K : ℕ} (L : LossProcess K) (t : ℕ) :
    Measurable (extendRun L t) := by
  have hl : Measurable (fun p : History K t × Fin K ↦ L.loss t p.1 p.2) :=
    measurable_from_prod_countable_left (fun i ↦ (L.measurable_loss t).eval (a := i))
  exact measurable_fst.prodMk (measurable_snd.prodMk hl)

def actionHistoryKernel {K : ℕ} (P : Policy K) (t : ℕ) :
    Kernel (History K t) (History K t × Fin K) :=
  Kernel.compProd Kernel.id (Kernel.prodMkLeft (History K t) (P.kernel t))

instance {K : ℕ} (P : Policy K) (t : ℕ) :
    IsMarkovKernel (actionHistoryKernel P t) := by
  unfold actionHistoryKernel
  infer_instance

theorem actionHistoryKernel_apply {K : ℕ} (P : Policy K) (t : ℕ) (h : History K t) :
    actionHistoryKernel P t h = (P.kernel t h).map (fun i ↦ (h, i)) := by
  ext S hS
  rw [actionHistoryKernel, Kernel.compProd_apply hS, Kernel.id_apply]
  simp only [Kernel.prodMkLeft_apply]
  rw [lintegral_dirac, Measure.map_apply measurable_prodMk_left hS]

def roundKernel {K : ℕ} (P : Policy K) (L : LossProcess K) (t : ℕ) :
    Kernel (History K t) (History K (t + 1)) :=
  Kernel.map (actionHistoryKernel P t) (extendRun L t)

instance {K : ℕ} (P : Policy K) (L : LossProcess K) (t : ℕ) :
    IsMarkovKernel (roundKernel P L t) := by
  unfold roundKernel
  exact Kernel.IsMarkovKernel.map _ (measurable_extendRun L t)

theorem roundKernel_apply {K : ℕ} (P : Policy K) (L : LossProcess K)
    (t : ℕ) (h : History K t) {S : Set (History K (t + 1))} (hS : MeasurableSet S) :
    roundKernel P L t h S = P.kernel t h {i | h.snoc i (L.loss t h i) ∈ S} := by
  rw [roundKernel, Kernel.map_apply' _ (measurable_extendRun L t) h hS,
    actionHistoryKernel_apply,
    Measure.map_apply measurable_prodMk_left ((measurable_extendRun L t) hS)]
  rfl

@[reducible] def runLaw {K : ℕ} (P : Policy K) (L : LossProcess K) :
    (t : ℕ) → Measure (History K t)
  | 0 => Measure.dirac ()
  | t + 1 => roundKernel P L t ∘ₘ runLaw P L t

@[simp] theorem runLaw_zero {K : ℕ} (P : Policy K) (L : LossProcess K) :
    runLaw P L 0 = Measure.dirac () := rfl

@[simp] theorem runLaw_succ {K : ℕ} (P : Policy K) (L : LossProcess K) (t : ℕ) :
    runLaw P L (t + 1) = roundKernel P L t ∘ₘ runLaw P L t := rfl

theorem runLaw_isProbabilityMeasure {K : ℕ} (P : Policy K) (L : LossProcess K) :
    ∀ t, IsProbabilityMeasure (runLaw P L t) := by
  intro t
  induction t with
  | zero => exact Measure.dirac.isProbabilityMeasure
  | succ t ih =>
      letI : IsProbabilityMeasure (runLaw P L t) := ih
      change IsProbabilityMeasure (roundKernel P L t ∘ₘ runLaw P L t)
      infer_instance

instance {K : ℕ} (P : Policy K) (L : LossProcess K) (t : ℕ) :
    IsProbabilityMeasure (runLaw P L t) := runLaw_isProbabilityMeasure P L t

def realizedCumulativeLoss {K : ℕ} (L : LossProcess K) :
    (t : ℕ) → History K t → ℝ
  | 0, _ => 0
  | t + 1, h => realizedCumulativeLoss L t h.1 + L.loss t h.1 h.2.1

def comparatorCumulativeLoss {K : ℕ} (L : LossProcess K) :
    (t : ℕ) → History K t → Fin K → ℝ
  | 0, _, _ => 0
  | t + 1, h, i => comparatorCumulativeLoss L t h.1 i + L.loss t h.1 i

def bestComparatorCumulativeLoss {K : ℕ} (L : LossProcess K)
    (t : ℕ) (h : History K t) : ℝ :=
  sInf (Set.range (comparatorCumulativeLoss L t h))

def pathRegret {K : ℕ} (L : LossProcess K) (t : ℕ) (h : History K t) : ℝ :=
  realizedCumulativeLoss L t h - bestComparatorCumulativeLoss L t h

end
end MsetsPaper.Lower.Ordinary
