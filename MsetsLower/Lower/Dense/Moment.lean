import MsetsLower.Lower.Dense.AdaptiveLaw
import MsetsLower.Probability.MeanToTail
import Mathlib.Probability.Kernel.Composition.IntegralCompProd
import Mathlib.Probability.Moments.Variance

/-!
# Mean and second moment for the dense paired construction

This file formalizes the block from `eq:lower-dense-positive-mean` through
`eq:lower-dense-positive-event`.  Unlike the observable law used for KL, the
probability space here retains the sampled item `J_t`; the learner still sees
only the scalar feedback from `eq:lower-dense-action-loss`.
-/

namespace MsetsLower.Lower.Dense

open MsetsLower
open MeasureTheory ProbabilityTheory
open scoped BigOperators ENNReal NNReal ProbabilityTheory

noncomputable section

/-! ## The genuine adaptive joint law -/

/-- A finite full history retaining both the learner action and the sampled
paired item.  The item is latent: it is not passed to the policy. -/
@[reducible] def PairedJointHistory (n k : Nat) : Nat → Type
  | 0 => Unit
  | t + 1 => PairedJointHistory n k t × (MSetAction n k × PairItem k)

@[reducible] private def pairedJointHistoryFintype (n k : Nat) :
    (t : Nat) → Fintype (PairedJointHistory n k t)
  | 0 => inferInstanceAs (Fintype Unit)
  | t + 1 => by
      letI := pairedJointHistoryFintype n k t
      change Fintype (PairedJointHistory n k t ×
        (MSetAction n k × PairItem k))
      infer_instance

instance (n k t : Nat) : Fintype (PairedJointHistory n k t) :=
  pairedJointHistoryFintype n k t

@[reducible] private def pairedJointHistoryMeasurableSpace (n k : Nat) :
    (t : Nat) → MeasurableSpace (PairedJointHistory n k t)
  | 0 => inferInstanceAs (MeasurableSpace Unit)
  | t + 1 => by
      letI := pairedJointHistoryMeasurableSpace n k t
      change MeasurableSpace (PairedJointHistory n k t ×
        (MSetAction n k × PairItem k))
      infer_instance

@[reducible] instance (n k t : Nat) :
    MeasurableSpace (PairedJointHistory n k t) :=
  pairedJointHistoryMeasurableSpace n k t

private theorem pairedJointHistoryDiscreteMeasurableSpace (n k : Nat) :
    ∀ t, DiscreteMeasurableSpace (PairedJointHistory n k t) := by
  intro t
  induction t with
  | zero => infer_instance
  | succ t ih =>
      letI : DiscreteMeasurableSpace (PairedJointHistory n k t) := ih
      change DiscreteMeasurableSpace
        (PairedJointHistory n k t × (MSetAction n k × PairItem k))
      infer_instance

instance (n k t : Nat) : DiscreteMeasurableSpace
    (PairedJointHistory n k t) :=
  pairedJointHistoryDiscreteMeasurableSpace n k t

private theorem pairedJointHistoryMeasurableSingletonClass (n k : Nat) :
    ∀ t, MeasurableSingletonClass (PairedJointHistory n k t) := by
  intro t
  induction t with
  | zero => infer_instance
  | succ t ih =>
      letI : MeasurableSingletonClass (PairedJointHistory n k t) := ih
      change MeasurableSingletonClass
        (PairedJointHistory n k t × (MSetAction n k × PairItem k))
      infer_instance

instance (n k t : Nat) : MeasurableSingletonClass
    (PairedJointHistory n k t) :=
  pairedJointHistoryMeasurableSingletonClass n k t

/-- Project a latent history to exactly the action--scalar-feedback history
available to the learner. -/
def pairedJointObservedHistory {n k : Nat} (hD : 2 * k ≤ n) :
    (t : Nat) → PairedJointHistory n k t → History n k t
  | 0, _ => ()
  | t + 1, (h, (A, J)) =>
      (pairedJointObservedHistory hD t h,
        (A, actionLoss A (pairedLoss hD J)))

theorem measurable_pairedJointObservedHistory {n k : Nat}
    (hD : 2 * k ≤ n) (t : Nat) :
    Measurable (pairedJointObservedHistory hD t) :=
  measurable_of_finite _

/-- The action kernel induced by the original policy on a latent prefix.
Only the observable projection is supplied to the policy. -/
def pairedJointActionKernel {n k : Nat} (P : Policy n k)
    (hD : 2 * k ≤ n) (t : Nat) :
    Kernel (PairedJointHistory n k t) (MSetAction n k) :=
  (P.kernel t).comap (pairedJointObservedHistory hD t)
    (measurable_pairedJointObservedHistory hD t)

instance pairedJointActionKernel.instIsMarkovKernel {n k : Nat}
    (P : Policy n k) (hD : 2 * k ≤ n) (t : Nat) :
    IsMarkovKernel (pairedJointActionKernel P hD t) := by
  unfold pairedJointActionKernel
  infer_instance

/-- Independently sample the current paired item after the action. -/
def pairedJointItemKernel {n k : Nat} (hk : 1 ≤ k)
    (θ : Fin k → PairSign) (ε : Real) (hε0 : 0 ≤ ε) (hε1 : ε ≤ 1)
    (t : Nat) :
    Kernel (PairedJointHistory n k t × MSetAction n k) (PairItem k) :=
  Kernel.const _ (pairedPMF hk θ ε hε0 hε1).toMeasure

instance pairedJointItemKernel.instIsMarkovKernel {n k : Nat}
    (hk : 1 ≤ k) (θ : Fin k → PairSign) (ε : Real)
    (hε0 : 0 ≤ ε) (hε1 : ε ≤ 1) (t : Nat) :
    IsMarkovKernel
      (pairedJointItemKernel (n := n) hk θ ε hε0 hε1 t) := by
  unfold pairedJointItemKernel
  infer_instance

/-- One genuine adaptive round: sample the policy action, then an independent
item `J_t ∼ p_θ`. -/
def pairedJointRoundKernel {n k : Nat} (P : Policy n k) (hk : 1 ≤ k)
    (hD : 2 * k ≤ n) (θ : Fin k → PairSign) (ε : Real)
    (hε0 : 0 ≤ ε) (hε1 : ε ≤ 1) (t : Nat) :
    Kernel (PairedJointHistory n k t) (MSetAction n k × PairItem k) :=
  pairedJointActionKernel P hD t ⊗ₖ
    pairedJointItemKernel (n := n) hk θ ε hε0 hε1 t

instance pairedJointRoundKernel.instIsMarkovKernel {n k : Nat}
    (P : Policy n k) (hk : 1 ≤ k) (hD : 2 * k ≤ n)
    (θ : Fin k → PairSign) (ε : Real) (hε0 : 0 ≤ ε)
    (hε1 : ε ≤ 1) (t : Nat) :
    IsMarkovKernel (pairedJointRoundKernel P hk hD θ ε hε0 hε1 t) := by
  unfold pairedJointRoundKernel
  infer_instance

/-- Law of the complete adaptive construction through `t` rounds. -/
@[reducible] def pairedJointLaw {n k : Nat} (P : Policy n k) (hk : 1 ≤ k)
    (hD : 2 * k ≤ n) (θ : Fin k → PairSign) (ε : Real)
    (hε0 : 0 ≤ ε) (hε1 : ε ≤ 1) :
    (t : Nat) → Measure (PairedJointHistory n k t)
  | 0 => Measure.dirac ()
  | t + 1 => pairedJointLaw P hk hD θ ε hε0 hε1 t ⊗ₘ
      pairedJointRoundKernel P hk hD θ ε hε0 hε1 t

theorem pairedJointLaw_isProbabilityMeasure {n k : Nat}
    (P : Policy n k) (hk : 1 ≤ k) (hD : 2 * k ≤ n)
    (θ : Fin k → PairSign) (ε : Real) (hε0 : 0 ≤ ε)
    (hε1 : ε ≤ 1) : ∀ t,
    IsProbabilityMeasure (pairedJointLaw P hk hD θ ε hε0 hε1 t) := by
  intro t
  induction t with
  | zero =>
      unfold pairedJointLaw
      infer_instance
  | succ t ih =>
      unfold pairedJointLaw
      letI : IsProbabilityMeasure
          (pairedJointLaw P hk hD θ ε hε0 hε1 t) := ih
      letI : IsMarkovKernel
          (pairedJointRoundKernel P hk hD θ ε hε0 hε1 t) := by
        unfold pairedJointRoundKernel
        infer_instance
      constructor
      exact Measure.compProd_apply_univ.trans measure_univ

/-- On a finite history space every real-valued function is integrable under
a finite measure. -/
theorem integrable_of_fintype_domain
    {Ω : Type*} [Fintype Ω] [MeasurableSpace Ω]
    [MeasurableSingletonClass Ω] (μ : Measure Ω) [IsFiniteMeasure μ]
    (f : Ω → Real) : Integrable f μ := by
  apply Integrable.of_bound (measurable_of_finite _).aestronglyMeasurable
    (∑ ω, ‖f ω‖)
  apply ae_of_all
  intro ω
  exact Finset.single_le_sum (fun x _ => norm_nonneg (f x))
    (Finset.mem_univ ω)

/-! ## Gap, predictable mean, and martingale part -/

/-- One-round realized gap against the fixed comparator `x^θ`. -/
def pairedGapIncrement {n k : Nat} (hD : 2 * k ≤ n)
    (θ : Fin k → PairSign) (A : MSetAction n k) (J : PairItem k) : Real :=
  actionLoss A (pairedLoss hD J) -
    actionLoss (pairedComparator hD θ) (pairedLoss hD J)

/-- Expected gap after fixing the current action. -/
def pairedActionMeanGap {n k : Nat} (hk : 1 ≤ k)
    (hD : 2 * k ≤ n) (θ : Fin k → PairSign) (ε : Real)
    (hε0 : 0 ≤ ε) (hε1 : ε ≤ 1) (A : MSetAction n k) : Real :=
  pairedExpectedActionLoss hk hD θ ε hε0 hε1 A -
    pairedExpectedActionLoss hk hD θ ε hε0 hε1
      (pairedComparator hD θ)

/-- Predictable mean of the next gap under the randomized policy, conditional
only on the observable past. -/
def pairedPredictableIncrement {n k : Nat} (P : Policy n k) (hk : 1 ≤ k)
    (hD : 2 * k ≤ n) (θ : Fin k → PairSign) (ε : Real)
    (hε0 : 0 ≤ ε) (hε1 : ε ≤ 1) (t : Nat)
    (h : PairedJointHistory n k t) : Real :=
  ∫ A, pairedActionMeanGap hk hD θ ε hε0 hε1 A
    ∂P.kernel t (pairedJointObservedHistory hD t h)

/-- Realized cumulative fixed-comparator gap `G_t^θ`. -/
def pairedGap {n k : Nat} (hD : 2 * k ≤ n) (θ : Fin k → PairSign) :
    (t : Nat) → PairedJointHistory n k t → Real
  | 0, _ => 0
  | t + 1, (h, (A, J)) =>
      pairedGap hD θ t h + pairedGapIncrement hD θ A J

/-- Predictable cumulative mean `A_t^θ`. -/
def pairedPredictableMean {n k : Nat} (P : Policy n k) (hk : 1 ≤ k)
    (hD : 2 * k ≤ n) (θ : Fin k → PairSign) (ε : Real)
    (hε0 : 0 ≤ ε) (hε1 : ε ≤ 1) :
    (t : Nat) → PairedJointHistory n k t → Real
  | 0, _ => 0
  | t + 1, (h, _) =>
      pairedPredictableMean P hk hD θ ε hε0 hε1 t h +
        pairedPredictableIncrement P hk hD θ ε hε0 hε1 t h

/-- Martingale part `M_t^θ = G_t^θ - A_t^θ`. -/
def pairedMartingalePart {n k : Nat} (P : Policy n k) (hk : 1 ≤ k)
    (hD : 2 * k ≤ n) (θ : Fin k → PairSign) (ε : Real)
    (hε0 : 0 ≤ ε) (hε1 : ε ≤ 1) (t : Nat)
    (h : PairedJointHistory n k t) : Real :=
  pairedGap hD θ t h -
    pairedPredictableMean P hk hD θ ε hε0 hε1 t h

theorem pairedGap_eq_predictableMean_add_martingalePart {n k : Nat}
    (P : Policy n k) (hk : 1 ≤ k) (hD : 2 * k ≤ n)
    (θ : Fin k → PairSign) (ε : Real) (hε0 : 0 ≤ ε)
    (hε1 : ε ≤ 1) (t : Nat) (h : PairedJointHistory n k t) :
    pairedGap hD θ t h =
      pairedPredictableMean P hk hD θ ε hε0 hε1 t h +
        pairedMartingalePart P hk hD θ ε hε0 hε1 t h := by
  simp [pairedMartingalePart]

theorem pairedGapIncrement_mem_Icc {n k : Nat} (hk : 1 ≤ k)
    (hD : 2 * k ≤ n) (θ : Fin k → PairSign)
    (A : MSetAction n k) (J : PairItem k) :
    pairedGapIncrement hD θ A J ∈ Set.Icc (-1 : Real) 1 := by
  have hA := lower_dense_action_loss_mem_Icc hk hD A J
  have hx := lower_dense_action_loss_mem_Icc hk hD
    (pairedComparator hD θ) J
  unfold pairedGapIncrement
  rcases hA with ⟨hA0, hA1⟩
  rcases hx with ⟨hx0, hx1⟩
  constructor <;> linarith

theorem pairedActionMeanGap_eq_disagreement {n k : Nat} (hk : 1 ≤ k)
    (hD : 2 * k ≤ n) (θ : Fin k → PairSign) (ε : Real)
    (hε0 : 0 ≤ ε) (hε1 : ε ≤ 1) (A : MSetAction n k) :
    pairedActionMeanGap hk hD θ ε hε0 hε1 A =
      ε / (3 * (k : Real)) * pairedDisagreement hD θ A := by
  exact (paired_pseudoregret hk hD θ ε hε0 hε1 A).2

theorem pairedActionMeanGap_mem_Icc {n k : Nat} (hk : 1 ≤ k)
    (hD : 2 * k ≤ n) (θ : Fin k → PairSign) {ε : Real}
    (hε0 : 0 ≤ ε) (hε1 : ε ≤ 1) (A : MSetAction n k) :
    pairedActionMeanGap hk hD θ ε hε0 hε1 A ∈
      Set.Icc (0 : Real) (2 * ε / 3) :=
  paired_pseudoregret_mem_Icc hk hD θ hε0 hε1 A

/-- The finite expectation over the actual sampled item is exactly the
one-action pseudoregret from `eq:paired-pseudoregret`. -/
theorem integral_pairedGapIncrement_pairedPMF {n k : Nat} (hk : 1 ≤ k)
    (hD : 2 * k ≤ n) (θ : Fin k → PairSign) (ε : Real)
    (hε0 : 0 ≤ ε) (hε1 : ε ≤ 1) (A : MSetAction n k) :
    (∫ J, pairedGapIncrement hD θ A J
      ∂(pairedPMF hk θ ε hε0 hε1).toMeasure) =
      pairedActionMeanGap hk hD θ ε hε0 hε1 A := by
  let p := pairedPMF hk θ ε hε0 hε1
  calc
    (∫ J, pairedGapIncrement hD θ A J ∂p.toMeasure) =
        ∑ J : PairItem k, (p J).toReal *
          pairedGapIncrement hD θ A J := by
      rw [integral_fintype .of_finite]
      apply Finset.sum_congr rfl
      intro J _
      rw [measureReal_def,
        PMF.toMeasure_apply_singleton p J (MeasurableSet.singleton J)]
      rfl
    _ = pairedActionMeanGap hk hD θ ε hε0 hε1 A := by
      rw [pairedActionMeanGap, pairedExpectedActionLoss,
        pairedExpectedActionLoss]
      simp only [pairedGapIncrement]
      rw [← Finset.sum_sub_distrib]
      apply Finset.sum_congr rfl
      intro J _
      ring

theorem pairedPredictableIncrement_mem_Icc {n k : Nat}
    (P : Policy n k) (hk : 1 ≤ k) (hD : 2 * k ≤ n)
    (θ : Fin k → PairSign) {ε : Real} (hε0 : 0 ≤ ε)
    (hε1 : ε ≤ 1) (t : Nat) (h : PairedJointHistory n k t) :
    pairedPredictableIncrement P hk hD θ ε hε0 hε1 t h ∈
      Set.Icc (0 : Real) (2 * ε / 3) := by
  let μ := P.kernel t (pairedJointObservedHistory hD t h)
  let f := pairedActionMeanGap hk hD θ ε hε0 hε1
  letI : IsProbabilityMeasure μ := by
    dsimp [μ]
    infer_instance
  have hf : Integrable f μ := integrable_of_fintype_domain μ f
  constructor
  · exact integral_nonneg fun A =>
      (pairedActionMeanGap_mem_Icc hk hD θ hε0 hε1 A).1
  · calc
      pairedPredictableIncrement P hk hD θ ε hε0 hε1 t h =
          ∫ A, f A ∂μ := rfl
      _ ≤ ∫ _A, 2 * ε / 3 ∂μ := by
        exact integral_mono hf (integrable_const _) fun A =>
          (pairedActionMeanGap_mem_Icc hk hD θ hε0 hε1 A).2
      _ = 2 * ε / 3 := by simp

/-- Conditional on a latent prefix, the next realized gap has precisely the
predictable mean defined above. -/
theorem integral_pairedGapIncrement_roundKernel {n k : Nat}
    (P : Policy n k) (hk : 1 ≤ k) (hD : 2 * k ≤ n)
    (θ : Fin k → PairSign) (ε : Real) (hε0 : 0 ≤ ε)
    (hε1 : ε ≤ 1) (t : Nat) (h : PairedJointHistory n k t) :
    (∫ z, pairedGapIncrement hD θ z.1 z.2
      ∂pairedJointRoundKernel P hk hD θ ε hε0 hε1 t h) =
      pairedPredictableIncrement P hk hD θ ε hε0 hε1 t h := by
  let κ := pairedJointRoundKernel P hk hD θ ε hε0 hε1 t
  letI : IsProbabilityMeasure (κ h) := by
    dsimp [κ]
    infer_instance
  have hint : Integrable
      (fun z : MSetAction n k × PairItem k =>
        pairedGapIncrement hD θ z.1 z.2) (κ h) :=
    integrable_of_fintype_domain _ _
  unfold pairedJointRoundKernel at hint ⊢
  rw [ProbabilityTheory.integral_compProd hint]
  simp_rw [pairedJointItemKernel, Kernel.const_apply,
    integral_pairedGapIncrement_pairedPMF hk hD θ ε hε0 hε1]
  rw [pairedJointActionKernel, Kernel.comap_apply]
  rfl

/-- Kernel form of the martingale property: the next martingale part has
conditional expectation equal to its current value. -/
theorem pairedMartingalePart_kernel_martingale {n k : Nat}
    (P : Policy n k) (hk : 1 ≤ k) (hD : 2 * k ≤ n)
    (θ : Fin k → PairSign) (ε : Real) (hε0 : 0 ≤ ε)
    (hε1 : ε ≤ 1) (t : Nat) (h : PairedJointHistory n k t) :
    (∫ z,
      pairedMartingalePart P hk hD θ ε hε0 hε1 (t + 1) (h, z)
      ∂pairedJointRoundKernel P hk hD θ ε hε0 hε1 t h) =
      pairedMartingalePart P hk hD θ ε hε0 hε1 t h := by
  let κ := pairedJointRoundKernel P hk hD θ ε hε0 hε1 t
  letI : IsProbabilityMeasure (κ h) := by
    dsimp [κ]
    infer_instance
  have hgap : Integrable
      (fun z : MSetAction n k × PairItem k =>
        pairedGapIncrement hD θ z.1 z.2) (κ h) :=
    integrable_of_fintype_domain _ _
  simp only [pairedMartingalePart, pairedGap, pairedPredictableMean]
  have hfun :
      (fun z : MSetAction n k × PairItem k =>
        pairedGap hD θ t h + pairedGapIncrement hD θ z.1 z.2 -
          (pairedPredictableMean P hk hD θ ε hε0 hε1 t h +
            pairedPredictableIncrement P hk hD θ ε hε0 hε1 t h)) =
      (fun z =>
        (pairedGap hD θ t h -
          pairedPredictableMean P hk hD θ ε hε0 hε1 t h) +
        (pairedGapIncrement hD θ z.1 z.2 -
          pairedPredictableIncrement P hk hD θ ε hε0 hε1 t h)) := by
    funext z
    ring
  rw [hfun]
  have hsplit :
      (∫ z : MSetAction n k × PairItem k,
        (pairedGap hD θ t h -
          pairedPredictableMean P hk hD θ ε hε0 hε1 t h) +
        (pairedGapIncrement hD θ z.1 z.2 -
          pairedPredictableIncrement P hk hD θ ε hε0 hε1 t h) ∂κ h) =
      (∫ _z : MSetAction n k × PairItem k,
        pairedGap hD θ t h -
          pairedPredictableMean P hk hD θ ε hε0 hε1 t h ∂κ h) +
      ∫ z : MSetAction n k × PairItem k,
        pairedGapIncrement hD θ z.1 z.2 -
          pairedPredictableIncrement P hk hD θ ε hε0 hε1 t h ∂κ h := by
    exact integral_add (integrable_const _)
      (hgap.sub (integrable_const _))
  have hsub :
      (∫ z : MSetAction n k × PairItem k,
        pairedGapIncrement hD θ z.1 z.2 -
          pairedPredictableIncrement P hk hD θ ε hε0 hε1 t h ∂κ h) =
      (∫ z : MSetAction n k × PairItem k,
        pairedGapIncrement hD θ z.1 z.2 ∂κ h) -
      ∫ _z : MSetAction n k × PairItem k,
        pairedPredictableIncrement P hk hD θ ε hε0 hε1 t h ∂κ h := by
    exact integral_sub' hgap (integrable_const _)
  rw [hsplit, hsub,
    integral_pairedGapIncrement_roundKernel P hk hD θ ε hε0 hε1 t h]
  simp

/-- Conditional variance of one realized gap is at most one, derived from
the pathwise interval `[-1,1]`; no second-moment hypothesis is assumed. -/
theorem integral_centeredGap_sq_roundKernel_le_one {n k : Nat}
    (P : Policy n k) (hk : 1 ≤ k) (hD : 2 * k ≤ n)
    (θ : Fin k → PairSign) (ε : Real) (hε0 : 0 ≤ ε)
    (hε1 : ε ≤ 1) (t : Nat) (h : PairedJointHistory n k t) :
    (∫ z,
      (pairedGapIncrement hD θ z.1 z.2 -
        pairedPredictableIncrement P hk hD θ ε hε0 hε1 t h) ^ 2
      ∂pairedJointRoundKernel P hk hD θ ε hε0 hε1 t h) ≤ 1 := by
  let μ := pairedJointRoundKernel P hk hD θ ε hε0 hε1 t h
  let X : MSetAction n k × PairItem k → Real :=
    fun z => pairedGapIncrement hD θ z.1 z.2
  let c := pairedPredictableIncrement P hk hD θ ε hε0 hε1 t h
  letI : IsProbabilityMeasure μ := by
    dsimp [μ]
    infer_instance
  have hXmeas : Measurable X := measurable_of_finite _
  have hXsq : Integrable (fun z => (X z) ^ 2) μ :=
    integrable_of_fintype_domain _ _
  have hXL2 : MemLp X 2 μ := by
    rw [memLp_two_iff_integrable_sq hXmeas.aestronglyMeasurable]
    exact hXsq
  have hmean : (∫ z, X z ∂μ) = c :=
    integral_pairedGapIncrement_roundKernel
      P hk hD θ ε hε0 hε1 t h
  change (∫ z, (X z - c) ^ 2 ∂μ) ≤ 1
  calc
    (∫ z, (X z - c) ^ 2 ∂μ) =
        ∫ z, (X z - ∫ y, X y ∂μ) ^ 2 ∂μ := by rw [hmean]
    _ = Var[X; μ] := (variance_eq_integral hXmeas.aemeasurable).symm
    _ = (∫ z, (X z) ^ 2 ∂μ) - (∫ z, X z ∂μ) ^ 2 :=
      variance_eq_sub hXL2
    _ ≤ ∫ z, (X z) ^ 2 ∂μ := by
      exact sub_le_self _ (sq_nonneg _)
    _ ≤ ∫ _z, (1 : Real) ∂μ := by
      apply integral_mono hXsq (integrable_const _)
      intro z
      have hz := pairedGapIncrement_mem_Icc hk hD θ z.1 z.2
      change -1 ≤ X z ∧ X z ≤ 1 at hz
      rcases hz with ⟨hz0, hz1⟩
      nlinarith [sq_nonneg (X z)]
    _ = 1 := by simp

theorem integral_martingalePart_succ_sq_roundKernel_le {n k : Nat}
    (P : Policy n k) (hk : 1 ≤ k) (hD : 2 * k ≤ n)
    (θ : Fin k → PairSign) (ε : Real) (hε0 : 0 ≤ ε)
    (hε1 : ε ≤ 1) (t : Nat) (h : PairedJointHistory n k t) :
    (∫ z,
      (pairedMartingalePart P hk hD θ ε hε0 hε1 (t + 1) (h, z)) ^ 2
      ∂pairedJointRoundKernel P hk hD θ ε hε0 hε1 t h) ≤
      (pairedMartingalePart P hk hD θ ε hε0 hε1 t h) ^ 2 + 1 := by
  let μ := pairedJointRoundKernel P hk hD θ ε hε0 hε1 t h
  let Y : MSetAction n k × PairItem k → Real := fun z =>
    pairedMartingalePart P hk hD θ ε hε0 hε1 (t + 1) (h, z)
  let m := pairedMartingalePart P hk hD θ ε hε0 hε1 t h
  letI : IsProbabilityMeasure μ := by
    dsimp [μ]
    infer_instance
  have hYmeas : Measurable Y := measurable_of_finite _
  have hYsq : Integrable (fun z => (Y z) ^ 2) μ :=
    integrable_of_fintype_domain _ _
  have hYL2 : MemLp Y 2 μ := by
    rw [memLp_two_iff_integrable_sq hYmeas.aestronglyMeasurable]
    exact hYsq
  have hmean : (∫ z, Y z ∂μ) = m :=
    pairedMartingalePart_kernel_martingale
      P hk hD θ ε hε0 hε1 t h
  have hcenter :
      (∫ z, (Y z - m) ^ 2 ∂μ) ≤ 1 := by
    have hfun : (fun z => (Y z - m) ^ 2) =
        (fun z =>
          (pairedGapIncrement hD θ z.1 z.2 -
            pairedPredictableIncrement P hk hD θ ε hε0 hε1 t h) ^ 2) := by
      funext z
      dsimp [Y, m, pairedMartingalePart, pairedGap,
        pairedPredictableMean]
      congr 1
      ring
    rw [hfun]
    exact integral_centeredGap_sq_roundKernel_le_one
      P hk hD θ ε hε0 hε1 t h
  have hvar : Var[Y; μ] ≤ 1 := by
    rw [variance_eq_integral hYmeas.aemeasurable, hmean]
    exact hcenter
  rw [variance_eq_sub hYL2] at hvar
  change (∫ z, (Y z) ^ 2 ∂μ) ≤ m ^ 2 + 1
  rw [hmean] at hvar
  change (∫ z, (Y z) ^ 2 ∂μ) - m ^ 2 ≤ 1 at hvar
  linarith

/-- The martingale square moment grows by at most one per round.  This is
the formal counterpart of the conditional-variance sum in the manuscript. -/
theorem integral_pairedMartingalePart_sq_le_time {n k : Nat}
    (P : Policy n k) (hk : 1 ≤ k) (hD : 2 * k ≤ n)
    (θ : Fin k → PairSign) (ε : Real) (hε0 : 0 ≤ ε)
    (hε1 : ε ≤ 1) : ∀ t : Nat,
    (∫ h,
      (pairedMartingalePart P hk hD θ ε hε0 hε1 t h) ^ 2
      ∂pairedJointLaw P hk hD θ ε hε0 hε1 t) ≤ (t : Real) := by
  intro t
  induction t with
  | zero => simp [pairedJointLaw, pairedMartingalePart, pairedGap,
      pairedPredictableMean]
  | succ t ih =>
      let μ : Measure (PairedJointHistory n k t) :=
        pairedJointLaw P hk hD θ ε hε0 hε1 t
      let κ : Kernel (PairedJointHistory n k t)
          (MSetAction n k × PairItem k) :=
        pairedJointRoundKernel P hk hD θ ε hε0 hε1 t
      letI : IsProbabilityMeasure μ :=
        pairedJointLaw_isProbabilityMeasure P hk hD θ ε hε0 hε1 t
      let hsf : SFinite μ := by infer_instance
      letI : SFinite μ := hsf
      letI : IsMarkovKernel κ := by
        dsimp [κ]
        infer_instance
      let hsk : IsSFiniteKernel κ := by infer_instance
      letI : IsProbabilityMeasure
          (pairedJointLaw P hk hD θ ε hε0 hε1 (t + 1)) :=
        pairedJointLaw_isProbabilityMeasure P hk hD θ ε hε0 hε1 (t + 1)
      letI : MeasurableSingletonClass (PairedJointHistory n k (t + 1)) :=
        pairedJointHistoryMeasurableSingletonClass n k (t + 1)
      let hfinJoint : IsFiniteMeasure
          (pairedJointLaw P hk hD θ ε hε0 hε1 (t + 1)) := by
        infer_instance
      have hfullJoint : Integrable
          (fun x : PairedJointHistory n k (t + 1) =>
            (pairedMartingalePart P hk hD θ ε hε0 hε1 (t + 1) x) ^ 2)
          (pairedJointLaw P hk hD θ ε hε0 hε1 (t + 1)) :=
        @integrable_of_fintype_domain
          (PairedJointHistory n k (t + 1))
          (pairedJointHistoryFintype n k (t + 1))
          (pairedJointHistoryMeasurableSpace n k (t + 1))
          (pairedJointHistoryMeasurableSingletonClass n k (t + 1))
          (pairedJointLaw P hk hD θ ε hε0 hε1 (t + 1))
          hfinJoint _
      have hfull : Integrable
          (fun x : PairedJointHistory n k t ×
              (MSetAction n k × PairItem k) =>
            (pairedMartingalePart P hk hD θ ε hε0 hε1 (t + 1) x) ^ 2)
          (μ ⊗ₘ κ) := by
        simpa [μ, κ, pairedJointLaw] using hfullJoint
      change (∫ x : PairedJointHistory n k t ×
          (MSetAction n k × PairItem k),
        (pairedMartingalePart P hk hD θ ε hε0 hε1 (t + 1) x) ^ 2
        ∂(μ ⊗ₘ κ)) ≤ ((t + 1 : Nat) : Real)
      have hfubini :
          (∫ x : PairedJointHistory n k t ×
              (MSetAction n k × PairItem k),
            (pairedMartingalePart P hk hD θ ε hε0 hε1 (t + 1) x) ^ 2
            ∂(μ ⊗ₘ κ)) =
          ∫ h, ∫ z,
            (pairedMartingalePart P hk hD θ ε hε0 hε1 (t + 1)
              (h, z)) ^ 2 ∂κ h ∂μ :=
        @Measure.integral_compProd
          (PairedJointHistory n k t)
          (MSetAction n k × PairItem k)
          (pairedJointHistoryMeasurableSpace n k t)
          (inferInstanceAs (MeasurableSpace
            (MSetAction n k × PairItem k)))
          κ μ hsf hsk Real inferInstance inferInstance _ hfull
      rw [hfubini]
      calc
        (∫ h, ∫ z,
          (pairedMartingalePart P hk hD θ ε hε0 hε1 (t + 1)
            (h, z)) ^ 2 ∂κ h ∂μ) ≤
            ∫ h,
              (pairedMartingalePart P hk hD θ ε hε0 hε1 t h) ^ 2 + 1
              ∂μ := by
          apply integral_mono
          · exact integrable_of_fintype_domain _ _
          · exact integrable_of_fintype_domain _ _
          · intro h
            exact integral_martingalePart_succ_sq_roundKernel_le
              P hk hD θ ε hε0 hε1 t h
        _ = (∫ h,
              (pairedMartingalePart P hk hD θ ε hε0 hε1 t h) ^ 2 ∂μ) +
              1 := by
          rw [integral_add (integrable_of_fintype_domain _ _)
            (integrable_const _)]
          simp
        _ ≤ (t : Real) + 1 := by
          simpa [μ, add_comm] using add_le_add_right ih 1
        _ = (t + 1 : Nat) := by norm_num

/-! ## Predictable-size and mean identities -/

/-- Cumulative manuscript discrepancy `∑_{s≤t} h_θ(S_s)` on the genuine
joint history. -/
def pairedTotalDisagreement {n k : Nat} (hD : 2 * k ≤ n)
    (θ : Fin k → PairSign) :
    (t : Nat) → PairedJointHistory n k t → Real
  | 0, _ => 0
  | t + 1, (h, (A, _J)) =>
      pairedTotalDisagreement hD θ t h + pairedDisagreement hD θ A

/-- Sum of the action-conditioned mean gaps.  It is pointwise a constant
multiple of `pairedTotalDisagreement`. -/
def pairedPseudoregretSum {n k : Nat} (hk : 1 ≤ k)
    (hD : 2 * k ≤ n) (θ : Fin k → PairSign) (ε : Real)
    (hε0 : 0 ≤ ε) (hε1 : ε ≤ 1) :
    (t : Nat) → PairedJointHistory n k t → Real
  | 0, _ => 0
  | t + 1, (h, (A, _J)) =>
      pairedPseudoregretSum hk hD θ ε hε0 hε1 t h +
        pairedActionMeanGap hk hD θ ε hε0 hε1 A

theorem pairedPseudoregretSum_eq_disagreement {n k : Nat} (hk : 1 ≤ k)
    (hD : 2 * k ≤ n) (θ : Fin k → PairSign) (ε : Real)
    (hε0 : 0 ≤ ε) (hε1 : ε ≤ 1) : ∀ t (h : PairedJointHistory n k t),
    pairedPseudoregretSum hk hD θ ε hε0 hε1 t h =
      ε / (3 * (k : Real)) * pairedTotalDisagreement hD θ t h := by
  intro t
  induction t with
  | zero => intro h; simp [pairedPseudoregretSum, pairedTotalDisagreement]
  | succ t ih =>
      rintro ⟨h, A, J⟩
      simp only [pairedPseudoregretSum, pairedTotalDisagreement]
      rw [ih h, pairedActionMeanGap_eq_disagreement]
      ring

theorem pairedPredictableMean_mem_Icc {n k : Nat}
    (P : Policy n k) (hk : 1 ≤ k) (hD : 2 * k ≤ n)
    (θ : Fin k → PairSign) {ε : Real} (hε0 : 0 ≤ ε)
    (hε1 : ε ≤ 1) : ∀ t (h : PairedJointHistory n k t),
    pairedPredictableMean P hk hD θ ε hε0 hε1 t h ∈
      Set.Icc (0 : Real) ((t : Real) * (2 * ε / 3)) := by
  intro t
  induction t with
  | zero => intro h; simp [pairedPredictableMean]
  | succ t ih =>
      rintro ⟨h, A, J⟩
      simp only [pairedPredictableMean]
      have hp := pairedPredictableIncrement_mem_Icc
        P hk hD θ hε0 hε1 t h
      have ht := ih h
      constructor <;> rcases hp with ⟨hp0, hp1⟩ <;>
        rcases ht with ⟨ht0, ht1⟩ <;>
        push_cast <;> nlinarith

/-- Fubini identity for one recursive step of the genuine joint law. -/
theorem integral_pairedJointLaw_succ {n k : Nat}
    (P : Policy n k) (hk : 1 ≤ k) (hD : 2 * k ≤ n)
    (θ : Fin k → PairSign) (ε : Real) (hε0 : 0 ≤ ε)
    (hε1 : ε ≤ 1) (t : Nat)
    (f : PairedJointHistory n k (t + 1) → Real) :
    (∫ x, f x ∂pairedJointLaw P hk hD θ ε hε0 hε1 (t + 1)) =
      ∫ h, ∫ z, f (h, z)
        ∂pairedJointRoundKernel P hk hD θ ε hε0 hε1 t h
        ∂pairedJointLaw P hk hD θ ε hε0 hε1 t := by
  let μ : Measure (PairedJointHistory n k t) :=
    pairedJointLaw P hk hD θ ε hε0 hε1 t
  let κ : Kernel (PairedJointHistory n k t)
      (MSetAction n k × PairItem k) :=
    pairedJointRoundKernel P hk hD θ ε hε0 hε1 t
  letI : IsProbabilityMeasure μ :=
    pairedJointLaw_isProbabilityMeasure P hk hD θ ε hε0 hε1 t
  let hsf : SFinite μ := by infer_instance
  letI : IsMarkovKernel κ := by dsimp [κ]; infer_instance
  let hsk : IsSFiniteKernel κ := by infer_instance
  letI : IsProbabilityMeasure
      (pairedJointLaw P hk hD θ ε hε0 hε1 (t + 1)) :=
    pairedJointLaw_isProbabilityMeasure P hk hD θ ε hε0 hε1 (t + 1)
  let hfin : IsFiniteMeasure
      (pairedJointLaw P hk hD θ ε hε0 hε1 (t + 1)) := by infer_instance
  have hf : Integrable f
      (pairedJointLaw P hk hD θ ε hε0 hε1 (t + 1)) :=
    @integrable_of_fintype_domain
      (PairedJointHistory n k (t + 1))
      (pairedJointHistoryFintype n k (t + 1))
      (pairedJointHistoryMeasurableSpace n k (t + 1))
      (pairedJointHistoryMeasurableSingletonClass n k (t + 1))
      (pairedJointLaw P hk hD θ ε hε0 hε1 (t + 1)) hfin f
  have hf' : Integrable
      (fun x : PairedJointHistory n k t ×
        (MSetAction n k × PairItem k) => f x) (μ ⊗ₘ κ) := by
    simpa [μ, κ, pairedJointLaw] using hf
  have hFubini := @Measure.integral_compProd
    (PairedJointHistory n k t)
    (MSetAction n k × PairItem k)
    (pairedJointHistoryMeasurableSpace n k t)
    (inferInstanceAs (MeasurableSpace (MSetAction n k × PairItem k)))
    κ μ hsf hsk Real inferInstance inferInstance
    (fun x => f x) hf'
  change (∫ x : PairedJointHistory n k t ×
      (MSetAction n k × PairItem k), f x ∂(μ ⊗ₘ κ)) =
    ∫ h, ∫ z, f (h, z) ∂κ h ∂μ
  exact hFubini

/-- Under a genuine round kernel, averaging the action-conditioned mean gap
over the sampled action gives the predictable increment.  The subsequently
sampled latent item integrates out because its law has mass one. -/
theorem integral_pairedActionMeanGap_roundKernel {n k : Nat}
    (P : Policy n k) (hk : 1 ≤ k) (hD : 2 * k ≤ n)
    (θ : Fin k → PairSign) (ε : Real) (hε0 : 0 ≤ ε)
    (hε1 : ε ≤ 1) (t : Nat) (h : PairedJointHistory n k t) :
    (∫ z, pairedActionMeanGap hk hD θ ε hε0 hε1 z.1
      ∂pairedJointRoundKernel P hk hD θ ε hε0 hε1 t h) =
      pairedPredictableIncrement P hk hD θ ε hε0 hε1 t h := by
  let κ := pairedJointRoundKernel P hk hD θ ε hε0 hε1 t
  letI : IsProbabilityMeasure (κ h) := by
    dsimp [κ]
    infer_instance
  have hint : Integrable
      (fun z : MSetAction n k × PairItem k =>
        pairedActionMeanGap hk hD θ ε hε0 hε1 z.1) (κ h) :=
    integrable_of_fintype_domain _ _
  unfold pairedJointRoundKernel at hint ⊢
  rw [ProbabilityTheory.integral_compProd hint]
  simp_rw [pairedJointItemKernel, Kernel.const_apply]
  simp only [integral_const]
  simp
  rw [pairedJointActionKernel, Kernel.comap_apply]
  rfl

theorem integral_pairedGap_succ_roundKernel {n k : Nat}
    (P : Policy n k) (hk : 1 ≤ k) (hD : 2 * k ≤ n)
    (θ : Fin k → PairSign) (ε : Real) (hε0 : 0 ≤ ε)
    (hε1 : ε ≤ 1) (t : Nat) (h : PairedJointHistory n k t) :
    (∫ z, pairedGap hD θ (t + 1) (h, z)
      ∂pairedJointRoundKernel P hk hD θ ε hε0 hε1 t h) =
      pairedGap hD θ t h +
        pairedPredictableIncrement P hk hD θ ε hε0 hε1 t h := by
  let μ := pairedJointRoundKernel P hk hD θ ε hε0 hε1 t h
  letI : IsProbabilityMeasure μ := by
    dsimp [μ]
    infer_instance
  change (∫ z, pairedGap hD θ t h +
      pairedGapIncrement hD θ z.1 z.2 ∂μ) = _
  rw [integral_add (integrable_const _)
    (integrable_of_fintype_domain _ _)]
  simp only [integral_const]
  simp
  rw [integral_pairedGapIncrement_roundKernel]

theorem integral_pairedPseudoregretSum_succ_roundKernel {n k : Nat}
    (P : Policy n k) (hk : 1 ≤ k) (hD : 2 * k ≤ n)
    (θ : Fin k → PairSign) (ε : Real) (hε0 : 0 ≤ ε)
    (hε1 : ε ≤ 1) (t : Nat) (h : PairedJointHistory n k t) :
    (∫ z, pairedPseudoregretSum hk hD θ ε hε0 hε1 (t + 1) (h, z)
      ∂pairedJointRoundKernel P hk hD θ ε hε0 hε1 t h) =
      pairedPseudoregretSum hk hD θ ε hε0 hε1 t h +
        pairedPredictableIncrement P hk hD θ ε hε0 hε1 t h := by
  let μ := pairedJointRoundKernel P hk hD θ ε hε0 hε1 t h
  letI : IsProbabilityMeasure μ := by
    dsimp [μ]
    infer_instance
  change (∫ z, pairedPseudoregretSum hk hD θ ε hε0 hε1 t h +
      pairedActionMeanGap hk hD θ ε hε0 hε1 z.1 ∂μ) = _
  rw [integral_add (integrable_const _)
    (integrable_of_fintype_domain _ _)]
  simp only [integral_const]
  simp
  rw [integral_pairedActionMeanGap_roundKernel]

/-- The expectation of the realized fixed-comparator gap equals the
expectation of the sum of its action-conditioned means. -/
theorem integral_pairedGap_eq_pseudoregretSum {n k : Nat}
    (P : Policy n k) (hk : 1 ≤ k) (hD : 2 * k ≤ n)
    (θ : Fin k → PairSign) (ε : Real) (hε0 : 0 ≤ ε)
    (hε1 : ε ≤ 1) : ∀ t : Nat,
    (∫ h, pairedGap hD θ t h
      ∂pairedJointLaw P hk hD θ ε hε0 hε1 t) =
      ∫ h, pairedPseudoregretSum hk hD θ ε hε0 hε1 t h
        ∂pairedJointLaw P hk hD θ ε hε0 hε1 t := by
  intro t
  induction t with
  | zero => simp [pairedJointLaw, pairedGap, pairedPseudoregretSum]
  | succ t ih =>
      letI : IsProbabilityMeasure
          (pairedJointLaw P hk hD θ ε hε0 hε1 t) :=
        pairedJointLaw_isProbabilityMeasure P hk hD θ ε hε0 hε1 t
      rw [integral_pairedJointLaw_succ,
        integral_pairedJointLaw_succ]
      simp_rw [integral_pairedGap_succ_roundKernel,
        integral_pairedPseudoregretSum_succ_roundKernel]
      rw [integral_add (integrable_of_fintype_domain _ _)
          (integrable_of_fintype_domain _ _),
        integral_add (integrable_of_fintype_domain _ _)
          (integrable_of_fintype_domain _ _), ih]

/-- Exact expectation identity behind `eq:lower-dense-positive-mean`. -/
theorem integral_pairedGap_eq_disagreement {n k : Nat}
    (P : Policy n k) (hk : 1 ≤ k) (hD : 2 * k ≤ n)
    (θ : Fin k → PairSign) (ε : Real) (hε0 : 0 ≤ ε)
    (hε1 : ε ≤ 1) (t : Nat) :
    (∫ h, pairedGap hD θ t h
      ∂pairedJointLaw P hk hD θ ε hε0 hε1 t) =
      ε / (3 * (k : Real)) *
        ∫ h, pairedTotalDisagreement hD θ t h
          ∂pairedJointLaw P hk hD θ ε hε0 hε1 t := by
  rw [integral_pairedGap_eq_pseudoregretSum]
  calc
    (∫ h, pairedPseudoregretSum hk hD θ ε hε0 hε1 t h
      ∂pairedJointLaw P hk hD θ ε hε0 hε1 t) =
        ∫ h, ε / (3 * (k : Real)) *
          pairedTotalDisagreement hD θ t h
          ∂pairedJointLaw P hk hD θ ε hε0 hε1 t := by
      apply integral_congr_ae
      filter_upwards [] with h
      rw [pairedPseudoregretSum_eq_disagreement]
    _ = _ := by rw [integral_const_mul]

/-! ## The manuscript's dense constants -/

theorem denseEpsilon_mul_horizon {k T : Nat} (hT : 1 ≤ T) :
    denseEpsilon k T * (T : Real) =
      (k : Real) * Real.sqrt T / 8 := by
  have hsqrt_pos : 0 < Real.sqrt (T : Real) :=
    Real.sqrt_pos.2 (by exact_mod_cast hT)
  have hsqrt_ne : Real.sqrt (T : Real) ≠ 0 := ne_of_gt hsqrt_pos
  have hsquare : (Real.sqrt (T : Real)) ^ 2 = (T : Real) :=
    Real.sq_sqrt (Nat.cast_nonneg T)
  have hquot : (T : Real) / Real.sqrt T = Real.sqrt T := by
    apply (div_eq_iff hsqrt_ne).2
    simpa [pow_two] using hsquare.symm
  rw [denseEpsilon]
  calc
    (k : Real) / (8 * Real.sqrt T) * T =
        (k : Real) * ((T : Real) / Real.sqrt T) / 8 := by ring
    _ = (k : Real) * Real.sqrt T / 8 := by rw [hquot]

theorem denseEpsilon_horizon_div_four {k T : Nat} (hT : 1 ≤ T) :
    denseEpsilon k T * (T : Real) / 4 =
      (k : Real) * Real.sqrt T / 32 := by
  rw [denseEpsilon_mul_horizon hT]
  ring

theorem densePredictableCap_eq {k T : Nat} (hT : 1 ≤ T) :
    (T : Real) * (2 * denseEpsilon k T / 3) =
      (k : Real) * Real.sqrt T / 12 := by
  calc
    (T : Real) * (2 * denseEpsilon k T / 3) =
        (2 / 3 : Real) * (denseEpsilon k T * T) := by ring
    _ = (2 / 3 : Real) * ((k : Real) * Real.sqrt T / 8) := by
      rw [denseEpsilon_mul_horizon hT]
    _ = (k : Real) * Real.sqrt T / 12 := by ring

/-- Equation `eq:lower-dense-positive-mean`.  Its sole statistical input is
the expected-disagreement lower bound supplied by the preceding Assouad
block; the equality converting it to expected gap is proved above. -/
theorem lower_dense_positive_mean {n k T : Nat}
    (P : Policy n k) (hk : 1 ≤ k) (hD : 2 * k ≤ n) (hT : 1 ≤ T)
    (θ : Fin k → PairSign)
    (hε1 : denseEpsilon k T ≤ 1)
    (hdisagreement :
      3 * (k : Real) * (T : Real) / 4 ≤
        ∫ h, pairedTotalDisagreement hD θ T h
          ∂pairedJointLaw P hk hD θ (denseEpsilon k T)
            (denseEpsilon_nonneg k T) hε1 T) :
    (k : Real) * Real.sqrt T / 32 ≤
      ∫ h, pairedGap hD θ T h
        ∂pairedJointLaw P hk hD θ (denseEpsilon k T)
          (denseEpsilon_nonneg k T) hε1 T := by
  rw [integral_pairedGap_eq_disagreement]
  have hkreal : 0 < (k : Real) := by exact_mod_cast hk
  have hcoeff : 0 ≤ denseEpsilon k T / (3 * (k : Real)) :=
    div_nonneg (denseEpsilon_nonneg k T) (by positivity)
  calc
    (k : Real) * Real.sqrt T / 32 =
        denseEpsilon k T * (T : Real) / 4 :=
      (denseEpsilon_horizon_div_four hT).symm
    _ = denseEpsilon k T / (3 * (k : Real)) *
        (3 * (k : Real) * (T : Real) / 4) := by
      field_simp [ne_of_gt hkreal]
      <;> ring
    _ ≤ denseEpsilon k T / (3 * (k : Real)) *
        ∫ h, pairedTotalDisagreement hD θ T h
          ∂pairedJointLaw P hk hD θ (denseEpsilon k T)
            (denseEpsilon_nonneg k T) hε1 T :=
      mul_le_mul_of_nonneg_left hdisagreement hcoeff

theorem pairedPredictableMean_dense_mem_Icc {n k T : Nat}
    (P : Policy n k) (hk : 1 ≤ k) (hD : 2 * k ≤ n) (hT : 1 ≤ T)
    (θ : Fin k → PairSign) (hε1 : denseEpsilon k T ≤ 1)
    (h : PairedJointHistory n k T) :
    pairedPredictableMean P hk hD θ (denseEpsilon k T)
        (denseEpsilon_nonneg k T) hε1 T h ∈
      Set.Icc (0 : Real) ((k : Real) * Real.sqrt T / 12) := by
  have hbound := pairedPredictableMean_mem_Icc P hk hD θ
    (denseEpsilon_nonneg k T) hε1 T h
  rw [densePredictableCap_eq hT] at hbound
  exact hbound

/-- Equation `eq:lower-dense-second-moment`.  The estimate is derived from
`G_T=A_T+M_T`, the pointwise predictable cap `A_T≤k√T/12`, and the proved
martingale estimate `E[M_T²]≤T`; no moment bound is assumed. -/
theorem lower_dense_second_moment {n k T : Nat}
    (P : Policy n k) (hk : 1 ≤ k) (hD : 2 * k ≤ n) (hT : 1 ≤ T)
    (θ : Fin k → PairSign) (hε1 : denseEpsilon k T ≤ 1) :
    (∫ h, (pairedGap hD θ T h) ^ 2
      ∂pairedJointLaw P hk hD θ (denseEpsilon k T)
        (denseEpsilon_nonneg k T) hε1 T) ≤
      3 * (k : Real) ^ 2 * (T : Real) := by
  let ε := denseEpsilon k T
  let hε0 : 0 ≤ ε := denseEpsilon_nonneg k T
  let μ : Measure (PairedJointHistory n k T) :=
    pairedJointLaw P hk hD θ ε hε0 hε1 T
  let G : PairedJointHistory n k T → Real := pairedGap hD θ T
  let A : PairedJointHistory n k T → Real :=
    pairedPredictableMean P hk hD θ ε hε0 hε1 T
  let M : PairedJointHistory n k T → Real :=
    pairedMartingalePart P hk hD θ ε hε0 hε1 T
  let cap : Real := (k : Real) * Real.sqrt T / 12
  let hμprob : IsProbabilityMeasure μ := by
    dsimp [μ]
    exact pairedJointLaw_isProbabilityMeasure P hk hD θ ε hε0 hε1 T
  letI : IsProbabilityMeasure μ := hμprob
  let hfin : IsFiniteMeasure μ := by infer_instance
  have hGsq : Integrable (fun h => (G h) ^ 2) μ :=
    @integrable_of_fintype_domain
      (PairedJointHistory n k T)
      (pairedJointHistoryFintype n k T)
      (pairedJointHistoryMeasurableSpace n k T)
      (pairedJointHistoryMeasurableSingletonClass n k T)
      μ hfin _
  have hAsq : Integrable (fun h => (A h) ^ 2) μ :=
    @integrable_of_fintype_domain
      (PairedJointHistory n k T)
      (pairedJointHistoryFintype n k T)
      (pairedJointHistoryMeasurableSpace n k T)
      (pairedJointHistoryMeasurableSingletonClass n k T)
      μ hfin _
  have hMsq : Integrable (fun h => (M h) ^ 2) μ :=
    @integrable_of_fintype_domain
      (PairedJointHistory n k T)
      (pairedJointHistoryFintype n k T)
      (pairedJointHistoryMeasurableSpace n k T)
      (pairedJointHistoryMeasurableSingletonClass n k T)
      μ hfin _
  have hpoint (h : PairedJointHistory n k T) :
      (G h) ^ 2 ≤ 2 * (A h) ^ 2 + 2 * (M h) ^ 2 := by
    have hdecomp := pairedGap_eq_predictableMean_add_martingalePart
      P hk hD θ ε hε0 hε1 T h
    change G h = A h + M h at hdecomp
    rw [hdecomp]
    nlinarith [sq_nonneg (A h - M h)]
  have hAcap (h : PairedJointHistory n k T) :
      0 ≤ A h ∧ A h ≤ cap := by
    dsimp [A, cap, ε, hε0]
    exact pairedPredictableMean_dense_mem_Icc P hk hD hT θ hε1 h
  have hAsecond : (∫ h, (A h) ^ 2 ∂μ) ≤ cap ^ 2 := by
    calc
      (∫ h, (A h) ^ 2 ∂μ) ≤ ∫ _h, cap ^ 2 ∂μ := by
        apply integral_mono hAsq (integrable_const _)
        intro h
        rcases hAcap h with ⟨hA0, hAcap'⟩
        nlinarith [sq_nonneg (cap - A h)]
      _ = cap ^ 2 := by simp
  have hMsecond : (∫ h, (M h) ^ 2 ∂μ) ≤ (T : Real) := by
    simpa [M, μ, ε, hε0] using
      integral_pairedMartingalePart_sq_le_time
        P hk hD θ ε hε0 hε1 T
  have hsquare : (Real.sqrt (T : Real)) ^ 2 = (T : Real) :=
    Real.sq_sqrt (Nat.cast_nonneg T)
  have hcapSquare : cap ^ 2 =
      (k : Real) ^ 2 * (T : Real) / 144 := by
    dsimp [cap]
    calc
      ((k : Real) * Real.sqrt T / 12) ^ 2 =
          (k : Real) ^ 2 * (Real.sqrt T) ^ 2 / 144 := by ring
      _ = (k : Real) ^ 2 * (T : Real) / 144 := by rw [hsquare]
  have hkreal : (1 : Real) ≤ (k : Real) := by exact_mod_cast hk
  have hkSq : (1 : Real) ≤ (k : Real) ^ 2 := by nlinarith
  have hTnonneg : (0 : Real) ≤ T := Nat.cast_nonneg T
  have hTk : (T : Real) ≤ (k : Real) ^ 2 * T := by
    calc
      (T : Real) = 1 * T := by ring
      _ ≤ (k : Real) ^ 2 * T :=
        mul_le_mul_of_nonneg_right hkSq hTnonneg
  change (∫ h, (G h) ^ 2 ∂μ) ≤ _
  calc
    (∫ h, (G h) ^ 2 ∂μ) ≤
        ∫ h, (2 * (A h) ^ 2 + 2 * (M h) ^ 2) ∂μ := by
      apply integral_mono hGsq
      · exact (hAsq.const_mul 2).add (hMsq.const_mul 2)
      · exact hpoint
    _ = 2 * (∫ h, (A h) ^ 2 ∂μ) +
        2 * (∫ h, (M h) ^ 2 ∂μ) := by
      rw [integral_add (hAsq.const_mul 2) (hMsq.const_mul 2),
        integral_const_mul, integral_const_mul]
    _ ≤ 2 * cap ^ 2 + 2 * (T : Real) := by
      gcongr
    _ = 2 * ((k : Real) ^ 2 * (T : Real) / 144) +
        2 * (T : Real) := by rw [hcapSquare]
    _ ≤ 3 * (k : Real) ^ 2 * (T : Real) := by
      linarith

/-! ## Pathwise external regret on the latent history -/

/-- The learner's cumulative loss along a latent paired history. -/
def pairedLearnerCumulativeLoss {n k : Nat} (hD : 2 * k ≤ n) :
    (t : Nat) → PairedJointHistory n k t → Real
  | 0, _ => 0
  | t + 1, (h, (A, J)) =>
      pairedLearnerCumulativeLoss hD t h +
        actionLoss A (pairedLoss hD J)

/-- Cumulative loss of a fixed action on the same sampled loss sequence. -/
def pairedFixedCumulativeLoss {n k : Nat} (hD : 2 * k ≤ n) :
    (t : Nat) → PairedJointHistory n k t → MSetAction n k → Real
  | 0, _, _ => 0
  | t + 1, (h, (_A, J)), B =>
      pairedFixedCumulativeLoss hD t h B +
        actionLoss B (pairedLoss hD J)

/-- Best fixed-action loss in hindsight on a latent history. -/
def pairedBestCumulativeLoss {n k : Nat} (hD : 2 * k ≤ n)
    (t : Nat) (h : PairedJointHistory n k t) : Real :=
  sInf (Set.range (pairedFixedCumulativeLoss hD t h))

/-- The genuine external regret for the stochastic paired loss sequence. -/
def pairedExternalRegret {n k : Nat} (hD : 2 * k ≤ n)
    (t : Nat) (h : PairedJointHistory n k t) : Real :=
  pairedLearnerCumulativeLoss hD t h -
    pairedBestCumulativeLoss hD t h

theorem pairedGap_eq_learner_sub_fixed {n k : Nat} (hD : 2 * k ≤ n)
    (θ : Fin k → PairSign) : ∀ t (h : PairedJointHistory n k t),
    pairedGap hD θ t h =
      pairedLearnerCumulativeLoss hD t h -
        pairedFixedCumulativeLoss hD t h (pairedComparator hD θ) := by
  intro t
  induction t with
  | zero => intro h; simp [pairedGap, pairedLearnerCumulativeLoss,
      pairedFixedCumulativeLoss]
  | succ t ih =>
      rintro ⟨h, A, J⟩
      simp only [pairedGap, pairedGapIncrement,
        pairedLearnerCumulativeLoss, pairedFixedCumulativeLoss]
      rw [ih h]
      ring

/-- The manuscript's pathwise comparison `R_T ≥ G_T^θ`. -/
theorem pairedGap_le_externalRegret {n k : Nat} (hD : 2 * k ≤ n)
    (θ : Fin k → PairSign) (t : Nat) (h : PairedJointHistory n k t) :
    pairedGap hD θ t h ≤ pairedExternalRegret hD t h := by
  rw [pairedGap_eq_learner_sub_fixed]
  unfold pairedExternalRegret pairedBestCumulativeLoss
  apply sub_le_sub_left
  have hbelow : BddBelow
      (Set.range (pairedFixedCumulativeLoss hD t h)) :=
    Finite.bddBelow_range _
  exact csInf_le hbelow ⟨pairedComparator hD θ, rfl⟩

/-! ## Positive-probability event -/

/-- Paley--Zygmund applied to the actual adaptive joint law, before the
pathwise enlargement from fixed-comparator gap to external regret. -/
theorem lower_dense_gap_positive_event {n k T : Nat}
    (P : Policy n k) (hk : 1 ≤ k) (hD : 2 * k ≤ n) (hT : 1 ≤ T)
    (θ : Fin k → PairSign) (hε1 : denseEpsilon k T ≤ 1)
    (hdisagreement :
      3 * (k : Real) * (T : Real) / 4 ≤
        ∫ h, pairedTotalDisagreement hD θ T h
          ∂pairedJointLaw P hk hD θ (denseEpsilon k T)
            (denseEpsilon_nonneg k T) hε1 T) :
    (1 : Real) / 12288 ≤
      (pairedJointLaw P hk hD θ (denseEpsilon k T)
        (denseEpsilon_nonneg k T) hε1 T).real
        {h | (k : Real) * Real.sqrt T / 64 ≤ pairedGap hD θ T h} := by
  let ε := denseEpsilon k T
  let hε0 : 0 ≤ ε := denseEpsilon_nonneg k T
  let μ : Measure (PairedJointHistory n k T) :=
    pairedJointLaw P hk hD θ ε hε0 hε1 T
  let G : PairedJointHistory n k T → Real := pairedGap hD θ T
  let mean : Real := ∫ h, G h ∂μ
  let second : Real := ∫ h, (G h) ^ 2 ∂μ
  let targetMean : Real := (k : Real) * Real.sqrt T / 32
  let hμprob : IsProbabilityMeasure μ := by
    dsimp [μ]
    exact pairedJointLaw_isProbabilityMeasure P hk hD θ ε hε0 hε1 T
  letI : IsProbabilityMeasure μ := hμprob
  let hfin : IsFiniteMeasure μ := by infer_instance
  have hGmeas : Measurable G := measurable_of_finite _
  have hGsq : Integrable (fun h => (G h) ^ 2) μ :=
    @integrable_of_fintype_domain
      (PairedJointHistory n k T)
      (pairedJointHistoryFintype n k T)
      (pairedJointHistoryMeasurableSpace n k T)
      (pairedJointHistoryMeasurableSingletonClass n k T)
      μ hfin _
  have hmean : targetMean ≤ mean := by
    dsimp [targetMean, mean, G, μ, ε, hε0]
    exact lower_dense_positive_mean P hk hD hT θ hε1 hdisagreement
  have hsecond : second ≤
      3 * (k : Real) ^ 2 * (T : Real) := by
    dsimp [second, G, μ, ε, hε0]
    exact lower_dense_second_moment P hk hD hT θ hε1
  have hkreal : 0 < (k : Real) := by exact_mod_cast hk
  have hsqrt_pos : 0 < Real.sqrt (T : Real) :=
    Real.sqrt_pos.2 (by exact_mod_cast hT)
  have htarget_pos : 0 < targetMean := by
    dsimp [targetMean]
    positivity
  have hmean_pos : 0 < mean := htarget_pos.trans_le hmean
  have hGL2 : MemLp G 2 μ := by
    rw [memLp_two_iff_integrable_sq hGmeas.aestronglyMeasurable]
    exact hGsq
  have hvariance : 0 ≤ second - mean ^ 2 := by
    have hv := variance_nonneg G μ
    have hvEq : variance G μ =
        (∫ h, (G h) ^ 2 ∂μ) - (∫ h, G h ∂μ) ^ 2 :=
      @variance_eq_sub
        (PairedJointHistory n k T)
        (pairedJointHistoryMeasurableSpace n k T)
        μ hμprob G hGL2
    rw [hvEq] at hv
    simpa [second, mean] using hv
  have hsecond_pos : 0 < second := by
    have hmeansq_pos : 0 < mean ^ 2 := sq_pos_of_pos hmean_pos
    linarith
  have hPZ : mean ^ 2 / (4 * second) ≤
      μ.real {h | mean / 2 ≤ G h} := by
    simpa [mean, second] using
      @MsetsLower.Probability.probability_ge_half_mean_of_second_moment
        (PairedJointHistory n k T)
        (pairedJointHistoryMeasurableSpace n k T)
        μ hμprob G hGmeas hGsq hmean_pos
  have hsquare : (Real.sqrt (T : Real)) ^ 2 = (T : Real) :=
    Real.sq_sqrt (Nat.cast_nonneg T)
  have htargetSquare : targetMean ^ 2 =
      (k : Real) ^ 2 * (T : Real) / 1024 := by
    dsimp [targetMean]
    calc
      ((k : Real) * Real.sqrt T / 32) ^ 2 =
          (k : Real) ^ 2 * (Real.sqrt T) ^ 2 / 1024 := by ring
      _ = (k : Real) ^ 2 * (T : Real) / 1024 := by rw [hsquare]
  have htargetSquare_le : targetMean ^ 2 ≤ mean ^ 2 := by
    have hprod := mul_nonneg (sub_nonneg.mpr hmean)
      (add_nonneg (le_of_lt hmean_pos) (le_of_lt htarget_pos))
    nlinarith
  have hratio : (1 : Real) / 12288 ≤ mean ^ 2 / (4 * second) := by
    apply (le_div_iff₀ (mul_pos (by norm_num) hsecond_pos)).2
    calc
      (1 : Real) / 12288 * (4 * second) ≤
          (1 : Real) / 12288 *
            (4 * (3 * (k : Real) ^ 2 * (T : Real))) := by
        gcongr
      _ = targetMean ^ 2 := by
        rw [htargetSquare]
        ring
      _ ≤ mean ^ 2 := htargetSquare_le
  have hsubset : {h | mean / 2 ≤ G h} ⊆
      {h | (k : Real) * Real.sqrt T / 64 ≤ G h} := by
    intro h hh
    have hthreshold : (k : Real) * Real.sqrt T / 64 ≤ mean / 2 := by
      calc
        (k : Real) * Real.sqrt T / 64 = targetMean / 2 := by
          dsimp [targetMean]
          ring
        _ ≤ mean / 2 := by linarith
    exact hthreshold.trans hh
  change (1 : Real) / 12288 ≤
    μ.real {h | (k : Real) * Real.sqrt T / 64 ≤ G h}
  exact hratio.trans (hPZ.trans (measureReal_mono hsubset))

/-- Equation `eq:lower-dense-positive-event`: the event is stated for the
genuine external regret, with the exact manuscript constant `1/12288`. -/
theorem lower_dense_positive_event {n k T : Nat}
    (P : Policy n k) (hk : 1 ≤ k) (hD : 2 * k ≤ n) (hT : 1 ≤ T)
    (θ : Fin k → PairSign) (hε1 : denseEpsilon k T ≤ 1)
    (hdisagreement :
      3 * (k : Real) * (T : Real) / 4 ≤
        ∫ h, pairedTotalDisagreement hD θ T h
          ∂pairedJointLaw P hk hD θ (denseEpsilon k T)
            (denseEpsilon_nonneg k T) hε1 T) :
    (1 : Real) / 12288 ≤
      (pairedJointLaw P hk hD θ (denseEpsilon k T)
        (denseEpsilon_nonneg k T) hε1 T).real
        {h | (k : Real) * Real.sqrt T / 64 ≤
          pairedExternalRegret hD T h} := by
  letI : IsProbabilityMeasure
      (pairedJointLaw P hk hD θ (denseEpsilon k T)
        (denseEpsilon_nonneg k T) hε1 T) :=
    pairedJointLaw_isProbabilityMeasure P hk hD θ (denseEpsilon k T)
      (denseEpsilon_nonneg k T) hε1 T
  calc
    (1 : Real) / 12288 ≤
        (pairedJointLaw P hk hD θ (denseEpsilon k T)
          (denseEpsilon_nonneg k T) hε1 T).real
          {h | (k : Real) * Real.sqrt T / 64 ≤ pairedGap hD θ T h} :=
      lower_dense_gap_positive_event P hk hD hT θ hε1 hdisagreement
    _ ≤ (pairedJointLaw P hk hD θ (denseEpsilon k T)
          (denseEpsilon_nonneg k T) hε1 T).real
          {h | (k : Real) * Real.sqrt T / 64 ≤
            pairedExternalRegret hD T h} := by
      apply measureReal_mono
      intro h hh
      exact hh.trans (pairedGap_le_externalRegret hD θ T h)
      exact measure_ne_top _ _

theorem one_div_12288_gt_two_zpow_neg_fourteen :
    (2 : Real) ^ (-14 : Int) < (1 : Real) / 12288 := by
  norm_num [zpow_neg]

theorem lower_dense_positive_event_gt_two_zpow_neg_fourteen {n k T : Nat}
    (P : Policy n k) (hk : 1 ≤ k) (hD : 2 * k ≤ n) (hT : 1 ≤ T)
    (θ : Fin k → PairSign) (hε1 : denseEpsilon k T ≤ 1)
    (hdisagreement :
      3 * (k : Real) * (T : Real) / 4 ≤
        ∫ h, pairedTotalDisagreement hD θ T h
          ∂pairedJointLaw P hk hD θ (denseEpsilon k T)
            (denseEpsilon_nonneg k T) hε1 T) :
    (2 : Real) ^ (-14 : Int) <
      (pairedJointLaw P hk hD θ (denseEpsilon k T)
        (denseEpsilon_nonneg k T) hε1 T).real
        {h | (k : Real) * Real.sqrt T / 64 ≤
          pairedExternalRegret hD T h} :=
  one_div_12288_gt_two_zpow_neg_fourteen.trans_le
    (lower_dense_positive_event P hk hD hT θ hε1 hdisagreement)

/-- Canonical `ε≤1` proof obtained from the manuscript's stronger
`ε≤1/16` parameter regime. -/
theorem denseEpsilon_le_one_paper_regime {n k T : Nat}
    (hk : 1 ≤ k) (hk_half : k ≤ n / 2) (horizon : n ^ 2 ≤ T) :
    denseEpsilon k T ≤ 1 :=
  (denseEpsilon_le_sixteenth hk hk_half horizon).trans (by norm_num)

/-- Paper-regime wrapper for the whole moment/tail block.  This version makes
the manuscript's `ε≤1/16` provenance explicit rather than accepting the
weaker support condition used by the internal lemmas. -/
theorem lower_dense_moment_block_paper_regime {n k T : Nat}
    (P : Policy n k) (hk : 1 ≤ k) (hD : 2 * k ≤ n) (hT : 1 ≤ T)
    (hk_half : k ≤ n / 2) (horizon : n ^ 2 ≤ T)
    (θ : Fin k → PairSign)
    (hdisagreement :
      3 * (k : Real) * (T : Real) / 4 ≤
        ∫ h, pairedTotalDisagreement hD θ T h
          ∂pairedJointLaw P hk hD θ (denseEpsilon k T)
            (denseEpsilon_nonneg k T)
            (denseEpsilon_le_one_paper_regime hk hk_half horizon) T) :
    ((k : Real) * Real.sqrt T / 32 ≤
        ∫ h, pairedGap hD θ T h
          ∂pairedJointLaw P hk hD θ (denseEpsilon k T)
            (denseEpsilon_nonneg k T)
            (denseEpsilon_le_one_paper_regime hk hk_half horizon) T) ∧
      ((∫ h, (pairedGap hD θ T h) ^ 2
          ∂pairedJointLaw P hk hD θ (denseEpsilon k T)
            (denseEpsilon_nonneg k T)
            (denseEpsilon_le_one_paper_regime hk hk_half horizon) T) ≤
        3 * (k : Real) ^ 2 * (T : Real)) ∧
      ((1 : Real) / 12288 ≤
        (pairedJointLaw P hk hD θ (denseEpsilon k T)
          (denseEpsilon_nonneg k T)
          (denseEpsilon_le_one_paper_regime hk hk_half horizon) T).real
          {h | (k : Real) * Real.sqrt T / 64 ≤
            pairedExternalRegret hD T h}) := by
  let hε1 := denseEpsilon_le_one_paper_regime hk hk_half horizon
  exact ⟨lower_dense_positive_mean P hk hD hT θ hε1 hdisagreement,
    lower_dense_second_moment P hk hD hT θ hε1,
    lower_dense_positive_event P hk hD hT θ hε1 hdisagreement⟩

end

end MsetsLower.Lower.Dense

#print axioms MsetsLower.Lower.Dense.pairedMartingalePart_kernel_martingale
#print axioms MsetsLower.Lower.Dense.integral_centeredGap_sq_roundKernel_le_one
#print axioms MsetsLower.Lower.Dense.integral_pairedMartingalePart_sq_le_time
#print axioms MsetsLower.Lower.Dense.integral_pairedGap_eq_disagreement
#print axioms MsetsLower.Lower.Dense.lower_dense_positive_mean
#print axioms MsetsLower.Lower.Dense.lower_dense_second_moment
#print axioms MsetsLower.Lower.Dense.pairedGap_le_externalRegret
#print axioms MsetsLower.Lower.Dense.lower_dense_positive_event
#print axioms MsetsLower.Lower.Dense.lower_dense_moment_block_paper_regime
