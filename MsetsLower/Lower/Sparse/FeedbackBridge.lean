import MsetsLower.Lower.Dense.Bridge
import MsetsLower.Lower.Sparse.Likelihood

/-!
# Affine feedback bridge for the sparse experiment

The likelihood calculation is naturally written for the centered observation
`F_u(Z)`, whereas the protocol observes the normalized action loss
`1/2 + F_u(Z)`.  This file records the measurable affine equivalence between
the two histories and transports an arbitrary policy across it.  It prevents
the common but invalid identification of those two policy inputs.
-/

set_option linter.style.header false

namespace MsetsLower.Lower.Sparse

open MsetsLower MeasureTheory ProbabilityTheory

noncomputable section

def sparseFeedbackShiftEquiv : Real ≃ᵐ Real where
  toEquiv :=
    { toFun := fun y => (1 : Real) / 2 + y
      invFun := fun y => y - (1 : Real) / 2
      left_inv := by intro y; ring
      right_inv := by intro y; ring }
  measurable_toFun := measurable_const.add measurable_id
  measurable_invFun := measurable_id.sub measurable_const

def sparseObservationShiftEquiv (d m : Nat) :
    (MSetAction d m × Real) ≃ᵐ (MSetAction d m × Real) :=
  MeasurableEquiv.prodCongr (MeasurableEquiv.refl (MSetAction d m))
    sparseFeedbackShiftEquiv

/-- Convert a centered history to the actual protocol history. -/
def sparseActualHistoryEquiv (d m : Nat) :
    (t : Nat) → History d m t ≃ᵐ History d m t
  | 0 => MeasurableEquiv.refl Unit
  | t + 1 => MeasurableEquiv.prodCongr
      (sparseActualHistoryEquiv d m t)
      (MeasurableEquiv.prodCongr (MeasurableEquiv.refl (MSetAction d m))
        sparseFeedbackShiftEquiv)

@[simp] theorem sparseActualHistoryEquiv_zero
    {d m : Nat} (h : History d m 0) :
    sparseActualHistoryEquiv d m 0 h = h := by
  rfl

@[simp] theorem sparseActualHistoryEquiv_succ
    {d m t : Nat} (h : History d m t)
    (A : MSetAction d m) (y : Real) :
    sparseActualHistoryEquiv d m (t + 1) (h, (A, y)) =
      (sparseActualHistoryEquiv d m t h, (A, (1 : Real) / 2 + y)) := by
  rfl

@[simp] theorem sparseActualHistoryEquiv_symm_succ
    {d m t : Nat} (h : History d m t)
    (A : MSetAction d m) (y : Real) :
    (sparseActualHistoryEquiv d m (t + 1)).symm (h, (A, y)) =
      ((sparseActualHistoryEquiv d m t).symm h,
        (A, y - (1 : Real) / 2)) := by
  rfl

/-- An arbitrary actual-feedback policy viewed on centered histories. -/
def sparseCenteredPolicy {d m : Nat} (P : Policy d m) : Policy d m where
  kernel t := (P.kernel t).comap
    (sparseActualHistoryEquiv d m t)
    (sparseActualHistoryEquiv d m t).measurable
  isMarkov t := by infer_instance

theorem sparseCenteredPolicy_kernel
    {d m : Nat} (P : Policy d m) (t : Nat)
    (h : History d m t) :
    (sparseCenteredPolicy P).kernel t h =
      P.kernel t (sparseActualHistoryEquiv d m t h) := by
  rw [sparseCenteredPolicy, Kernel.comap_apply]

/-- Forgetting scalar feedback commutes with the affine history bridge. -/
theorem sparseBlockSelectedCount_actualHistory
    {n k q : Nat} (i : Fin n) :
    ∀ t (h : History n k t),
      sparseBlockSelectedCount q i t
          (sparseActualHistoryEquiv n k t h) =
        sparseBlockSelectedCount q i t h := by
  intro t
  induction t with
  | zero => intro h; rfl
  | succ t ih =>
      intro history
      rcases history with ⟨h, A, y⟩
      rw [sparseActualHistoryEquiv_succ h A y]
      simp only [sparseBlockSelectedCount_succ]
      split_ifs
      · rw [ih]
      · rfl

theorem sparseActive_actualHistory
    {n k q c0 t : Nat} (i : Fin n) (h : History n k t) :
    sparseActive q c0 i t (sparseActualHistoryEquiv n k t h) =
      sparseActive q c0 i t h := by
  unfold sparseActive
  rw [sparseBlockSelectedCount_actualHistory]

theorem sparseActionScore_actualHistory
    {n k n' q c0 t : Nat} (U : Nat → Fin n → Real)
    (h : History n k t) (A : MSetAction n k) :
    sparseActionScore n' q c0 U t
        (sparseActualHistoryEquiv n k t h) A =
      sparseActionScore n' q c0 U t h A := by
  unfold sparseActionScore
  rw [actionLoss_eq_finset_sum, actionLoss_eq_finset_sum]
  apply Finset.sum_congr rfl
  intro i hi
  rw [sparseActive_actualHistory i h]

theorem sparseFeedbackParameter_actualHistory
    {n k n' q c0 t : Nat} (eta : Real) (U : Nat → Fin n → Real)
    (h : History n k t) (A : MSetAction n k) :
    sparseFeedbackParameter eta n' q c0 U t
        (sparseActualHistoryEquiv n k t h) A =
      sparseFeedbackParameter eta n' q c0 U t h A := by
  unfold sparseFeedbackParameter
  rw [sparseActionScore_actualHistory]

/-- The actual-history kernel obtained from a centered adaptive experiment. -/
def sparseActualAdaptiveRoundKernel
    {n k : Nat} (P : Policy n k) (V : SparseAdaptiveParameters n k)
    (t : Nat) : Kernel (History n k t) (MSetAction n k × Real) :=
  ((sparseAdaptiveRoundKernel (sparseCenteredPolicy P) V t).comap
      (sparseActualHistoryEquiv n k t).symm
      (sparseActualHistoryEquiv n k t).symm.measurable).map
    (sparseObservationShiftEquiv n k)

instance sparseActualAdaptiveRoundKernel.instIsMarkovKernel
    {n k : Nat} (P : Policy n k) (V : SparseAdaptiveParameters n k)
    (t : Nat) : IsMarkovKernel (sparseActualAdaptiveRoundKernel P V t) := by
  unfold sparseActualAdaptiveRoundKernel
  letI : IsMarkovKernel
      (sparseAdaptiveRoundKernel (sparseCenteredPolicy P) V t) :=
    sparseAdaptiveRoundKernel_isMarkov (sparseCenteredPolicy P) V t
  letI : IsMarkovKernel
      ((sparseAdaptiveRoundKernel (sparseCenteredPolicy P) V t).comap
        (sparseActualHistoryEquiv n k t).symm
        (sparseActualHistoryEquiv n k t).symm.measurable) := by
    infer_instance
  exact Kernel.IsMarkovKernel.map _
    (sparseObservationShiftEquiv n k).measurable

def sparseActualAdaptiveProcess
    {n k : Nat} (P : Policy n k) (V : SparseAdaptiveParameters n k) :
    HistoryKernelProcess n k where
  kernel t := sparseActualAdaptiveRoundKernel P V t
  isMarkov t :=
    sparseActualAdaptiveRoundKernel.instIsMarkovKernel P V t

theorem sparseActualAdaptiveRoundKernel_at_actualHistory
    {n k : Nat} (P : Policy n k) (V : SparseAdaptiveParameters n k)
    (t : Nat) (h : History n k t) :
    sparseActualAdaptiveRoundKernel P V t
        (sparseActualHistoryEquiv n k t h) =
      (sparseAdaptiveRoundKernel (sparseCenteredPolicy P) V t h).map
        (sparseObservationShiftEquiv n k) := by
  unfold sparseActualAdaptiveRoundKernel
  rw [Kernel.map_apply _ (sparseObservationShiftEquiv n k).measurable,
    Kernel.comap_apply]
  simp

theorem sparseAdaptiveRoundKernel_map_actualHistory
    {n k : Nat} (P : Policy n k) (V : SparseAdaptiveParameters n k)
    (t : Nat) :
    ((sparseAdaptiveProcess (sparseCenteredPolicy P) V).kernel t).map
        (sparseObservationShiftEquiv n k) =
      Kernel.comap ((sparseActualAdaptiveProcess P V).kernel t)
        (sparseActualHistoryEquiv n k t)
        (sparseActualHistoryEquiv n k t).measurable := by
  ext h s hs
  change (((sparseAdaptiveRoundKernel (sparseCenteredPolicy P) V t).map
      (sparseObservationShiftEquiv n k)) h) s =
    (((sparseActualAdaptiveRoundKernel P V t).comap
      (sparseActualHistoryEquiv n k t)
      (sparseActualHistoryEquiv n k t).measurable) h) s
  rw [Kernel.map_apply _ (sparseObservationShiftEquiv n k).measurable,
    Kernel.comap_apply]
  have hm := congrArg (fun mu : Measure (MSetAction n k × Real) => mu s)
    (sparseActualAdaptiveRoundKernel_at_actualHistory P V t h).symm
  exact hm

/-- The centered process pushed through `y ↦ 1/2+y` is exactly the actual
history process. -/
theorem sparseActualHistory_map_adaptiveLaw
    {n k : Nat} (P : Policy n k) (V : SparseAdaptiveParameters n k) :
    ∀ t : Nat,
      ((sparseAdaptiveProcess (sparseCenteredPolicy P) V).law t).map
          (sparseActualHistoryEquiv n k t) =
        (sparseActualAdaptiveProcess P V).law t := by
  intro t
  induction t with
  | zero => simp [HistoryKernelProcess.law]
  | succ t ih =>
      let mu : Measure (History n k t) :=
        (sparseAdaptiveProcess (sparseCenteredPolicy P) V).law t
      let nu : Measure (History n k t) :=
        (sparseActualAdaptiveProcess P V).law t
      let kappa : Kernel (History n k t) (MSetAction n k × Real) :=
        (sparseAdaptiveProcess (sparseCenteredPolicy P) V).kernel t
      let eta : Kernel (History n k t) (MSetAction n k × Real) :=
        (sparseActualAdaptiveProcess P V).kernel t
      letI : SFinite mu := by infer_instance
      letI : SFinite nu := by infer_instance
      letI : IsSFiniteKernel kappa := by
        dsimp [kappa]
        infer_instance
      letI : IsSFiniteKernel eta := by
        dsimp [eta]
        infer_instance
      have hfun : sparseActualHistoryEquiv n k (t + 1) =
          MeasurableEquiv.prodCongr (sparseActualHistoryEquiv n k t)
            (sparseObservationShiftEquiv n k) := rfl
      change (mu ⊗ₘ kappa).map (sparseActualHistoryEquiv n k (t + 1)) =
        nu ⊗ₘ eta
      rw [hfun]
      exact @MsetsLower.Lower.Dense.map_compProd_of_map_apply
        (History n k t) (History n k t)
        (MSetAction n k × Real) (MSetAction n k × Real)
        (inferInstanceAs (MeasurableSpace (History n k t)))
        (inferInstanceAs (MeasurableSpace (History n k t)))
        (inferInstanceAs (MeasurableSpace (MSetAction n k × Real)))
        (inferInstanceAs (MeasurableSpace (MSetAction n k × Real)))
        mu nu kappa eta (by infer_instance) (by infer_instance)
        (by infer_instance) (by infer_instance)
        (sparseActualHistoryEquiv n k t)
        (sparseObservationShiftEquiv n k)
        (sparseActualHistoryEquiv n k t).measurable
        (sparseObservationShiftEquiv n k).measurable
        (by simpa [mu, nu] using ih)
        (fun h => by
          simpa only [kappa, eta, sparseAdaptiveProcess,
            sparseActualAdaptiveProcess] using
            (sparseActualAdaptiveRoundKernel_at_actualHistory P V t h).symm)

#print axioms sparseCenteredPolicy_kernel
#print axioms sparseFeedbackParameter_actualHistory
#print axioms sparseActualHistory_map_adaptiveLaw

end

end MsetsLower.Lower.Sparse
