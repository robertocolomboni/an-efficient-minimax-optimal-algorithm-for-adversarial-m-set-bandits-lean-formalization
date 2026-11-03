import MsetsPaper.Probability.ExecutionMeasure
import MsetsLower.Core.Protocol

/-! # Finite action-tree semantics for every observable policy

Unlike the exponential-weight specialization, this bridge allows arbitrary
history-dependent action kernels, including zero action probabilities.
-/

noncomputable section
open scoped BigOperators ENNReal
open MeasureTheory ProbabilityTheory MsetsLower MsetsLower.History

namespace MsetsPaper.Probability.PolicyActionTree

variable {d m : ℕ}

def historyOfActions (L : LossProcess d m) :
    (t : ℕ) → ActionTree (MSetAction d m) t → History d m t
  | 0, _ => ()
  | t + 1, (h, a) => (historyOfActions L t h).snoc a
      (actionLoss a (L.itemLoss t (historyOfActions L t h)))

def actionsOfHistory : (t : ℕ) → History d m t → ActionTree (MSetAction d m) t
  | 0, _ => ()
  | t + 1, (h, (a, _)) => (actionsOfHistory t h, a)

theorem actionsOfHistory_historyOfActions (L : LossProcess d m) :
    ∀ t h, actionsOfHistory t (historyOfActions L t h) = h := by
  intro t
  induction t with
  | zero => intro h; cases h; rfl
  | succ t ih =>
    rintro ⟨h, a⟩
    change (actionsOfHistory t (historyOfActions L t h), a) = (h, a)
    rw [ih]

theorem historyOfActions_injective (L : LossProcess d m) (t : ℕ) :
    Function.Injective (historyOfActions L t) :=
  Function.LeftInverse.injective (actionsOfHistory_historyOfActions L t)

theorem finite_measure_eq_atomic {α : Type*} [Fintype α]
    [MeasurableSpace α] [MeasurableSingletonClass α]
    (μ : Measure α) [IsFiniteMeasure μ] :
    μ = finiteAtomicMeasure (fun a => μ.real {a}) id := by
  classical
  symm
  simpa only [finiteAtomicMeasure, measureReal_def,
    ENNReal.ofReal_toReal (measure_ne_top _ _), id_eq, Measure.sum_fintype] using
    μ.sum_smul_dirac

theorem sum_action_probability (P : Policy d m) (t : ℕ) (h : History d m t) :
    ∑ a, (P.kernel t h).real {a} = 1 := by
  simpa using sum_measureReal_singleton (μ := P.kernel t h) Finset.univ

def branchingLaw (P : Policy d m) (L : LossProcess d m) : BranchingLaw (MSetAction d m) where
  next t h a := (P.kernel t (historyOfActions L t h)).real {a}
  nonneg _ _ _ := measureReal_nonneg
  sum_one t h := sum_action_probability P t (historyOfActions L t h)

theorem roundKernel_eq_finiteAtomicMeasure (P : Policy d m) (L : LossProcess d m)
    (t : ℕ) (h : History d m t) :
    roundKernel P L t h = finiteAtomicMeasure (fun a => (P.kernel t h).real {a})
      (fun a => h.snoc a (actionLoss a (L.itemLoss t h))) := by
  classical
  ext s hs
  rw [roundKernel_apply _ _ _ _ hs]
  conv_lhs => rw [finite_measure_eq_atomic (P.kernel t h)]
  rw [finiteAtomicMeasure_apply _ _ _ MeasurableSet.of_discrete,
    finiteAtomicMeasure_apply _ _ _ hs]
  rfl

/-- The complete law, derived by the finite tower identity. -/
theorem runLaw_eq_finiteAtomicMeasure (P : Policy d m) (L : LossProcess d m) (T : ℕ) :
    runLaw P L T = finiteAtomicMeasure ((branchingLaw P L).mass T) (historyOfActions L T) := by
  classical
  let W := branchingLaw P L
  change runLaw P L T = finiteAtomicMeasure (W.mass T) (historyOfActions L T)
  induction T with
  | zero =>
    change Measure.dirac (() : Unit) = ∑ _h : Unit, ENNReal.ofReal 1 • Measure.dirac ()
    rw [Fintype.sum_unique]
    simp
  | succ t ih =>
    ext s hs
    rw [runLaw_succ_apply _ _ _ hs, ih, lintegral_finiteAtomicMeasure,
      finiteAtomicMeasure_apply _ _ _ hs]
    have hround (h : ActionTree (MSetAction d m) t) :
        roundKernel P L t (historyOfActions L t h) s =
          ∑ a, ENNReal.ofReal ((P.kernel t (historyOfActions L t h)).real {a}) *
            (if (historyOfActions L t h).snoc a
              (actionLoss a (L.itemLoss t (historyOfActions L t h))) ∈ s then 1 else 0) := by
      have heq := congrArg (fun μ : Measure (History d m (t + 1)) => μ s)
        (roundKernel_eq_finiteAtomicMeasure P L t (historyOfActions L t h))
      exact heq.trans (finiteAtomicMeasure_apply _ _ _ hs)
    simp_rw [hround]
    change (∑ h : ActionTree (MSetAction d m) t, ENNReal.ofReal (W.mass t h) *
      ∑ a, ENNReal.ofReal ((P.kernel t (historyOfActions L t h)).real {a}) *
        (if (historyOfActions L t h).snoc a
          (actionLoss a (L.itemLoss t (historyOfActions L t h))) ∈ s then 1 else 0)) =
      ∑ ha : ActionTree (MSetAction d m) t × MSetAction d m,
        ENNReal.ofReal (W.mass t ha.1 * W.next t ha.1 ha.2) *
          (if historyOfActions L (t + 1) ha ∈ s then 1 else 0)
    rw [Fintype.sum_prod_type]
    apply Finset.sum_congr rfl
    intro h _
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro a _
    rw [ENNReal.ofReal_mul (W.mass_nonneg t h)]
    exact (mul_assoc _ _ _).symm

theorem runLaw_real_eq_tree (P : Policy d m) (L : LossProcess d m) (T : ℕ)
    (E : Set (History d m T)) :
    (runLaw P L T).real E = (branchingLaw P L).probability T
      {h | historyOfActions L T h ∈ E} := by
  rw [runLaw_eq_finiteAtomicMeasure,
    finiteAtomicMeasure_real_apply_of_singletons _ ((branchingLaw P L).mass_nonneg T)]
  rfl

end MsetsPaper.Probability.PolicyActionTree
