import MsetsPaper.Probability.ExecutionMeasure
import MsetsPaper.Upper.AdaptiveLeverage

/-!
# Observable execution of the signed upper-bound experiment

Losses are normalized at action level by `|actionLoss| ≤ 1`.  The loss vector
and the exponential-law parameter depend only on the preceding observable
history.  This file proves, rather than assumes, the equality between the
Markov-kernel run law and the explicit finite action-tree experiment.
-/

noncomputable section

open scoped BigOperators ENNReal ProbabilityTheory
open MeasureTheory ProbabilityTheory
open MsetsLower MsetsLower.History MsetsPaper.Probability

namespace MsetsPaper.Upper

variable {d m : ℕ}

/-- Deterministic adaptive non-anticipating signed losses.  No coordinatewise
normalization is imposed: exactly the aggregate losses lie in `[-1,1]`. -/
structure SignedLossProcess (d m : ℕ) where
  itemLoss : (t : ℕ) → History d m t → Fin d → ℝ
  measurable_itemLoss : ∀ t, Measurable (itemLoss t)
  action_abs_le_one : ∀ t h (a : Action d m), |actionLoss a (itemLoss t h)| ≤ 1

def signedExtendRun (L : SignedLossProcess d m) (t : ℕ) :
    History d m t × Action d m → History d m (t + 1)
  | (h, a) => h.snoc a (actionLoss a (L.itemLoss t h))

theorem measurable_signedExtendRun (L : SignedLossProcess d m) (t : ℕ) :
    Measurable (signedExtendRun L t) := by
  change Measurable (fun p : History d m t × Action d m ↦
    (p.1, (p.2, actionLoss p.2 (L.itemLoss t p.1))))
  exact measurable_fst.prodMk
    (measurable_snd.prodMk (measurable_actionLoss_joint (L.measurable_itemLoss t)))

def signedRoundKernel (P : Policy d m) (L : SignedLossProcess d m) (t : ℕ) :
    Kernel (History d m t) (History d m (t + 1)) :=
  Kernel.map (actionHistoryKernel P t) (signedExtendRun L t)

instance signedRoundKernel.instIsMarkovKernel
    (P : Policy d m) (L : SignedLossProcess d m) (t : ℕ) :
    IsMarkovKernel (signedRoundKernel P L t) := by
  unfold signedRoundKernel
  exact Kernel.IsMarkovKernel.map _ (measurable_signedExtendRun L t)

theorem signedRoundKernel_apply (P : Policy d m) (L : SignedLossProcess d m)
    (t : ℕ) (h : History d m t) {s : Set (History d m (t + 1))}
    (hs : MeasurableSet s) :
    signedRoundKernel P L t h s =
      P.kernel t h {a | h.snoc a (actionLoss a (L.itemLoss t h)) ∈ s} := by
  rw [signedRoundKernel, Kernel.map_apply' _ (measurable_signedExtendRun L t) h hs,
    actionHistoryKernel_apply]
  rw [Measure.map_apply measurable_prodMk_left ((measurable_signedExtendRun L t) hs)]
  rfl

@[reducible] def signedRunLaw (P : Policy d m) (L : SignedLossProcess d m) :
    (t : ℕ) → Measure (History d m t)
  | 0 => Measure.dirac ()
  | t + 1 => signedRoundKernel P L t ∘ₘ signedRunLaw P L t

theorem signedRunLaw_isProbabilityMeasure (P : Policy d m) (L : SignedLossProcess d m) :
    ∀ t, IsProbabilityMeasure (signedRunLaw P L t) := by
  intro t
  induction t with
  | zero => exact Measure.dirac.isProbabilityMeasure
  | succ t ih =>
    letI := ih
    change IsProbabilityMeasure (signedRoundKernel P L t ∘ₘ signedRunLaw P L t)
    infer_instance

instance signedRunLaw.instIsProbabilityMeasure
    (P : Policy d m) (L : SignedLossProcess d m) (t : ℕ) :
    IsProbabilityMeasure (signedRunLaw P L t) := signedRunLaw_isProbabilityMeasure P L t

theorem signedRunLaw_succ_apply (P : Policy d m) (L : SignedLossProcess d m) (t : ℕ)
    {s : Set (History d m (t + 1))} (hs : MeasurableSet s) :
    signedRunLaw P L (t + 1) s =
      ∫⁻ h, signedRoundKernel P L t h s ∂signedRunLaw P L t := by
  change (signedRunLaw P L t).bind (signedRoundKernel P L t) s = _
  exact Measure.bind_apply hs (Kernel.aemeasurable _)

theorem measurable_partition {Ω : Type*} [MeasurableSpace Ω]
    (theta : Ω → Fin d → ℝ) (htheta : Measurable theta) :
    Measurable (fun h => partition (m := m) (theta h)) := by
  unfold partition
  exact Finset.measurable_sum _ (fun a _ => (measurable_actionLoss a htheta).exp)

theorem measurable_weightedLaw {Ω : Type*} [MeasurableSpace Ω]
    (theta : Ω → Fin d → ℝ) (htheta : Measurable theta) (a : Action d m) :
    Measurable (fun h => weightedLaw (theta h) a) :=
  (measurable_actionLoss a htheta).exp.div (measurable_partition theta htheta)

def weightedActionKernel {Ω : Type*} [MeasurableSpace Ω]
    (theta : Ω → Fin d → ℝ) (htheta : Measurable theta) : Kernel Ω (Action d m) where
  toFun h := finiteAtomicMeasure (weightedLaw (theta h)) id
  measurable' := measurable_finiteAtomicMeasure
    (fun h => weightedLaw (theta h)) (measurable_weightedLaw theta htheta) id

theorem weightedActionKernel_isMarkov {Ω : Type*} [MeasurableSpace Ω]
    (theta : Ω → Fin d → ℝ) (htheta : Measurable theta) (hmd : m ≤ d) :
    IsMarkovKernel (weightedActionKernel (m := m) theta htheta) where
  isProbabilityMeasure h := finiteAtomicMeasure_isProbabilityMeasure _
    (fun a => (weightedLaw_pos (theta h) hmd a).le) id (sum_weightedLaw (theta h) hmd)

/-- A genuine observable-history policy, with precisely the exponential law
and no information beyond preceding actions and their scalar feedback. -/
def observableWeightedPolicy
    (theta : (t : ℕ) → History d m t → Fin d → ℝ)
    (htheta : ∀ t, Measurable (theta t)) (hmd : m ≤ d) : Policy d m where
  kernel t := weightedActionKernel (theta t) (htheta t)
  isMarkov t := weightedActionKernel_isMarkov (theta t) (htheta t) hmd

/-- Recover exactly the observable feedback history from the action prefix. -/
def historyOfActions (L : SignedLossProcess d m) :
    (t : ℕ) → ActionTree (Action d m) t → History d m t
  | 0, _ => ()
  | t + 1, (h, a) => (historyOfActions L t h).snoc a
      (actionLoss a (L.itemLoss t (historyOfActions L t h)))

/-- Forget feedback, retaining the actions in their original order. -/
def actionsOfHistory : (t : ℕ) → History d m t → ActionTree (Action d m) t
  | 0, _ => ()
  | t + 1, (h, (a, _)) => (actionsOfHistory t h, a)

theorem actionsOfHistory_historyOfActions (L : SignedLossProcess d m) :
    ∀ t h, actionsOfHistory t (historyOfActions L t h) = h := by
  intro t
  induction t with
  | zero => intro h; cases h; rfl
  | succ t ih =>
    rintro ⟨h, a⟩
    change (actionsOfHistory t (historyOfActions L t h), a) = (h, a)
    rw [ih]

theorem historyOfActions_injective (L : SignedLossProcess d m) (t : ℕ) :
    Function.Injective (historyOfActions L t) :=
  Function.LeftInverse.injective (actionsOfHistory_historyOfActions L t)

theorem measurableSet_actionsOfHistory_fiber :
    ∀ t (a : ActionTree (Action d m) t),
      MeasurableSet {h : History d m t | actionsOfHistory t h = a} := by
  intro t
  induction t with
  | zero => intro a; cases a; simp [actionsOfHistory]
  | succ t ih =>
    rintro ⟨h, a⟩
    have hp : MeasurableSet {H : History d m (t + 1) | actionsOfHistory t H.1 = h} :=
      (ih h).preimage measurable_fst
    have ha : MeasurableSet {H : History d m (t + 1) | H.2.1 = a} :=
      (measurableSet_singleton a).preimage (measurable_fst.comp measurable_snd)
    have heq : {H : History d m (t + 1) | actionsOfHistory (t + 1) H = (h, a)} =
        {H : History d m (t + 1) | actionsOfHistory t H.1 = h} ∩
          {H : History d m (t + 1) | H.2.1 = a} := by
      ext H
      rcases H with ⟨H, a', y⟩
      change (actionsOfHistory t H, a') = (h, a) ↔ actionsOfHistory t H = h ∧ a' = a
      constructor
      · intro hpair
        exact ⟨congrArg Prod.fst hpair, congrArg Prod.snd hpair⟩
      · rintro ⟨hh, ha⟩
        exact Prod.ext hh ha
    rw [heq]
    exact hp.inter ha

/-- Every predicate on the finite action prefix is observable-measurable. -/
theorem measurableSet_actionsOfHistory_mem (T : ℕ)
    (E : Set (ActionTree (Action d m) T)) :
    MeasurableSet {h : History d m T | actionsOfHistory T h ∈ E} := by
  have heq : {h : History d m T | actionsOfHistory T h ∈ E} =
      ⋃ a ∈ E, {h | actionsOfHistory T h = a} := by
    ext h
    simp
  rw [heq]
  exact MeasurableSet.iUnion (fun a => MeasurableSet.iUnion
    (fun _ => measurableSet_actionsOfHistory_fiber T a))

def parametersOnActions
    (theta : (t : ℕ) → History d m t → Fin d → ℝ) (L : SignedLossProcess d m)
    (t : ℕ) (h : ActionTree (Action d m) t) : Fin d → ℝ :=
  theta t (historyOfActions L t h)

theorem signedRoundKernel_weighted_eq_finiteAtomicMeasure
    (theta : (t : ℕ) → History d m t → Fin d → ℝ)
    (htheta : ∀ t, Measurable (theta t)) (hmd : m ≤ d)
    (L : SignedLossProcess d m) (t : ℕ) (h : History d m t) :
    signedRoundKernel (observableWeightedPolicy theta htheta hmd) L t h =
      finiteAtomicMeasure (weightedLaw (theta t h))
        (fun a => h.snoc a (actionLoss a (L.itemLoss t h))) := by
  classical
  ext s hs
  rw [signedRoundKernel_apply _ _ _ _ hs]
  change finiteAtomicMeasure (weightedLaw (theta t h)) id
    {a | h.snoc a (actionLoss a (L.itemLoss t h)) ∈ s} = _
  rw [finiteAtomicMeasure_apply _ _ _ MeasurableSet.of_discrete,
    finiteAtomicMeasure_apply _ _ _ hs]
  rfl

/-- Exact conditional integral, derived from the actual transition kernel. -/
theorem integral_signedRoundKernel_weighted
    (theta : (t : ℕ) → History d m t → Fin d → ℝ)
    (htheta : ∀ t, Measurable (theta t)) (hmd : m ≤ d)
    (L : SignedLossProcess d m) (t : ℕ) (h : History d m t)
    (f : History d m (t + 1) → ℝ) :
    (∫ h', f h' ∂signedRoundKernel (observableWeightedPolicy theta htheta hmd) L t h) =
      ∑ a, weightedLaw (theta t h) a * f (h.snoc a (actionLoss a (L.itemLoss t h))) := by
  rw [signedRoundKernel_weighted_eq_finiteAtomicMeasure]
  exact integral_finiteAtomicMeasure _ (fun a => (weightedLaw_pos (theta t h) hmd a).le) _ _

/-- The complete law of observable histories is exactly the weighted
action-tree law with its deterministic feedback reconstruction. -/
theorem signedRunLaw_eq_finiteAtomicMeasure
    (theta : (t : ℕ) → History d m t → Fin d → ℝ)
    (htheta : ∀ t, Measurable (theta t)) (hmd : m ≤ d)
    (L : SignedLossProcess d m) (T : ℕ) :
    signedRunLaw (observableWeightedPolicy theta htheta hmd) L T =
      finiteAtomicMeasure ((weightedBranchingLaw (parametersOnActions theta L) hmd).mass T)
        (historyOfActions L T) := by
  classical
  let W := weightedBranchingLaw (parametersOnActions theta L) hmd
  change signedRunLaw _ L T = finiteAtomicMeasure (W.mass T) (historyOfActions L T)
  induction T with
  | zero =>
    change Measure.dirac (() : Unit) = ∑ _h : Unit, ENNReal.ofReal 1 • Measure.dirac ()
    rw [Fintype.sum_unique]
    simp
  | succ t ih =>
    ext s hs
    rw [signedRunLaw_succ_apply _ _ _ hs, ih, lintegral_finiteAtomicMeasure,
      finiteAtomicMeasure_apply _ _ _ hs]
    have hround (h : ActionTree (Action d m) t) :
        signedRoundKernel (observableWeightedPolicy theta htheta hmd) L t
            (historyOfActions L t h) s =
          ∑ a, ENNReal.ofReal (weightedLaw (theta t (historyOfActions L t h)) a) *
            (if (historyOfActions L t h).snoc a
              (actionLoss a (L.itemLoss t (historyOfActions L t h))) ∈ s then 1 else 0) := by
      have heq := congrArg (fun μ : Measure (History d m (t + 1)) => μ s)
        (signedRoundKernel_weighted_eq_finiteAtomicMeasure
          theta htheta hmd L t (historyOfActions L t h))
      exact heq.trans (finiteAtomicMeasure_apply _ _ _ hs)
    simp_rw [hround]
    change (∑ h : ActionTree (Action d m) t, ENNReal.ofReal (W.mass t h) *
      ∑ a, ENNReal.ofReal (weightedLaw (theta t (historyOfActions L t h)) a) *
        (if (historyOfActions L t h).snoc a
          (actionLoss a (L.itemLoss t (historyOfActions L t h))) ∈ s then 1 else 0)) =
      ∑ ha : ActionTree (Action d m) t × Action d m,
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

theorem signedRunLaw_probability_eq_tree
    (theta : (t : ℕ) → History d m t → Fin d → ℝ)
    (htheta : ∀ t, Measurable (theta t)) (hmd : m ≤ d)
    (L : SignedLossProcess d m) (T : ℕ)
    (s : Set (History d m T)) (hs : MeasurableSet s) :
    (signedRunLaw (observableWeightedPolicy theta htheta hmd) L T).real s =
      (weightedBranchingLaw (parametersOnActions theta L) hmd).probability T
        {h | historyOfActions L T h ∈ s} := by
  rw [signedRunLaw_eq_finiteAtomicMeasure, finiteAtomicMeasure_real_apply _
    ((weightedBranchingLaw (parametersOnActions theta L) hmd).mass_nonneg T) _ _ hs]
  rfl

theorem integrable_signedRunLaw_weighted
    (theta : (t : ℕ) → History d m t → Fin d → ℝ)
    (htheta : ∀ t, Measurable (theta t)) (hmd : m ≤ d)
    (L : SignedLossProcess d m) (T : ℕ) (f : History d m T → ℝ) :
    Integrable f (signedRunLaw (observableWeightedPolicy theta htheta hmd) L T) := by
  rw [signedRunLaw_eq_finiteAtomicMeasure]
  exact integrable_finiteAtomicMeasure _ _ _

theorem integral_signedRunLaw_eq_tree
    (theta : (t : ℕ) → History d m t → Fin d → ℝ)
    (htheta : ∀ t, Measurable (theta t)) (hmd : m ≤ d)
    (L : SignedLossProcess d m) (T : ℕ) (f : History d m T → ℝ) :
    (∫ h, f h ∂signedRunLaw (observableWeightedPolicy theta htheta hmd) L T) =
      (weightedBranchingLaw (parametersOnActions theta L) hmd).expectation T
        (fun h => f (historyOfActions L T h)) := by
  rw [signedRunLaw_eq_finiteAtomicMeasure, integral_finiteAtomicMeasure _
    ((weightedBranchingLaw (parametersOnActions theta L) hmd).mass_nonneg T)]
  rfl

/-- The conditional-expectation testing identity: multiplying by any
function of the preceding history gives exactly the kernel conditional
average.  All integrals exist because these runs have finite support. -/
theorem integral_signedRunLaw_succ_test
    (theta : (t : ℕ) → History d m t → Fin d → ℝ)
    (htheta : ∀ t, Measurable (theta t)) (hmd : m ≤ d)
    (L : SignedLossProcess d m) (t : ℕ)
    (F : History d m t → ℝ) (g : History d m (t + 1) → ℝ) :
    (∫ h', F h'.1 * g h'
      ∂signedRunLaw (observableWeightedPolicy theta htheta hmd) L (t + 1)) =
      ∫ h, F h * (∑ a, weightedLaw (theta t h) a *
        g (h.snoc a (actionLoss a (L.itemLoss t h))))
        ∂signedRunLaw (observableWeightedPolicy theta htheta hmd) L t := by
  rw [integral_signedRunLaw_eq_tree, integral_signedRunLaw_eq_tree,
    BranchingLaw.expectation_succ]
  congr 1
  funext h
  change (∑ a, weightedLaw (theta t (historyOfActions L t h)) a *
    (F (historyOfActions L t h) *
      g ((historyOfActions L t h).snoc a
        (actionLoss a (L.itemLoss t (historyOfActions L t h)))))) = _
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro a _
  ring

theorem integral_signedRunLaw_succ_tower
    (theta : (t : ℕ) → History d m t → Fin d → ℝ)
    (htheta : ∀ t, Measurable (theta t)) (hmd : m ≤ d)
    (L : SignedLossProcess d m) (t : ℕ) (g : History d m (t + 1) → ℝ) :
    (∫ h', g h' ∂signedRunLaw (observableWeightedPolicy theta htheta hmd) L (t + 1)) =
      ∫ h, (∫ h', g h'
        ∂signedRoundKernel (observableWeightedPolicy theta htheta hmd) L t h)
        ∂signedRunLaw (observableWeightedPolicy theta htheta hmd) L t := by
  simp_rw [integral_signedRoundKernel_weighted theta htheta hmd L t]
  simpa only [one_mul] using
    integral_signedRunLaw_succ_test theta htheta hmd L t (fun _ => 1) g

/-- Every finite-tree event transfers to an actual measurable observable
event with exactly the same probability, not merely a probability bound. -/
theorem signedRunLaw_probability_actions_eq_tree
    (theta : (t : ℕ) → History d m t → Fin d → ℝ)
    (htheta : ∀ t, Measurable (theta t)) (hmd : m ≤ d)
    (L : SignedLossProcess d m) (T : ℕ) (E : Set (ActionTree (Action d m) T)) :
    (signedRunLaw (observableWeightedPolicy theta htheta hmd) L T).real
        {h | actionsOfHistory T h ∈ E} =
      (weightedBranchingLaw (parametersOnActions theta L) hmd).probability T E := by
  rw [signedRunLaw_probability_eq_tree _ _ _ _ _ _ (measurableSet_actionsOfHistory_mem T E)]
  congr 1
  ext h
  simp only [Set.mem_setOf_eq, actionsOfHistory_historyOfActions]

/-- Real-valued functions of the actions likewise preserve expectations. -/
theorem integral_signedRunLaw_actions_eq_tree
    (theta : (t : ℕ) → History d m t → Fin d → ℝ)
    (htheta : ∀ t, Measurable (theta t)) (hmd : m ≤ d)
    (L : SignedLossProcess d m) (T : ℕ) (f : ActionTree (Action d m) T → ℝ) :
    (∫ h, f (actionsOfHistory T h)
      ∂signedRunLaw (observableWeightedPolicy theta htheta hmd) L T) =
      (weightedBranchingLaw (parametersOnActions theta L) hmd).expectation T f := by
  rw [integral_signedRunLaw_eq_tree]
  simp only [actionsOfHistory_historyOfActions]

/-- Finite support makes the law identity valid for every set, including
events expressed using functions only defined measurably on reachable nodes. -/
theorem signedRunLaw_probability_eq_tree_all_sets
    (theta : (t : ℕ) → History d m t → Fin d → ℝ)
    (htheta : ∀ t, Measurable (theta t)) (hmd : m ≤ d)
    (L : SignedLossProcess d m) (T : ℕ) (s : Set (History d m T)) :
    (signedRunLaw (observableWeightedPolicy theta htheta hmd) L T).real s =
      (weightedBranchingLaw (parametersOnActions theta L) hmd).probability T
        {h | historyOfActions L T h ∈ s} := by
  rw [signedRunLaw_eq_finiteAtomicMeasure, finiteAtomicMeasure_real_apply_of_singletons _
    ((weightedBranchingLaw (parametersOnActions theta L) hmd).mass_nonneg T)]
  rfl

theorem signedRunLaw_ae_history_reconstruction
    (theta : (t : ℕ) → History d m t → Fin d → ℝ)
    (htheta : ∀ t, Measurable (theta t)) (hmd : m ≤ d)
    (L : SignedLossProcess d m) (T : ℕ) :
    ∀ᵐ h ∂signedRunLaw (observableWeightedPolicy theta htheta hmd) L T,
      historyOfActions L T (actionsOfHistory T h) = h := by
  rw [signedRunLaw_eq_finiteAtomicMeasure]
  apply ae_finiteAtomicMeasure_of_forall
  intro h
  rw [actionsOfHistory_historyOfActions]

/-- The literal cumulative statistic of preceding observable histories and
the freshly sampled action; feedback is not replaced in this definition. -/
def observablePathSum (g : (t : ℕ) → History d m t → Action d m → ℝ) :
    (t : ℕ) → History d m t → ℝ
  | 0, _ => 0
  | t + 1, (h, (a, _)) => observablePathSum g t h + g t h a

def incrementsOnActions
    (g : (t : ℕ) → History d m t → Action d m → ℝ) (L : SignedLossProcess d m)
    (t : ℕ) (h : ActionTree (Action d m) t) (a : Action d m) : ℝ :=
  g t (historyOfActions L t h) a

theorem observablePathSum_historyOfActions
    (g : (t : ℕ) → History d m t → Action d m → ℝ) (L : SignedLossProcess d m) :
    ∀ T h, observablePathSum g T (historyOfActions L T h) =
      pathSum (incrementsOnActions g L) T h := by
  intro T
  induction T with
  | zero => intro h; cases h; rfl
  | succ T ih =>
    rintro ⟨h, a⟩
    change observablePathSum g T (historyOfActions L T h) +
      g T (historyOfActions L T h) a =
      pathSum (incrementsOnActions g L) T h + incrementsOnActions g L T h a
    rw [ih]
    rfl

end MsetsPaper.Upper
