import MsetsLower.Core.Protocol

/-!
# Complement symmetry for dense and sparse set actions

This file formalizes `lem:lower-complement`.  A `(d-s)`-set action is sent to
its `s`-set complement, and the equivalence is lifted round-by-round to
observable histories without changing scalar feedback.  The loss transform is
the literal transform from the manuscript.
-/

namespace MsetsLower.Lower

open MsetsLower MeasureTheory ProbabilityTheory
open scoped BigOperators ProbabilityTheory

noncomputable section

/-- Complementation is a bijection between `(d-s)`-sets and `s`-sets. -/
def actionComplementEquiv (d s : Nat) (hsd : s ≤ d) :
    MSetAction d (d - s) ≃ MSetAction d s where
  toFun a := ⟨a.1ᶜ, by simp [Finset.card_compl, a.2, Nat.sub_sub_self hsd]⟩
  invFun b := ⟨b.1ᶜ, by simp [Finset.card_compl, b.2]⟩
  left_inv a := by
    apply Subtype.ext
    simp
  right_inv b := by
    apply Subtype.ext
    simp

/-- The action-complement bijection is measurable in both directions. -/
def actionComplementMeasurableEquiv (d s : Nat) (hsd : s ≤ d) :
    MSetAction d (d - s) ≃ᵐ MSetAction d s where
  toEquiv := actionComplementEquiv d s hsd
  measurable_toFun := measurable_of_finite _
  measurable_invFun := measurable_of_finite _

@[simp] theorem actionComplementEquiv_val (d s : Nat) (hsd : s ≤ d)
    (a : MSetAction d (d - s)) :
    (actionComplementEquiv d s hsd a).1 = a.1ᶜ :=
  rfl

@[simp] theorem actionComplementEquiv_symm_val (d s : Nat) (hsd : s ≤ d)
    (a : MSetAction d s) :
    ((actionComplementEquiv d s hsd).symm a).1 = a.1ᶜ :=
  rfl

/-- Complement every action in a history and retain every scalar feedback. -/
def historyComplementEquiv (d s : Nat) (hsd : s ≤ d) :
    (t : Nat) → History d (d - s) t ≃ᵐ History d s t
  | 0 => MeasurableEquiv.refl Unit
  | t + 1 => MeasurableEquiv.prodCongr (historyComplementEquiv d s hsd t)
      (MeasurableEquiv.prodCongr (actionComplementMeasurableEquiv d s hsd)
        (MeasurableEquiv.refl Real))

@[simp] theorem historyComplementEquiv_zero (d s : Nat) (hsd : s ≤ d)
    (h : History d (d - s) 0) :
    historyComplementEquiv d s hsd 0 h = h :=
  rfl

@[simp] theorem historyComplementEquiv_succ (d s t : Nat) (hsd : s ≤ d)
    (h : History d (d - s) t) (a : MSetAction d (d - s)) (z : Real) :
    historyComplementEquiv d s hsd (t + 1) (h.snoc a z) =
      (historyComplementEquiv d s hsd t h).snoc
        (actionComplementEquiv d s hsd a) z :=
  rfl

@[simp] theorem historyComplementEquiv_symm_succ (d s t : Nat) (hsd : s ≤ d)
    (h : History d s t) (a : MSetAction d s) (z : Real) :
    (historyComplementEquiv d s hsd (t + 1)).symm (h.snoc a z) =
      ((historyComplementEquiv d s hsd t).symm h).snoc
        ((actionComplementEquiv d s hsd).symm a) z :=
  rfl

/-- The item-loss transform `-g + ((1ᵀg)/m) 1` from the manuscript. -/
def complementItemLoss {d : Nat} (m : Nat) (g : Fin d → Real) : Fin d → Real :=
  fun i => -g i + (∑ j : Fin d, g j) / (m : Real)

@[simp] theorem complementItemLoss_apply {d m : Nat} (g : Fin d → Real)
    (i : Fin d) :
    complementItemLoss m g i = -g i + (∑ j : Fin d, g j) / (m : Real) :=
  rfl

/-- A dense action under the transformed loss receives exactly the loss of its
sparse complement.  This is the displayed algebraic identity in the proof of
`lem:lower-complement`. -/
theorem actionLoss_complementItemLoss {d s : Nat} (hsd : s ≤ d)
    (hm : 0 < d - s) (g : Fin d → Real) (a : MSetAction d (d - s)) :
    actionLoss a (complementItemLoss (d - s) g) =
      actionLoss (actionComplementEquiv d s hsd a) g := by
  classical
  rw [actionLoss_eq_finset_sum, actionLoss_eq_finset_sum]
  change (∑ i ∈ a.1, (-g i + (∑ j : Fin d, g j) / ((d - s : Nat) : Real))) =
    ∑ i ∈ a.1ᶜ, g i
  have hm0 : ((d - s : Nat) : Real) ≠ 0 := by
    exact_mod_cast (Nat.ne_of_gt hm)
  have hscale : ((d - s : Nat) : Real) *
      ((∑ j : Fin d, g j) / ((d - s : Nat) : Real)) = ∑ j : Fin d, g j := by
    field_simp
  have hleft :
      (∑ i ∈ a.1, (-g i + (∑ j : Fin d, g j) / ((d - s : Nat) : Real))) =
        -(∑ i ∈ a.1, g i) + ∑ j : Fin d, g j := by
    rw [Finset.sum_add_distrib, Finset.sum_neg_distrib, Finset.sum_const,
      nsmul_eq_mul, a.2, hscale]
  rw [hleft]
  have hpartition := Finset.sum_compl_add_sum a.1 g
  linarith

/-- Transport a deterministic non-anticipating sparse loss process to the
dense game.  At round `t`, the sparse process is evaluated only on the
complemented dense history through round `t-1`. -/
def complementLossProcess {d s : Nat} (hsd : s ≤ d) (hm : 0 < d - s)
    (G : LossProcess d s) : LossProcess d (d - s) where
  itemLoss t h := complementItemLoss (d - s)
    (G.itemLoss t (historyComplementEquiv d s hsd t h))
  measurable_itemLoss t := by
    have hg : Measurable (fun h : History d (d - s) t =>
        G.itemLoss t (historyComplementEquiv d s hsd t h)) :=
      (G.measurable_itemLoss t).comp
        (historyComplementEquiv d s hsd t).measurable
    have htotal : Measurable (fun h : History d (d - s) t =>
        ∑ j : Fin d, G.itemLoss t (historyComplementEquiv d s hsd t h) j) := by
      exact Finset.measurable_sum _ fun j _ => hg.eval (a := j)
    refine Measurable.of_eval fun i => ?_
    exact (hg.eval (a := i)).neg.add
      (htotal.div_const ((d - s : Nat) : Real))
  action_nonneg t h a := by
    rw [actionLoss_complementItemLoss hsd hm]
    exact G.action_nonneg t (historyComplementEquiv d s hsd t h)
      (actionComplementEquiv d s hsd a)
  action_le_one t h a := by
    rw [actionLoss_complementItemLoss hsd hm]
    exact G.action_le_one t (historyComplementEquiv d s hsd t h)
      (actionComplementEquiv d s hsd a)

@[simp] theorem complementLossProcess_itemLoss {d s : Nat} (hsd : s ≤ d)
    (hm : 0 < d - s) (G : LossProcess d s) (t : Nat)
    (h : History d (d - s) t) :
    (complementLossProcess hsd hm G).itemLoss t h =
      complementItemLoss (d - s)
        (G.itemLoss t (historyComplementEquiv d s hsd t h)) :=
  rfl

/-- Feedback is identical for every complementary action/history pair. -/
@[simp] theorem actionLoss_complementLossProcess {d s : Nat} (hsd : s ≤ d)
    (hm : 0 < d - s) (G : LossProcess d s) (t : Nat)
    (h : History d (d - s) t) (a : MSetAction d (d - s)) :
    actionLoss a ((complementLossProcess hsd hm G).itemLoss t h) =
      actionLoss (actionComplementEquiv d s hsd a)
        (G.itemLoss t (historyComplementEquiv d s hsd t h)) :=
  actionLoss_complementItemLoss hsd hm _ _

/-- In particular, every transformed dense action loss lies in `[0,1]`. -/
theorem complementLossProcess_action_mem_Icc {d s : Nat} (hsd : s ≤ d)
    (hm : 0 < d - s) (G : LossProcess d s) (t : Nat)
    (h : History d (d - s) t) (a : MSetAction d (d - s)) :
    actionLoss a ((complementLossProcess hsd hm G).itemLoss t h) ∈
      Set.Icc (0 : Real) 1 := by
  rw [actionLoss_complementLossProcess hsd hm]
  exact G.action_mem_Icc t (historyComplementEquiv d s hsd t h)
    (actionComplementEquiv d s hsd a)

/-- The loss chosen at a dense history is determined by its observable
complement history; this is the explicit non-anticipation statement. -/
theorem complementLossProcess_nonanticipating {d s : Nat} (hsd : s ≤ d)
    (hm : 0 < d - s) (G : LossProcess d s) (t : Nat)
    {h h' : History d (d - s) t}
    (hh : historyComplementEquiv d s hsd t h =
      historyComplementEquiv d s hsd t h') :
    (complementLossProcess hsd hm G).itemLoss t h =
      (complementLossProcess hsd hm G).itemLoss t h' := by
  simp only [complementLossProcess_itemLoss, hh]

/-- One protocol update commutes with complementation, including its scalar
feedback coordinate. -/
theorem complement_extendRun {d s : Nat} (hsd : s ≤ d) (hm : 0 < d - s)
    (G : LossProcess d s) (t : Nat) (h : History d (d - s) t)
    (a : MSetAction d (d - s)) :
    historyComplementEquiv d s hsd (t + 1)
        (extendRun (complementLossProcess hsd hm G) t (h, a)) =
      extendRun G t
        (historyComplementEquiv d s hsd t h,
          actionComplementEquiv d s hsd a) := by
  change (historyComplementEquiv d s hsd t h).snoc
      (actionComplementEquiv d s hsd a)
        (actionLoss a (complementItemLoss (d - s)
          (G.itemLoss t (historyComplementEquiv d s hsd t h)))) =
    (historyComplementEquiv d s hsd t h).snoc
      (actionComplementEquiv d s hsd a)
        (actionLoss (actionComplementEquiv d s hsd a)
          (G.itemLoss t (historyComplementEquiv d s hsd t h)))
  rw [actionLoss_complementItemLoss hsd hm]

/-- Couple a dense policy to the sparse game: translate the observed history
back to the dense game, use the original kernel, and complement its action. -/
def complementPolicy {d s : Nat} (hsd : s ≤ d)
    (P : Policy d (d - s)) : Policy d s where
  kernel t := Kernel.map
    (Kernel.comap (P.kernel t) (historyComplementEquiv d s hsd t).symm
      (historyComplementEquiv d s hsd t).symm.measurable)
    (actionComplementMeasurableEquiv d s hsd)
  isMarkov t := by
    letI : IsMarkovKernel (P.kernel t) := P.isMarkov t
    letI : IsMarkovKernel
        (Kernel.comap (P.kernel t) (historyComplementEquiv d s hsd t).symm
          (historyComplementEquiv d s hsd t).symm.measurable) := by
      infer_instance
    exact Kernel.IsMarkovKernel.map _
      (actionComplementMeasurableEquiv d s hsd).measurable

/-- Conditional on complementary histories, the sparse action law is exactly
the pushforward of the dense action law by complementation.  This is the
measure-theoretic form of using the same private randomization. -/
theorem complementPolicy_kernel {d s : Nat} (hsd : s ≤ d)
    (P : Policy d (d - s)) (t : Nat) (h : History d (d - s) t) :
    (complementPolicy hsd P).kernel t
        (historyComplementEquiv d s hsd t h) =
      (P.kernel t h).map (actionComplementMeasurableEquiv d s hsd) := by
  change (Kernel.map
      (Kernel.comap (P.kernel t) (historyComplementEquiv d s hsd t).symm
        (historyComplementEquiv d s hsd t).symm.measurable)
      (actionComplementMeasurableEquiv d s hsd))
        (historyComplementEquiv d s hsd t h) = _
  rw [Kernel.map_apply _
    (actionComplementMeasurableEquiv d s hsd).measurable,
    Kernel.comap_apply]
  simp

theorem complementPolicy_kernel_apply {d s : Nat} (hsd : s ≤ d)
    (P : Policy d (d - s)) (t : Nat) (h : History d (d - s) t)
    {u : Set (MSetAction d s)} (hu : MeasurableSet u) :
    (complementPolicy hsd P).kernel t
      (historyComplementEquiv d s hsd t h) u =
      P.kernel t h ((actionComplementMeasurableEquiv d s hsd) ⁻¹' u) := by
  rw [complementPolicy_kernel hsd P t h,
    Measure.map_apply (actionComplementMeasurableEquiv d s hsd).measurable hu]

/-- The conditional law of one complemented round is the pushforward of the
dense round law. -/
theorem complement_roundKernel {d s : Nat} (hsd : s ≤ d)
    (hm : 0 < d - s) (P : Policy d (d - s)) (G : LossProcess d s)
    (t : Nat) (h : History d (d - s) t) :
    roundKernel (complementPolicy hsd P) G t
        (historyComplementEquiv d s hsd t h) =
      (roundKernel P (complementLossProcess hsd hm G) t h).map
        (historyComplementEquiv d s hsd (t + 1)) := by
  ext u hu
  rw [roundKernel_apply (complementPolicy hsd P) G t
      (historyComplementEquiv d s hsd t h) hu,
    complementPolicy_kernel hsd P t h]
  rw [Measure.map_apply
    (actionComplementMeasurableEquiv d s hsd).measurable
    (MeasurableSet.of_discrete : MeasurableSet
      {a : MSetAction d s |
        (historyComplementEquiv d s hsd t h).snoc a
          (actionLoss a (G.itemLoss t
            (historyComplementEquiv d s hsd t h))) ∈ u})]
  rw [Measure.map_apply (historyComplementEquiv d s hsd (t + 1)).measurable hu,
    roundKernel_apply P (complementLossProcess hsd hm G) t h
      ((historyComplementEquiv d s hsd (t + 1)).measurable hu)]
  congr 1
  ext a
  simp only [Set.mem_preimage, Set.mem_setOf_eq]
  change extendRun G t
      (historyComplementEquiv d s hsd t h,
        actionComplementEquiv d s hsd a) ∈ u ↔
    historyComplementEquiv d s hsd (t + 1)
      (extendRun (complementLossProcess hsd hm G) t (h, a)) ∈ u
  rw [complement_extendRun hsd hm G t h a]

/-- Pulling a kernel back along a measurable equivalence and then composing a
measure is the same as first pushing the measure forward. -/
private theorem comap_comp_eq_comp_map
    {α β γ : Type*} [MeasurableSpace α] [MeasurableSpace β]
    [MeasurableSpace γ] (e : α ≃ᵐ β) (μ : Measure α) (κ : Kernel β γ) :
    (Kernel.comap κ e e.measurable) ∘ₘ μ = κ ∘ₘ μ.map e := by
  ext u hu
  rw [Measure.bind_apply hu (Kernel.aemeasurable _),
    Measure.bind_apply hu (Kernel.aemeasurable _),
    MeasureTheory.lintegral_map (Kernel.measurable_coe κ hu) e.measurable]
  rfl

/-- At every horizon, the whole sparse run law is the history-complement
pushforward of the dense run law. -/
theorem complement_runLaw {d s : Nat} (hsd : s ≤ d) (hm : 0 < d - s)
    (P : Policy d (d - s)) (G : LossProcess d s) (t : Nat) :
    (runLaw P (complementLossProcess hsd hm G) t).map
        (historyComplementEquiv d s hsd t) =
      runLaw (complementPolicy hsd P) G t := by
  induction t with
  | zero =>
      exact Measure.map_dirac' (historyComplementEquiv d s hsd 0).measurable ()
  | succ t ih =>
      rw [runLaw_succ, runLaw_succ,
        Measure.map_comp _ _ (historyComplementEquiv d s hsd (t + 1)).measurable]
      have hk :
          (roundKernel P (complementLossProcess hsd hm G) t).map
              (historyComplementEquiv d s hsd (t + 1)) =
            Kernel.comap (roundKernel (complementPolicy hsd P) G t)
              (historyComplementEquiv d s hsd t)
              (historyComplementEquiv d s hsd t).measurable := by
        ext h u hu
        rw [Kernel.map_apply _
          (historyComplementEquiv d s hsd (t + 1)).measurable,
          Kernel.comap_apply]
        exact congr_arg (fun μ : Measure (History d s (t + 1)) => μ u)
          (complement_roundKernel hsd hm P G t h).symm
      rw [hk, comap_comp_eq_comp_map, ih]

/-! ## Pathwise external regret -/

/-- Cumulative loss of the actions stored in a finite observable history.
The stored feedback coordinate is not trusted: loss is recomputed from the
non-anticipating process at each preceding history. -/
def realizedCumulativeLoss {d m : Nat} (L : LossProcess d m) :
    (t : Nat) → History d m t → Real
  | 0, _ => 0
  | t + 1, h =>
      realizedCumulativeLoss L t h.1 +
        actionLoss h.2.1 (L.itemLoss t h.1)

/-- Cumulative loss of a fixed comparator along the loss sequence generated
on a realized history. -/
def comparatorCumulativeLoss {d m : Nat} (L : LossProcess d m) :
    (t : Nat) → History d m t → MSetAction d m → Real
  | 0, _, _ => 0
  | t + 1, h, a =>
      comparatorCumulativeLoss L t h.1 a +
        actionLoss a (L.itemLoss t h.1)

/-- Loss of the best fixed action in hindsight.  The `sInf` presentation is
extensionally the usual finite minimum and makes transport across an action
equivalence direct. -/
def bestComparatorCumulativeLoss {d m : Nat} (L : LossProcess d m)
    (t : Nat) (h : History d m t) : Real :=
  sInf (Set.range (comparatorCumulativeLoss L t h))

/-- External regret on one concrete finite history. -/
def pathRegret {d m : Nat} (L : LossProcess d m) (t : Nat)
    (h : History d m t) : Real :=
  realizedCumulativeLoss L t h - bestComparatorCumulativeLoss L t h

/-- Played cumulative loss is invariant under the coupled path. -/
theorem realizedCumulativeLoss_complement {d s : Nat} (hsd : s ≤ d)
    (hm : 0 < d - s) (G : LossProcess d s) (t : Nat)
    (h : History d (d - s) t) :
    realizedCumulativeLoss (complementLossProcess hsd hm G) t h =
      realizedCumulativeLoss G t (historyComplementEquiv d s hsd t h) := by
  induction t with
  | zero => rfl
  | succ t ih =>
      rcases h with ⟨h, a, z⟩
      simp only [realizedCumulativeLoss]
      rw [ih h, actionLoss_complementLossProcess hsd hm]
      rfl

/-- Every fixed dense comparator has the same cumulative loss as its fixed
sparse complement. -/
theorem comparatorCumulativeLoss_complement {d s : Nat} (hsd : s ≤ d)
    (hm : 0 < d - s) (G : LossProcess d s) (t : Nat)
    (h : History d (d - s) t) (a : MSetAction d (d - s)) :
    comparatorCumulativeLoss (complementLossProcess hsd hm G) t h a =
      comparatorCumulativeLoss G t (historyComplementEquiv d s hsd t h)
        (actionComplementEquiv d s hsd a) := by
  induction t with
  | zero => rfl
  | succ t ih =>
      rcases h with ⟨h, played, z⟩
      simp only [comparatorCumulativeLoss]
      rw [ih h, actionLoss_complementLossProcess hsd hm]
      rfl

/-- Complementation identifies the two sets of fixed-comparator cumulative
losses, hence their best values. -/
theorem bestComparatorCumulativeLoss_complement {d s : Nat} (hsd : s ≤ d)
    (hm : 0 < d - s) (G : LossProcess d s) (t : Nat)
    (h : History d (d - s) t) :
    bestComparatorCumulativeLoss (complementLossProcess hsd hm G) t h =
      bestComparatorCumulativeLoss G t
        (historyComplementEquiv d s hsd t h) := by
  unfold bestComparatorCumulativeLoss
  congr 1
  ext z
  constructor
  · rintro ⟨a, rfl⟩
    refine ⟨actionComplementEquiv d s hsd a, ?_⟩
    exact (comparatorCumulativeLoss_complement hsd hm G t h a).symm
  · rintro ⟨a, rfl⟩
    refine ⟨(actionComplementEquiv d s hsd).symm a, ?_⟩
    simpa using comparatorCumulativeLoss_complement hsd hm G t h
      ((actionComplementEquiv d s hsd).symm a)

/-- Pathwise equality of the dense and sparse external regrets. -/
theorem pathRegret_complement {d s : Nat} (hsd : s ≤ d)
    (hm : 0 < d - s) (G : LossProcess d s) (t : Nat)
    (h : History d (d - s) t) :
    pathRegret (complementLossProcess hsd hm G) t h =
      pathRegret G t (historyComplementEquiv d s hsd t h) := by
  unfold pathRegret
  rw [realizedCumulativeLoss_complement hsd hm,
    bestComparatorCumulativeLoss_complement hsd hm]

/-- The manuscript assumptions imply the two arithmetic hypotheses used by
the construction. -/
theorem complement_parameters_of_sparse_half {d s : Nat} (hs_one : 1 ≤ s)
    (hs_half : s ≤ d / 2) : s ≤ d ∧ 0 < d - s := by
  omega

/-- All clauses of `lem:lower-complement` in one capstone statement.  The
hypotheses `s ≤ d` and `0 < d-s` are slightly weaker than the manuscript's
`1 ≤ s ≤ d/2`; `complement_parameters_of_sparse_half` supplies them from the
literal manuscript assumptions. -/
theorem lower_complement {d s : Nat} (hsd : s ≤ d) (hm : 0 < d - s)
    (P : Policy d (d - s)) (G : LossProcess d s) :
    (∀ (t : Nat) (h : History d (d - s) t),
      (complementPolicy hsd P).kernel t
          (historyComplementEquiv d s hsd t h) =
        (P.kernel t h).map (actionComplementMeasurableEquiv d s hsd)) ∧
    (∀ (t : Nat) (h : History d (d - s) t)
        (a : MSetAction d (d - s)),
      actionLoss a ((complementLossProcess hsd hm G).itemLoss t h) =
        actionLoss (actionComplementEquiv d s hsd a)
          (G.itemLoss t (historyComplementEquiv d s hsd t h))) ∧
    (∀ (t : Nat) (h : History d (d - s) t)
        (a : MSetAction d (d - s)),
      actionLoss a ((complementLossProcess hsd hm G).itemLoss t h) ∈
        Set.Icc (0 : Real) 1) ∧
    (∀ t, Measurable ((complementLossProcess hsd hm G).itemLoss t)) ∧
    (∀ t (h h' : History d (d - s) t),
      historyComplementEquiv d s hsd t h =
          historyComplementEquiv d s hsd t h' →
        (complementLossProcess hsd hm G).itemLoss t h =
          (complementLossProcess hsd hm G).itemLoss t h') ∧
    (∀ (t : Nat),
      (runLaw P (complementLossProcess hsd hm G) t).map
          (historyComplementEquiv d s hsd t) =
        runLaw (complementPolicy hsd P) G t) ∧
    (∀ (t : Nat) (h : History d (d - s) t),
      pathRegret (complementLossProcess hsd hm G) t h =
        pathRegret G t (historyComplementEquiv d s hsd t h)) := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact complementPolicy_kernel hsd P
  · exact actionLoss_complementLossProcess hsd hm G
  · exact complementLossProcess_action_mem_Icc hsd hm G
  · exact (complementLossProcess hsd hm G).measurable_itemLoss
  · exact complementLossProcess_nonanticipating hsd hm G
  · exact complement_runLaw hsd hm P G
  · exact pathRegret_complement hsd hm G

#print axioms lower_complement
#print axioms complement_runLaw
#print axioms pathRegret_complement

end

end MsetsLower.Lower
