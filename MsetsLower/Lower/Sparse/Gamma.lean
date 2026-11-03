import MsetsLower.Lower.Sparse.ScoreBridge
import MsetsLower.Lower.Sparse.GoodPartition
import Mathlib.MeasureTheory.Order.Lattice

/-!
# The observable sparse maximum and `Gamma`

For a fixed equipartition, this file takes the maximum observable coordinate
score in every group and subtracts the observable learner score.  The resulting
quantity is measurable and uniformly bounded on the genuine feedback support.
Choosing one maximizer per group produces an exact `k`-set, so after the
fixed-table score bridge the source-table maximum dominates `Gamma` pathwise.
-/

namespace MsetsLower.Lower.Sparse

open MsetsLower Feedback MeasureTheory ProbabilityTheory Set
open scoped BigOperators ENNReal ProbabilityTheory

noncomputable section

/-! ## Group maxima and the history-level observable -/

theorem sparsePartitionGroup_nonempty
    {n' k r : Nat} (hprod : n' = k * r) (hr : 0 < r)
    (sigma : Equiv.Perm (Fin n')) (g : Fin k) :
    (sparsePartitionGroup hprod sigma g).Nonempty := by
  apply Finset.card_pos.mp
  rw [card_sparsePartitionGroup hprod sigma g]
  exact hr

/-- Maximum observable coordinate score in one group of the fixed
equipartition. -/
def sparseObservableGroupMax
    {n n' k r : Nat} (hprod : n' = k * r) (hr : 0 < r)
    (sigma : Equiv.Perm (Fin n')) (V : SparseAdaptiveParameters n k)
    (hn' : n' <= n) (q c0 : Nat) (U : Nat -> Fin n -> Real) (g : Fin k)
    (T : Nat) (h : History n k T) : Real :=
  (sparsePartitionGroup hprod sigma g).sup'
    (sparsePartitionGroup_nonempty hprod hr sigma g)
    (fun j => sparseObservableCoordinateScore V hn' q c0 U j T h)

/-- The manuscript's observable `Gamma`: the sum of the group maxima minus
the learner score. -/
def sparseHistoryGamma
    {n n' k r : Nat} (hprod : n' = k * r) (hr : 0 < r)
    (sigma : Equiv.Perm (Fin n')) (V : SparseAdaptiveParameters n k)
    (hn' : n' <= n) (q c0 : Nat) (U : Nat -> Fin n -> Real)
    (T : Nat) (h : History n k T) : Real :=
  (∑ g : Fin k,
      sparseObservableGroupMax hprod hr sigma V hn' q c0 U g T h) -
    sparseObservableLearnerScore V n' q c0 U T h

theorem measurable_sparseObservableGroupMax
    {n n' k r : Nat} (hprod : n' = k * r) (hr : 0 < r)
    (sigma : Equiv.Perm (Fin n')) (V : SparseAdaptiveParameters n k)
    (hn' : n' <= n) (q c0 : Nat) (U : Nat -> Fin n -> Real) (g : Fin k)
    (T : Nat) :
    Measurable (sparseObservableGroupMax hprod hr sigma V hn' q c0 U g T) := by
  unfold sparseObservableGroupMax
  let G := sparsePartitionGroup hprod sigma g
  let hG := sparsePartitionGroup_nonempty hprod hr sigma g
  have hm : Measurable (G.sup' hG
      (fun j => sparseObservableCoordinateScore V hn' q c0 U j T)) :=
    Finset.measurable_sup' hG fun j hj =>
      measurable_sparseObservableCoordinateScore
        (q := q) (c0 := c0) V hn' U j T
  have heq : G.sup' hG
        (fun j => sparseObservableCoordinateScore V hn' q c0 U j T) =
      (fun h => G.sup' hG
        (fun j => sparseObservableCoordinateScore V hn' q c0 U j T h)) := by
    funext h
    exact Finset.apply_sup'_eq_sup'_comp hG
      (fun f : History n k T -> Real => f h)
      (fun (_ _ : History n k T -> Real) => rfl)
  rw [← heq]
  exact hm

theorem measurable_sparseHistoryGamma
    {n n' k r : Nat} (hprod : n' = k * r) (hr : 0 < r)
    (sigma : Equiv.Perm (Fin n')) (V : SparseAdaptiveParameters n k)
    (hn' : n' <= n) (q c0 : Nat) (U : Nat -> Fin n -> Real) (T : Nat) :
    Measurable (sparseHistoryGamma hprod hr sigma V hn' q c0 U T) := by
  unfold sparseHistoryGamma
  exact (Finset.measurable_sum _ fun g _ =>
    measurable_sparseObservableGroupMax hprod hr sigma V hn' q c0 U g T).sub
      (measurable_sparseObservableLearnerScore V U T)

theorem sparseObservableGroupMax_abs_le
    {n n' k r T : Nat} (hprod : n' = k * r) (hr : 0 < r)
    (sigma : Equiv.Perm (Fin n')) (V : SparseAdaptiveParameters n k)
    (hn' : n' <= n) (q c0 : Nat) (U : Nat -> Fin n -> Real)
    (hU : forall b i, |U b i| <= 1) (g : Fin k)
    (h : History n k T) (hsupp : sparseHistoryInFeedbackSupport T h) :
    |sparseObservableGroupMax hprod hr sigma V hn' q c0 U g T h| <=
      (T : Real) := by
  let G := sparsePartitionGroup hprod sigma g
  have hG : G.Nonempty := sparsePartitionGroup_nonempty hprod hr sigma g
  have hcoord : forall j : Fin n',
      |sparseObservableCoordinateScore V hn' q c0 U j T h| <= (T : Real) :=
    fun j => sparseObservableCoordinateScore_abs_le V hn' U hU j T h hsupp
  have hupp : G.sup' hG
      (fun j => sparseObservableCoordinateScore V hn' q c0 U j T h) <=
      (T : Real) := by
    apply Finset.sup'_le hG
    intro j hj
    exact (abs_le.mp (hcoord j)).2
  have hlow : -(T : Real) <= G.sup' hG
      (fun j => sparseObservableCoordinateScore V hn' q c0 U j T h) := by
    exact Finset.le_sup'_of_le _ hG.choose_spec
      (abs_le.mp (hcoord hG.choose)).1
  exact (abs_le).2 <| by
    simpa [sparseObservableGroupMax, G] using And.intro hlow hupp

theorem sparseHistoryGamma_abs_le
    {n n' k r T : Nat} (hk : 1 <= k)
    (hprod : n' = k * r) (hr : 0 < r)
    (sigma : Equiv.Perm (Fin n')) (V : SparseAdaptiveParameters n k)
    (hn' : n' <= n) (q c0 : Nat) (U : Nat -> Fin n -> Real)
    (hU : forall b i, |U b i| <= 1)
    (h : History n k T) (hsupp : sparseHistoryInFeedbackSupport T h) :
    |sparseHistoryGamma hprod hr sigma V hn' q c0 U T h| <=
      2 * (k : Real) * (T : Real) := by
  have hgroups :
      |∑ g : Fin k,
          sparseObservableGroupMax hprod hr sigma V hn' q c0 U g T h| <=
        (k : Real) * (T : Real) := by
    calc
      |∑ g : Fin k,
          sparseObservableGroupMax hprod hr sigma V hn' q c0 U g T h| <=
          ∑ g : Fin k,
            |sparseObservableGroupMax hprod hr sigma V hn' q c0 U g T h| :=
        Finset.abs_sum_le_sum_abs _ _
      _ <= ∑ _g : Fin k, (T : Real) := by
        exact Finset.sum_le_sum fun g _ =>
            sparseObservableGroupMax_abs_le hprod hr sigma V hn' q c0 U hU g h hsupp
      _ = (k : Real) * (T : Real) := by simp
  have hlearner := sparseObservableLearnerScore_abs_le
    (n' := n') (q := q) (c0 := c0)
      hk V U hU T h hsupp
  unfold sparseHistoryGamma
  calc
    |(∑ g : Fin k,
          sparseObservableGroupMax hprod hr sigma V hn' q c0 U g T h) -
        sparseObservableLearnerScore V n' q c0 U T h| <=
      |∑ g : Fin k,
          sparseObservableGroupMax hprod hr sigma V hn' q c0 U g T h| +
        |sparseObservableLearnerScore V n' q c0 U T h| := by
      simpa only [sub_eq_add_neg, abs_neg] using
        (abs_add_le
          (∑ g : Fin k,
            sparseObservableGroupMax hprod hr sigma V hn' q c0 U g T h)
          (-sparseObservableLearnerScore V n' q c0 U T h))
    _ <= (k : Real) * (T : Real) + (k : Real) * (T : Real) :=
      add_le_add hgroups hlearner
    _ = 2 * (k : Real) * (T : Real) := by ring

/-! ## The finite maximizer construction -/

/-- Choosing one member from every group gives a `k`-set.  Consequently the
sum of the group maxima is below the maximum over all exact `k`-sets. -/
theorem sum_sparsePartitionGroup_sup_le_actionSup
    {n' k r : Nat} (hprod : n' = k * r) (hr : 0 < r)
    (sigma : Equiv.Perm (Fin n')) (score : Fin n' -> Real) :
    (∑ g : Fin k,
        (sparsePartitionGroup hprod sigma g).sup'
          (sparsePartitionGroup_nonempty hprod hr sigma g) score) <=
      (iSup fun J : MSetAction n' k => ∑ j ∈ J.1, score j) := by
  classical
  let pick : Fin k -> Fin n' := fun g =>
    Classical.choose (Finset.exists_mem_eq_sup'
      (sparsePartitionGroup_nonempty hprod hr sigma g) score)
  have pick_mem : forall g,
      pick g ∈ sparsePartitionGroup hprod sigma g := fun g =>
    (Classical.choose_spec (Finset.exists_mem_eq_sup'
      (sparsePartitionGroup_nonempty hprod hr sigma g) score)).1
  have pick_eq : forall g,
      (sparsePartitionGroup hprod sigma g).sup'
          (sparsePartitionGroup_nonempty hprod hr sigma g) score = score (pick g) :=
    fun g => (Classical.choose_spec (Finset.exists_mem_eq_sup'
      (sparsePartitionGroup_nonempty hprod hr sigma g) score)).2
  have pick_injective : Function.Injective pick := by
    intro g l hgl
    have hglabel : sparsePartitionLabel hprod sigma (pick g) = g := by
      simpa [sparsePartitionGroup] using pick_mem g
    have hllabel : sparsePartitionLabel hprod sigma (pick l) = l := by
      simpa [sparsePartitionGroup] using pick_mem l
    exact Fin.ext <| congrArg Fin.val <| hglabel.symm.trans <| by
      rw [hgl]
      exact hllabel
  let J : MSetAction n' k :=
    ⟨Finset.univ.image pick, by
      rw [Finset.card_image_of_injective _ pick_injective]
      simp⟩
  letI : Nonempty (MSetAction n' k) := ⟨J⟩
  have hJ : (∑ j ∈ J.1, score j) <=
      (iSup fun K : MSetAction n' k => ∑ j ∈ K.1, score j) :=
    le_ciSup (Finite.bddAbove_range
      (fun K : MSetAction n' k => ∑ j ∈ K.1, score j)) J
  calc
    (∑ g : Fin k,
        (sparsePartitionGroup hprod sigma g).sup'
          (sparsePartitionGroup_nonempty hprod hr sigma g) score) =
        ∑ g : Fin k, score (pick g) := by
      apply Finset.sum_congr rfl
      intro g hg
      exact pick_eq g
    _ = ∑ j ∈ J.1, score j := by
      dsimp [J]
      rw [Finset.sum_image]
      exact pick_injective.injOn
    _ <= (iSup fun K : MSetAction n' k => ∑ j ∈ K.1, score j) := hJ

/-- A selected coordinate in every group is bounded by the corresponding
group maximum.  This is the pointwise direction used before choosing the
maximizers. -/
theorem sum_selectedCoordinateScore_le_groupMax
    {n' k r : Nat} (hprod : n' = k * r) (hr : 0 < r)
    (sigma : Equiv.Perm (Fin n')) (score : Fin n' -> Real)
    (selected : Fin k -> Fin n')
    (hselected : forall g, selected g ∈ sparsePartitionGroup hprod sigma g) :
    (∑ g : Fin k, score (selected g)) <=
      ∑ g : Fin k,
        (sparsePartitionGroup hprod sigma g).sup'
          (sparsePartitionGroup_nonempty hprod hr sigma g) score := by
  exact Finset.sum_le_sum fun g _ => Finset.le_sup' score (hselected g)

/-! ## Joint hidden-table observable -/

private theorem measurable_finset_pointwise_sup'
    {Omega I : Type*} [MeasurableSpace Omega]
    (s : Finset I) (hs : s.Nonempty) (f : I -> Omega -> Real)
    (hf : ∀ i ∈ s, Measurable (f i)) :
    Measurable (fun omega => s.sup' hs (fun i => f i omega)) := by
  have hm : Measurable (s.sup' hs f) := Finset.measurable_sup' hs hf
  have heq : s.sup' hs f =
      (fun omega => s.sup' hs (fun i => f i omega)) := by
    funext omega
    exact Finset.apply_sup'_eq_sup'_comp hs
      (fun g : Omega -> Real => g omega)
      (fun (_ _ : Omega -> Real) => rfl)
  rw [← heq]
  exact hm

set_option maxHeartbeats 2000000 in
-- The recursive dependent history type makes joint hidden/history measurability expensive.
/-- Joint measurability of a coordinate score when both the hidden table and
the history vary. -/
theorem measurable_sparseFamilyObservableCoordinateScore
    {Omega : Type*} [MeasurableSpace Omega]
    {n n' k : Nat} (F : SparseAdaptiveParameterFamily Omega n k)
    (U : Omega -> Nat -> Fin n -> Real)
    (hU : forall b i, Measurable (fun omega => U omega b i))
    (hn' : n' <= n) (q c0 : Nat) (j : Fin n') : forall T,
    Measurable (fun z : Omega × History n k T =>
      sparseObservableCoordinateScore (F.at z.1) hn' q c0 (U z.1) j T z.2) := by
  intro T
  induction T with
  | zero => exact measurable_const
  | succ t ih =>
      have hprev : Measurable (fun z : Omega × History n k (t + 1) =>
          sparseObservableCoordinateScore (F.at z.1) hn' q c0 (U z.1) j t z.2.1) :=
        ih.comp (measurable_fst.prodMk (measurable_fst.comp measurable_snd))
      have htable : Measurable (fun z : Omega × History n k (t + 1) =>
          U z.1 (t / q) (sparseSignalCoordinate hn' j)) :=
        (hU (t / q) (sparseSignalCoordinate hn' j)).comp measurable_fst
      have hactive : Measurable (fun z : Omega × History n k (t + 1) =>
          sparseActive q c0 (sparseSignalCoordinate hn' j) t z.2.1) :=
        (measurable_sparseActive (sparseSignalCoordinate hn' j) t).comp
          (measurable_fst.comp measurable_snd)
      have hparameter : Measurable (fun z : Omega × History n k (t + 1) =>
          F.value t z.1 z.2.1 z.2.2.1) :=
        (F.measurable_value t).comp <|
          (measurable_fst.prodMk (measurable_fst.comp measurable_snd)).prodMk
            (measurable_fst.comp (measurable_snd.comp measurable_snd))
      have hfeedback : Measurable (fun z : Omega × History n k (t + 1) =>
          z.2.2.2) := measurable_snd.comp (measurable_snd.comp measurable_snd)
      have hpair : Measurable (fun z : Omega × History n k (t + 1) =>
          (F.value t z.1 z.2.1 z.2.2.1, z.2.2.2)) :=
        hparameter.prodMk hfeedback
      have hshape : Measurable (fun z : Omega × History n k (t + 1) =>
          feedbackScoreShape (F.value t z.1 z.2.1 z.2.2.1) z.2.2.2) := by
        exact measurable_feedbackScoreShape_uncurry.comp hpair
      simp only [sparseObservableCoordinateScore_succ,
        SparseAdaptiveParameterFamily.at]
      convert hprev.add ((htable.mul hactive).mul hshape) using 1 <;> rfl

set_option maxHeartbeats 2000000 in
-- The learner score adds a varying finite action sum to the same dependent recursion.
/-- Joint measurability of the observable learner score. -/
theorem measurable_sparseFamilyObservableLearnerScore
    {Omega : Type*} [MeasurableSpace Omega]
    {n k : Nat} (F : SparseAdaptiveParameterFamily Omega n k)
    (U : Omega -> Nat -> Fin n -> Real)
    (hU : forall b i, Measurable (fun omega => U omega b i))
    (n' q c0 : Nat) : forall T,
    Measurable (fun z : Omega × History n k T =>
      sparseObservableLearnerScore (F.at z.1) n' q c0 (U z.1) T z.2) := by
  intro T
  induction T with
  | zero => exact measurable_const
  | succ t ih =>
      have hprevMap : Measurable (fun z : Omega × History n k (t + 1) =>
          (z.1, z.2.1)) :=
        measurable_fst.prodMk (measurable_fst.comp measurable_snd)
      have hprev : Measurable (fun z : Omega × History n k (t + 1) =>
          sparseObservableLearnerScore (F.at z.1) n' q c0 (U z.1) t z.2.1) :=
        ih.comp hprevMap
      have hitem : Measurable (fun z : Omega × History n k t =>
          fun i : Fin n => sparseActive q c0 i t z.2 *
            sparseSignalWeight n' q (U z.1) t i) := by
        refine Measurable.of_eval fun i => ?_
        have ha : Measurable (fun z : Omega × History n k t =>
            sparseActive q c0 i t z.2) :=
          (measurable_sparseActive i t).comp measurable_snd
        have hw : Measurable (fun z : Omega × History n k t =>
            sparseSignalWeight n' q (U z.1) t i) := by
          by_cases hi : i.1 < n'
          · simp only [sparseSignalWeight, hi, if_true]
            exact (hU (t / q) i).comp measurable_fst
          · simp only [sparseSignalWeight, hi, if_false]
            exact measurable_const
        exact ha.mul hw
      have hscore : Measurable (fun z : Omega × History n k (t + 1) =>
          sparseActionScore n' q c0 (U z.1) t z.2.1 z.2.2.1) := by
        exact (measurable_actionLoss_joint hitem).comp <|
          hprevMap.prodMk
            (measurable_fst.comp (measurable_snd.comp measurable_snd))
      have hparameter : Measurable (fun z : Omega × History n k (t + 1) =>
          F.value t z.1 z.2.1 z.2.2.1) :=
        (F.measurable_value t).comp <|
          hprevMap.prodMk
            (measurable_fst.comp (measurable_snd.comp measurable_snd))
      have hfeedback : Measurable (fun z : Omega × History n k (t + 1) =>
          z.2.2.2) := measurable_snd.comp (measurable_snd.comp measurable_snd)
      have hpair : Measurable (fun z : Omega × History n k (t + 1) =>
          (F.value t z.1 z.2.1 z.2.2.1, z.2.2.2)) :=
        hparameter.prodMk hfeedback
      have hshape : Measurable (fun z : Omega × History n k (t + 1) =>
          feedbackScoreShape (F.value t z.1 z.2.1 z.2.2.1) z.2.2.2) := by
        exact measurable_feedbackScoreShape_uncurry.comp hpair
      simp only [sparseObservableLearnerScore_succ,
        SparseAdaptiveParameterFamily.at]
      convert hprev.add (hshape.mul hscore) using 1 <;> rfl

/-- `Gamma` on the genuine hidden-table/history product space. -/
def sparseGamma
    {n n' k r B : Nat} (hk : 1 <= k)
    (eta : Real) (heta0 : 0 <= eta) (heta : eta <= (1 : Real) / 16)
    (q c0 : Nat) (hn' : n' <= n) (hprod : n' = k * r) (hr : 0 < r)
    (sigma : Equiv.Perm (Fin n')) (T : Nat) :
    SparseHiddenTable B n × History n k T -> Real := fun z =>
  sparseHistoryGamma hprod hr sigma
    ((sparseHiddenTableParameterFamily hk eta heta0 heta n' q c0 B).at z.1)
    hn' q c0 (sparseHiddenTableU z.1) T z.2

theorem measurable_sparseGamma
    {n n' k r B : Nat} (hk : 1 <= k)
    (eta : Real) (heta0 : 0 <= eta) (heta : eta <= (1 : Real) / 16)
    (q c0 : Nat) (hn' : n' <= n) (hprod : n' = k * r) (hr : 0 < r)
    (sigma : Equiv.Perm (Fin n')) (T : Nat) :
    Measurable (sparseGamma (B := B) hk eta heta0 heta q c0 hn'
      hprod hr sigma T) := by
  let F : SparseAdaptiveParameterFamily (SparseHiddenTable B n) n k :=
    sparseHiddenTableParameterFamily hk eta heta0 heta n' q c0 B
  let U : SparseHiddenTable B n -> Nat -> Fin n -> Real := sparseHiddenTableU
  have hU : forall b i, Measurable (fun table : SparseHiddenTable B n => U table b i) :=
    fun b i => measurable_sparseHiddenTableU B n b i
  have hcoord : forall j : Fin n', Measurable
      (fun z : SparseHiddenTable B n × History n k T =>
        sparseObservableCoordinateScore (F.at z.1) hn' q c0 (U z.1) j T z.2) :=
    fun j => measurable_sparseFamilyObservableCoordinateScore F U hU hn' q c0 j T
  have hgroup : forall g : Fin k, Measurable
      (fun z : SparseHiddenTable B n × History n k T =>
        (sparsePartitionGroup hprod sigma g).sup'
          (sparsePartitionGroup_nonempty hprod hr sigma g)
          (fun j => sparseObservableCoordinateScore
            (F.at z.1) hn' q c0 (U z.1) j T z.2)) := fun g =>
    measurable_finset_pointwise_sup' _
      (sparsePartitionGroup_nonempty hprod hr sigma g) _
      (fun j hj => hcoord j)
  have hlearner : Measurable
      (fun z : SparseHiddenTable B n × History n k T =>
        sparseObservableLearnerScore (F.at z.1) n' q c0 (U z.1) T z.2) :=
    measurable_sparseFamilyObservableLearnerScore F U hU n' q c0 T
  unfold sparseGamma sparseHistoryGamma sparseObservableGroupMax
  exact (Finset.measurable_sum _ fun g _ => hgroup g).sub hlearner

theorem sparseGamma_abs_le_on_support
    {n n' k r B T : Nat} (hk : 1 <= k)
    (eta : Real) (heta0 : 0 <= eta) (heta : eta <= (1 : Real) / 16)
    (q c0 : Nat) (hn' : n' <= n) (hprod : n' = k * r) (hr : 0 < r)
    (sigma : Equiv.Perm (Fin n'))
    (z : SparseHiddenTable B n × History n k T)
    (hsupp : sparseHistoryInFeedbackSupport T z.2) :
    |sparseGamma hk eta heta0 heta q c0 hn' hprod hr sigma T z| <=
      2 * (k : Real) * (T : Real) := by
  exact sparseHistoryGamma_abs_le hk hprod hr sigma
    ((sparseHiddenTableParameterFamily hk eta heta0 heta n' q c0 B).at z.1)
    hn' q c0 (sparseHiddenTableU z.1)
      (sparseHiddenTableU_abs_le_one z.1) z.2 hsupp

theorem ae_sparseGamma_abs_le
    {n n' k r B T : Nat} (hk : 1 <= k)
    (eta : Real) (heta0 : 0 <= eta) (heta : eta <= (1 : Real) / 16)
    (q c0 : Nat) (hn' : n' <= n) (hprod : n' = k * r) (hr : 0 < r)
    (sigma : Equiv.Perm (Fin n')) (P : Policy n k) :
    ∀ᵐ z ∂sparseJointLaw (sparseHiddenTableMeasure B n) P
        (sparseHiddenTableParameterFamily hk eta heta0 heta n' q c0 B) T,
      |sparseGamma hk eta heta0 heta q c0 hn' hprod hr sigma T z| <=
        2 * (k : Real) * (T : Real) := by
  filter_upwards [ae_sparseJointLaw_history_support
    (sparseHiddenTableMeasure B n) P
      (sparseHiddenTableParameterFamily hk eta heta0 heta n' q c0 B) T] with z hz
  exact sparseGamma_abs_le_on_support hk eta heta0 heta q c0 hn'
    hprod hr sigma z hz

theorem integrable_sparseGamma
    {n n' k r B T : Nat} (hk : 1 <= k)
    (eta : Real) (heta0 : 0 <= eta) (heta : eta <= (1 : Real) / 16)
    (q c0 : Nat) (hn' : n' <= n) (hprod : n' = k * r) (hr : 0 < r)
    (sigma : Equiv.Perm (Fin n')) (P : Policy n k) :
    Integrable (sparseGamma hk eta heta0 heta q c0 hn' hprod hr sigma T)
      (sparseJointLaw (sparseHiddenTableMeasure B n) P
        (sparseHiddenTableParameterFamily hk eta heta0 heta n' q c0 B) T) := by
  let mu := sparseJointLaw (sparseHiddenTableMeasure B n) P
    (sparseHiddenTableParameterFamily hk eta heta0 heta n' q c0 B) T
  letI : IsProbabilityMeasure mu := by
    dsimp [mu, sparseJointLaw]
    infer_instance
  apply Integrable.mono' (integrable_const (2 * (k : Real) * (T : Real)))
  · exact (measurable_sparseGamma (B := B) hk eta heta0 heta q c0 hn'
      hprod hr sigma T).aestronglyMeasurable
  · simpa only [Real.norm_eq_abs, mu] using
      ae_sparseGamma_abs_le (B := B) hk eta heta0 heta q c0 hn'
        hprod hr sigma P

/-- Fubini form of the base-law expectation: sample the hidden table first,
then integrate over its conditional adaptive history law. -/
theorem integral_sparseGamma_eq_iterated
    {n n' k r B T : Nat} (hk : 1 <= k)
    (eta : Real) (heta0 : 0 <= eta) (heta : eta <= (1 : Real) / 16)
    (q c0 : Nat) (hn' : n' <= n) (hprod : n' = k * r) (hr : 0 < r)
    (sigma : Equiv.Perm (Fin n')) (P : Policy n k) :
    (∫ z, sparseGamma hk eta heta0 heta q c0 hn' hprod hr sigma T z
        ∂sparseJointLaw (sparseHiddenTableMeasure B n) P
          (sparseHiddenTableParameterFamily hk eta heta0 heta n' q c0 B) T) =
      ∫ table, ∫ h,
        sparseGamma hk eta heta0 heta q c0 hn' hprod hr sigma T (table, h)
          ∂(sparseAdaptiveProcess P
            ((sparseHiddenTableParameterFamily hk eta heta0 heta
              n' q c0 B).at table)).law T
        ∂sparseHiddenTableMeasure B n := by
  unfold sparseJointLaw
  rw [Measure.integral_compProd
    (integrable_sparseGamma (B := B) hk eta heta0 heta q c0 hn'
      hprod hr sigma P)]
  simp_rw [sparseFamilyLawKernel_apply]

/-- The history marginal of a joint hidden-state experiment is the mixture of
its conditional adaptive history laws. -/
theorem sparseJointLaw_map_snd
    {Omega : Type*} [MeasurableSpace Omega]
    {n k T : Nat} (mu : Measure Omega) [SFinite mu]
    (P : Policy n k) (F : SparseAdaptiveParameterFamily Omega n k) :
    Measure.map Prod.snd (sparseJointLaw mu P F T) =
      sparseFamilyLawKernel P F T ∘ₘ mu := by
  rw [← Measure.snd]
  unfold sparseJointLaw
  exact Measure.snd_compProd _ _

/-! ## Bridge to the fixed source table -/

/-- After a hidden table and noise table are fixed, the exact source-table
maximum score minus the learner score dominates the observable `Gamma`.
The only history hypothesis is the protocol-support fact supplied by the
ordinary run law. -/
theorem sparseGamma_le_sparseMaxSignalScore_sub_learner_of_compatible
    {n n' k r B T : Nat} (hk : 1 <= k)
    (eta : Real) (heta0 : 0 <= eta) (heta : eta <= (1 : Real) / 16)
    (q c0 : Nat) (hn' : n' <= n) (hprod : n' = k * r) (hr : 0 < r)
    (sigma : Equiv.Perm (Fin n')) (table : SparseHiddenTable B n)
    (Z : Nat -> Real) (hZ : forall t, Z t ∈ Icc (-1 : Real) 1)
    (h : History n k T)
    (hcompat : SparseProtocolHistoryCompatible
      (sparseLossProcess hk eta heta0 heta n' q c0 T
        (sparseHiddenTableU table) (sparseHiddenTableU_abs_le_one table)
        Z hZ) T h) :
    sparseGamma hk eta heta0 heta q c0 hn' hprod hr sigma T
        (table, (sparseActualHistoryEquiv n k T).symm h) <=
      sparseMaxSignalScore q c0 hn' (sparseHiddenTableU table) Z T h -
        sparseLearnerScore n' q c0 (sparseHiddenTableU table) Z T h := by
  let U := sparseHiddenTableU table
  let V := sparseAdaptiveParametersOfTable hk eta heta0 heta n' q c0 U
    (sparseHiddenTableU_abs_le_one table)
  have hcoordinate : forall j : Fin n',
      sparseObservableCoordinateScore V hn' q c0 U j T
          ((sparseActualHistoryEquiv n k T).symm h) =
        sparseCoordinateScore n' q c0 U Z
          (sparseSignalCoordinate hn' j) T h := fun j =>
    sparseObservableCoordinateScore_centered_eq_table hk hn' eta heta0 heta
      U (sparseHiddenTableU_abs_le_one table) Z hZ j T h le_rfl hcompat
  have hlearner :
      sparseObservableLearnerScore V n' q c0 U T
          ((sparseActualHistoryEquiv n k T).symm h) =
        sparseLearnerScore n' q c0 U Z T h :=
    sparseObservableLearnerScore_centered_eq_table hk eta heta0 heta
      U (sparseHiddenTableU_abs_le_one table) Z hZ T h le_rfl hcompat
  have hgroups :
      (∑ g : Fin k,
        (sparsePartitionGroup hprod sigma g).sup'
          (sparsePartitionGroup_nonempty hprod hr sigma g)
          (fun j => sparseCoordinateScore n' q c0 U Z
            (sparseSignalCoordinate hn' j) T h)) <=
        sparseMaxSignalScore q c0 hn' U Z T h := by
    simpa only [sparseMaxSignalScore, sparseSignalScore] using
      sum_sparsePartitionGroup_sup_le_actionSup hprod hr sigma
        (fun j : Fin n' => sparseCoordinateScore n' q c0 U Z
          (sparseSignalCoordinate hn' j) T h)
  have hgamma :
      sparseGamma hk eta heta0 heta q c0 hn' hprod hr sigma T
          (table, (sparseActualHistoryEquiv n k T).symm h) =
        (∑ g : Fin k,
          (sparsePartitionGroup hprod sigma g).sup'
            (sparsePartitionGroup_nonempty hprod hr sigma g)
            (fun j => sparseCoordinateScore n' q c0 U Z
              (sparseSignalCoordinate hn' j) T h)) -
          sparseLearnerScore n' q c0 U Z T h := by
    unfold sparseGamma sparseHistoryGamma sparseObservableGroupMax
    rw [sparseHiddenTableParameterFamily_at]
    change
      (∑ g : Fin k,
          (sparsePartitionGroup hprod sigma g).sup'
            (sparsePartitionGroup_nonempty hprod hr sigma g)
            (fun j => sparseObservableCoordinateScore V hn' q c0 U j T
              ((sparseActualHistoryEquiv n k T).symm h))) -
          sparseObservableLearnerScore V n' q c0 U T
            ((sparseActualHistoryEquiv n k T).symm h) = _
    rw [hlearner]
    congr 1
    apply Finset.sum_congr rfl
    intro g hg
    apply Finset.sup'_congr
      (sparsePartitionGroup_nonempty hprod hr sigma g) rfl
    intro j hj
    exact hcoordinate j
  rw [hgamma]
  exact sub_le_sub_right hgroups _

/-- Membership in a lower-tail event for `Gamma` implies membership in the
corresponding fixed-table maximum-score event. -/
theorem sparseGamma_event_implies_maxScoreGap
    {n n' k r B T : Nat} (hk : 1 <= k)
    (eta : Real) (heta0 : 0 <= eta) (heta : eta <= (1 : Real) / 16)
    (q c0 : Nat) (hn' : n' <= n) (hprod : n' = k * r) (hr : 0 < r)
    (sigma : Equiv.Perm (Fin n')) (table : SparseHiddenTable B n)
    (Z : Nat -> Real) (hZ : forall t, Z t ∈ Icc (-1 : Real) 1)
    (h : History n k T)
    (hcompat : SparseProtocolHistoryCompatible
      (sparseLossProcess hk eta heta0 heta n' q c0 T
        (sparseHiddenTableU table) (sparseHiddenTableU_abs_le_one table)
        Z hZ) T h) (threshold : Real)
    (hGamma : threshold <= sparseGamma hk eta heta0 heta q c0 hn'
      hprod hr sigma T (table, (sparseActualHistoryEquiv n k T).symm h)) :
    threshold <=
      sparseMaxSignalScore q c0 hn' (sparseHiddenTableU table) Z T h -
        sparseLearnerScore n' q c0 (sparseHiddenTableU table) Z T h :=
  hGamma.trans <|
    sparseGamma_le_sparseMaxSignalScore_sub_learner_of_compatible
      hk eta heta0 heta q c0 hn' hprod hr sigma table Z hZ h hcompat

/-- A single downstream interface for the observable sparse maximum.  It
packages the groupwise domination, joint measurability and integrability, the
uniform almost-sure upper bound, and the fixed-table event implication. -/
theorem sparseGamma_joint_certificate
    {n n' k r B T : Nat} (hk : 1 <= k)
    (eta : Real) (heta0 : 0 <= eta) (heta : eta <= (1 : Real) / 16)
    (q c0 : Nat) (hn' : n' <= n) (hprod : n' = k * r) (hr : 0 < r)
    (sigma : Equiv.Perm (Fin n')) (P : Policy n k) :
    (forall (z : SparseHiddenTable B n × History n k T)
        (selected : Fin k -> Fin n'),
      (forall g, selected g ∈ sparsePartitionGroup hprod sigma g) ->
      (∑ g : Fin k,
          sparseObservableCoordinateScore
            ((sparseHiddenTableParameterFamily hk eta heta0 heta
              n' q c0 B).at z.1) hn' q c0 (sparseHiddenTableU z.1)
              (selected g) T z.2) <=
        ∑ g : Fin k,
          sparseObservableGroupMax hprod hr sigma
            ((sparseHiddenTableParameterFamily hk eta heta0 heta
              n' q c0 B).at z.1) hn' q c0 (sparseHiddenTableU z.1) g T z.2) ∧
    Measurable (sparseGamma (B := B) hk eta heta0 heta q c0 hn'
      hprod hr sigma T) ∧
    Integrable (sparseGamma hk eta heta0 heta q c0 hn' hprod hr sigma T)
      (sparseJointLaw (sparseHiddenTableMeasure B n) P
        (sparseHiddenTableParameterFamily hk eta heta0 heta n' q c0 B) T) ∧
    (∀ᵐ z ∂sparseJointLaw (sparseHiddenTableMeasure B n) P
        (sparseHiddenTableParameterFamily hk eta heta0 heta n' q c0 B) T,
      sparseGamma hk eta heta0 heta q c0 hn' hprod hr sigma T z <=
        2 * (k : Real) * (T : Real)) ∧
    (forall (table : SparseHiddenTable B n) (Z : Nat -> Real)
        (hZ : forall t, Z t ∈ Icc (-1 : Real) 1) (h : History n k T),
      SparseProtocolHistoryCompatible
          (sparseLossProcess hk eta heta0 heta n' q c0 T
            (sparseHiddenTableU table) (sparseHiddenTableU_abs_le_one table)
            Z hZ) T h ->
      forall threshold : Real,
        threshold <= sparseGamma hk eta heta0 heta q c0 hn' hprod hr sigma T
          (table, (sparseActualHistoryEquiv n k T).symm h) ->
        threshold <=
          sparseMaxSignalScore q c0 hn' (sparseHiddenTableU table) Z T h -
            sparseLearnerScore n' q c0 (sparseHiddenTableU table) Z T h) := by
  refine ⟨?_, measurable_sparseGamma (B := B) hk eta heta0 heta q c0 hn'
    hprod hr sigma T, integrable_sparseGamma (B := B) hk eta heta0 heta
      q c0 hn' hprod hr sigma P, ?_, ?_⟩
  · intro z selected hselected
    simpa only [sparseObservableGroupMax] using
      sum_selectedCoordinateScore_le_groupMax hprod hr sigma
        (fun j : Fin n' =>
          sparseObservableCoordinateScore
            ((sparseHiddenTableParameterFamily hk eta heta0 heta
              n' q c0 B).at z.1) hn' q c0 (sparseHiddenTableU z.1) j T z.2)
        selected hselected
  · filter_upwards [ae_sparseGamma_abs_le (B := B) hk eta heta0 heta
      q c0 hn' hprod hr sigma P] with z hz
    exact (le_abs_self _).trans hz
  · intro table Z hZ h hcompat threshold hthreshold
    exact sparseGamma_event_implies_maxScoreGap hk eta heta0 heta q c0 hn'
      hprod hr sigma table Z hZ h hcompat threshold hthreshold

end

end MsetsLower.Lower.Sparse
