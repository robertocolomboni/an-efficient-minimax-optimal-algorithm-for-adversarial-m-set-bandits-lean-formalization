import MsetsLower.Lower.Dense.Bridge
import MsetsLower.Lower.Dense.Table
import MsetsLower.Lower.ParametricRegret
import MsetsLower.Lower.Statement
import Mathlib.MeasureTheory.Integral.Lebesgue.Countable
import Mathlib.Analysis.Complex.ExponentialBounds

/-!
# Fixing the iid table in the dense construction

This file identifies the table-mixture experiment with the genuine latent
paired process, fixes one deterministic table, and performs the literal
threshold comparison in `prop:lower-bounded-action`.
-/

namespace MsetsLower.Lower.Dense

open MsetsLower MsetsLower.Lower
open MeasureTheory ProbabilityTheory
open scoped BigOperators ENNReal NNReal ProbabilityTheory

noncomputable section

/-! ## Measurable table-to-latent map -/

/-- The reconstruction map is jointly measurable in the finite table and the
observable history. -/
theorem measurable_denseLatentHistory_joint {n k T : Nat} (hk : 1 ≤ k) :
    ∀ t : Nat, Measurable
      (fun input : DenseItemTable k T × History n k t =>
        denseLatentHistory hk input.1 t input.2) := by
  intro t
  induction t with
  | zero => exact measurable_const
  | succ t ih =>
      have hprefix : Measurable
          (fun input : DenseItemTable k T × History n k (t + 1) =>
            (input.1, input.2.1)) :=
        measurable_fst.prodMk (measurable_fst.comp measurable_snd)
      have haction : Measurable
          (fun input : DenseItemTable k T × History n k (t + 1) =>
            input.2.2.1) :=
        measurable_fst.comp (measurable_snd.comp measurable_snd)
      have hitem : Measurable
          (fun input : DenseItemTable k T × History n k (t + 1) =>
            denseTableItem hk input.1 t) :=
        (measurable_of_finite (denseTableItem hk · t)).comp measurable_fst
      exact (ih.comp hprefix).prodMk (haction.prodMk hitem)

def denseMixtureToLatent {n k T : Nat} (hk : 1 ≤ k) :
    DenseItemTable k T × History n k T → PairedJointHistory n k T :=
  fun input => denseLatentHistory hk input.1 T input.2

theorem measurable_denseMixtureToLatent {n k T : Nat} (hk : 1 ≤ k) :
    Measurable (denseMixtureToLatent (n := n) (T := T) hk) :=
  measurable_denseLatentHistory_joint hk T

/-! ## Singleton recursions -/

/-- One latent round has the product atom expected from first sampling the
policy action and then the independent paired item. -/
theorem pairedJointRoundKernel_apply_singleton
    {n k : Nat} (P : Policy n k) (hk : 1 ≤ k)
    (hD : 2 * k ≤ n) (θ : Fin k → PairSign) (ε : Real)
    (hε0 : 0 ≤ ε) (hε1 : ε ≤ 1) (t : Nat)
    (h : PairedJointHistory n k t) (A : MSetAction n k) (J : PairItem k) :
    pairedJointRoundKernel P hk hD θ ε hε0 hε1 t h {(A, J)} =
      P.kernel t (pairedJointObservedHistory hD t h) {A} *
        (pairedPMF hk θ ε hε0 hε1).toMeasure {J} := by
  rw [pairedJointRoundKernel, Kernel.compProd_apply
    (MeasurableSet.singleton (A, J))]
  unfold pairedJointActionKernel
  rw [Kernel.comap_apply]
  rw [lintegral_fintype]
  classical
  rw [Finset.sum_eq_single A]
  · unfold pairedJointItemKernel
    rw [Kernel.const_apply]
    have hpre : Prod.mk A ⁻¹' ({(A, J)} : Set (MSetAction n k × PairItem k)) =
        {J} := by
      ext J'
      simp
    rw [hpre]
    exact mul_comm _ _
  · intro B _ hBA
    unfold pairedJointItemKernel
    rw [Kernel.const_apply]
    have hpre : Prod.mk B ⁻¹' ({(A, J)} : Set (MSetAction n k × PairItem k)) =
        ∅ := by
      ext J'
      simp [hBA]
    rw [hpre, measure_empty, zero_mul]
  · simp

/-- Singleton recursion for the genuine latent adaptive law. -/
theorem pairedJointLaw_apply_singleton_succ
    {n k : Nat} (P : Policy n k) (hk : 1 ≤ k)
    (hD : 2 * k ≤ n) (θ : Fin k → PairSign) (ε : Real)
    (hε0 : 0 ≤ ε) (hε1 : ε ≤ 1) (t : Nat)
    (h : PairedJointHistory n k t) (A : MSetAction n k) (J : PairItem k) :
    pairedJointLaw P hk hD θ ε hε0 hε1 (t + 1) {(h, (A, J))} =
      pairedJointLaw P hk hD θ ε hε0 hε1 t {h} *
        P.kernel t (pairedJointObservedHistory hD t h) {A} *
        (pairedPMF hk θ ε hε0 hε1).toMeasure {J} := by
  change (pairedJointLaw P hk hD θ ε hε0 hε1 t ⊗ₘ
      pairedJointRoundKernel P hk hD θ ε hε0 hε1 t)
      ({(h, (A, J))} : Set (PairedJointHistory n k t ×
        (MSetAction n k × PairItem k))) = _
  rw [Measure.compProd_apply
    (MeasurableSet.singleton (h, (A, J))), lintegral_fintype]
  classical
  rw [Finset.sum_eq_single h]
  · have hpre : Prod.mk h ⁻¹'
        ({(h, (A, J))} : Set (PairedJointHistory n k t ×
          (MSetAction n k × PairItem k))) = {(A, J)} := by
      ext z
      simp
    rw [hpre, pairedJointRoundKernel_apply_singleton]
    ring
  · intro h' _ hh'
    have hpre : Prod.mk h' ⁻¹'
        ({(h, (A, J))} : Set (PairedJointHistory n k t ×
          (MSetAction n k × PairItem k))) = ∅ := by
      ext z
      simp [hh']
    rw [hpre, measure_empty, zero_mul]
  · simp

/-! ## Item trajectories and their product mass -/

def pairedJointItemAt {n k : Nat} :
    (t : Nat) → PairedJointHistory n k t → Fin t → PairItem k
  | 0, _h, r => Fin.elim0 r
  | t + 1, h, r =>
      Fin.lastCases h.2.2 (fun i => pairedJointItemAt t h.1 i) r

@[simp] theorem pairedJointItemAt_succ_last {n k t : Nat}
    (h : PairedJointHistory n k t) (A : MSetAction n k) (J : PairItem k) :
    pairedJointItemAt (t + 1) (h, (A, J)) (Fin.last t) = J := by
  simp [pairedJointItemAt]

@[simp] theorem pairedJointItemAt_succ_castSucc {n k t : Nat}
    (h : PairedJointHistory n k t) (A : MSetAction n k) (J : PairItem k)
    (r : Fin t) :
    pairedJointItemAt (t + 1) (h, (A, J)) r.castSucc =
      pairedJointItemAt t h r := by
  simp [pairedJointItemAt]

def pairedJointItemTable {n k T : Nat}
    (h : PairedJointHistory n k T) : DenseItemTable k T :=
  pairedJointItemAt T h

theorem pairedJointItemAt_denseLatentHistory
    {n k T : Nat} (hk : 1 ≤ k) (table : DenseItemTable k T) :
    ∀ (t : Nat) (history : History n k t) (r : Fin t),
      pairedJointItemAt t (denseLatentHistory hk table t history) r =
        denseTableItem hk table r.1 := by
  intro t
  induction t with
  | zero =>
      intro history r
      exact Fin.elim0 r
  | succ t ih =>
      intro history r
      refine Fin.lastCases ?_ (fun i => ?_) r
      · simp [denseLatentHistory]
      · simp [denseLatentHistory, ih]

@[simp] theorem pairedJointItemTable_denseLatentHistory
    {n k T : Nat} (hk : 1 ≤ k) (table : DenseItemTable k T)
    (history : History n k T) :
    pairedJointItemTable (denseLatentHistory hk table T history) = table := by
  funext r
  rw [pairedJointItemTable, pairedJointItemAt_denseLatentHistory]
  exact denseTableItem_of_lt hk table r.2

theorem denseItemTableMeasure_apply_singleton_itemTable
    {n k T : Nat} (hk : 1 ≤ k) (θ : Fin k → PairSign)
    (ε : Real) (hε0 : 0 ≤ ε) (hε1 : ε ≤ 1)
    (h : PairedJointHistory n k T) :
    denseItemTableMeasure (T := T) hk θ ε hε0 hε1
        {pairedJointItemTable h} =
      ∏ r : Fin T,
        (pairedPMF hk θ ε hε0 hε1).toMeasure
          {pairedJointItemAt T h r} := by
  unfold denseItemTableMeasure pairedJointItemTable
  exact Measure.pi_singleton _ _

/-! ## The fixed-table run is supported on canonical feedback histories -/

def denseCanonicalHistory {n k T : Nat} (hD : 2 * k ≤ n) (hk : 1 ≤ k)
    (table : DenseItemTable k T) (t : Nat) (history : History n k t) :
    History n k t :=
  pairedJointObservedHistory hD t
    (denseLatentHistory hk table t history)

theorem measurable_denseCanonicalHistory {n k T : Nat}
    (hD : 2 * k ≤ n) (hk : 1 ≤ k)
    (table : DenseItemTable k T) (t : Nat) :
    Measurable (denseCanonicalHistory hD hk table t) :=
  (measurable_pairedJointObservedHistory hD t).comp
    (measurable_denseLatentHistory hk table t)

def denseHistoryConsistentSet {n k T : Nat} (hD : 2 * k ≤ n)
    (hk : 1 ≤ k) (table : DenseItemTable k T) (t : Nat) :
    Set (History n k t) :=
  {history | denseCanonicalHistory hD hk table t history = history}

theorem measurableSet_denseHistoryConsistentSet {n k T : Nat}
    (hD : 2 * k ≤ n) (hk : 1 ≤ k)
    (table : DenseItemTable k T) : ∀ t : Nat,
    MeasurableSet (denseHistoryConsistentSet hD hk table t) := by
  intro t
  induction t with
  | zero =>
      simp [denseHistoryConsistentSet, denseCanonicalHistory,
        pairedJointObservedHistory]
  | succ t ih =>
      have hset : denseHistoryConsistentSet hD hk table (t + 1) =
          {history : History n k (t + 1) |
            history.1 ∈ denseHistoryConsistentSet hD hk table t ∧
            actionLoss history.2.1
              (pairedLoss hD (denseTableItem hk table t)) = history.2.2} := by
        ext history
        simp only [denseHistoryConsistentSet, Set.mem_setOf_eq]
        change
          (denseCanonicalHistory hD hk table t history.1,
              (history.2.1, actionLoss history.2.1
                (pairedLoss hD (denseTableItem hk table t)))) = history ↔ _
        rcases history with ⟨history, A, y⟩
        simp
      rw [hset]
      have hactionLoss : Measurable
          (fun history : History n k (t + 1) =>
            actionLoss history.2.1
              (pairedLoss hD (denseTableItem hk table t))) :=
        (measurable_of_finite
          (fun A : MSetAction n k =>
            actionLoss A (pairedLoss hD (denseTableItem hk table t)))).comp
          (measurable_fst.comp measurable_snd)
      exact (ih.preimage measurable_fst).inter
        (measurableSet_eq_fun hactionLoss
          (measurable_snd.comp measurable_snd))

theorem denseCanonicalHistory_extendRun
    {n k T : Nat} (hD : 2 * k ≤ n) (hk : 1 ≤ k)
    (table : DenseItemTable k T) (t : Nat) (history : History n k t)
    (A : MSetAction n k) :
    denseCanonicalHistory hD hk table (t + 1)
        (extendRun ((denseTableLossProcess hk hD T).at table) t (history, A)) =
      (denseCanonicalHistory hD hk table t history,
        (A, actionLoss A (pairedLoss hD (denseTableItem hk table t)))) := by
  rfl

theorem ae_roundKernel_denseHistoryConsistent
    {n k T : Nat} (P : Policy n k) (hD : 2 * k ≤ n)
    (hk : 1 ≤ k) (table : DenseItemTable k T) (t : Nat)
    (history : History n k t)
    (hconsistent : denseCanonicalHistory hD hk table t history = history) :
    ∀ᵐ history' ∂roundKernel P
        ((denseTableLossProcess hk hD T).at table) t history,
      denseCanonicalHistory hD hk table (t + 1) history' = history' := by
  let L := (denseTableLossProcess hk hD T).at table
  unfold roundKernel
  rw [Kernel.map_apply _ (measurable_extendRun L t) history]
  change ∀ᵐ history' ∂(actionHistoryKernel P t history).map
      (extendRun L t),
    history' ∈ denseHistoryConsistentSet hD hk table (t + 1)
  apply (ae_map_iff (measurable_extendRun L t).aemeasurable
    (measurableSet_denseHistoryConsistentSet hD hk table (t + 1))).2
  rw [actionHistoryKernel_apply]
  apply (ae_map_iff measurable_prodMk_left.aemeasurable
    ((measurableSet_denseHistoryConsistentSet hD hk table (t + 1)).preimage
      (measurable_extendRun L t))).2
  apply ae_of_all
  intro A
  change denseCanonicalHistory hD hk table (t + 1)
      (extendRun L t (history, A)) = extendRun L t (history, A)
  rw [denseCanonicalHistory_extendRun, hconsistent]
  rfl

theorem ae_runLaw_denseHistoryConsistent
    {n k T : Nat} (P : Policy n k) (hD : 2 * k ≤ n)
    (hk : 1 ≤ k) (table : DenseItemTable k T) :
    ∀ t : Nat, ∀ᵐ history ∂runLaw P
        ((denseTableLossProcess hk hD T).at table) t,
      denseCanonicalHistory hD hk table t history = history := by
  intro t
  induction t with
  | zero =>
      simp [runLaw, denseCanonicalHistory,
        pairedJointObservedHistory]
  | succ t ih =>
      rw [runLaw_succ]
      apply Measure.ae_comp_of_ae_ae
        (measurableSet_denseHistoryConsistentSet hD hk table (t + 1))
      filter_upwards [ih] with history hhistory
      exact ae_roundKernel_denseHistoryConsistent
        P hD hk table t history hhistory

theorem denseLatentHistory_observed_eq_of_items
    {n k T : Nat} (hk : 1 ≤ k) (hD : 2 * k ≤ n)
    (table : DenseItemTable k T) :
    ∀ (t : Nat) (h : PairedJointHistory n k t),
      (∀ r : Fin t,
        denseTableItem hk table r.1 = pairedJointItemAt t h r) →
      denseLatentHistory hk table t
          (pairedJointObservedHistory hD t h) = h := by
  intro t
  induction t with
  | zero =>
      intro h hitems
      rfl
  | succ t ih =>
      rintro ⟨h, A, J⟩ hitems
      have hprefix : ∀ r : Fin t,
          denseTableItem hk table r.1 = pairedJointItemAt t h r := by
        intro r
        simpa using hitems r.castSucc
      have hlast : denseTableItem hk table t = J := by
        simpa using hitems (Fin.last t)
      simp only [pairedJointObservedHistory, denseLatentHistory]
      rw [ih h hprefix, hlast]

@[simp] theorem denseLatentHistory_itemTable_observed
    {n k T : Nat} (hk : 1 ≤ k) (hD : 2 * k ≤ n)
    (h : PairedJointHistory n k T) :
    denseLatentHistory hk (pairedJointItemTable h) T
        (pairedJointObservedHistory hD T h) = h := by
  apply denseLatentHistory_observed_eq_of_items hk hD
  intro r
  rw [denseTableItem_of_lt hk (pairedJointItemTable h) r.2]
  rfl

/-- On the fixed-table run, a latent-history fiber has the same mass as the
single canonical observable history. -/
theorem runLaw_denseLatent_fiber_eq_singleton
    {n k T : Nat} (P : Policy n k) (hk : 1 ≤ k)
    (hD : 2 * k ≤ n) (table : DenseItemTable k T)
    (h : PairedJointHistory n k T)
    (htable : table = pairedJointItemTable h) :
    runLaw P ((denseTableLossProcess hk hD T).at table) T
        {history | denseLatentHistory hk table T history = h} =
      runLaw P ((denseTableLossProcess hk hD T).at table) T
        {pairedJointObservedHistory hD T h} := by
  apply measure_congr
  filter_upwards [ae_runLaw_denseHistoryConsistent P hD hk table T]
    with history hconsistent
  apply propext
  constructor
  · intro hlatent
    have hcanonical := congrArg (pairedJointObservedHistory hD T) hlatent
    change history = pairedJointObservedHistory hD T h
    calc
      history = denseCanonicalHistory hD hk table T history := hconsistent.symm
      _ = pairedJointObservedHistory hD T h := hcanonical
  · intro hsingleton
    have heq : history = pairedJointObservedHistory hD T h := by
      change history = pairedJointObservedHistory hD T h at hsingleton
      exact hsingleton
    subst history
    subst table
    exact denseLatentHistory_itemTable_observed hk hD h

theorem runLaw_denseTable_observed_singleton_succ
    {n k T : Nat} (P : Policy n k) (hk : 1 ≤ k)
    (hD : 2 * k ≤ n) (table : DenseItemTable k T) (t : Nat)
    (h : PairedJointHistory n k t) (A : MSetAction n k) (J : PairItem k)
    (hitem : denseTableItem hk table t = J) :
    runLaw P ((denseTableLossProcess hk hD T).at table) (t + 1)
        {pairedJointObservedHistory hD (t + 1) (h, (A, J))} =
      runLaw P ((denseTableLossProcess hk hD T).at table) t
          {pairedJointObservedHistory hD t h} *
        P.kernel t (pairedJointObservedHistory hD t h) {A} := by
  let L := (denseTableLossProcess hk hD T).at table
  let observed := pairedJointObservedHistory hD t h
  let target := pairedJointObservedHistory hD (t + 1) (h, (A, J))
  rw [runLaw_succ_apply P L t (MeasurableSet.singleton target)]
  have hkernel (history : History n k t) :
      roundKernel P L t history {target} =
        ({observed} : Set (History n k t)).indicator
          (fun _ => P.kernel t observed {A}) history := by
    rw [roundKernel_apply P L t history (MeasurableSet.singleton target)]
    by_cases hh : history = observed
    · subst history
      have hset :
          {a : MSetAction n k |
            (pairedJointObservedHistory hD t h,
              (a, actionLoss a (pairedLoss hD J))) =
                pairedJointObservedHistory hD (t + 1) (h, (A, J))} = {A} := by
        ext a
        constructor
        · intro ha
          exact congrArg (fun z => z.2.1) ha
        · intro ha
          change a = A at ha
          subst a
          rfl
      rw [Set.indicator_of_mem (Set.mem_singleton observed)]
      change P.kernel t (pairedJointObservedHistory hD t h)
          {a : MSetAction n k |
            (pairedJointObservedHistory hD t h,
              (a, actionLoss a
                (pairedLoss hD (denseTableItem hk table t)))) =
                pairedJointObservedHistory hD (t + 1) (h, (A, J))} = _
      rw [hitem]
      rw [hset]
    · have hset :
          {a : MSetAction n k |
            History.snoc history a (actionLoss a (L.itemLoss t history)) ∈
              ({target} : Set (History n k (t + 1)))} = ∅ := by
        ext a
        constructor
        · intro ha
          have hp := congrArg Prod.fst ha
          have hp' : history = pairedJointObservedHistory hD t h := by
            change history =
              (pairedJointObservedHistory hD (t + 1) (h, (A, J))).1 at hp
            exact hp
          exact (hh hp').elim
        · intro ha
          exact ha.elim
      rw [hset, measure_empty]
      simp [Set.indicator, hh]
  simp_rw [hkernel]
  rw [lintegral_indicator (MeasurableSet.singleton observed),
    lintegral_singleton]
  exact mul_comm _ _

def pairedJointActionMass {n k : Nat} (P : Policy n k)
    (hD : 2 * k ≤ n) :
    (t : Nat) → PairedJointHistory n k t → ENNReal
  | 0, _ => 1
  | t + 1, (h, (A, _J)) =>
      pairedJointActionMass P hD t h *
        P.kernel t (pairedJointObservedHistory hD t h) {A}

theorem runLaw_denseTable_observed_singleton_eq_actionMass
    {n k T : Nat} (P : Policy n k) (hk : 1 ≤ k)
    (hD : 2 * k ≤ n) (table : DenseItemTable k T) :
    ∀ (t : Nat) (h : PairedJointHistory n k t),
      (∀ r : Fin t,
        denseTableItem hk table r.1 = pairedJointItemAt t h r) →
      runLaw P ((denseTableLossProcess hk hD T).at table) t
          {pairedJointObservedHistory hD t h} =
        pairedJointActionMass P hD t h := by
  intro t
  induction t with
  | zero =>
      intro h hitems
      change (Measure.dirac () : Measure Unit) {()} = 1
      simp
  | succ t ih =>
      rintro ⟨h, A, J⟩ hitems
      have hprefix : ∀ r : Fin t,
          denseTableItem hk table r.1 = pairedJointItemAt t h r := by
        intro r
        simpa using hitems r.castSucc
      have hlast : denseTableItem hk table t = J := by
        simpa using hitems (Fin.last t)
      rw [runLaw_denseTable_observed_singleton_succ
        P hk hD table t h A J hlast, ih h hprefix]
      rfl

theorem pairedJointLaw_singleton_eq_actionMass_mul_itemProduct
    {n k : Nat} (P : Policy n k) (hk : 1 ≤ k)
    (hD : 2 * k ≤ n) (θ : Fin k → PairSign) (ε : Real)
    (hε0 : 0 ≤ ε) (hε1 : ε ≤ 1) :
    ∀ (t : Nat) (h : PairedJointHistory n k t),
      pairedJointLaw P hk hD θ ε hε0 hε1 t {h} =
        pairedJointActionMass P hD t h *
          ∏ r : Fin t,
            (pairedPMF hk θ ε hε0 hε1).toMeasure
              {pairedJointItemAt t h r} := by
  intro t
  induction t with
  | zero =>
      intro h
      simp [pairedJointLaw, pairedJointActionMass]
  | succ t ih =>
      rintro ⟨h, A, J⟩
      rw [pairedJointLaw_apply_singleton_succ, ih h,
        Fin.prod_univ_castSucc]
      simp only [pairedJointItemAt_succ_castSucc,
        pairedJointItemAt_succ_last, pairedJointActionMass]
      ring

/-! ## Exact table-mixture law -/

def denseParametricJointMeasure
    {n k T : Nat} (P : Policy n k) (hk : 1 ≤ k)
    (hD : 2 * k ≤ n) (θ : Fin k → PairSign) (ε : Real)
    (hε0 : 0 ≤ ε) (hε1 : ε ≤ 1) :
    Measure (DenseItemTable k T × History n k T) :=
  parametricRunWithParameterKernel P (denseTableLossProcess hk hD T) T ∘ₘ
    denseItemTableMeasure (T := T) hk θ ε hε0 hε1

def denseLatentMixtureLaw
    {n k T : Nat} (P : Policy n k) (hk : 1 ≤ k)
    (hD : 2 * k ≤ n) (θ : Fin k → PairSign) (ε : Real)
    (hε0 : 0 ≤ ε) (hε1 : ε ≤ 1) :
    Measure (PairedJointHistory n k T) :=
  (denseParametricJointMeasure P hk hD θ ε hε0 hε1).map
    (denseMixtureToLatent (n := n) (T := T) hk)

theorem parametricRunWithParameterKernel_denseLatent_preimage
    {n k T : Nat} (P : Policy n k) (hk : 1 ≤ k)
    (hD : 2 * k ≤ n) (table : DenseItemTable k T)
    (h : PairedJointHistory n k T) :
    parametricRunWithParameterKernel P (denseTableLossProcess hk hD T) T table
        ((denseMixtureToLatent (n := n) (T := T) hk) ⁻¹' {h}) =
      runLaw P ((denseTableLossProcess hk hD T).at table) T
        {history | denseLatentHistory hk table T history = h} := by
  rw [parametricRunWithParameterKernel_apply]
  rw [Measure.map_apply measurable_prodMk_left
    ((MeasurableSet.singleton h).preimage
      (measurable_denseMixtureToLatent hk))]
  congr 1

theorem denseLatent_fiber_empty_of_table_ne
    {n k T : Nat} (hk : 1 ≤ k) (table : DenseItemTable k T)
    (h : PairedJointHistory n k T)
    (hne : table ≠ pairedJointItemTable h) :
    {history : History n k T |
      denseLatentHistory hk table T history = h} = ∅ := by
  ext history
  constructor
  · intro hlatent
    have htables := congrArg pairedJointItemTable hlatent
    rw [pairedJointItemTable_denseLatentHistory] at htables
    exact (hne htables).elim
  · intro hempty
    exact hempty.elim

theorem denseLatentMixtureLaw_apply_singleton
    {n k T : Nat} (P : Policy n k) (hk : 1 ≤ k)
    (hD : 2 * k ≤ n) (θ : Fin k → PairSign) (ε : Real)
    (hε0 : 0 ≤ ε) (hε1 : ε ≤ 1)
    (h : PairedJointHistory n k T) :
    denseLatentMixtureLaw (T := T) P hk hD θ ε hε0 hε1 {h} =
      pairedJointLaw P hk hD θ ε hε0 hε1 T {h} := by
  unfold denseLatentMixtureLaw
  rw [Measure.map_apply (measurable_denseMixtureToLatent hk)
    (MeasurableSet.singleton h)]
  unfold denseParametricJointMeasure
  rw [Measure.bind_apply
    ((MeasurableSet.singleton h).preimage
      (measurable_denseMixtureToLatent hk))
    (Kernel.aemeasurable _), lintegral_fintype]
  classical
  rw [Finset.sum_eq_single (pairedJointItemTable h)]
  · rw [parametricRunWithParameterKernel_denseLatent_preimage]
    rw [runLaw_denseLatent_fiber_eq_singleton
      P hk hD (pairedJointItemTable h) h rfl]
    rw [runLaw_denseTable_observed_singleton_eq_actionMass]
    · rw [denseItemTableMeasure_apply_singleton_itemTable,
        pairedJointLaw_singleton_eq_actionMass_mul_itemProduct]
    · intro r
      rw [denseTableItem_of_lt hk (pairedJointItemTable h) r.2]
      rfl
  · intro table _ htable
    rw [parametricRunWithParameterKernel_denseLatent_preimage]
    rw [denseLatent_fiber_empty_of_table_ne hk table h htable,
      measure_empty, zero_mul]
  · simp

/-- Exact mixture equality requested by the fixing step: sample the complete
iid item table, run the genuine table-indexed protocol kernel, retain the
table, and reconstruct the latent trajectory.  Its pushforward is precisely
`pairedJointLaw`. -/
theorem denseLatentMixtureLaw_eq_pairedJointLaw
    {n k T : Nat} (P : Policy n k) (hk : 1 ≤ k)
    (hD : 2 * k ≤ n) (θ : Fin k → PairSign) (ε : Real)
    (hε0 : 0 ≤ ε) (hε1 : ε ≤ 1) :
    denseLatentMixtureLaw (T := T) P hk hD θ ε hε0 hε1 =
      pairedJointLaw P hk hD θ ε hε0 hε1 T := by
  apply Measure.ext_of_singleton
  intro h
  exact denseLatentMixtureLaw_apply_singleton
    (T := T) P hk hD θ ε hε0 hε1 h

/-! ## Regret-event transfer and deterministic fixing -/

/-- The exact mixture equality also preserves the regret event.  The key
point is that `parametricPathRegret` for the table process is definitionally
the regret of its fixed table, while `pathRegret_denseTable` identifies that
quantity with the latent paired external regret. -/
theorem denseParametricJointMeasure_regretEvent_eq_pairedJointLaw
    {n k T : Nat} (P : Policy n k) (hk : 1 ≤ k)
    (hD : 2 * k ≤ n) (θ : Fin k → PairSign) (ε : Real)
    (hε0 : 0 ≤ ε) (hε1 : ε ≤ 1) (threshold : Real) :
    (denseParametricJointMeasure (T := T) P hk hD θ ε hε0 hε1).real
        (parametricRegretEvent (denseTableLossProcess hk hD T) T threshold) =
      (pairedJointLaw P hk hD θ ε hε0 hε1 T).real
        {h | threshold ≤ pairedExternalRegret hD T h} := by
  have hkn : k ≤ n := by omega
  letI : Nonempty (MSetAction n k) := nonempty_MSetAction hkn
  let event : Set (PairedJointHistory n k T) :=
    {h | threshold ≤ pairedExternalRegret hD T h}
  have hevent : MeasurableSet event := MeasurableSet.of_discrete
  have hpreimage :
      parametricRegretEvent (denseTableLossProcess hk hD T) T threshold =
        denseMixtureToLatent (n := n) (T := T) hk ⁻¹' event := by
    ext input
    change threshold ≤
        parametricPathRegret (denseTableLossProcess hk hD T) T input ↔
      threshold ≤ pairedExternalRegret hD T
        (denseLatentHistory hk input.1 T input.2)
    rw [parametricPathRegret_eq_at, pathRegret_denseTable]
  have hlaw := denseLatentMixtureLaw_eq_pairedJointLaw
    (T := T) P hk hD θ ε hε0 hε1
  have happ := congrArg (fun μ : Measure (PairedJointHistory n k T) => μ event) hlaw
  unfold denseLatentMixtureLaw at happ
  rw [Measure.map_apply (measurable_denseMixtureToLatent hk) hevent] at happ
  rw [hpreimage]
  exact congrArg ENNReal.toReal happ

/-- Fix the iid table after the adaptive paired experiment.  No master tape
or externally postulated mixture identity occurs here: the average supplied
to `exists_fixed_parametric_regret` is rewritten by the exact pushforward
identity above. -/
theorem exists_fixed_denseTable_base_regret
    {n k T : Nat} (P : Policy n k) (hk : 1 ≤ k)
    (hD : 2 * k ≤ n) (hT : 1 ≤ T)
    (hk_half : k ≤ n / 2) (horizon : n ^ 2 ≤ T) :
    ∃ table : DenseItemTable k T,
      (2 : Real) ^ (-14 : Int) ≤
        (runLaw P ((denseTableLossProcess hk hD T).at table) T).real
          {history | (k : Real) * Real.sqrt T / 64 ≤
            pathRegret ((denseTableLossProcess hk hD T).at table) T history} := by
  have hkn : k ≤ n := by omega
  obtain ⟨θ, hpaired⟩ := lower_dense_probabilistic_action_capstone
    P hk hD hT hk_half horizon
  let μ : Measure (DenseItemTable k T) :=
    denseItemTableMeasure (T := T) hk θ (denseEpsilon k T)
      (denseEpsilon_nonneg k T)
      (denseEpsilon_le_one_paper_regime hk hk_half horizon)
  have haverage :
      (2 : Real) ^ (-14 : Int) ≤
        ((parametricRunWithParameterKernel P
            (denseTableLossProcess hk hD T) T) ∘ₘ μ).real
          (parametricRegretEvent (denseTableLossProcess hk hD T) T
            ((k : Real) * Real.sqrt T / 64)) := by
    change (2 : Real) ^ (-14 : Int) ≤
      (denseParametricJointMeasure (T := T) P hk hD θ (denseEpsilon k T)
        (denseEpsilon_nonneg k T)
        (denseEpsilon_le_one_paper_regime hk hk_half horizon)).real
        (parametricRegretEvent (denseTableLossProcess hk hD T) T
          ((k : Real) * Real.sqrt T / 64))
    rw [denseParametricJointMeasure_regretEvent_eq_pairedJointLaw]
    exact hpaired.le
  exact exists_fixed_parametric_regret hkn μ P
    (denseTableLossProcess hk hD T) T
    ((k : Real) * Real.sqrt T / 64) ((2 : Real) ^ (-14 : Int)) haverage

/-- Strong form of the fixing output recording explicitly that the selected
section is fixed in advance (its loss vector is independent of history). -/
theorem exists_fixedInAdvance_denseTable_base_regret
    {n k T : Nat} (P : Policy n k) (hk : 1 ≤ k)
    (hD : 2 * k ≤ n) (hT : 1 ≤ T)
    (hk_half : k ≤ n / 2) (horizon : n ^ 2 ≤ T) :
    ∃ table : DenseItemTable k T,
      (∀ (t : Nat) (history history' : History n k t),
        ((denseTableLossProcess hk hD T).at table).itemLoss t history =
          ((denseTableLossProcess hk hD T).at table).itemLoss t history') ∧
      (2 : Real) ^ (-14 : Int) ≤
        (runLaw P ((denseTableLossProcess hk hD T).at table) T).real
          {history | (k : Real) * Real.sqrt T / 64 ≤
            pathRegret ((denseTableLossProcess hk hD T).at table) T history} := by
  obtain ⟨table, htable⟩ := exists_fixed_denseTable_base_regret
    P hk hD hT hk_half horizon
  exact ⟨table, denseTableLossProcess_fixedInAdvance hk hD T table, htable⟩

/-- Semantic lower-tail statement at the natural dense threshold `k√T/64`,
witnessed by a deterministic table fixed before play. -/
theorem lower_dense_fixed_base_tail
    {n k T : Nat} (P : Policy n k) (hk : 1 ≤ k)
    (hD : 2 * k ≤ n) (hT : 1 ≤ T)
    (hk_half : k ≤ n / 2) (horizon : n ^ 2 ≤ T) :
    HasRegretLowerTail (show k ≤ n by omega) P T
      ((k : Real) * Real.sqrt T / 64) ((2 : Real) ^ (-14 : Int)) := by
  have hkn : k ≤ n := by omega
  obtain ⟨table, htable⟩ := exists_fixed_denseTable_base_regret
    P hk hD hT hk_half horizon
  refine ⟨(denseTableLossProcess hk hD T).at table, ?_⟩
  unfold regretTailProbability
  apply (ENNReal.ofReal_le_iff_le_toReal (measure_ne_top _ _)).2
  simpa [measureReal_def] using htable

/-- Literal numerical comparison at the end of the dense construction.
The quotient hypothesis is the manuscript's `r = n / k < 2^32`; no real
ratio surrogate is assumed. -/
theorem lower_dense_literal_threshold_lt
    {n k T : Nat} (hk : 1 ≤ k) (hk_half : k ≤ n / 2)
    (hT : 1 ≤ T) (hr : n / k < 2 ^ 32) :
    (2 : Real) ^ (-38 : Int) *
        Real.sqrt ((n : Real) * (T : Real) *
          Real.log (n.choose k : Real)) <
      (k : Real) * Real.sqrt T / 64 := by
  have hkposNat : 0 < k := by omega
  have hkn : k ≤ n := by omega
  have hmod : n % k < k := Nat.mod_lt n hkposNat
  have hnltQuotient : n < (n / k + 1) * k := by
    calc
      n = k * (n / k) + n % k := (Nat.div_add_mod n k).symm
      _ < k * (n / k) + k := Nat.add_lt_add_left hmod _
      _ = (n / k + 1) * k := by ring
  have hquotient : n / k + 1 ≤ 2 ^ 32 := by omega
  have hquotientMul : (n / k + 1) * k ≤ (2 ^ 32) * k :=
    Nat.mul_le_mul_right k hquotient
  have hnscaleNat : n < (2 ^ 32) * k :=
    hnltQuotient.trans_le hquotientMul
  have hnscale : (n : Real) < (2 : Real) ^ 32 * (k : Real) := by
    exact_mod_cast hnscaleNat

  have hchoosePosNat : 0 < n.choose k := Nat.choose_pos hkn
  have hchoosePos : 0 < (n.choose k : Real) := by
    exact_mod_cast hchoosePosNat
  have hchoose : (n.choose k : Real) ≤ (2 : Real) ^ n := by
    exact_mod_cast Nat.choose_le_two_pow n k
  have hlogPow :
      Real.log (n.choose k : Real) ≤ (n : Real) * Real.log 2 := by
    have hlog := Real.log_le_log hchoosePos hchoose
    rwa [Real.log_pow] at hlog
  have hlogTwo : Real.log 2 ≤ (1 : Real) :=
    (Real.log_two_lt_d9.trans (by norm_num)).le
  have hnnonneg : 0 ≤ (n : Real) := by positivity
  have hlog : Real.log (n.choose k : Real) ≤ (n : Real) := by
    calc
      Real.log (n.choose k : Real) ≤ (n : Real) * Real.log 2 := hlogPow
      _ ≤ (n : Real) * 1 := mul_le_mul_of_nonneg_left hlogTwo hnnonneg
      _ = (n : Real) := mul_one _

  have hTnonneg : 0 ≤ (T : Real) := by positivity
  have hnTnonneg : 0 ≤ (n : Real) * (T : Real) :=
    mul_nonneg hnnonneg hTnonneg
  have hinside :
      (n : Real) * (T : Real) * Real.log (n.choose k : Real) ≤
        (n : Real) ^ 2 * (T : Real) := by
    calc
      (n : Real) * (T : Real) * Real.log (n.choose k : Real) ≤
          (n : Real) * (T : Real) * (n : Real) :=
        mul_le_mul_of_nonneg_left hlog hnTnonneg
      _ = (n : Real) ^ 2 * (T : Real) := by ring
  have hsqrt :
      Real.sqrt ((n : Real) * (T : Real) *
          Real.log (n.choose k : Real)) ≤
        (n : Real) * Real.sqrt T := by
    calc
      Real.sqrt ((n : Real) * (T : Real) *
          Real.log (n.choose k : Real)) ≤
          Real.sqrt ((n : Real) ^ 2 * (T : Real)) :=
        Real.sqrt_le_sqrt hinside
      _ = Real.sqrt ((n : Real) ^ 2) * Real.sqrt T := by
        rw [Real.sqrt_mul (sq_nonneg (n : Real))]
      _ = (n : Real) * Real.sqrt T := by
        rw [Real.sqrt_sq_eq_abs, abs_of_nonneg hnnonneg]

  have hconstant :
      (2 : Real) ^ (-38 : Int) * (n : Real) < (k : Real) / 64 := by
    rw [zpow_neg]
    norm_num at hnscale ⊢
    nlinarith
  have hsqrtTpos : 0 < Real.sqrt (T : Real) := by
    exact Real.sqrt_pos.2 (by exact_mod_cast (show 0 < T by omega))
  have hconstantNonneg : 0 ≤ (2 : Real) ^ (-38 : Int) := by positivity
  calc
    (2 : Real) ^ (-38 : Int) *
        Real.sqrt ((n : Real) * (T : Real) *
          Real.log (n.choose k : Real)) ≤
        (2 : Real) ^ (-38 : Int) *
          ((n : Real) * Real.sqrt T) :=
      mul_le_mul_of_nonneg_left hsqrt hconstantNonneg
    _ = ((2 : Real) ^ (-38 : Int) * (n : Real)) * Real.sqrt T := by ring
    _ < ((k : Real) / 64) * Real.sqrt T :=
      mul_lt_mul_of_pos_right hconstant hsqrtTpos
    _ = (k : Real) * Real.sqrt T / 64 := by ring

/-- Literal semantic form of `prop:lower-bounded-action`.  The witness hidden
inside `HasRegretLowerTail` is the fixed table section produced above, hence
is deterministic, non-anticipating, and in fact history-independent. -/
theorem lower_dense_bounded_action
    {n k T : Nat} (P : Policy n k) (hk : 1 ≤ k)
    (hk_half : k ≤ n / 2) (hr : n / k < 2 ^ 32)
    (horizon : n ^ 2 ≤ T) :
    HasRegretLowerTail (show k ≤ n by omega) P T
      ((2 : Real) ^ (-38 : Int) *
        Real.sqrt ((n : Real) * (T : Real) *
          Real.log (n.choose k : Real)))
      ((2 : Real) ^ (-14 : Int)) := by
  have hkn : k ≤ n := by omega
  have hD : 2 * k ≤ n := by omega
  have hn : 1 ≤ n := hkn.trans' hk
  have hnsq : 1 ≤ n ^ 2 := one_le_pow_of_one_le' hn 2
  have hT : 1 ≤ T := hnsq.trans horizon
  have hbase := lower_dense_fixed_base_tail
    P hk hD hT hk_half horizon
  exact hbase.mono
    (lower_dense_literal_threshold_lt hk hk_half hT hr).le le_rfl

/-- Dense-branch instance of the common action-count semantic statement,
with the constants written through the shared names used by the final case
split. -/
theorem lower_dense_actionCountConclusion
    {n k T : Nat} (hk : 1 ≤ k) (hk_half : k ≤ n / 2)
    (hr : n / k < 2 ^ 32) (horizon : n ^ 2 ≤ T) :
    ActionCountConclusion n k T (show k ≤ n by omega) := by
  intro P
  have h := lower_dense_bounded_action P hk hk_half hr horizon
  convert h using 1 <;>
    simp [actionCountConstant, actionCountProbability, zpow_neg]

#print axioms denseLatentMixtureLaw_eq_pairedJointLaw
#print axioms denseParametricJointMeasure_regretEvent_eq_pairedJointLaw
#print axioms exists_fixed_denseTable_base_regret
#print axioms exists_fixedInAdvance_denseTable_base_regret
#print axioms lower_dense_fixed_base_tail
#print axioms lower_dense_literal_threshold_lt
#print axioms lower_dense_bounded_action
#print axioms lower_dense_actionCountConclusion

end

end MsetsLower.Lower.Dense
