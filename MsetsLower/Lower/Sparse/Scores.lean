import MsetsLower.Lower.Sparse.Construction
import Mathlib.Order.ConditionallyCompleteLattice.Finset

/-!
# Sparse comparator and learner scores

The declarations here are the literal pathwise scores `S_i` and `S_L` from
the manuscript.  Their final theorem is `eq:lower-regret-identity`, with the
maximum taken over exact `k`-subsets of the first `n'` coordinates.
-/

namespace MsetsLower.Lower.Sparse

open MsetsLower Set
open scoped BigOperators

noncomputable section

/-- The coordinate score
`S_i=sum_b U_{b,i} sum_{t in b} A_{t,i} g(Z_t)` accumulated recursively. -/
def sparseCoordinateScore {n k : Nat} (n' q c0 : Nat)
    (U : Nat → Fin n → Real) (Z : Nat → Real) (i : Fin n) :
    (t : Nat) → History n k t → Real
  | 0, _ => 0
  | t + 1, h =>
      sparseCoordinateScore n' q c0 U Z i t h.1 +
        sparseSignalWeight n' q U t i * sparseActive q c0 i t h.1 *
          Feedback.shape (Z t)

@[simp] theorem sparseCoordinateScore_zero
    {n k n' q c0 : Nat} (U : Nat → Fin n → Real) (Z : Nat → Real)
    (i : Fin n) (h : History n k 0) :
    sparseCoordinateScore n' q c0 U Z i 0 h = 0 := rfl

@[simp] theorem sparseCoordinateScore_succ
    {n k n' q c0 t : Nat} (U : Nat → Fin n → Real) (Z : Nat → Real)
    (i : Fin n) (h : History n k (t + 1)) :
    sparseCoordinateScore n' q c0 U Z i (t + 1) h =
      sparseCoordinateScore n' q c0 U Z i t h.1 +
        sparseSignalWeight n' q U t i * sparseActive q c0 i t h.1 *
          Feedback.shape (Z t) := rfl

/-- The learner score
`S_L=sum_t g(Z_t) sum_{i in X_t} A_{t,i}U_{b(t),i}`. -/
def sparseLearnerScore {n k : Nat} (n' q c0 : Nat)
    (U : Nat → Fin n → Real) (Z : Nat → Real) :
    (t : Nat) → History n k t → Real
  | 0, _ => 0
  | t + 1, h =>
      sparseLearnerScore n' q c0 U Z t h.1 +
        Feedback.shape (Z t) *
          sparseActionScore n' q c0 U t h.1 h.2.1

@[simp] theorem sparseLearnerScore_zero
    {n k n' q c0 : Nat} (U : Nat → Fin n → Real) (Z : Nat → Real)
    (h : History n k 0) :
    sparseLearnerScore n' q c0 U Z 0 h = 0 := rfl

@[simp] theorem sparseLearnerScore_succ
    {n k n' q c0 t : Nat} (U : Nat → Fin n → Real) (Z : Nat → Real)
    (h : History n k (t + 1)) :
    sparseLearnerScore n' q c0 U Z (t + 1) h =
      sparseLearnerScore n' q c0 U Z t h.1 +
        Feedback.shape (Z t) *
          sparseActionScore n' q c0 U t h.1 h.2.1 := rfl

/-- Score accumulated by a fixed comparator. -/
def sparseComparatorScore {n k : Nat} (n' q c0 : Nat)
    (U : Nat → Fin n → Real) (Z : Nat → Real) (A : MSetAction n k) :
    (t : Nat) → History n k t → Real
  | 0, _ => 0
  | t + 1, h =>
      sparseComparatorScore n' q c0 U Z A t h.1 +
        Feedback.shape (Z t) * sparseActionScore n' q c0 U t h.1 A

@[simp] theorem sparseComparatorScore_zero
    {n k n' q c0 : Nat} (U : Nat → Fin n → Real) (Z : Nat → Real)
    (A : MSetAction n k) (h : History n k 0) :
    sparseComparatorScore n' q c0 U Z A 0 h = 0 := rfl

@[simp] theorem sparseComparatorScore_succ
    {n k n' q c0 t : Nat} (U : Nat → Fin n → Real) (Z : Nat → Real)
    (A : MSetAction n k) (h : History n k (t + 1)) :
    sparseComparatorScore n' q c0 U Z A (t + 1) h =
      sparseComparatorScore n' q c0 U Z A t h.1 +
        Feedback.shape (Z t) * sparseActionScore n' q c0 U t h.1 A := rfl

/-- A comparator's score is exactly the sum of its coordinate scores. -/
theorem sparseComparatorScore_eq_coordinate_sum
    {n k n' q c0 : Nat} (U : Nat → Fin n → Real) (Z : Nat → Real)
    (A : MSetAction n k) :
    ∀ t (h : History n k t),
      sparseComparatorScore n' q c0 U Z A t h =
        ∑ i ∈ A.1, sparseCoordinateScore n' q c0 U Z i t h := by
  intro t
  induction t with
  | zero => intro h; simp
  | succ t ih =>
      intro h
      rcases h with ⟨hprev, played, feedback⟩
      rw [sparseComparatorScore_succ, ih hprev]
      unfold sparseActionScore
      rw [actionLoss_eq_finset_sum]
      change
        (∑ i ∈ A.1, sparseCoordinateScore n' q c0 U Z i t hprev) +
            Feedback.shape (Z t) *
              (∑ i ∈ A.1, sparseActive q c0 i t hprev *
                sparseSignalWeight n' q U t i) =
          ∑ i ∈ A.1,
            (sparseCoordinateScore n' q c0 U Z i t hprev +
              sparseSignalWeight n' q U t i * sparseActive q c0 i t hprev *
                Feedback.shape (Z t))
      rw [Finset.sum_add_distrib, Finset.mul_sum]
      congr 1
      apply Finset.sum_congr rfl
      intro i hi
      ring

/-- One-round cancellation of the common baseline in
`eq:lower-sparse-loss`. -/
theorem sparse_played_sub_comparator
    {n k : Nat} (hk : 1 ≤ k) (eta : Real) (n' q c0 T0 : Nat)
    (U : Nat → Fin n → Real) (Z : Nat → Real)
    {t : Nat} (ht : t < T0) (h : History n k t)
    (played A : MSetAction n k) :
    actionLoss played (sparseItemLoss eta n' q c0 T0 U Z t h) -
        actionLoss A (sparseItemLoss eta n' q c0 T0 U Z t h) =
      eta / (k : Real) *
        (Feedback.shape (Z t) * sparseActionScore n' q c0 U t h A -
          Feedback.shape (Z t) * sparseActionScore n' q c0 U t h played) := by
  rw [lower_sparse_action_loss hk eta n' q c0 T0 U Z ht h played,
    lower_sparse_action_loss hk eta n' q c0 T0 U Z ht h A]
  simp only [Feedback.feedbackMap, sparseFeedbackParameter]
  ring

/-- Regret against a fixed comparator is exactly its score minus the learner
score, scaled by `eta/k`, for every prefix contained in `[T0]`. -/
theorem sparse_comparator_regret_identity
    {n k : Nat} (hk : 1 ≤ k) (eta : Real) (heta0 : 0 ≤ eta)
    (heta : eta ≤ (1 : Real) / 16) (n' q c0 T0 : Nat)
    (U : Nat → Fin n → Real) (hU : ∀ b i, |U b i| ≤ 1)
    (Z : Nat → Real) (hZ : ∀ t, Z t ∈ Icc (-1 : Real) 1)
    (A : MSetAction n k) :
    ∀ t (h : History n k t), t ≤ T0 →
      realizedCumulativeLoss
          (sparseLossProcess hk eta heta0 heta n' q c0 T0 U hU Z hZ) t h -
        comparatorCumulativeLoss
          (sparseLossProcess hk eta heta0 heta n' q c0 T0 U hU Z hZ) t h A =
      eta / (k : Real) *
        (sparseComparatorScore n' q c0 U Z A t h -
          sparseLearnerScore n' q c0 U Z t h) := by
  intro t
  induction t with
  | zero => intro h ht; simp [realizedCumulativeLoss, comparatorCumulativeLoss]
  | succ t ih =>
      intro h ht
      rcases h with ⟨hprev, played, feedback⟩
      have hround : t < T0 := by omega
      simp only [realizedCumulativeLoss, comparatorCumulativeLoss,
        sparseComparatorScore_succ, sparseLearnerScore_succ]
      change
        realizedCumulativeLoss
              (sparseLossProcess hk eta heta0 heta n' q c0 T0 U hU Z hZ) t hprev +
            actionLoss played (sparseItemLoss eta n' q c0 T0 U Z t hprev) -
          (comparatorCumulativeLoss
              (sparseLossProcess hk eta heta0 heta n' q c0 T0 U hU Z hZ) t hprev A +
            actionLoss A (sparseItemLoss eta n' q c0 T0 U Z t hprev)) = _
      have hprevEq := ih hprev (Nat.le_of_succ_le ht)
      have hstep :=
        sparse_played_sub_comparator hk eta n' q c0 T0 U Z hround hprev played A
      calc
        _ =
            (realizedCumulativeLoss
                (sparseLossProcess hk eta heta0 heta n' q c0 T0 U hU Z hZ) t hprev -
              comparatorCumulativeLoss
                (sparseLossProcess hk eta heta0 heta n' q c0 T0 U hU Z hZ) t hprev A) +
              (actionLoss played (sparseItemLoss eta n' q c0 T0 U Z t hprev) -
                actionLoss A (sparseItemLoss eta n' q c0 T0 U Z t hprev)) := by ring
        _ = _ := by rw [hprevEq, hstep]; ring

/-! ## Exact maximum over signal comparators -/

/-- Embed a signal coordinate from `[n']` into `[n]`. -/
def sparseSignalCoordinate {n n' : Nat} (hn' : n' ≤ n) (i : Fin n') : Fin n :=
  Fin.castLE hn' i

theorem sparseSignalCoordinate_injective {n n' : Nat} (hn' : n' ≤ n) :
    Function.Injective (sparseSignalCoordinate hn') := by
  intro i j hij
  apply Fin.ext
  exact congrArg (fun x : Fin n => x.1) hij

/-- Regard a `k`-subset of signal coordinates as an action in `[n]`. -/
def sparseSignalComparator {n n' k : Nat} (hn' : n' ≤ n)
    (J : MSetAction n' k) : MSetAction n k :=
  ⟨J.1.image (sparseSignalCoordinate hn'), by
    rw [Finset.card_image_of_injective]
    · exact J.2
    · exact sparseSignalCoordinate_injective hn'⟩

/-- `sum_{i∈J} S_i` in the displayed regret identity. -/
def sparseSignalScore {n n' k : Nat} (q c0 : Nat) (hn' : n' ≤ n)
    (U : Nat → Fin n → Real) (Z : Nat → Real)
    (t : Nat) (h : History n k t) (J : MSetAction n' k) : Real :=
  ∑ i ∈ J.1,
    sparseCoordinateScore n' q c0 U Z (sparseSignalCoordinate hn' i) t h

theorem sparseSignalScore_eq_comparatorScore
    {n n' k q c0 : Nat} (hn' : n' ≤ n)
    (U : Nat → Fin n → Real) (Z : Nat → Real)
    (t : Nat) (h : History n k t) (J : MSetAction n' k) :
    sparseSignalScore q c0 hn' U Z t h J =
      sparseComparatorScore n' q c0 U Z (sparseSignalComparator hn' J) t h := by
  rw [sparseComparatorScore_eq_coordinate_sum]
  change (∑ i ∈ J.1,
      sparseCoordinateScore n' q c0 U Z (sparseSignalCoordinate hn' i) t h) =
    ∑ i ∈ J.1.image (sparseSignalCoordinate hn'),
      sparseCoordinateScore n' q c0 U Z i t h
  rw [Finset.sum_image]
  exact (sparseSignalCoordinate_injective hn').injOn

/-- The literal finite maximum in `eq:lower-regret-identity`. -/
def sparseMaxSignalScore {n n' k : Nat} (q c0 : Nat) (hn' : n' ≤ n)
    (U : Nat → Fin n → Real) (Z : Nat → Real)
    (t : Nat) (h : History n k t) : Real :=
  ⨆ J : MSetAction n' k, sparseSignalScore q c0 hn' U Z t h J

private theorem comparatorRegret_le_pathRegret
    {n k : Nat} (L : LossProcess n k)
    (t : Nat) (h : History n k t) (A : MSetAction n k) :
    realizedCumulativeLoss L t h - comparatorCumulativeLoss L t h A ≤
      pathRegret L t h := by
  have hbelow : BddBelow (Set.range (comparatorCumulativeLoss L t h)) :=
    Finite.bddBelow_range _
  have hbest : bestComparatorCumulativeLoss L t h ≤
      comparatorCumulativeLoss L t h A :=
    csInf_le hbelow ⟨A, rfl⟩
  unfold pathRegret
  linarith

/-- Equation `eq:lower-regret-identity`: external regret dominates the best
signal-coordinate score minus the learner score. -/
theorem lower_sparse_regret_identity
    {n n' k q c0 T0 : Nat} (hk : 1 ≤ k) (hkn' : k ≤ n') (hn' : n' ≤ n)
    (eta : Real) (heta0 : 0 ≤ eta) (heta : eta ≤ (1 : Real) / 16)
    (U : Nat → Fin n → Real) (hU : ∀ b i, |U b i| ≤ 1)
    (Z : Nat → Real) (hZ : ∀ t, Z t ∈ Icc (-1 : Real) 1)
    (h : History n k T0) :
    eta / (k : Real) *
        (sparseMaxSignalScore q c0 hn' U Z T0 h -
          sparseLearnerScore n' q c0 U Z T0 h) ≤
      pathRegret
        (sparseLossProcess hk eta heta0 heta n' q c0 T0 U hU Z hZ) T0 h := by
  letI : Nonempty (MSetAction n' k) := nonempty_MSetAction hkn'
  obtain ⟨J, hJ⟩ :=
    exists_eq_ciSup_of_finite
      (f := fun J : MSetAction n' k => sparseSignalScore q c0 hn' U Z T0 h J)
  have hid := sparse_comparator_regret_identity hk eta heta0 heta n' q c0 T0
    U hU Z hZ (sparseSignalComparator hn' J) T0 h le_rfl
  have hdom := comparatorRegret_le_pathRegret
    (sparseLossProcess hk eta heta0 heta n' q c0 T0 U hU Z hZ) T0 h
      (sparseSignalComparator hn' J)
  calc
    eta / (k : Real) *
        (sparseMaxSignalScore q c0 hn' U Z T0 h -
          sparseLearnerScore n' q c0 U Z T0 h) =
      eta / (k : Real) *
        (sparseComparatorScore n' q c0 U Z
            (sparseSignalComparator hn' J) T0 h -
          sparseLearnerScore n' q c0 U Z T0 h) := by
        rw [sparseMaxSignalScore, ← hJ,
          sparseSignalScore_eq_comparatorScore]
    _ = realizedCumulativeLoss
          (sparseLossProcess hk eta heta0 heta n' q c0 T0 U hU Z hZ) T0 h -
        comparatorCumulativeLoss
          (sparseLossProcess hk eta heta0 heta n' q c0 T0 U hU Z hZ) T0 h
            (sparseSignalComparator hn' J) := hid.symm
    _ ≤ pathRegret
          (sparseLossProcess hk eta heta0 heta n' q c0 T0 U hU Z hZ) T0 h := hdom

#print axioms sparseComparatorScore_eq_coordinate_sum
#print axioms sparse_comparator_regret_identity
#print axioms lower_sparse_regret_identity

end

end MsetsLower.Lower.Sparse
