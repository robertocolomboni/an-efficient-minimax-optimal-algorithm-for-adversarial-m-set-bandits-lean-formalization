import MsetsLower.Lower.Sparse.ScoreBias
import MsetsLower.Feedback.Score
import Mathlib.Analysis.Calculus.MeanValue

/-!
# History-preserving positive drift of sparse comparator scores

The hidden-coordinate change leaves the action--feedback history fixed.  To
compare the old and changed latent scores on that common history, this file
uses the observable representation `G_y(u)=g(F_u^{-1}(y))`.  The derivative
bound from `Feedback.Score` gives a pathwise comparison for every coordinate,
and the actual active-pull count spends at most `k` units per round.
-/

namespace MsetsLower.Lower.Sparse

open MsetsLower Feedback Set
open MeasureTheory ProbabilityTheory
open scoped BigOperators ENNReal ProbabilityTheory

noncomputable section

/-! ## A uniform additive consequence of the score derivative bound -/

/-- On the admissible parameter interval, `G_y` is `6`-Lipschitz.  This
additive form is slightly stronger for the later counting argument than the
manuscript's multiplicative `12 |s| G_y(u)` estimate. -/
theorem feedbackScoreShape_lipschitz
    {u v y : Real}
    (hu : |u| <= (1 : Real) / 16) (hv : |v| <= (1 : Real) / 16)
    (hy : y ∈ Icc (-1 / 2 : Real) (1 / 2 : Real)) :
    |feedbackScoreShape v y - feedbackScoreShape u y| <= 6 * |v - u| := by
  have huIcc : u ∈ Icc (-1 / 16 : Real) (1 / 16 : Real) := by
    have hu' := (abs_le).1 hu
    constructor <;> linarith [hu'.1, hu'.2]
  have hvIcc : v ∈ Icc (-1 / 16 : Real) (1 / 16 : Real) := by
    have hv' := (abs_le).1 hv
    constructor <;> linarith [hv'.1, hv'.2]
  have h := Convex.norm_image_sub_le_of_norm_deriv_le
      (f := fun w : Real => feedbackScoreShape w y)
      (s := Icc (-1 / 16 : Real) (1 / 16 : Real))
      (x := u) (y := v) (C := 6)
      (fun w hw => by
        have hwabs : |w| <= (1 : Real) / 16 := by
          rw [abs_le]
          constructor <;> linarith [hw.1, hw.2]
        exact (hasDerivAt_feedbackScoreShape_param hwabs hy).differentiableAt)
      (fun w hw => by
        have hwabs : |w| <= (1 : Real) / 16 := by
          rw [abs_le]
          constructor <;> linarith [hw.1, hw.2]
        rw [Real.norm_eq_abs]
        have hder := abs_deriv_feedbackScoreShape_le hwabs hy
        have hG := feedbackScoreShape_mem_Icc hwabs hy
        calc
          |deriv (fun z => feedbackScoreShape z y) w| <=
              6 * feedbackScoreShape w y := hder
          _ <= 6 * 1 :=
            mul_le_mul_of_nonneg_left hG.2 (by norm_num : (0 : Real) <= 6)
          _ = 6 := by norm_num)
      (convex_Icc (-1 / 16 : Real) (1 / 16 : Real))
      huIcc hvIcc
  simpa [Real.norm_eq_abs] using h

/-! ## Observable versions of the sparse coordinate score -/

/-- Coordinate score reconstructed from the common observed feedback
history.  Under the experiment with parameter field `V`, the final factor is
exactly `g(Z_t)`. -/
def sparseObservableCoordinateScore {n n' k : Nat}
    (V : SparseAdaptiveParameters n k) (hn' : n' <= n) (q c0 : Nat)
    (U : Nat -> Fin n -> Real) (j : Fin n') :
    (T : Nat) -> History n k T -> Real
  | 0, _ => 0
  | t + 1, h =>
      sparseObservableCoordinateScore V hn' q c0 U j t h.1 +
        U (t / q) (sparseSignalCoordinate hn' j) *
          sparseActive q c0 (sparseSignalCoordinate hn' j) t h.1 *
          feedbackScoreShape (V.value t h.1 h.2.1) h.2.2

@[simp] theorem sparseObservableCoordinateScore_zero
    {n n' k q c0 : Nat} (V : SparseAdaptiveParameters n k)
    (hn' : n' <= n) (U : Nat -> Fin n -> Real) (j : Fin n')
    (h : History n k 0) :
    sparseObservableCoordinateScore V hn' q c0 U j 0 h = 0 := rfl

@[simp] theorem sparseObservableCoordinateScore_succ
    {n n' k q c0 t : Nat} (V : SparseAdaptiveParameters n k)
    (hn' : n' <= n) (U : Nat -> Fin n -> Real) (j : Fin n')
    (h : History n k (t + 1)) :
    sparseObservableCoordinateScore V hn' q c0 U j (t + 1) h =
      sparseObservableCoordinateScore V hn' q c0 U j t h.1 +
        U (t / q) (sparseSignalCoordinate hn' j) *
          sparseActive q c0 (sparseSignalCoordinate hn' j) t h.1 *
          feedbackScoreShape (V.value t h.1 h.2.1) h.2.2 := rfl

theorem measurable_feedbackScoreShape_uncurry :
    Measurable (fun p : Real × Real => feedbackScoreShape p.1 p.2) := by
  unfold feedbackScoreShape
  exact measurable_shape.comp measurable_feedbackInverse_uncurry

set_option maxHeartbeats 2000000 in
-- Elaborating measurability through the dependent recursive history type is expensive.
theorem measurable_sparseObservableCoordinateScore
    {n n' k q c0 : Nat} (V : SparseAdaptiveParameters n k)
    (hn' : n' <= n) (U : Nat -> Fin n -> Real) (j : Fin n') :
    forall T, Measurable (sparseObservableCoordinateScore V hn' q c0 U j T) := by
  intro T
  induction T with
  | zero => exact measurable_const
  | succ t ih =>
      have hparameter : Measurable (fun h : History n k (t + 1) =>
          V.value t h.1 h.2.1) :=
        (V.measurable_value t).comp
          (measurable_fst.prodMk (measurable_fst.comp measurable_snd))
      have hfeedback : Measurable (fun h : History n k (t + 1) => h.2.2) :=
        measurable_snd.comp measurable_snd
      exact (ih.comp measurable_fst).add <|
        (measurable_const.mul
          ((measurable_sparseActive
            (q := q) (c0 := c0) (sparseSignalCoordinate hn' j) t).comp
              measurable_fst)).mul
          (measurable_feedbackScoreShape_uncurry.comp
            (hparameter.prodMk hfeedback))

/-- The positive main term in the changed-score comparison. -/
def sparseObservablePositiveCore {n n' k : Nat}
    (V : SparseAdaptiveParameters n k) (hn' : n' <= n) (q c0 : Nat)
    (U : Nat -> Fin n -> Real) (j : Fin n') :
    (T : Nat) -> History n k T -> Real
  | 0, _ => 0
  | t + 1, h =>
      sparseObservablePositiveCore V hn' q c0 U j t h.1 +
        shape (U (t / q) (sparseSignalCoordinate hn' j)) *
          sparseActive q c0 (sparseSignalCoordinate hn' j) t h.1 *
          feedbackScoreShape (V.value t h.1 h.2.1) h.2.2

/-- Number of active pulls of one signal coordinate, accumulated on the
actual observable history. -/
def sparseObservablePullCount {n n' k : Nat}
    (hn' : n' <= n) (q c0 : Nat) (j : Fin n') :
    (T : Nat) -> History n k T -> Real
  | 0, _ => 0
  | t + 1, h =>
      sparseObservablePullCount hn' q c0 j t h.1 +
        sparsePullIndicator hn' q c0 j t h.1 h.2.1

@[simp] theorem sparseObservablePositiveCore_succ
    {n n' k q c0 t : Nat} (V : SparseAdaptiveParameters n k)
    (hn' : n' <= n) (U : Nat -> Fin n -> Real) (j : Fin n')
    (h : History n k (t + 1)) :
    sparseObservablePositiveCore V hn' q c0 U j (t + 1) h =
      sparseObservablePositiveCore V hn' q c0 U j t h.1 +
        shape (U (t / q) (sparseSignalCoordinate hn' j)) *
          sparseActive q c0 (sparseSignalCoordinate hn' j) t h.1 *
          feedbackScoreShape (V.value t h.1 h.2.1) h.2.2 := rfl

@[simp] theorem sparseObservablePullCount_succ
    {n n' k q c0 t : Nat} (hn' : n' <= n) (j : Fin n')
    (h : History n k (t + 1)) :
    sparseObservablePullCount hn' q c0 j (t + 1) h =
      sparseObservablePullCount hn' q c0 j t h.1 +
        sparsePullIndicator hn' q c0 j t h.1 h.2.1 := rfl

/-! ## One-round and chronological changed-score comparisons -/

/-- The one-round deterministic inequality behind the positive drift.  The
changed hidden value is `T_a(x)=x+a g(x)`, while the observed feedback `y`
is held fixed. -/
theorem sparse_changed_score_increment_lower
    {k : Nat} (hk : 1 <= k)
    {a eta x u v m y : Real}
    (ha0 : 0 <= a) (ha : a <= (1 : Real) / 8)
    (heta : 0 <= eta) (hx : x ∈ Icc (-1 : Real) 1)
    (hm : m ∈ Icc (0 : Real) 1)
    (hu : |u| <= (1 : Real) / 16) (hv : |v| <= (1 : Real) / 16)
    (hy : y ∈ Icc (-1 / 2 : Real) (1 / 2 : Real))
    (hshift : v - u = -(a * eta / (k : Real)) * m * shape x) :
    (x + a * shape x) * feedbackScoreShape v y -
        x * feedbackScoreShape u y >=
      a * shape x * feedbackScoreShape u y -
        6 * a * eta / (k : Real) * m * shape x := by
  have hkreal : 0 < (k : Real) := by exact_mod_cast hk
  have hshape := shape_mem_Icc hx
  have hchanged : x + a * shape x ∈ Icc (-1 : Real) 1 := by
    exact sparseHiddenMapCore_mem_Icc
      (a := a) (u := x) (by rw [abs_of_nonneg ha0]; exact ha) hx
  have hchangedAbs : |x + a * shape x| <= 1 := (abs_le).2 hchanged
  have hGdiff := feedbackScoreShape_lipschitz hu hv hy
  have hcoef0 : 0 <= a * eta / (k : Real) * m * shape x := by
    exact mul_nonneg
      (mul_nonneg (div_nonneg (mul_nonneg ha0 heta) hkreal.le) hm.1)
      hshape.1
  have hshiftAbs : |v - u| = a * eta / (k : Real) * m * shape x := by
    rw [hshift, show -(a * eta / (k : Real)) * m * shape x =
      -(a * eta / (k : Real) * m * shape x) by ring,
      abs_neg, abs_of_nonneg hcoef0]
  rw [hshiftAbs] at hGdiff
  have herror :
      (x + a * shape x) *
          (feedbackScoreShape v y - feedbackScoreShape u y) >=
        -(6 * a * eta / (k : Real) * m * shape x) := by
    have habsMul :
        |(x + a * shape x) *
            (feedbackScoreShape v y - feedbackScoreShape u y)| <=
          6 * a * eta / (k : Real) * m * shape x := by
      rw [abs_mul]
      calc
        |x + a * shape x| *
            |feedbackScoreShape v y - feedbackScoreShape u y| <=
          1 * (6 * (a * eta / (k : Real) * m * shape x)) :=
            mul_le_mul hchangedAbs hGdiff (abs_nonneg _) (by norm_num)
        _ = 6 * a * eta / (k : Real) * m * shape x := by ring
    exact (abs_le.mp habsMul).1
  calc
    (x + a * shape x) * feedbackScoreShape v y -
        x * feedbackScoreShape u y =
      a * shape x * feedbackScoreShape u y +
        (x + a * shape x) *
          (feedbackScoreShape v y - feedbackScoreShape u y) := by ring
    _ >= a * shape x * feedbackScoreShape u y -
        6 * a * eta / (k : Real) * m * shape x := by linarith
    _ = a * shape x * feedbackScoreShape u y -
        6 * a * eta / (k : Real) * m * shape x := rfl

/-- Chronological comparison for one transformed signal coordinate on a
history in the genuine feedback support.  The hypothesis `hshift` is the
local exact parameter identity and is discharged below for the concrete
sparse table transformation. -/
theorem sparse_observable_coordinate_drift
    {n n' k q c0 : Nat} (hk : 1 <= k) (hn' : n' <= n)
    {a eta : Real} (ha0 : 0 <= a) (ha : a <= (1 : Real) / 8)
    (heta : 0 <= eta) (U : Nat -> Fin n -> Real)
    (hU : forall b i, U b i ∈ Icc (-1 : Real) 1)
    (j : Fin n') (V W : SparseAdaptiveParameters n k)
    (hshift : forall t h A,
      W.value t h A - V.value t h A =
        -(a * eta / (k : Real)) *
          sparsePullIndicator hn' q c0 j t h A *
            shape (U (t / q) (sparseSignalCoordinate hn' j))) :
    forall T (h : History n k T), sparseHistoryInFeedbackSupport T h ->
      sparseObservableCoordinateScore W hn' q c0
          (sparseTransformTableCoordinate a hn' U j) j T h -
        sparseObservableCoordinateScore V hn' q c0 U j T h >=
      a * sparseObservablePositiveCore V hn' q c0 U j T h -
        6 * a * eta / (k : Real) *
          sparseObservablePullCount hn' q c0 j T h := by
  intro T
  induction T with
  | zero => intro h _; simp [sparseObservablePositiveCore,
      sparseObservablePullCount]
  | succ t ih =>
      intro h hsupp
      have hprev := ih h.1 hsupp.1
      let i0 := sparseSignalCoordinate hn' j
      let x := U (t / q) i0
      let m := sparsePullIndicator hn' q c0 j t h.1 h.2.1
      let u := V.value t h.1 h.2.1
      let v := W.value t h.1 h.2.1
      have hx : x ∈ Icc (-1 : Real) 1 := hU (t / q) i0
      have hm : m ∈ Icc (0 : Real) 1 :=
        sparsePullIndicator_mem_Icc hn' j h.1 h.2.1
      have hround := sparse_changed_score_increment_lower hk ha0 ha heta
        hx hm (V.abs_le t h.1 h.2.1) (W.abs_le t h.1 h.2.1) hsupp.2
        (hshift t h.1 h.2.1)
      have hi0 : i0.1 < n' := by
        simpa [i0, sparseSignalCoordinate] using j.2
      have htable :
          sparseTransformTableCoordinate a hn' U j (t / q) i0 =
            x + a * shape x := by
        simp [sparseTransformTableCoordinate, i0, x]
      rw [sparseObservableCoordinateScore_succ,
        sparseObservableCoordinateScore_succ,
        sparseObservablePositiveCore_succ,
        sparseObservablePullCount_succ, htable]
      dsimp [i0, x, m, u, v] at hround ⊢
      by_cases hactive :
          sparseBlockSelectedCount q (sparseSignalCoordinate hn' j) t h.1 <
            (c0 : Real)
      · simp [sparseActive, hactive, sparsePullIndicator] at hround ⊢
        have hshape := shape_mem_Icc
          (hU (t / q) (sparseSignalCoordinate hn' j))
        have hselected := History.selectedIndicator_mem_Icc
          (sparseSignalCoordinate hn' j) h.2.1
        have hprod :
            History.selectedIndicator (sparseSignalCoordinate hn' j) h.2.1 *
                shape (U (t / q) (sparseSignalCoordinate hn' j)) <=
              History.selectedIndicator (sparseSignalCoordinate hn' j) h.2.1 := by
          nlinarith [mul_nonneg hselected.1
            (sub_nonneg.mpr hshape.2)]
        have hcoef : 0 <= 6 * a * eta / (k : Real) := by
          exact div_nonneg (mul_nonneg (mul_nonneg (by norm_num) ha0) heta)
            (Nat.cast_nonneg k)
        have herror := mul_le_mul_of_nonneg_left hprod hcoef
        nlinarith [hprev, hround, herror]
      · simp [sparseActive, hactive, sparsePullIndicator] at hround ⊢
        linarith [hprev]

/-! ## Spending the pull-error term -/

/-- The sum of the `0/1` pull indicators is the number of active selected
signal coordinates. -/
theorem sum_sparsePullIndicator_eq_card
    {n n' k q c0 t : Nat} (hn' : n' <= n)
    (h : History n k t) (A : MSetAction n k) :
    (∑ j : Fin n', sparsePullIndicator hn' q c0 j t h A) =
      ((sparseActiveSelectedSignals hn' q c0 t h A).card : Real) := by
  classical
  let S := sparseActiveSelectedSignals hn' q c0 t h A
  calc
    (∑ j : Fin n', sparsePullIndicator hn' q c0 j t h A) =
        ∑ j ∈ (Finset.univ : Finset (Fin n')),
          if j ∈ S then (1 : Real) else 0 := by
      apply Finset.sum_congr rfl
      intro j hj
      rw [sparsePullIndicator_eq_indicator]
    _ = (((Finset.univ : Finset (Fin n')).filter fun j => j ∈ S).card : Real) := by
      simpa using
        (Finset.sum_boole (R := Real) (fun j : Fin n' => j ∈ S) Finset.univ)
    _ = (S.card : Real) := by
      rw [show (Finset.univ : Finset (Fin n')).filter (fun j => j ∈ S) = S by
        ext j
        simp]
    _ = ((sparseActiveSelectedSignals hn' q c0 t h A).card : Real) := rfl

/-- Across all signal coordinates, there are at most `kT` active pulls. -/
theorem sum_sparseObservablePullCount_le
    {n n' k q c0 : Nat} (hn' : n' <= n) :
    forall T (h : History n k T),
      (∑ j : Fin n', sparseObservablePullCount hn' q c0 j T h) <=
        (k : Real) * (T : Real) := by
  intro T
  induction T with
  | zero => intro h; simp [sparseObservablePullCount]
  | succ t ih =>
      intro h
      simp_rw [sparseObservablePullCount_succ, Finset.sum_add_distrib]
      rw [sum_sparsePullIndicator_eq_card hn' h.1 h.2.1]
      have hround := card_sparseActiveSelectedSignals_le
        (q := q) (c0 := c0) hn' h.1 h.2.1
      have hroundReal :
          ((sparseActiveSelectedSignals hn' q c0 t h.1 h.2.1).card : Real) <=
            (k : Real) := by exact_mod_cast hround
      push_cast
      nlinarith [ih h.1]

/-! ## Inactive-time counting -/

/-- Signal coordinates selected at one round, without the activity filter. -/
def sparseSelectedSignals {n n' k : Nat} (hn' : n' <= n)
    (A : MSetAction n k) : Finset (Fin n') :=
  Finset.univ.filter fun j => sparseSignalCoordinate hn' j ∈ A.1

theorem sum_signal_selectedIndicator_eq_card
    {n n' k : Nat} (hn' : n' <= n) (A : MSetAction n k) :
    (∑ j : Fin n',
        History.selectedIndicator (sparseSignalCoordinate hn' j) A) =
      ((sparseSelectedSignals hn' A).card : Real) := by
  classical
  unfold sparseSelectedSignals
  simp_rw [History.selectedIndicator]
  simpa using (Finset.sum_boole (R := Real)
    (fun j : Fin n' => sparseSignalCoordinate hn' j ∈ A.1) Finset.univ)

theorem card_sparseSelectedSignals_le
    {n n' k : Nat} (hn' : n' <= n) (A : MSetAction n k) :
    (sparseSelectedSignals hn' A).card <= k := by
  calc
    (sparseSelectedSignals hn' A).card <= A.1.card := by
      apply Finset.card_le_card_of_injOn (sparseSignalCoordinate hn')
      · intro j hj
        exact (Finset.mem_filter.mp hj).2
      · exact (sparseSignalCoordinate_injective hn').injOn
    _ = k := A.2

/-- Sum of the within-block counters over the signal coordinates. -/
def sparseSignalBlockCountSum {n n' k : Nat} (hn' : n' <= n) (q : Nat)
    (t : Nat) (h : History n k t) : Real :=
  ∑ j : Fin n',
    sparseBlockSelectedCount q (sparseSignalCoordinate hn' j) t h

/-- At zero-based time `t`, the total signal-coordinate counter is at most
`k (t mod q)`.  This is the exact invariant behind the manuscript's
within-block inactive-coordinate estimate. -/
theorem sparseSignalBlockCountSum_le_mod
    {n n' k q : Nat} (hq : 0 < q) (hn' : n' <= n) :
    forall t (h : History n k t),
      sparseSignalBlockCountSum hn' q t h <=
        (k : Real) * (t % q : Nat) := by
  intro t
  induction t with
  | zero => intro h; simp [sparseSignalBlockCountSum]
  | succ t ih =>
      intro h
      by_cases hblock : t / q = (t + 1) / q
      · have hmod : (t + 1) % q = t % q + 1 := by
          have ht := Nat.mod_add_div t q
          have hs := Nat.mod_add_div (t + 1) q
          rw [<- hblock] at hs
          omega
        simp only [sparseSignalBlockCountSum, sparseBlockSelectedCount_succ,
          hblock, if_true, Finset.sum_add_distrib]
        rw [hmod]
        have hselected := card_sparseSelectedSignals_le hn' h.2.1
        have hselectedReal :
            (∑ j : Fin n', History.selectedIndicator
              (sparseSignalCoordinate hn' j) h.2.1) <= (k : Real) := by
          rw [sum_signal_selectedIndicator_eq_card]
          exact_mod_cast hselected
        have hprev := ih h.1
        change (∑ j : Fin n',
            sparseBlockSelectedCount q (sparseSignalCoordinate hn' j) t h.1) <=
          (k : Real) * (t % q : Nat) at hprev
        push_cast
        nlinarith
      · simp only [sparseSignalBlockCountSum, sparseBlockSelectedCount_succ,
          hblock, if_false, Finset.sum_const_zero]
        exact mul_nonneg (Nat.cast_nonneg k) (Nat.cast_nonneg _)

/-- Inactive signal coordinates at one round. -/
def sparseInactiveSignals {n n' k : Nat} (hn' : n' <= n)
    (q c0 : Nat) (t : Nat) (h : History n k t) : Finset (Fin n') :=
  Finset.univ.filter fun j =>
    ¬ (sparseBlockSelectedCount q (sparseSignalCoordinate hn' j) t h <
      (c0 : Real))

/-- Markov's counting step: `c0 * #inactive <= kq`. -/
theorem sparse_inactive_count_mul_le
    {n n' k q c0 t : Nat} (hq : 0 < q) (hn' : n' <= n)
    (h : History n k t) :
    (c0 : Real) * ((sparseInactiveSignals hn' q c0 t h).card : Real) <=
      (k : Real) * (q : Real) := by
  classical
  let S := sparseInactiveSignals hn' q c0 t h
  have hcounter : ∀ j, j ∈ S ->
      (c0 : Real) <=
        sparseBlockSelectedCount q (sparseSignalCoordinate hn' j) t h := by
    intro j hj
    have hj' := (Finset.mem_filter.mp hj).2
    exact le_of_not_gt hj'
  have hnonneg : ∀ j : Fin n',
      0 <= sparseBlockSelectedCount q (sparseSignalCoordinate hn' j) t h :=
    fun j => sparseBlockSelectedCount_nonneg _ t h
  calc
    (c0 : Real) * (S.card : Real) = ∑ _j ∈ S, (c0 : Real) := by
      simp [mul_comm]
    _ <= ∑ j ∈ S,
        sparseBlockSelectedCount q (sparseSignalCoordinate hn' j) t h := by
      exact Finset.sum_le_sum fun j hj => hcounter j hj
    _ <= ∑ j : Fin n',
        sparseBlockSelectedCount q (sparseSignalCoordinate hn' j) t h := by
      exact Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ S)
        (fun j _hj _ => hnonneg j)
    _ = sparseSignalBlockCountSum hn' q t h := rfl
    _ <= (k : Real) * (t % q : Nat) :=
      sparseSignalBlockCountSum_le_mod hq hn' t h
    _ <= (k : Real) * (q : Real) := by
      exact mul_le_mul_of_nonneg_left
        (by exact_mod_cast (Nat.mod_lt t hq).le) (Nat.cast_nonneg k)

/-- Total number of inactive signal-coordinate times. -/
def sparseInactiveTime {n n' k : Nat} (hn' : n' <= n) (q c0 : Nat) :
    (T : Nat) -> History n k T -> Real
  | 0, _ => 0
  | t + 1, h => sparseInactiveTime hn' q c0 t h.1 +
      ((sparseInactiveSignals hn' q c0 t h.1).card : Real)

/-- Summed inactive-time bound before substituting `q=r ell`, `c0=8 ell`. -/
theorem sparseInactiveTime_mul_le
    {n n' k q c0 : Nat} (hq : 0 < q) (hn' : n' <= n) :
    forall T (h : History n k T),
      (c0 : Real) * sparseInactiveTime hn' q c0 T h <=
        (T : Real) * (k : Real) * (q : Real) := by
  intro T
  induction T with
  | zero => intro h; simp [sparseInactiveTime]
  | succ t ih =>
      intro h
      rw [show sparseInactiveTime hn' q c0 (t + 1) h =
        sparseInactiveTime hn' q c0 t h.1 +
          ((sparseInactiveSignals hn' q c0 t h.1).card : Real) by rfl]
      have hround := sparse_inactive_count_mul_le (c0 := c0) hq hn' h.1
      push_cast
      nlinarith [ih h.1]

/-- With `q=r ell`, `c0=8 ell`, and `n'=kr`, inactive signal-coordinate
time is at most `n'T/8`.  This coarser bound (the manuscript proves `1/16`)
still leaves enough slack for the literal `a k T/3` endpoint. -/
theorem sparseInactiveTime_le_eighth
    {n n' k q c0 r ell T : Nat} (hr : 0 < r) (hell : 0 < ell)
    (hn' : n' <= n) (hnprod : n' = k * r)
    (hqeq : q = r * ell) (hc0eq : c0 = 8 * ell)
    (h : History n k T) :
    sparseInactiveTime hn' q c0 T h <=
      (n' : Real) * (T : Real) / 8 := by
  subst q
  subst c0
  have hraw := sparseInactiveTime_mul_le
    (c0 := 8 * ell) (q := r * ell) (Nat.mul_pos hr hell) hn' T h
  have hellReal : 0 < (ell : Real) := by exact_mod_cast hell
  have hnprodReal : (n' : Real) = (k : Real) * (r : Real) := by
    exact_mod_cast hnprod
  push_cast at hraw
  have hfactor :
      (ell : Real) *
          (8 * sparseInactiveTime hn' (r * ell) (8 * ell) T h) <=
        (ell : Real) * ((T : Real) * (k : Real) * (r : Real)) := by
    calc
      (ell : Real) *
          (8 * sparseInactiveTime hn' (r * ell) (8 * ell) T h) =
        8 * (ell : Real) *
          sparseInactiveTime hn' (r * ell) (8 * ell) T h := by ring
      _ <= (T : Real) * (k : Real) * ((r : Real) * (ell : Real)) := hraw
      _ = (ell : Real) * ((T : Real) * (k : Real) * (r : Real)) := by ring
  have hcancel :
      8 * sparseInactiveTime hn' (r * ell) (8 * ell) T h <=
        (T : Real) * (k : Real) * (r : Real) :=
    le_of_mul_le_mul_left hfactor hellReal
  apply (le_div_iff₀ (by norm_num : (0 : Real) < 8)).2
  rw [hnprodReal]
  nlinarith

/-- Summing the one-coordinate drift inequalities spends at most
`6 a eta T`; the factor `k` cancels pathwise against the active-pull count. -/
theorem sparse_observable_total_drift
    {n n' k q c0 T : Nat} (hk : 1 <= k) (hn' : n' <= n)
    {a eta : Real} (ha0 : 0 <= a) (ha : a <= (1 : Real) / 8)
    (heta : 0 <= eta) (U : Nat -> Fin n -> Real)
    (hU : forall b i, U b i ∈ Icc (-1 : Real) 1)
    (V : SparseAdaptiveParameters n k)
    (W : Fin n' -> SparseAdaptiveParameters n k)
    (hshift : forall j t h A,
      (W j).value t h A - V.value t h A =
        -(a * eta / (k : Real)) *
          sparsePullIndicator hn' q c0 j t h A *
            shape (U (t / q) (sparseSignalCoordinate hn' j)))
    (h : History n k T) (hsupp : sparseHistoryInFeedbackSupport T h) :
    (∑ j : Fin n',
        (sparseObservableCoordinateScore (W j) hn' q c0
            (sparseTransformTableCoordinate a hn' U j) j T h -
          sparseObservableCoordinateScore V hn' q c0 U j T h)) >=
      a * (∑ j : Fin n',
          sparseObservablePositiveCore V hn' q c0 U j T h) -
        6 * a * eta * (T : Real) := by
  have hj : forall j : Fin n',
      sparseObservableCoordinateScore (W j) hn' q c0
          (sparseTransformTableCoordinate a hn' U j) j T h -
        sparseObservableCoordinateScore V hn' q c0 U j T h >=
      a * sparseObservablePositiveCore V hn' q c0 U j T h -
        6 * a * eta / (k : Real) *
          sparseObservablePullCount hn' q c0 j T h := fun j =>
    sparse_observable_coordinate_drift hk hn' ha0 ha heta U hU j V (W j)
      (hshift j) T h hsupp
  have hsum := Finset.sum_le_sum fun j (_hj : j ∈ (Finset.univ : Finset (Fin n'))) =>
    hj j
  rw [Finset.sum_sub_distrib, <- Finset.mul_sum, <- Finset.mul_sum] at hsum
  have hpulls := sum_sparseObservablePullCount_le
    (q := q) (c0 := c0) hn' T h
  have hkreal : 0 < (k : Real) := by exact_mod_cast hk
  have hcoef : 0 <= 6 * a * eta / (k : Real) := by positivity
  have herror := mul_le_mul_of_nonneg_left hpulls hcoef
  have hcancel :
      6 * a * eta / (k : Real) * ((k : Real) * (T : Real)) =
        6 * a * eta * (T : Real) := by field_simp
  rw [hcancel] at herror
  linarith

/-! ## Concrete parameter identity and final constant arithmetic -/

theorem sparseTransformTableCoordinate_mem_Icc
    {n n' : Nat} {a : Real} (ha0 : 0 <= a) (ha : a <= (1 : Real) / 8)
    (hn' : n' <= n) {U : Nat -> Fin n -> Real}
    (hU : forall b i, U b i ∈ Icc (-1 : Real) 1)
    (j : Fin n') (b : Nat) (i : Fin n) :
    sparseTransformTableCoordinate a hn' U j b i ∈ Icc (-1 : Real) 1 := by
  by_cases hi : i = sparseSignalCoordinate hn' j
  · subst i
    simp only [sparseTransformTableCoordinate, if_pos rfl]
    exact sparseHiddenMapCore_mem_Icc
      (by rw [abs_of_nonneg ha0]; exact ha) (hU b _)
  · simp [sparseTransformTableCoordinate, hi, hU]

/-- The actual sparse parameter fields satisfy the shift premise of the
history-preserving drift theorem, without any abstract conclusion premise. -/
theorem sparse_concrete_parameter_shift
    {n n' k q c0 : Nat} (hk : 1 <= k) (hn' : n' <= n)
    {a eta : Real} (heta0 : 0 <= eta) (heta : eta <= (1 : Real) / 16)
    (ha0 : 0 <= a) (ha : a <= (1 : Real) / 8)
    (U : Nat -> Fin n -> Real)
    (hU : forall b i, U b i ∈ Icc (-1 : Real) 1) (j : Fin n')
    (t : Nat) (h : History n k t) (A : MSetAction n k) :
    (sparseAdaptiveParametersOfTable hk eta heta0 heta n' q c0
        (sparseTransformTableCoordinate a hn' U j)
        (fun b i => (abs_le).2
          (sparseTransformTableCoordinate_mem_Icc ha0 ha hn' hU j b i))).value
          t h A -
      (sparseAdaptiveParametersOfTable hk eta heta0 heta n' q c0 U
        (fun b i => (abs_le).2 (hU b i))).value t h A =
      -(a * eta / (k : Real)) *
        sparsePullIndicator hn' q c0 j t h A *
          shape (U (t / q) (sparseSignalCoordinate hn' j)) := by
  exact sparseFeedbackParameter_transform_coordinate_sub
    a eta hn' U j t h A

/-- Arithmetic endpoint of `eq:lower-positive-drift`.  The preceding
pathwise theorem supplies `hdrift`; after the independent `U,Z` expectations
and inactive-time estimate supply `hcore`, this spends the manuscript's
constants and returns `a k T/3`. -/
theorem lower_positive_drift_arithmetic
    {a eta r k T core drift : Real}
    (ha0 : 0 <= a) (_heta0 : 0 <= eta) (hr : 2 ^ 32 <= r)
    (hk : 1 <= k) (hT : 0 <= T) (heta : eta <= (1 : Real) / 16)
    (hcore : (13 / 36 : Real) * k * T <= core)
    (hdrift : a * core - 6 * a * eta * T / r <= drift) :
    a / 3 * k * T <= drift := by
  have hrpos : 0 < r := lt_of_lt_of_le (by positivity) hr
  have hsmall : 6 * eta / r <= k / 36 := by
    have hk0 : 0 <= k := le_trans (by norm_num) hk
    apply (div_le_iff₀ hrpos).2
    have hrLarge : (6 : Real) * (1 / 16 : Real) * 36 <= r := by
      norm_num at hr ⊢
      linarith
    nlinarith
  have hcoefFinal : k / 3 <= (13 / 36 : Real) * k - 6 * eta / r := by
    linarith
  have hscaled := mul_le_mul_of_nonneg_left hcoefFinal ha0
  have hscaledT := mul_le_mul_of_nonneg_right hscaled hT
  have hleft : a / 3 * k * T = (a * (k / 3)) * T := by ring
  have hright :
      a * ((13 / 36 : Real) * k * T) - 6 * a * eta * T / r =
        (a * ((13 / 36 : Real) * k - 6 * eta / r)) * T := by ring
  calc
    a / 3 * k * T <=
        a * ((13 / 36 : Real) * k * T) -
          6 * a * eta * T / r := by
      rw [hleft, hright]
      exact hscaledT
    _ <= a * core - 6 * a * eta * T / r := by
      exact sub_le_sub_right (mul_le_mul_of_nonneg_left hcore ha0) _
    _ <= drift := hdrift

#print axioms feedbackScoreShape_lipschitz
#print axioms measurable_sparseObservableCoordinateScore
#print axioms sparse_changed_score_increment_lower
#print axioms sparse_observable_coordinate_drift
#print axioms sum_sparseObservablePullCount_le
#print axioms sparse_observable_total_drift
#print axioms sparse_concrete_parameter_shift
#print axioms lower_positive_drift_arithmetic

end

end MsetsLower.Lower.Sparse
