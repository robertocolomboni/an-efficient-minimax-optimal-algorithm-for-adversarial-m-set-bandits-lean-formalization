import MsetsLower.Lower.Sparse.Scores
import Mathlib.Data.Finset.Prod
import Mathlib.Order.ConditionallyCompleteLattice.Finset

/-!
# A sparse equipartition with few simultaneous selections

This file formalizes the pathwise counting argument and the finite averaging
step in `eq:lower-good-partition` (manuscript lines 4695--4782).  The
zero-based pull indicator below is exactly
`m_{t,j}=A_{t,j} 1{j in X_t}`.
-/

namespace MsetsLower.Lower.Sparse

open MsetsLower MeasureTheory Set
open scoped BigOperators

noncomputable section

/-! ## Simultaneous active pulls -/

/-- The manuscript's `m_{t,j}` for a signal coordinate `j : Fin n'`. -/
def sparsePullIndicator {n n' k : Nat} (hn' : n' ≤ n) (q c0 : Nat)
    (j : Fin n') (t : Nat) (h : History n k t) (A : MSetAction n k) : Real :=
  sparseActive q c0 (sparseSignalCoordinate hn' j) t h *
    History.selectedIndicator (sparseSignalCoordinate hn' j) A

theorem sparsePullIndicator_mem_Icc
    {n n' k q c0 t : Nat} (hn' : n' ≤ n) (j : Fin n')
    (h : History n k t) (A : MSetAction n k) :
    sparsePullIndicator hn' q c0 j t h A ∈ Icc (0 : Real) 1 := by
  have ha := sparseActive_mem_Icc (q := q) (c0 := c0)
    (sparseSignalCoordinate hn' j) h
  have hs := History.selectedIndicator_mem_Icc
    (sparseSignalCoordinate hn' j) A
  exact ⟨mul_nonneg ha.1 hs.1,
    (mul_le_mul ha.2 hs.2 hs.1 (by norm_num)).trans (by norm_num)⟩

/-- Active selected signal coordinates at one round. -/
def sparseActiveSelectedSignals {n n' k : Nat} (hn' : n' ≤ n)
    (q c0 : Nat) (t : Nat) (h : History n k t) (A : MSetAction n k) :
    Finset (Fin n') :=
  Finset.univ.filter fun j =>
    sparseBlockSelectedCount q (sparseSignalCoordinate hn' j) t h < (c0 : Real) ∧
      sparseSignalCoordinate hn' j ∈ A.1

@[simp] theorem mem_sparseActiveSelectedSignals
    {n n' k q c0 t : Nat} (hn' : n' ≤ n) (j : Fin n')
    (h : History n k t) (A : MSetAction n k) :
    j ∈ sparseActiveSelectedSignals hn' q c0 t h A ↔
      sparseBlockSelectedCount q (sparseSignalCoordinate hn' j) t h < (c0 : Real) ∧
        sparseSignalCoordinate hn' j ∈ A.1 := by
  simp [sparseActiveSelectedSignals]

/-- `m_{t,j}` is the `0/1` membership indicator of the preceding finset. -/
theorem sparsePullIndicator_eq_indicator
    {n n' k q c0 t : Nat} (hn' : n' ≤ n) (j : Fin n')
    (h : History n k t) (A : MSetAction n k) :
    sparsePullIndicator hn' q c0 j t h A =
      if j ∈ sparseActiveSelectedSignals hn' q c0 t h A then 1 else 0 := by
  by_cases hactive :
      sparseBlockSelectedCount q (sparseSignalCoordinate hn' j) t h < (c0 : Real)
  · by_cases hselected : sparseSignalCoordinate hn' j ∈ A.1
    · simp [sparsePullIndicator, sparseActive, History.selectedIndicator,
        hactive, hselected]
    · simp [sparsePullIndicator, sparseActive, History.selectedIndicator,
        hactive, hselected]
  · simp [sparsePullIndicator, sparseActive, History.selectedIndicator,
      hactive]

/-- At most `k` signal coordinates can be active and selected in one round. -/
theorem card_sparseActiveSelectedSignals_le
    {n n' k q c0 t : Nat} (hn' : n' ≤ n)
    (h : History n k t) (A : MSetAction n k) :
    (sparseActiveSelectedSignals hn' q c0 t h A).card ≤ k := by
  calc
    (sparseActiveSelectedSignals hn' q c0 t h A).card ≤ A.1.card := by
      apply Finset.card_le_card_of_injOn (sparseSignalCoordinate hn')
      · intro j hj
        exact (mem_sparseActiveSelectedSignals hn' j h A).mp hj |>.2
      · exact (sparseSignalCoordinate_injective hn').injOn
    _ = k := A.2

/-- The exact one-round ordered-pair count. -/
theorem sparse_round_ordered_pairs_eq_card
    {n n' k q c0 t : Nat} (hn' : n' ≤ n)
    (h : History n k t) (A : MSetAction n k) :
    (∑ p ∈ (Finset.univ : Finset (Fin n')).offDiag,
        sparsePullIndicator hn' q c0 p.1 t h A *
          sparsePullIndicator hn' q c0 p.2 t h A) =
      ((sparseActiveSelectedSignals hn' q c0 t h A).offDiag.card : Real) := by
  classical
  let S := sparseActiveSelectedSignals hn' q c0 t h A
  calc
    (∑ p ∈ (Finset.univ : Finset (Fin n')).offDiag,
        sparsePullIndicator hn' q c0 p.1 t h A *
          sparsePullIndicator hn' q c0 p.2 t h A) =
      ∑ p ∈ (Finset.univ : Finset (Fin n')).offDiag,
        if p ∈ S.offDiag then (1 : Real) else 0 := by
          apply Finset.sum_congr rfl
          intro p hp
          rw [sparsePullIndicator_eq_indicator,
            sparsePullIndicator_eq_indicator]
          have hpne : p.1 ≠ p.2 := (Finset.mem_offDiag.mp hp).2.2
          by_cases hp1 : p.1 ∈ S <;> by_cases hp2 : p.2 ∈ S <;>
            simp [S, hp1, hp2, Finset.mem_offDiag, hpne]
    _ = (((Finset.univ : Finset (Fin n')).offDiag.filter
          fun p => p ∈ S.offDiag).card : Real) := by
      simpa using
        (Finset.sum_boole (R := Real) (fun p : Fin n' × Fin n' => p ∈ S.offDiag)
          (Finset.univ.offDiag))
    _ = (S.offDiag.card : Real) := by
      have hfilter :
          (Finset.univ : Finset (Fin n')).offDiag.filter
              (fun p => p ∈ S.offDiag) = S.offDiag := by
        ext p
        simp [Finset.mem_offDiag]
      rw [hfilter]

/-- At one round the number of ordered pairs is at most `k(k-1)`, hence at
most `k²`, exactly as used in the manuscript. -/
theorem sparse_round_ordered_pairs_le_sq
    {n n' k q c0 t : Nat} (hn' : n' ≤ n)
    (h : History n k t) (A : MSetAction n k) :
    ((sparseActiveSelectedSignals hn' q c0 t h A).offDiag.card : Real) ≤
      (k : Real) ^ 2 := by
  have hcard := card_sparseActiveSelectedSignals_le
    (q := q) (c0 := c0) hn' h A
  have hoff :
      (sparseActiveSelectedSignals hn' q c0 t h A).offDiag.card ≤ k * k := by
    rw [Finset.offDiag_card]
    exact (Nat.sub_le _ _).trans (Nat.mul_le_mul hcard hcard)
  have hoffReal :
      ((sparseActiveSelectedSignals hn' q c0 t h A).offDiag.card : Real) ≤
        ((k * k : Nat) : Real) := by exact_mod_cast hoff
  simpa [pow_two] using hoffReal

/-- The unnormalized simultaneous-pull sum for a fixed ordered pair. -/
def sparsePairPullSum {n n' k : Nat} (hn' : n' ≤ n) (q c0 : Nat)
    (j l : Fin n') : (t : Nat) → History n k t → Real
  | 0, _ => 0
  | t + 1, h =>
      sparsePairPullSum hn' q c0 j l t h.1 +
        sparsePullIndicator hn' q c0 j t h.1 h.2.1 *
          sparsePullIndicator hn' q c0 l t h.1 h.2.1

@[simp] theorem sparsePairPullSum_zero
    {n n' k q c0 : Nat} (hn' : n' ≤ n) (j l : Fin n')
    (h : History n k 0) :
    sparsePairPullSum hn' q c0 j l 0 h = 0 := rfl

@[simp] theorem sparsePairPullSum_succ
    {n n' k q c0 t : Nat} (hn' : n' ≤ n) (j l : Fin n')
    (h : History n k (t + 1)) :
    sparsePairPullSum hn' q c0 j l (t + 1) h =
      sparsePairPullSum hn' q c0 j l t h.1 +
        sparsePullIndicator hn' q c0 j t h.1 h.2.1 *
          sparsePullIndicator hn' q c0 l t h.1 h.2.1 := rfl

/-- The literal quantity `N_{jl}=k⁻² sum_t m_{t,j}m_{t,l}`. -/
def sparseN {n n' k : Nat} (hn' : n' ≤ n) (q c0 : Nat)
    (j l : Fin n') (t : Nat) (h : History n k t) : Real :=
  sparsePairPullSum hn' q c0 j l t h / (k : Real) ^ 2

theorem sparsePairPullSum_nonneg
    {n n' k q c0 : Nat} (hn' : n' ≤ n) (j l : Fin n') :
    ∀ t (h : History n k t), 0 ≤ sparsePairPullSum hn' q c0 j l t h := by
  intro t
  induction t with
  | zero => intro h; simp
  | succ t ih =>
      intro h
      rw [sparsePairPullSum_succ]
      exact add_nonneg (ih h.1)
        (mul_nonneg (sparsePullIndicator_mem_Icc hn' j h.1 h.2.1).1
          (sparsePullIndicator_mem_Icc hn' l h.1 h.2.1).1)

theorem sparseN_nonneg
    {n n' k q c0 t : Nat} (hn' : n' ≤ n) (j l : Fin n')
    (h : History n k t) : 0 ≤ sparseN hn' q c0 j l t h := by
  exact div_nonneg (sparsePairPullSum_nonneg hn' j l t h) (sq_nonneg _)

theorem measurable_sparsePullIndicator_joint
    {n n' k q c0 t : Nat} (hn' : n' ≤ n) (j : Fin n') :
    Measurable (fun p : History n k t × MSetAction n k =>
      sparsePullIndicator hn' q c0 j t p.1 p.2) := by
  exact ((measurable_sparseActive (q := q) (c0 := c0)
    (sparseSignalCoordinate hn' j) t).comp measurable_fst).mul
      ((measurable_of_finite
        (History.selectedIndicator (sparseSignalCoordinate hn' j))).comp measurable_snd)

theorem measurable_sparsePairPullSum
    {n n' k q c0 : Nat} (hn' : n' ≤ n) (j l : Fin n') :
    ∀ t, Measurable (sparsePairPullSum (k := k) hn' q c0 j l t) := by
  intro t
  induction t with
  | zero => exact measurable_const
  | succ t ih =>
      change Measurable (fun h : History n k (t + 1) =>
        sparsePairPullSum hn' q c0 j l t h.1 +
          sparsePullIndicator hn' q c0 j t h.1 h.2.1 *
            sparsePullIndicator hn' q c0 l t h.1 h.2.1)
      have hpair : Measurable (fun h : History n k (t + 1) => (h.1, h.2.1)) :=
        measurable_fst.prodMk (measurable_fst.comp measurable_snd)
      exact (ih.comp measurable_fst).add
        (((measurable_sparsePullIndicator_joint (q := q) (c0 := c0) hn' j).comp
          hpair).mul
        ((measurable_sparsePullIndicator_joint (q := q) (c0 := c0) hn' l).comp
          hpair))

theorem measurable_sparseN
    {n n' k q c0 : Nat} (hn' : n' ≤ n) (j l : Fin n') (t : Nat) :
    Measurable (sparseN (k := k) hn' q c0 j l t) :=
  (measurable_sparsePairPullSum (k := k) hn' j l t).div_const _

theorem sparsePairPullSum_le
    {n n' k q c0 : Nat} (hn' : n' ≤ n) (j l : Fin n') :
    ∀ t (h : History n k t), sparsePairPullSum hn' q c0 j l t h ≤ (t : Real) := by
  intro t
  induction t with
  | zero => intro h; simp
  | succ t ih =>
      intro h
      rw [sparsePairPullSum_succ]
      have hj := sparsePullIndicator_mem_Icc (q := q) (c0 := c0) hn' j h.1 h.2.1
      have hl := sparsePullIndicator_mem_Icc (q := q) (c0 := c0) hn' l h.1 h.2.1
      have hprod :
          sparsePullIndicator hn' q c0 j t h.1 h.2.1 *
            sparsePullIndicator hn' q c0 l t h.1 h.2.1 ≤ 1 :=
        (mul_le_mul hj.2 hl.2 hl.1 (by norm_num)).trans (by norm_num)
      push_cast
      nlinarith [ih h.1]

theorem sparseN_le_rounds
    {n n' k q c0 t : Nat} (hk : 1 ≤ k) (hn' : n' ≤ n)
    (j l : Fin n') (h : History n k t) :
    sparseN hn' q c0 j l t h ≤ (t : Real) := by
  have hkpos : 0 < (k : Real) := by exact_mod_cast hk
  have hkone : (1 : Real) ≤ (k : Real) := by exact_mod_cast hk
  have hden : (1 : Real) ≤ (k : Real) ^ 2 := by nlinarith
  rw [sparseN]
  apply (div_le_iff₀ (sq_pos_of_pos hkpos)).2
  exact (sparsePairPullSum_le hn' j l t h).trans
    (le_mul_of_one_le_right (Nat.cast_nonneg t) hden)

/-- `N_{jl}` is integrable under every finite law on the final history. -/
theorem integrable_sparseN
    {n n' k q c0 t : Nat} (hk : 1 ≤ k) (hn' : n' ≤ n)
    (j l : Fin n') (μ : Measure (History n k t)) [IsFiniteMeasure μ] :
    Integrable (sparseN hn' q c0 j l t) μ := by
  apply Integrable.mono' (integrable_const (t : Real))
  · exact (measurable_sparseN hn' j l t).aestronglyMeasurable
  · filter_upwards with h
    rw [Real.norm_eq_abs, abs_of_nonneg (sparseN_nonneg hn' j l h)]
    exact sparseN_le_rounds hk hn' j l h

/-- Expectation of `N_{jl}` under a history law. -/
def sparseExpectedN
    {n n' k t : Nat} (μ : Measure (History n k t)) (hn' : n' ≤ n)
    (q c0 : Nat) (j l : Fin n') : Real :=
  ∫ h, sparseN hn' q c0 j l t h ∂μ

theorem sparseExpectedN_nonneg
    {n n' k q c0 t : Nat} (μ : Measure (History n k t))
    (hn' : n' ≤ n) (j l : Fin n') :
    0 ≤ sparseExpectedN μ hn' q c0 j l :=
  integral_nonneg fun h => sparseN_nonneg hn' j l h

/-- Total number of active selected ordered signal pairs along a history. -/
def sparseTotalOrderedPulls {n n' k : Nat} (hn' : n' ≤ n) (q c0 : Nat) :
    (t : Nat) → History n k t → Real
  | 0, _ => 0
  | t + 1, h =>
      sparseTotalOrderedPulls hn' q c0 t h.1 +
        ((sparseActiveSelectedSignals hn' q c0 t h.1 h.2.1).offDiag.card : Real)

/-- Summing the pairwise pull counts gives the total ordered-pair count. -/
theorem sum_sparsePairPullSum_eq_total
    {n n' k q c0 : Nat} (hn' : n' ≤ n) :
    ∀ t (h : History n k t),
      (∑ p ∈ (Finset.univ : Finset (Fin n')).offDiag,
          sparsePairPullSum hn' q c0 p.1 p.2 t h) =
        sparseTotalOrderedPulls hn' q c0 t h := by
  intro t
  induction t with
  | zero => intro h; simp [sparseTotalOrderedPulls]
  | succ t ih =>
      intro h
      rcases h with ⟨hprev, A, feedback⟩
      change
        (∑ p ∈ (Finset.univ : Finset (Fin n')).offDiag,
          (sparsePairPullSum hn' q c0 p.1 p.2 t hprev +
            sparsePullIndicator hn' q c0 p.1 t hprev A *
              sparsePullIndicator hn' q c0 p.2 t hprev A)) =
        sparseTotalOrderedPulls hn' q c0 t hprev +
          ((sparseActiveSelectedSignals hn' q c0 t hprev A).offDiag.card : Real)
      rw [Finset.sum_add_distrib, ih hprev,
        sparse_round_ordered_pairs_eq_card]

/-- Pathwise, the total ordered-pair count is at most `t k²`. -/
theorem sparseTotalOrderedPulls_le
    {n n' k q c0 : Nat} (hn' : n' ≤ n) :
    ∀ t (h : History n k t),
      sparseTotalOrderedPulls hn' q c0 t h ≤ (t : Real) * (k : Real) ^ 2 := by
  intro t
  induction t with
  | zero => intro h; simp [sparseTotalOrderedPulls]
  | succ t ih =>
      intro h
      rcases h with ⟨hprev, A, feedback⟩
      change sparseTotalOrderedPulls hn' q c0 t hprev +
          ((sparseActiveSelectedSignals hn' q c0 t hprev A).offDiag.card : Real) ≤
        ((t + 1 : Nat) : Real) * (k : Real) ^ 2
      have hround := sparse_round_ordered_pairs_le_sq
        (q := q) (c0 := c0) hn' hprev A
      push_cast
      nlinarith [ih hprev]

/-- The pathwise estimate `sum_{j≠l} N_{jl} ≤ T0`. -/
theorem sum_sparseN_offDiag_le
    {n n' k q c0 t : Nat} (hk : 1 ≤ k) (hn' : n' ≤ n)
    (h : History n k t) :
    (∑ p ∈ (Finset.univ : Finset (Fin n')).offDiag,
        sparseN hn' q c0 p.1 p.2 t h) ≤ (t : Real) := by
  have hkpos : 0 < (k : Real) := by exact_mod_cast hk
  simp only [sparseN]
  rw [← Finset.sum_div]
  rw [sum_sparsePairPullSum_eq_total]
  apply (div_le_iff₀ (sq_pos_of_pos hkpos)).2
  simpa [mul_comm] using sparseTotalOrderedPulls_le hn' t h

/-- Integrating the pathwise ordered-pair bound gives the corresponding
bound on the sum of expectations. -/
theorem sum_sparseExpectedN_offDiag_le
    {n n' k q c0 t : Nat} (hk : 1 ≤ k) (hn' : n' ≤ n)
    (μ : Measure (History n k t)) [IsProbabilityMeasure μ] :
    (∑ p ∈ (Finset.univ : Finset (Fin n')).offDiag,
        sparseExpectedN μ hn' q c0 p.1 p.2) ≤ (t : Real) := by
  have hint : ∀ p ∈ (Finset.univ : Finset (Fin n')).offDiag,
      Integrable (sparseN hn' q c0 p.1 p.2 t) μ := by
    intro p hp
    exact integrable_sparseN hk hn' p.1 p.2 μ
  have hsumInt : Integrable (fun h =>
      ∑ p ∈ (Finset.univ : Finset (Fin n')).offDiag,
        sparseN hn' q c0 p.1 p.2 t h) μ :=
    integrable_finsetSum _ hint
  have hmono := integral_mono hsumInt (integrable_const (t : Real))
    (fun h => sum_sparseN_offDiag_le hk hn' h)
  rw [integral_finsetSum _ hint] at hmono
  have hconst : (∫ _h : History n k t, (t : Real) ∂μ) = (t : Real) := by simp
  rw [hconst] at hmono
  unfold sparseExpectedN
  exact hmono

/-! ## Uniform equipartitions from permutations -/

/-- The canonical identification `[n'] ≃ [k] × [r]` when `n'=kr`. -/
def sparseProductEquiv {n' k r : Nat} (hprod : n' = k * r) :
    Fin n' ≃ Fin k × Fin r :=
  (Equiv.cast (congrArg Fin hprod)).trans finProdFinEquiv.symm

/-- A permutation determines a labeled equipartition: apply the permutation,
then take the first coordinate under `[n'] ≃ [k] × [r]`. -/
def sparsePartitionLabel {n' k r : Nat} (hprod : n' = k * r)
    (σ : Equiv.Perm (Fin n')) (j : Fin n') : Fin k :=
  (sparseProductEquiv hprod (σ j)).1

/-- Group `G_g` of the equipartition encoded by `σ`. -/
def sparsePartitionGroup {n' k r : Nat} (hprod : n' = k * r)
    (σ : Equiv.Perm (Fin n')) (g : Fin k) : Finset (Fin n') :=
  Finset.univ.filter fun j => sparsePartitionLabel hprod σ j = g

private def sparseBaseGroupEquiv {n' k r : Nat} (hprod : n' = k * r)
    (g : Fin k) :
    {j : Fin n' // j ∈ Finset.univ.filter
      (fun x => (sparseProductEquiv hprod x).1 = g)} ≃ Fin r where
  toFun j := (sparseProductEquiv hprod j.1).2
  invFun s := ⟨(sparseProductEquiv hprod).symm (g, s), by
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    simp⟩
  left_inv j := by
    apply Subtype.ext
    apply (sparseProductEquiv hprod).injective
    have hj : (sparseProductEquiv hprod j.1).1 = g := by
      simpa only [Finset.mem_filter, Finset.mem_univ, true_and] using j.2
    rw [Equiv.apply_symm_apply]
    apply Prod.ext
    · exact hj.symm
    · rfl
  right_inv s := by simp

/-- Every group in the permutation equipartition has exactly `r` elements. -/
theorem card_sparsePartitionGroup
    {n' k r : Nat} (hprod : n' = k * r)
    (σ : Equiv.Perm (Fin n')) (g : Fin k) :
    (sparsePartitionGroup hprod σ g).card = r := by
  classical
  let base : Finset (Fin n') :=
    Finset.univ.filter fun x => (sparseProductEquiv hprod x).1 = g
  have hperm : (sparsePartitionGroup hprod σ g).card = base.card := by
    apply Finset.card_equiv σ
    intro j
    change (j ∈ Finset.univ.filter (fun x => (sparseProductEquiv hprod (σ x)).1 = g)) ↔
      (σ j ∈ Finset.univ.filter (fun x => (sparseProductEquiv hprod x).1 = g))
    constructor <;> intro hj
    · exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, (Finset.mem_filter.mp hj).2⟩
    · exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, (Finset.mem_filter.mp hj).2⟩
  rw [hperm, ← Fintype.card_coe]
  exact (Fintype.card_congr (sparseBaseGroupEquiv hprod g)).trans
    (Fintype.card_fin r)

/-- Ordered pairs put in the same group by `σ`. -/
def sparseSameGroupPairs {n' k r : Nat} (hprod : n' = k * r)
    (σ : Equiv.Perm (Fin n')) : Finset (Fin n' × Fin n') :=
  (Finset.univ : Finset (Fin n')).offDiag.filter fun p =>
    sparsePartitionLabel hprod σ p.1 = sparsePartitionLabel hprod σ p.2

/-- The same-group ordered pairs are the disjoint union of the group
off-diagonals. -/
theorem sparseSameGroupPairs_eq_biUnion
    {n' k r : Nat} (hprod : n' = k * r)
    (σ : Equiv.Perm (Fin n')) :
    sparseSameGroupPairs hprod σ =
      Finset.univ.biUnion fun g : Fin k =>
        (sparsePartitionGroup hprod σ g).offDiag := by
  classical
  ext p
  constructor
  · intro hp
    have hpfilter := Finset.mem_filter.mp hp
    have hpoff := Finset.mem_offDiag.mp hpfilter.1
    apply Finset.mem_biUnion.mpr
    refine ⟨sparsePartitionLabel hprod σ p.1, Finset.mem_univ _, ?_⟩
    apply Finset.mem_offDiag.mpr
    refine ⟨?_, ?_, hpoff.2.2⟩
    · simp [sparsePartitionGroup]
    · simpa [sparsePartitionGroup] using hpfilter.2.symm
  · intro hp
    rcases Finset.mem_biUnion.mp hp with ⟨g, hg, hpg⟩
    have hp' := Finset.mem_offDiag.mp hpg
    have h1 : sparsePartitionLabel hprod σ p.1 = g := by
      simpa [sparsePartitionGroup] using hp'.1
    have h2 : sparsePartitionLabel hprod σ p.2 = g := by
      simpa [sparsePartitionGroup] using hp'.2.1
    apply Finset.mem_filter.mpr
    exact ⟨Finset.mem_offDiag.mpr
      ⟨Finset.mem_univ _, Finset.mem_univ _, hp'.2.2⟩, h1.trans h2.symm⟩

/-- Every equipartition has exactly `n'(r-1)` ordered same-group pairs. -/
theorem card_sparseSameGroupPairs
    {n' k r : Nat} (hprod : n' = k * r)
    (σ : Equiv.Perm (Fin n')) :
    (sparseSameGroupPairs hprod σ).card = n' * (r - 1) := by
  classical
  rw [sparseSameGroupPairs_eq_biUnion]
  have hdisj :
      ((Finset.univ : Finset (Fin k)) : Set (Fin k)).PairwiseDisjoint
        (fun g => (sparsePartitionGroup hprod σ g).offDiag) := by
    intro g hg l hl hgl
    change Disjoint (sparsePartitionGroup hprod σ g).offDiag
      (sparsePartitionGroup hprod σ l).offDiag
    rw [Finset.disjoint_left]
    intro p hpg hpl
    have hpg' := Finset.mem_offDiag.mp hpg
    have hpl' := Finset.mem_offDiag.mp hpl
    have hglabel : sparsePartitionLabel hprod σ p.1 = g := by
      simpa [sparsePartitionGroup] using hpg'.1
    have hllabel : sparsePartitionLabel hprod σ p.1 = l := by
      simpa [sparsePartitionGroup] using hpl'.1
    exact hgl (hglabel.symm.trans hllabel)
  rw [Finset.card_biUnion hdisj]
  simp_rw [Finset.offDiag_card, card_sparsePartitionGroup hprod]
  simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin,
    nsmul_eq_mul]
  subst n'
  have hrsub : r * r - r = r * (r - 1) := by
    calc
      r * r - r = r * r - r * 1 := by simp
      _ = r * (r - 1) := (Nat.mul_sub_left_distrib r r 1).symm
  rw [hrsub]
  norm_num
  ac_rfl

/-- Number of permutations that put a fixed ordered pair in one group. -/
def sparseUniformPairCount {n' k r : Nat} (hprod : n' = k * r)
    (p : Fin n' × Fin n') : Nat :=
  ((Finset.univ : Finset (Equiv.Perm (Fin n'))).filter fun σ =>
    sparsePartitionLabel hprod σ p.1 = sparsePartitionLabel hprod σ p.2).card

private theorem pairEmbedding_injective
    {n' : Nat} {a b : Fin n'} (hab : a ≠ b) :
    Function.Injective (fun s : Bool => if s then b else a) := by
  intro s t hst
  cases s <;> cases t <;> simp_all

/-- By relabeling coordinates, every ordered distinct pair occurs in the same
number of permutation equipartitions. -/
theorem sparseUniformPairCount_eq
    {n' k r : Nat} (hprod : n' = k * r)
    {p q : Fin n' × Fin n'}
    (hp : p ∈ (Finset.univ : Finset (Fin n')).offDiag)
    (hq : q ∈ (Finset.univ : Finset (Fin n')).offDiag) :
    sparseUniformPairCount hprod p = sparseUniformPairCount hprod q := by
  classical
  have hpne : p.1 ≠ p.2 := (Finset.mem_offDiag.mp hp).2.2
  have hqne : q.1 ≠ q.2 := (Finset.mem_offDiag.mp hq).2.2
  obtain ⟨τ, hτ⟩ := Equiv.Perm.exists_extending_pair
    (fun s : Bool => if s then q.2 else q.1)
    (fun s : Bool => if s then p.2 else p.1)
    (pairEmbedding_injective hqne) (pairEmbedding_injective hpne)
  have hτ1 : τ q.1 = p.1 := by simpa using hτ false
  have hτ2 : τ q.2 = p.2 := by simpa using hτ true
  unfold sparseUniformPairCount
  apply Finset.card_equiv (Equiv.mulRight τ)
  intro σ
  simp only [Finset.mem_filter, Finset.mem_univ, true_and,
    Equiv.coe_mulRight]
  change
    (sparseProductEquiv hprod (σ p.1)).1 =
        (sparseProductEquiv hprod (σ p.2)).1 ↔
      (sparseProductEquiv hprod ((σ * τ) q.1)).1 =
        (sparseProductEquiv hprod ((σ * τ) q.2)).1
  rw [Equiv.Perm.mul_apply, Equiv.Perm.mul_apply]
  rw [hτ1, hτ2]

/-- Double counting the same-group incidences over all permutations. -/
theorem sum_sparseUniformPairCount
    {n' k r : Nat} (hprod : n' = k * r) :
    (∑ p ∈ (Finset.univ : Finset (Fin n')).offDiag,
        sparseUniformPairCount hprod p) =
      Fintype.card (Equiv.Perm (Fin n')) * (n' * (r - 1)) := by
  classical
  calc
    (∑ p ∈ (Finset.univ : Finset (Fin n')).offDiag,
        sparseUniformPairCount hprod p) =
      ∑ p ∈ (Finset.univ : Finset (Fin n')).offDiag,
        ∑ σ : Equiv.Perm (Fin n'),
          if sparsePartitionLabel hprod σ p.1 =
              sparsePartitionLabel hprod σ p.2 then 1 else 0 := by
        apply Finset.sum_congr rfl
        intro p hp
        rw [sparseUniformPairCount]
        exact (Finset.sum_boole (R := Nat)
          (fun σ : Equiv.Perm (Fin n') =>
            sparsePartitionLabel hprod σ p.1 =
              sparsePartitionLabel hprod σ p.2) Finset.univ).symm
    _ = ∑ σ : Equiv.Perm (Fin n'),
        ∑ p ∈ (Finset.univ : Finset (Fin n')).offDiag,
          if sparsePartitionLabel hprod σ p.1 =
              sparsePartitionLabel hprod σ p.2 then 1 else 0 := by
        rw [Finset.sum_comm]
    _ = ∑ σ : Equiv.Perm (Fin n'), (sparseSameGroupPairs hprod σ).card := by
        apply Finset.sum_congr rfl
        intro σ hσ
        rw [sparseSameGroupPairs]
        exact Finset.sum_boole (R := Nat)
          (fun p : Fin n' × Fin n' =>
            sparsePartitionLabel hprod σ p.1 =
              sparsePartitionLabel hprod σ p.2) Finset.univ.offDiag
    _ = Fintype.card (Equiv.Perm (Fin n')) * (n' * (r - 1)) := by
      simp_rw [card_sparseSameGroupPairs (hprod := hprod)]
      simp

/-- Exact same-group probability for the uniform permutation
equipartition: `(r-1)/(n'-1)`. -/
theorem sparseUniformPairFraction
    {n' k r : Nat} (hn' : 2 ≤ n') (hprod : n' = k * r)
    {p : Fin n' × Fin n'}
    (hp : p ∈ (Finset.univ : Finset (Fin n')).offDiag) :
    (sparseUniformPairCount hprod p : Real) /
        (Fintype.card (Equiv.Perm (Fin n')) : Real) =
      ((r - 1 : Nat) : Real) / ((n' - 1 : Nat) : Real) := by
  classical
  let C := Fintype.card (Equiv.Perm (Fin n'))
  let M := sparseUniformPairCount hprod p
  have hconstant :
      (∑ q ∈ (Finset.univ : Finset (Fin n')).offDiag,
          sparseUniformPairCount hprod q) =
        ((Finset.univ : Finset (Fin n')).offDiag.card) * M := by
    calc
      _ = ∑ _q ∈ (Finset.univ : Finset (Fin n')).offDiag, M := by
        apply Finset.sum_congr rfl
        intro q hq
        exact sparseUniformPairCount_eq hprod hq hp
      _ = ((Finset.univ : Finset (Fin n')).offDiag.card) * M := by simp
  have hcount :
      n' * (n' - 1) * M = C * (n' * (r - 1)) := by
    rw [← sum_sparseUniformPairCount hprod, hconstant]
    simp only [Finset.offDiag_card, Finset.card_univ, Fintype.card_fin]
    have hsub : n' * n' - n' = n' * (n' - 1) := by
      calc
        n' * n' - n' = n' * n' - n' * 1 := by simp
        _ = n' * (n' - 1) := (Nat.mul_sub_left_distrib n' n' 1).symm
    rw [hsub]
  have hnpos : 0 < n' := by omega
  have hcancel : (n' - 1) * M = C * (r - 1) := by
    apply Nat.mul_left_cancel hnpos
    calc
      n' * ((n' - 1) * M) = n' * (n' - 1) * M := by ring
      _ = C * (n' * (r - 1)) := hcount
      _ = n' * (C * (r - 1)) := by ring
  have hCpos : 0 < C := by
    dsimp [C]
    exact Fintype.card_pos_iff.mpr ⟨1⟩
  have hnsubpos : 0 < n' - 1 := by omega
  have hcancelReal :
      ((n' - 1 : Nat) : Real) * (M : Real) =
        (C : Real) * ((r - 1 : Nat) : Real) := by exact_mod_cast hcancel
  apply (div_eq_div_iff (by exact_mod_cast (Nat.ne_of_gt hCpos))
    (by exact_mod_cast (Nat.ne_of_gt hnsubpos))).2
  dsimp [M, C] at hcancelReal ⊢
  nlinarith

/-- The manuscript's numerical comparison
`(r-1)/(n'-1) ≤ 1/k`. -/
theorem sparseUniformPairFraction_le
    {n' k r : Nat} (hk : 1 ≤ k)
    (hn' : 2 ≤ n') (hprod : n' = k * r)
    {p : Fin n' × Fin n'}
    (hp : p ∈ (Finset.univ : Finset (Fin n')).offDiag) :
    (sparseUniformPairCount hprod p : Real) /
        (Fintype.card (Equiv.Perm (Fin n')) : Real) ≤
      (1 : Real) / (k : Real) := by
  rw [sparseUniformPairFraction hn' hprod hp]
  have hkpos : 0 < (k : Real) := by exact_mod_cast hk
  have hnsubposNat : 0 < n' - 1 := by omega
  have hnsubpos : 0 < ((n' - 1 : Nat) : Real) := by exact_mod_cast hnsubposNat
  have hnat : (r - 1) * k ≤ n' - 1 := by
    subst n'
    calc
      (r - 1) * k = r * k - 1 * k := Nat.sub_mul r 1 k
      _ = k * r - k := by simp [mul_comm]
      _ ≤ k * r - 1 := Nat.sub_le_sub_left hk (k * r)
  have hreal : ((r - 1 : Nat) : Real) * (k : Real) ≤
      ((n' - 1 : Nat) : Real) := by exact_mod_cast hnat
  apply (div_le_iff₀ hnsubpos).2
  calc
    ((r - 1 : Nat) : Real) ≤ ((n' - 1 : Nat) : Real) / (k : Real) :=
      (le_div_iff₀ hkpos).2 hreal
    _ = (1 : Real) / (k : Real) * ((n' - 1 : Nat) : Real) := by ring

/-- Weighted same-group sum for the equipartition encoded by `σ`. -/
def sparsePartitionCrossWeight {n' k r : Nat} (hprod : n' = k * r)
    (W : Fin n' × Fin n' → Real) (σ : Equiv.Perm (Fin n')) : Real :=
  ∑ p ∈ (Finset.univ : Finset (Fin n')).offDiag,
    if sparsePartitionLabel hprod σ p.1 =
        sparsePartitionLabel hprod σ p.2 then W p else 0

theorem pairwiseDisjoint_sparsePartitionGroups_offDiag
    {n' k r : Nat} (hprod : n' = k * r)
    (σ : Equiv.Perm (Fin n')) :
    ((Finset.univ : Finset (Fin k)) : Set (Fin k)).PairwiseDisjoint
      (fun g => (sparsePartitionGroup hprod σ g).offDiag) := by
  classical
  intro g hg l hl hgl
  change Disjoint (sparsePartitionGroup hprod σ g).offDiag
    (sparsePartitionGroup hprod σ l).offDiag
  rw [Finset.disjoint_left]
  intro p hpg hpl
  have hpg' := Finset.mem_offDiag.mp hpg
  have hpl' := Finset.mem_offDiag.mp hpl
  have hglabel : sparsePartitionLabel hprod σ p.1 = g := by
    simpa [sparsePartitionGroup] using hpg'.1
  have hllabel : sparsePartitionLabel hprod σ p.1 = l := by
    simpa [sparsePartitionGroup] using hpl'.1
  exact hgl (hglabel.symm.trans hllabel)

/-- Rewriting the label presentation as the displayed sum over groups. -/
theorem sparsePartitionCrossWeight_eq_group_sum
    {n' k r : Nat} (hprod : n' = k * r)
    (W : Fin n' × Fin n' → Real) (σ : Equiv.Perm (Fin n')) :
    sparsePartitionCrossWeight hprod W σ =
      ∑ g : Fin k, ∑ p ∈ (sparsePartitionGroup hprod σ g).offDiag, W p := by
  classical
  calc
    sparsePartitionCrossWeight hprod W σ =
        ∑ p ∈ sparseSameGroupPairs hprod σ, W p := by
      unfold sparsePartitionCrossWeight sparseSameGroupPairs
      exact (Finset.sum_filter _ W).symm
    _ = ∑ p ∈ Finset.univ.biUnion
          (fun g : Fin k => (sparsePartitionGroup hprod σ g).offDiag), W p := by
      rw [← sparseSameGroupPairs_eq_biUnion hprod σ]
    _ = ∑ g : Fin k,
          ∑ p ∈ (sparsePartitionGroup hprod σ g).offDiag, W p :=
      Finset.sum_biUnion
        (pairwiseDisjoint_sparsePartitionGroups_offDiag hprod σ)

/-- Fubini expansion of the sum over uniform permutation equipartitions. -/
theorem sum_sparsePartitionCrossWeight
    {n' k r : Nat} (hprod : n' = k * r)
    (W : Fin n' × Fin n' → Real) :
    (∑ σ : Equiv.Perm (Fin n'), sparsePartitionCrossWeight hprod W σ) =
      ∑ p ∈ (Finset.univ : Finset (Fin n')).offDiag,
        W p * (sparseUniformPairCount hprod p : Real) := by
  classical
  unfold sparsePartitionCrossWeight
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro p hp
  calc
    (∑ σ : Equiv.Perm (Fin n'),
        if sparsePartitionLabel hprod σ p.1 =
            sparsePartitionLabel hprod σ p.2 then W p else 0) =
      W p * ∑ σ : Equiv.Perm (Fin n'),
        if sparsePartitionLabel hprod σ p.1 =
            sparsePartitionLabel hprod σ p.2 then (1 : Real) else 0 := by
          rw [Finset.mul_sum]
          apply Finset.sum_congr rfl
          intro σ hσ
          split_ifs <;> ring
    _ = W p * (sparseUniformPairCount hprod p : Real) := by
      rw [sparseUniformPairCount]
      congr 1
      exact Finset.sum_boole (R := Real)
        (fun σ : Equiv.Perm (Fin n') =>
          sparsePartitionLabel hprod σ p.1 =
            sparsePartitionLabel hprod σ p.2) Finset.univ

/-- The average weighted cross-group contribution is at most `1/k` of the
total off-diagonal weight. -/
theorem sparse_uniform_cross_average_le
    {n' k r : Nat} (hk : 1 ≤ k)
    (hn' : 2 ≤ n') (hprod : n' = k * r)
    (W : Fin n' × Fin n' → Real) (hW : ∀ p, 0 ≤ W p) :
    (∑ σ : Equiv.Perm (Fin n'), sparsePartitionCrossWeight hprod W σ) /
        (Fintype.card (Equiv.Perm (Fin n')) : Real) ≤
      (∑ p ∈ (Finset.univ : Finset (Fin n')).offDiag, W p) / (k : Real) := by
  classical
  let C : Real := Fintype.card (Equiv.Perm (Fin n'))
  have hCposNat : 0 < Fintype.card (Equiv.Perm (Fin n')) :=
    Fintype.card_pos_iff.mpr ⟨1⟩
  have hCpos : 0 < C := by
    dsimp [C]
    exact_mod_cast hCposNat
  rw [sum_sparsePartitionCrossWeight]
  have hterm : ∀ p ∈ (Finset.univ : Finset (Fin n')).offDiag,
      W p * (sparseUniformPairCount hprod p : Real) ≤
        W p * (C / (k : Real)) := by
    intro p hp
    apply mul_le_mul_of_nonneg_left _ (hW p)
    have hfraction := sparseUniformPairFraction_le hk hn' hprod hp
    have hfraction' :
        (sparseUniformPairCount hprod p : Real) / C ≤
          (1 : Real) / (k : Real) := by simpa [C] using hfraction
    have hmul := (div_le_iff₀ hCpos).mp hfraction'
    calc
      (sparseUniformPairCount hprod p : Real) ≤
          (1 : Real) / (k : Real) * C := hmul
      _ = C / (k : Real) := by ring
  have hsum := Finset.sum_le_sum hterm
  calc
    (∑ p ∈ (Finset.univ : Finset (Fin n')).offDiag,
        W p * (sparseUniformPairCount hprod p : Real)) / C ≤
      (∑ p ∈ (Finset.univ : Finset (Fin n')).offDiag,
        W p * (C / (k : Real))) / C :=
          div_le_div_of_nonneg_right hsum hCpos.le
    _ = (∑ p ∈ (Finset.univ : Finset (Fin n')).offDiag, W p) /
        (k : Real) := by
      rw [← Finset.sum_mul]
      field_simp

/-- Probabilistic-method conclusion for arbitrary nonnegative pair weights. -/
theorem exists_sparse_good_partition_of_weights
    {n' k r : Nat} (hk : 1 ≤ k)
    (hn' : 2 ≤ n') (hprod : n' = k * r)
    (W : Fin n' × Fin n' → Real) (hW : ∀ p, 0 ≤ W p)
    {M : Real}
    (htotal : (∑ p ∈ (Finset.univ : Finset (Fin n')).offDiag, W p) ≤ M) :
    ∃ σ : Equiv.Perm (Fin n'),
      sparsePartitionCrossWeight hprod W σ ≤ M / (k : Real) := by
  classical
  let C : Real := Fintype.card (Equiv.Perm (Fin n'))
  have hCposNat : 0 < Fintype.card (Equiv.Perm (Fin n')) :=
    Fintype.card_pos_iff.mpr ⟨1⟩
  have hCpos : 0 < C := by
    dsimp [C]
    exact_mod_cast hCposNat
  have hkpos : 0 < (k : Real) := by exact_mod_cast hk
  have havg := sparse_uniform_cross_average_le hk hn' hprod W hW
  have htotaldiv :
      (∑ p ∈ (Finset.univ : Finset (Fin n')).offDiag, W p) /
          (k : Real) ≤ M / (k : Real) :=
    div_le_div_of_nonneg_right htotal hkpos.le
  have havgM :
      (∑ σ : Equiv.Perm (Fin n'), sparsePartitionCrossWeight hprod W σ) / C ≤
        M / (k : Real) := havg.trans htotaldiv
  by_contra hnone
  push Not at hnone
  have huniv : (Finset.univ : Finset (Equiv.Perm (Fin n'))).Nonempty :=
    ⟨1, Finset.mem_univ _⟩
  have hstrict :
      (∑ _σ : Equiv.Perm (Fin n'), M / (k : Real)) <
        ∑ σ : Equiv.Perm (Fin n'), sparsePartitionCrossWeight hprod W σ :=
    Finset.sum_lt_sum_of_nonempty huniv fun σ hσ => hnone σ
  have hsumle :
      (∑ σ : Equiv.Perm (Fin n'), sparsePartitionCrossWeight hprod W σ) ≤
        (M / (k : Real)) * C :=
    (div_le_iff₀ hCpos).mp havgM
  have hconst :
      (∑ _σ : Equiv.Perm (Fin n'), M / (k : Real)) =
        (M / (k : Real)) * C := by
    simp [C, mul_comm]
  rw [hconst] at hstrict
  linarith

/-- Equation `eq:lower-good-partition` for the genuine history expectations.
The returned groups all have size `r`. -/
theorem lower_good_partition
    {n n' k r q c0 t : Nat} (hk : 1 ≤ k)
    (hn' : 2 ≤ n') (hn'n : n' ≤ n) (hprod : n' = k * r)
    (μ : Measure (History n k t)) [IsProbabilityMeasure μ] :
    ∃ σ : Equiv.Perm (Fin n'),
      (∀ g : Fin k, (sparsePartitionGroup hprod σ g).card = r) ∧
      (∑ g : Fin k,
        ∑ p ∈ (sparsePartitionGroup hprod σ g).offDiag,
          sparseExpectedN μ hn'n q c0 p.1 p.2) ≤ (t : Real) / (k : Real) := by
  let W : Fin n' × Fin n' → Real := fun p =>
    sparseExpectedN μ hn'n q c0 p.1 p.2
  have hW : ∀ p, 0 ≤ W p := fun p => sparseExpectedN_nonneg μ hn'n p.1 p.2
  have htotal :
      (∑ p ∈ (Finset.univ : Finset (Fin n')).offDiag, W p) ≤ (t : Real) :=
    sum_sparseExpectedN_offDiag_le hk hn'n μ
  obtain ⟨σ, hσ⟩ :=
    exists_sparse_good_partition_of_weights hk hn' hprod W hW htotal
  refine ⟨σ, fun g => card_sparsePartitionGroup hprod σ g, ?_⟩
  rw [← sparsePartitionCrossWeight_eq_group_sum hprod W σ]
  exact hσ

#print axioms sparse_round_ordered_pairs_eq_card
#print axioms sparse_round_ordered_pairs_le_sq
#print axioms sum_sparseN_offDiag_le
#print axioms integrable_sparseN
#print axioms sparseUniformPairFraction
#print axioms lower_good_partition

end

end MsetsLower.Lower.Sparse
