import MsetsLower.Core.HistoryStats
import MsetsLower.Feedback.Map
import MsetsLower.Lower.RegretMeasurability
import MsetsLower.Lower.Sparse.Parameters

/-!
# The deterministic sparse loss construction

This file fixes the auxiliary table `(U,Z)` and formalizes the pathwise part
of `prop:lower-sparse-action`: the within-block active counts, the item loss
`eq:lower-sparse-loss`, its scalar-feedback identity and normalization, and
the score identity behind `eq:lower-regret-identity`.
-/

namespace MsetsLower.Lower.Sparse

open MsetsLower Set
open scoped BigOperators

noncomputable section

/-! ## Within-block activity -/

/-- Number of prior selections of `i` in the block containing zero-based
round `t`.  At a block boundary the count is reset before round `t`. -/
def sparseBlockSelectedCount {n k : Nat} (q : Nat) (i : Fin n) :
    (t : Nat) → History n k t → Real
  | 0, _ => 0
  | t + 1, h =>
      if t / q = (t + 1) / q then
        sparseBlockSelectedCount q i t h.1 + History.selectedIndicator i h.2.1
      else 0

@[simp] theorem sparseBlockSelectedCount_zero
    {n k q : Nat} (i : Fin n) (h : History n k 0) :
    sparseBlockSelectedCount q i 0 h = 0 := rfl

@[simp] theorem sparseBlockSelectedCount_succ
    {n k q t : Nat} (i : Fin n) (h : History n k (t + 1)) :
    sparseBlockSelectedCount q i (t + 1) h =
      if t / q = (t + 1) / q then
        sparseBlockSelectedCount q i t h.1 + History.selectedIndicator i h.2.1
      else 0 := rfl

theorem measurable_sparseBlockSelectedCount
    {n k q : Nat} (i : Fin n) :
    ∀ t, Measurable (sparseBlockSelectedCount (k := k) q i t) := by
  intro t
  induction t with
  | zero => exact measurable_const
  | succ t ih =>
      change Measurable (fun h : History n k (t + 1) =>
        if t / q = (t + 1) / q then
          sparseBlockSelectedCount q i t h.1 +
            History.selectedIndicator i h.2.1
        else 0)
      apply Measurable.ite
      · by_cases hblock : t / q = (t + 1) / q <;> simp [hblock]
      · exact (ih.comp measurable_fst).add
          ((measurable_of_finite (History.selectedIndicator i)).comp
            (measurable_fst.comp measurable_snd))
      · exact measurable_const

theorem sparseBlockSelectedCount_nonneg
    {n k q : Nat} (i : Fin n) :
    ∀ t (h : History n k t), 0 ≤ sparseBlockSelectedCount q i t h := by
  intro t
  induction t with
  | zero => intro h; simp
  | succ t ih =>
      intro h
      rw [sparseBlockSelectedCount_succ]
      split_ifs
      · exact add_nonneg (ih h.1) (History.selectedIndicator_mem_Icc i h.2.1).1
      · norm_num

/-- The active indicator `A_{t,i}=1{C_{t,i}<c0}`. -/
def sparseActive {n k : Nat} (q c0 : Nat) (i : Fin n)
    (t : Nat) (h : History n k t) : Real :=
  if sparseBlockSelectedCount q i t h < (c0 : Real) then 1 else 0

theorem measurable_sparseActive
    {n k q c0 : Nat} (i : Fin n) (t : Nat) :
    Measurable (sparseActive (k := k) q c0 i t) := by
  apply Measurable.ite
  · change MeasurableSet
      (sparseBlockSelectedCount (k := k) q i t ⁻¹' Iio (c0 : Real))
    exact measurable_sparseBlockSelectedCount i t measurableSet_Iio
  · exact measurable_const
  · exact measurable_const

theorem sparseActive_mem_Icc
    {n k q c0 t : Nat} (i : Fin n) (h : History n k t) :
    sparseActive q c0 i t h ∈ Icc (0 : Real) 1 := by
  by_cases ha : sparseBlockSelectedCount q i t h < (c0 : Real) <;>
    simp [sparseActive, ha]

/-! ## Loss and scalar feedback -/

/-- The table entry on signal coordinates and zero on fillers. -/
def sparseSignalWeight {n : Nat} (n' q : Nat)
    (U : Nat → Fin n → Real) (t : Nat) (i : Fin n) : Real :=
  if i.1 < n' then U (t / q) i else 0

theorem abs_sparseSignalWeight_le_one
    {n n' q : Nat} {U : Nat → Fin n → Real}
    (hU : ∀ b i, |U b i| ≤ 1) (t : Nat) (i : Fin n) :
    |sparseSignalWeight n' q U t i| ≤ 1 := by
  by_cases hi : i.1 < n' <;> simp [sparseSignalWeight, hi, hU]

/-- The manuscript's `h_t(A)=sum_{i∈A} A_{t,i}U_{b(t),i}`. -/
def sparseActionScore {n k : Nat} (n' q c0 : Nat)
    (U : Nat → Fin n → Real) (t : Nat) (h : History n k t)
    (A : MSetAction n k) : Real :=
  actionLoss A (fun i =>
    sparseActive q c0 i t h * sparseSignalWeight n' q U t i)

/-- The scalar parameter `u_t(A)=-eta h_t(A)/k`. -/
def sparseFeedbackParameter {n k : Nat} (eta : Real) (n' q c0 : Nat)
    (U : Nat → Fin n → Real) (t : Nat) (h : History n k t)
    (A : MSetAction n k) : Real :=
  -(eta / (k : Real)) * sparseActionScore n' q c0 U t h A

/-- Equation `eq:lower-sparse-loss`, with zero loss after `T0`. -/
def sparseItemLoss {n k : Nat} (eta : Real) (n' q c0 T0 : Nat)
    (U : Nat → Fin n → Real) (Z : Nat → Real)
    (t : Nat) (h : History n k t) (i : Fin n) : Real :=
  if t < T0 then
    (1 + Z t) / (2 * (k : Real)) -
      eta / (k : Real) * Feedback.shape (Z t) *
        sparseActive q c0 i t h * sparseSignalWeight n' q U t i
  else 0

@[simp] theorem sparseItemLoss_of_le
    {n k : Nat} (eta : Real) (n' q c0 T0 : Nat)
    (U : Nat → Fin n → Real) (Z : Nat → Real)
    {t : Nat} (ht : T0 ≤ t) (h : History n k t) (i : Fin n) :
    sparseItemLoss eta n' q c0 T0 U Z t h i = 0 := by
  simp [sparseItemLoss, Nat.not_lt.mpr ht]

private theorem sparse_actionLoss_const {n k : Nat}
    (A : MSetAction n k) (c : Real) :
    actionLoss A (fun _ => c) = (k : Real) * c := by
  rw [actionLoss_eq_finset_sum]
  simp [A.2]

private theorem sparse_actionLoss_mul_left {n k : Nat}
    (A : MSetAction n k) (c : Real) (f : Fin n → Real) :
    actionLoss A (fun i => c * f i) = c * actionLoss A f := by
  rw [actionLoss_eq_finset_sum, actionLoss_eq_finset_sum, Finset.mul_sum]

private theorem sparse_actionLoss_sub {n k : Nat}
    (A : MSetAction n k) (f g : Fin n → Real) :
    actionLoss A (fun i => f i - g i) = actionLoss A f - actionLoss A g := by
  rw [actionLoss_eq_finset_sum, actionLoss_eq_finset_sum,
    actionLoss_eq_finset_sum, Finset.sum_sub_distrib]

/-- The exact identity `⟨A,ell_t⟩=1/2+F_{u_t(A)}(Z_t)`. -/
theorem lower_sparse_action_loss
    {n k : Nat} (hk : 1 ≤ k) (eta : Real) (n' q c0 T0 : Nat)
    (U : Nat → Fin n → Real) (Z : Nat → Real)
    {t : Nat} (ht : t < T0) (h : History n k t) (A : MSetAction n k) :
    actionLoss A (sparseItemLoss eta n' q c0 T0 U Z t h) =
      (1 : Real) / 2 +
        Feedback.feedbackMap
          (sparseFeedbackParameter eta n' q c0 U t h A) (Z t) := by
  have hk0 : (k : Real) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt hk)
  change actionLoss A (fun i =>
      if t < T0 then
        (1 + Z t) / (2 * (k : Real)) -
          eta / (k : Real) * Feedback.shape (Z t) *
            sparseActive q c0 i t h * sparseSignalWeight n' q U t i
      else 0) = _
  have hitem :
      (fun i : Fin n =>
        if t < T0 then
          (1 + Z t) / (2 * (k : Real)) -
            eta / (k : Real) * Feedback.shape (Z t) *
              sparseActive q c0 i t h * sparseSignalWeight n' q U t i
        else 0) =
      (fun i : Fin n =>
        (1 + Z t) / (2 * (k : Real)) -
          eta / (k : Real) * Feedback.shape (Z t) *
            sparseActive q c0 i t h * sparseSignalWeight n' q U t i) := by
    funext i
    exact if_pos ht
  rw [hitem]
  have hgroup :
      (fun i : Fin n =>
        (1 + Z t) / (2 * (k : Real)) -
          eta / (k : Real) * Feedback.shape (Z t) *
            sparseActive q c0 i t h * sparseSignalWeight n' q U t i) =
      (fun i : Fin n =>
        (1 + Z t) / (2 * (k : Real)) -
          (eta / (k : Real) * Feedback.shape (Z t)) *
            (sparseActive q c0 i t h * sparseSignalWeight n' q U t i)) := by
    funext i
    ring
  rw [hgroup]
  rw [sparse_actionLoss_sub, sparse_actionLoss_const,
    sparse_actionLoss_mul_left]
  simp only [sparseActionScore, sparseFeedbackParameter,
    Feedback.feedbackMap]
  field_simp
  ring

theorem sparseActionScore_abs_le
    {n k n' q c0 : Nat} {U : Nat → Fin n → Real}
    (hU : ∀ b i, |U b i| ≤ 1)
    (t : Nat) (h : History n k t) (A : MSetAction n k) :
    |sparseActionScore n' q c0 U t h A| ≤ (k : Real) := by
  rw [sparseActionScore, actionLoss_eq_finset_sum]
  calc
    |∑ i ∈ A.1, sparseActive q c0 i t h *
        sparseSignalWeight n' q U t i| ≤
        ∑ i ∈ A.1, |sparseActive q c0 i t h *
          sparseSignalWeight n' q U t i| := Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ _i ∈ A.1, (1 : Real) := by
      apply Finset.sum_le_sum
      intro i hi
      rw [abs_mul]
      have ha := sparseActive_mem_Icc (q := q) (c0 := c0) i h
      have habs : |sparseActive q c0 i t h| ≤ 1 := by
        rw [abs_of_nonneg ha.1]
        exact ha.2
      exact (mul_le_mul habs (abs_sparseSignalWeight_le_one hU t i)
        (abs_nonneg _) (by norm_num)).trans (by norm_num)
    _ = (k : Real) := by simp [A.2]

theorem sparseFeedbackParameter_abs_le
    {n k n' q c0 : Nat} (hk : 1 ≤ k) {eta : Real} (heta : 0 ≤ eta)
    {U : Nat → Fin n → Real} (hU : ∀ b i, |U b i| ≤ 1)
    (t : Nat) (h : History n k t) (A : MSetAction n k) :
    |sparseFeedbackParameter eta n' q c0 U t h A| ≤ eta := by
  have hkpos : 0 < (k : Real) := by exact_mod_cast hk
  rw [sparseFeedbackParameter, abs_mul, abs_neg, abs_div,
    abs_of_nonneg heta, abs_of_pos hkpos]
  rw [div_mul_eq_mul_div]
  apply (div_le_iff₀ hkpos).2
  calc
    eta * |sparseActionScore n' q c0 U t h A| ≤ eta * (k : Real) :=
      mul_le_mul_of_nonneg_left (sparseActionScore_abs_le hU t h A) heta
    _ = eta * (k : Real) := rfl

/-- Every action loss in the active construction belongs to `[0,1]`. -/
theorem lower_sparse_action_loss_mem_Icc
    {n k : Nat} (hk : 1 ≤ k) {eta : Real} (heta0 : 0 ≤ eta)
    (heta : eta ≤ (1 : Real) / 16) (n' q c0 T0 : Nat)
    {U : Nat → Fin n → Real} (hU : ∀ b i, |U b i| ≤ 1)
    {Z : Nat → Real} (hZ : ∀ t, Z t ∈ Icc (-1 : Real) 1)
    (t : Nat) (h : History n k t) (A : MSetAction n k) :
    actionLoss A (sparseItemLoss eta n' q c0 T0 U Z t h) ∈ Icc (0 : Real) 1 := by
  by_cases ht : t < T0
  · rw [lower_sparse_action_loss hk eta n' q c0 T0 U Z ht]
    have hu : |sparseFeedbackParameter eta n' q c0 U t h A| ≤
        (1 : Real) / 16 :=
      (sparseFeedbackParameter_abs_le hk heta0 hU t h A).trans heta
    have hmap := (Feedback.feedbackMap_bijOn hu).mapsTo (hZ t)
    exact ⟨by linarith [hmap.1], by linarith [hmap.2]⟩
  · change actionLoss A (fun i =>
      if t < T0 then
        (1 + Z t) / (2 * (k : Real)) -
          eta / (k : Real) * Feedback.shape (Z t) *
            sparseActive q c0 i t h * sparseSignalWeight n' q U t i
      else 0) ∈ Icc (0 : Real) 1
    have hitem :
        (fun i : Fin n =>
          if t < T0 then
            (1 + Z t) / (2 * (k : Real)) -
              eta / (k : Real) * Feedback.shape (Z t) *
                sparseActive q c0 i t h * sparseSignalWeight n' q U t i
          else 0) = (fun _i : Fin n => 0) := by
      funext i
      exact if_neg ht
    rw [hitem]
    simp

theorem measurable_sparseItemLoss
    {n k : Nat} (eta : Real) (n' q c0 T0 : Nat)
    (U : Nat → Fin n → Real) (Z : Nat → Real) (t : Nat) :
    Measurable (sparseItemLoss (k := k) eta n' q c0 T0 U Z t) := by
  change Measurable (fun h : History n k t => fun i : Fin n =>
    if t < T0 then
      (1 + Z t) / (2 * (k : Real)) -
        eta / (k : Real) * Feedback.shape (Z t) *
          sparseActive q c0 i t h * sparseSignalWeight n' q U t i
    else 0)
  by_cases ht : t < T0
  · simp only [ht, if_true]
    refine Measurable.of_eval fun i => ?_
    exact measurable_const.sub
      (((measurable_const.mul (measurable_sparseActive i t)).mul
        measurable_const))
  · simp only [ht, if_false]
    exact measurable_const

/-- Fixing `(U,Z)` yields a genuine deterministic, non-anticipating
`LossProcess`; its only adaptive input is the preceding observable history. -/
def sparseLossProcess
    {n k : Nat} (hk : 1 ≤ k) (eta : Real) (heta0 : 0 ≤ eta)
    (heta : eta ≤ (1 : Real) / 16) (n' q c0 T0 : Nat)
    (U : Nat → Fin n → Real) (hU : ∀ b i, |U b i| ≤ 1)
    (Z : Nat → Real) (hZ : ∀ t, Z t ∈ Icc (-1 : Real) 1) :
    LossProcess n k where
  itemLoss := sparseItemLoss eta n' q c0 T0 U Z
  measurable_itemLoss := measurable_sparseItemLoss eta n' q c0 T0 U Z
  action_nonneg t h A :=
    (lower_sparse_action_loss_mem_Icc hk heta0 heta n' q c0 T0 hU hZ t h A).1
  action_le_one t h A :=
    (lower_sparse_action_loss_mem_Icc hk heta0 heta n' q c0 T0 hU hZ t h A).2

theorem sparseLossProcess_is_adaptive_adversary
    {n k : Nat} (hk : 1 ≤ k) (eta : Real) (heta0 : 0 ≤ eta)
    (heta : eta ≤ (1 : Real) / 16) (n' q c0 T0 : Nat)
    (U : Nat → Fin n → Real) (hU : ∀ b i, |U b i| ≤ 1)
    (Z : Nat → Real) (hZ : ∀ t, Z t ∈ Icc (-1 : Real) 1) :
    (∀ t, Measurable ((sparseLossProcess hk eta heta0 heta n' q c0 T0
      U hU Z hZ).itemLoss t)) ∧
    (∀ t h (A : MSetAction n k),
      actionLoss A ((sparseLossProcess hk eta heta0 heta n' q c0 T0
        U hU Z hZ).itemLoss t h) ∈ Icc (0 : Real) 1) := by
  constructor
  · exact (sparseLossProcess hk eta heta0 heta n' q c0 T0
      U hU Z hZ).measurable_itemLoss
  · intro t h A
    exact (sparseLossProcess hk eta heta0 heta n' q c0 T0
      U hU Z hZ).action_mem_Icc t h A

#print axioms measurable_sparseBlockSelectedCount
#print axioms lower_sparse_action_loss
#print axioms lower_sparse_action_loss_mem_Icc
#print axioms sparseLossProcess_is_adaptive_adversary

end

end MsetsLower.Lower.Sparse
