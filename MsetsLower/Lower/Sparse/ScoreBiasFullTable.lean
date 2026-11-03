import MsetsLower.Lower.Sparse.ScoreBridge
import MsetsLower.Lower.Sparse.TableChange
import Mathlib.MeasureTheory.Group.MeasurableEquiv
import Mathlib.MeasureTheory.Measure.Haar.Unique

/-!
# The sparse score bias on the genuine hidden table

This file closes the cell-by-cell sign comparison from the manuscript on the
literal finite iid hidden table.  Negating one table cell is a
measure-preserving involution; the two induced adaptive feedback laws are
then compared by the sequential KL/Pinsker estimate from `ScoreBias`.
-/

set_option linter.style.header false

namespace MsetsLower.Lower.Sparse

open MsetsLower Feedback MeasureTheory ProbabilityTheory Set
open scoped BigOperators ENNReal ProbabilityTheory

noncomputable section

/-! ## Negating one cell of the iid hidden table -/

/-- Negation preserves the uniform source law on `[-1,1]`. -/
theorem sourceUniformMeasure_map_neg :
    Measure.map Neg.neg sourceUniformMeasure = sourceUniformMeasure := by
  unfold sourceUniformMeasure
  rw [Measure.map_smul _ (measurable_neg : Measurable (Neg.neg : ℝ → ℝ)).aemeasurable]
  congr 1
  conv_rhs =>
    rw [← Measure.map_neg_eq_self (volume : Measure Real),
      measurableEmbedding_neg.restrict_map]
  congr 1
  ext z
  simp

/-- Negate one raw entry of a recursively represented hidden column. -/
def sparseHiddenColumnCellNegEquiv :
    (B : Nat) -> Fin B -> SparseHiddenColumn B ≃ᵐ SparseHiddenColumn B
  | 0, b => Fin.elim0 b
  | B + 1, b =>
      Fin.lastCases
        (MeasurableEquiv.prodCongr (MeasurableEquiv.refl _)
          (MeasurableEquiv.neg Real))
        (fun r => MeasurableEquiv.prodCongr
          (sparseHiddenColumnCellNegEquiv B r) (MeasurableEquiv.refl _)) b

/-- Negate cell `(b,i)` of a full hidden table and leave every other cell
unchanged. -/
def sparseHiddenTableCellNegEquiv (B n : Nat) (b : Fin B) (i : Fin n) :
    SparseHiddenTable B n ≃ᵐ SparseHiddenTable B n :=
  MeasurableEquiv.piCongrRight fun j =>
    if _h : j = i then sparseHiddenColumnCellNegEquiv B b
    else MeasurableEquiv.refl _

@[simp] theorem sparseHiddenColumnCellNegEquiv_last_apply
    (B : Nat) (column : SparseHiddenColumn (B + 1)) :
    sparseHiddenColumnCellNegEquiv (B + 1) (Fin.last B) column =
      (column.1, -column.2) := by
  unfold sparseHiddenColumnCellNegEquiv
  rw [Fin.lastCases_last]
  rfl

@[simp] theorem sparseHiddenColumnCellNegEquiv_castSucc_apply
    (B : Nat) (r : Fin B) (column : SparseHiddenColumn (B + 1)) :
    sparseHiddenColumnCellNegEquiv (B + 1) r.castSucc column =
      (sparseHiddenColumnCellNegEquiv B r column.1, column.2) := by
  conv_lhs => unfold sparseHiddenColumnCellNegEquiv
  rw [Fin.lastCases_castSucc]
  rfl

@[simp] theorem sparseHiddenColumnRawAt_last
    (B : Nat) (column : SparseHiddenColumn (B + 1)) :
    sparseHiddenColumnRawAt column (Fin.last B) = column.2 := by
  unfold sparseHiddenColumnRawAt
  rw [Fin.lastCases_last]

@[simp] theorem sparseHiddenColumnRawAt_castSucc
    (B : Nat) (r : Fin B) (column : SparseHiddenColumn (B + 1)) :
    sparseHiddenColumnRawAt column r.castSucc =
      sparseHiddenColumnRawAt column.1 r := by
  change (Fin.lastCases column.2
      (fun q : Fin B => sparseHiddenColumnRawAt column.1 q) r.castSucc : Real) = _
  rw [Fin.lastCases_castSucc]

@[simp] theorem sparseClampUnit_neg (z : Real) :
    sparseClampUnit (-z) = -sparseClampUnit z := by
  simp only [sparseClampUnit, max_def, min_def]
  split_ifs <;> linarith

@[simp] theorem sparseHiddenColumnRawAt_cellNeg
    (B : Nat) (b : Fin B) (column : SparseHiddenColumn B) :
    sparseHiddenColumnRawAt (sparseHiddenColumnCellNegEquiv B b column) b =
      -sparseHiddenColumnRawAt column b := by
  induction B with
  | zero => exact Fin.elim0 b
  | succ B ih =>
      refine Fin.lastCases ?_ (fun r => ?_) b
      · rw [sparseHiddenColumnCellNegEquiv_last_apply]
        simp
      · rw [sparseHiddenColumnCellNegEquiv_castSucc_apply]
        simpa using ih r column.1

@[simp] theorem sparseHiddenColumnAt_cellNeg
    (B : Nat) (b : Fin B) (column : SparseHiddenColumn B) :
    sparseHiddenColumnAt (sparseHiddenColumnCellNegEquiv B b column) b.1 =
      -sparseHiddenColumnAt column b.1 := by
  simp [sparseHiddenColumnAt, b.2]

theorem sparseHiddenColumnCellNeg_measurePreserving :
    forall (B : Nat) (b : Fin B),
      MeasurePreserving (sparseHiddenColumnCellNegEquiv B b)
        (sparseHiddenColumnMeasure B) (sparseHiddenColumnMeasure B) := by
  intro B
  induction B with
  | zero => intro b; exact Fin.elim0 b
  | succ B ih =>
      intro b
      refine Fin.lastCases ?_ (fun r => ?_) b
      · have hneg : MeasurePreserving Neg.neg sourceUniformMeasure
            sourceUniformMeasure := ⟨measurable_neg, sourceUniformMeasure_map_neg⟩
        let hp := (MeasurePreserving.id
          (sparseHiddenColumnMeasure B)).prod hneg
        refine ⟨(sparseHiddenColumnCellNegEquiv
          (B + 1) (Fin.last B)).measurable, ?_⟩
        rw [sparseHiddenColumnMeasure]
        rw [show (sparseHiddenColumnCellNegEquiv
              (B + 1) (Fin.last B) : SparseHiddenColumn (B + 1) ->
                SparseHiddenColumn (B + 1)) = Prod.map id Neg.neg by
          funext column
          rw [sparseHiddenColumnCellNegEquiv_last_apply]
          cases column
          rfl]
        exact hp.map_eq
      · let hp := (ih r).prod (MeasurePreserving.id sourceUniformMeasure)
        refine ⟨(sparseHiddenColumnCellNegEquiv
          (B + 1) r.castSucc).measurable, ?_⟩
        rw [sparseHiddenColumnMeasure]
        rw [show (sparseHiddenColumnCellNegEquiv
              (B + 1) r.castSucc : SparseHiddenColumn (B + 1) ->
                SparseHiddenColumn (B + 1)) =
              Prod.map (sparseHiddenColumnCellNegEquiv B r) id by
          funext column
          rw [sparseHiddenColumnCellNegEquiv_castSucc_apply]
          cases column
          rfl]
        exact hp.map_eq

theorem sparseHiddenTableCellNeg_measurePreserving
    (B n : Nat) (b : Fin B) (i : Fin n) :
    MeasurePreserving (sparseHiddenTableCellNegEquiv B n b i)
      (sparseHiddenTableMeasure B n) (sparseHiddenTableMeasure B n) := by
  let e : Fin n -> SparseHiddenColumn B -> SparseHiddenColumn B := fun j =>
    if h : j = i then sparseHiddenColumnCellNegEquiv B b else id
  have he : forall j, MeasurePreserving (e j)
      (sparseHiddenColumnMeasure B) (sparseHiddenColumnMeasure B) := by
    intro j
    by_cases hji : j = i
    · subst j
      simpa [e] using sparseHiddenColumnCellNeg_measurePreserving B b
    · simpa [e, hji] using MeasurePreserving.id (sparseHiddenColumnMeasure B)
  have hpi := measurePreserving_pi
    (fun _ : Fin n => sparseHiddenColumnMeasure B)
    (fun _ : Fin n => sparseHiddenColumnMeasure B) he
  refine ⟨(sparseHiddenTableCellNegEquiv B n b i).measurable, ?_⟩
  have hcoe : (sparseHiddenTableCellNegEquiv B n b i :
      SparseHiddenTable B n -> SparseHiddenTable B n) =
      (fun table j => e j (table j)) := by
    funext table j
    change (if _h : j = i then sparseHiddenColumnCellNegEquiv B b
      else MeasurableEquiv.refl _) (table j) = e j (table j)
    by_cases hji : j = i <;> simp [e, hji]
  rw [hcoe]
  exact hpi.map_eq

@[simp] theorem sparseHiddenTableCellNeg_apply_same
    (B n : Nat) (b : Fin B) (i : Fin n)
    (table : SparseHiddenTable B n) :
    sparseHiddenTableCellNegEquiv B n b i table i =
      sparseHiddenColumnCellNegEquiv B b (table i) := by
  change (if h : i = i then sparseHiddenColumnCellNegEquiv B b
    else MeasurableEquiv.refl _) (table i) = _
  simp

@[simp] theorem sparseHiddenTableU_cellNeg_same
    (B n : Nat) (b : Fin B) (i : Fin n)
    (table : SparseHiddenTable B n) :
    sparseHiddenTableU (sparseHiddenTableCellNegEquiv B n b i table) b.1 i =
      -sparseHiddenTableU table b.1 i := by
  simp [sparseHiddenTableU]

theorem sparseHiddenColumnRawAt_cellNeg_other
    (B : Nat) (b r : Fin B) (hbr : r ≠ b)
    (column : SparseHiddenColumn B) :
    sparseHiddenColumnRawAt (sparseHiddenColumnCellNegEquiv B b column) r =
      sparseHiddenColumnRawAt column r := by
  induction B with
  | zero => exact Fin.elim0 b
  | succ B ih =>
      refine Fin.lastCases
        (fun r hne => Fin.lastCases
          (fun h => (h rfl).elim)
          (fun r0 _ => by
            rw [sparseHiddenColumnCellNegEquiv_last_apply]
            simp)
          r hne)
        (fun b0 r hne => Fin.lastCases
          (fun _ => by
            rw [sparseHiddenColumnCellNegEquiv_castSucc_apply]
            simp)
          (fun r0 hne0 => by
            rw [sparseHiddenColumnCellNegEquiv_castSucc_apply]
            simpa using ih b0 r0 (by
              intro h
              apply hne0
              subst r0
              rfl) column.1)
          r hne)
        b r hbr

theorem sparseHiddenColumnAt_cellNeg_other
    (B : Nat) (b r : Fin B) (hbr : r ≠ b)
    (column : SparseHiddenColumn B) :
    sparseHiddenColumnAt (sparseHiddenColumnCellNegEquiv B b column) r.1 =
      sparseHiddenColumnAt column r.1 := by
  simp only [sparseHiddenColumnAt, r.2, dif_pos]
  rw [sparseHiddenColumnRawAt_cellNeg_other B b r hbr]

@[simp] theorem sparseHiddenTableCellNeg_apply_other
    (B n : Nat) (b : Fin B) {i j : Fin n} (hji : j ≠ i)
    (table : SparseHiddenTable B n) :
    sparseHiddenTableCellNegEquiv B n b i table j = table j := by
  change (if h : j = i then sparseHiddenColumnCellNegEquiv B b
    else MeasurableEquiv.refl _) (table j) = _
  simp [hji]

/-- Exact read semantics of a one-cell sign flip. -/
theorem sparseHiddenTableU_cellNeg
    (B n : Nat) (b : Fin B) (i : Fin n)
    (table : SparseHiddenTable B n) (b' : Nat) (j : Fin n) :
    sparseHiddenTableU (sparseHiddenTableCellNegEquiv B n b i table) b' j =
      if b' = b.1 ∧ j = i then -sparseHiddenTableU table b' j
      else sparseHiddenTableU table b' j := by
  by_cases hji : j = i
  · subst j
    by_cases hbb : b' = b.1
    · subst b'
      simp
    · simp only [hbb, true_and, if_false]
      by_cases hb' : b' < B
      · let r : Fin B := ⟨b', hb'⟩
        have hrb : r ≠ b := by
          intro h
          apply hbb
          exact congrArg Fin.val h
        unfold sparseHiddenTableU
        rw [sparseHiddenTableCellNeg_apply_same]
        simpa [r] using sparseHiddenColumnAt_cellNeg_other B b r hrb (table i)
      · simp [sparseHiddenTableU, sparseHiddenColumnAt, hb']
  · simp [hji, sparseHiddenTableU]

/-! ## The literal active-pull budget of one block--coordinate cell -/

/-- Active pulls of one signal coordinate restricted to one fixed block. -/
def sparseObservableCellPullCount {n n' k : Nat}
    (hn' : n' <= n) (q c0 b : Nat) (j : Fin n') :
    (T : Nat) -> History n k T -> Real
  | 0, _ => 0
  | t + 1, h =>
      sparseObservableCellPullCount hn' q c0 b j t h.1 +
        if t / q = b then sparsePullIndicator hn' q c0 j t h.1 h.2.1 else 0

@[simp] theorem sparseObservableCellPullCount_zero
    {n n' k q c0 b : Nat} (hn' : n' <= n) (j : Fin n')
    (h : History n k 0) :
    sparseObservableCellPullCount hn' q c0 b j 0 h = 0 := rfl

@[simp] theorem sparseObservableCellPullCount_succ
    {n n' k q c0 b t : Nat} (hn' : n' <= n) (j : Fin n')
    (h : History n k (t + 1)) :
    sparseObservableCellPullCount hn' q c0 b j (t + 1) h =
      sparseObservableCellPullCount hn' q c0 b j t h.1 +
        if t / q = b then sparsePullIndicator hn' q c0 j t h.1 h.2.1 else 0 :=
  rfl

theorem measurable_sparseObservableCellPullCount
    {n n' k q c0 b : Nat} (hn' : n' <= n) (j : Fin n') : forall T,
    Measurable (sparseObservableCellPullCount (k := k) hn' q c0 b j T) := by
  intro T
  induction T with
  | zero => exact measurable_const
  | succ t ih =>
      change Measurable (fun h : History n k (t + 1) =>
        sparseObservableCellPullCount hn' q c0 b j t h.1 +
          if t / q = b then sparsePullIndicator hn' q c0 j t h.1 h.2.1 else 0)
      apply (ih.comp measurable_fst).add
      by_cases htb : t / q = b
      · simp only [if_pos htb]
        exact (measurable_sparsePullIndicator_joint
          (q := q) (c0 := c0) hn' j).comp
            (measurable_fst.prodMk (measurable_fst.comp measurable_snd))
      · simp only [if_neg htb]
        exact measurable_const

/-- The block counter is integer valued.  This local copy is kept with the
cell argument so the score-bias capstone does not depend on the unrelated
full-column chi-square file. -/
private theorem sparseBlockSelectedCount_isNat
    {n k q : Nat} (i : Fin n) : forall t (h : History n k t),
    exists m : Nat, sparseBlockSelectedCount q i t h = (m : Real) := by
  intro t
  induction t with
  | zero => intro h; exact ⟨0, by simp⟩
  | succ t ih =>
      intro h
      by_cases hblock : t / q = (t + 1) / q
      · rcases ih h.1 with ⟨m, hm⟩
        by_cases hselected : i ∈ h.2.1.1
        · refine ⟨m + 1, ?_⟩
          rw [sparseBlockSelectedCount_succ, if_pos hblock, hm]
          simp [History.selectedIndicator, hselected]
        · refine ⟨m, ?_⟩
          rw [sparseBlockSelectedCount_succ, if_pos hblock, hm]
          simp [History.selectedIndicator, hselected]
      · refine ⟨0, ?_⟩
        rw [sparseBlockSelectedCount_succ, if_neg hblock]
        norm_num

private theorem min_natCast_add_indicator (m c : Nat) (s : Real)
    (hs : s = 0 ∨ s = 1) :
    min (c : Real) (m : Real) +
        (if (m : Real) < (c : Real) then 1 else 0) * s =
      min (c : Real) ((m : Real) + s) := by
  rcases hs with rfl | rfl
  · simp
  · by_cases hmc : (m : Real) < (c : Real)
    · have hmcNat : m < c := by exact_mod_cast hmc
      have hsuccNat : m + 1 <= c := by omega
      have hsucc : (m : Real) + 1 <= (c : Real) := by exact_mod_cast hsuccNat
      rw [if_pos hmc, mul_one, min_eq_right hmc.le, min_eq_right hsucc]
    · have hcm : (c : Real) <= (m : Real) := le_of_not_gt hmc
      rw [if_neg hmc, zero_mul, add_zero, min_eq_left hcm,
        min_eq_left (hcm.trans (by linarith))]

/-- Simultaneous ceiling/current-block/before-block invariant. -/
private theorem sparseObservableCellPullCount_invariant
    {n n' k q c0 : Nat} (hn' : n' <= n) (b : Nat) (j : Fin n') :
    forall T (h : History n k T),
      sparseObservableCellPullCount hn' q c0 b j T h <= (c0 : Real) ∧
      (T / q = b ->
        sparseObservableCellPullCount hn' q c0 b j T h =
          min (c0 : Real) (sparseBlockSelectedCount q
            (sparseSignalCoordinate hn' j) T h)) ∧
      (T / q < b -> sparseObservableCellPullCount hn' q c0 b j T h = 0) := by
  intro T
  induction T with
  | zero =>
      intro h
      constructor
      · simp
      constructor
      · intro _; simp
      · intro _; simp
  | succ t ih =>
      intro h
      let i := sparseSignalCoordinate hn' j
      let C := sparseBlockSelectedCount q i t h.1
      have hprev := ih h.1
      have hmono : t / q <= (t + 1) / q := Nat.div_le_div_right (by omega)
      have hs01 : History.selectedIndicator i h.2.1 = 0 ∨
          History.selectedIndicator i h.2.1 = 1 := by
        unfold History.selectedIndicator
        split <;> simp
      have hpull : sparsePullIndicator hn' q c0 j t h.1 h.2.1 =
          (if C < (c0 : Real) then 1 else 0) *
            History.selectedIndicator i h.2.1 := by rfl
      have hCnat := sparseBlockSelectedCount_isNat (q := q) i t h.1
      rcases hCnat with ⟨m, hm⟩
      have hCm : C = (m : Real) := by simpa [C] using hm
      have hminstep : min (c0 : Real) C +
          (if C < (c0 : Real) then 1 else 0) *
              History.selectedIndicator i h.2.1 =
        min (c0 : Real) (C + History.selectedIndicator i h.2.1) := by
        simpa [hCm] using min_natCast_add_indicator m c0
          (History.selectedIndicator i h.2.1) hs01
      have hle : sparseObservableCellPullCount hn' q c0 b j (t + 1) h <=
          (c0 : Real) := by
        by_cases htb : t / q = b
        · rw [sparseObservableCellPullCount_succ, if_pos htb, hpull]
          have hexact := hprev.2.1 htb
          rw [hexact]
          calc
            min (c0 : Real) C +
                (if C < (c0 : Real) then 1 else 0) *
                  History.selectedIndicator i h.2.1 =
                min (c0 : Real) (C + History.selectedIndicator i h.2.1) :=
              hminstep
            _ <= (c0 : Real) := min_le_left _ _
        · rw [sparseObservableCellPullCount_succ, if_neg htb, add_zero]
          exact hprev.1
      refine ⟨hle, ?_, ?_⟩
      · intro hnext
        have htle : t / q <= b := by omega
        by_cases htb : t / q = b
        · have hsame : t / q = (t + 1) / q := htb.trans hnext.symm
          rw [sparseObservableCellPullCount_succ, if_pos htb, hpull,
            hprev.2.1 htb, sparseBlockSelectedCount_succ, if_pos hsame]
          exact hminstep
        · have htlt : t / q < b := lt_of_le_of_ne htle htb
          have hcross : t / q ≠ (t + 1) / q := by omega
          rw [sparseObservableCellPullCount_succ, if_neg htb,
            hprev.2.2 htlt, zero_add, sparseBlockSelectedCount_succ,
            if_neg hcross]
          simp
      · intro hbefore
        have htbefore : t / q < b := lt_of_le_of_lt hmono hbefore
        have htb : t / q ≠ b := ne_of_lt htbefore
        rw [sparseObservableCellPullCount_succ, if_neg htb,
          hprev.2.2 htbefore, zero_add]

/-- The exact cell budget used in the manuscript's conditional KL bound. -/
theorem sparseObservableCellPullCount_le
    {n n' k q c0 : Nat} (hn' : n' <= n) (b : Nat) (j : Fin n')
    (T : Nat) (h : History n k T) :
    sparseObservableCellPullCount hn' q c0 b j T h <= (c0 : Real) :=
  (sparseObservableCellPullCount_invariant hn' b j T h).1

/-! ## Exact cellwise parameter displacement -/

/-- Negating a signal cell subtracts precisely its twice-weighted active
selection from the action score, and changes no other round. -/
theorem sparseActionScore_hiddenTableCellNeg
    {B n n' k q c0 : Nat} (hn' : n' <= n)
    (b : Fin B) (j : Fin n') (table : SparseHiddenTable B n)
    (t : Nat) (h : History n k t) (A : MSetAction n k) :
    sparseActionScore n' q c0
        (sparseHiddenTableU
          (sparseHiddenTableCellNegEquiv B n b
            (sparseSignalCoordinate hn' j) table)) t h A =
      sparseActionScore n' q c0 (sparseHiddenTableU table) t h A -
        2 * sparseHiddenTableU table b.1
            (sparseSignalCoordinate hn' j) *
          (if t / q = b.1 then sparsePullIndicator hn' q c0 j t h A else 0) := by
  classical
  let i0 : Fin n := sparseSignalCoordinate hn' j
  let u : Real := sparseHiddenTableU table b.1 i0
  by_cases hblock : t / q = b.1
  · have hi0 : i0.1 < n' := by
      simpa [i0, sparseSignalCoordinate] using j.2
    have hpoint : (fun i : Fin n =>
        sparseActive q c0 i t h *
          sparseSignalWeight n' q
            (sparseHiddenTableU
              (sparseHiddenTableCellNegEquiv B n b i0 table)) t i) =
        fun i =>
          sparseActive q c0 i t h *
              sparseSignalWeight n' q (sparseHiddenTableU table) t i +
            if i = i0 then sparseActive q c0 i0 t h * (-2 * u) else 0 := by
      funext i
      by_cases hi : i = i0
      · subst i
        simp [sparseSignalWeight, sparseHiddenTableU_cellNeg, hblock,
          i0, u, hi0]
        ring
      · by_cases hin : i.1 < n'
        · simp [sparseSignalWeight, sparseHiddenTableU_cellNeg, hblock,
            i0, u, hin, hi]
        · simp [sparseSignalWeight, i0, hin, hi]
    unfold sparseActionScore
    rw [hpoint, actionLoss_add]
    rw [if_pos hblock]
    congr 1
    unfold actionLoss sparsePullIndicator History.selectedIndicator
    by_cases hmem : i0 ∈ A.1
    · simp [i0, u, hmem]
      ring
    · simp [i0, u, hmem]
  · have hread : forall i : Fin n,
        sparseHiddenTableU
            (sparseHiddenTableCellNegEquiv B n b
              (sparseSignalCoordinate hn' j) table) (t / q) i =
          sparseHiddenTableU table (t / q) i := by
      intro i
      rw [sparseHiddenTableU_cellNeg]
      simp [hblock]
    rw [if_neg hblock, mul_zero, sub_zero]
    unfold sparseActionScore actionLoss
    congr 2
    funext i
    by_cases hmem : i ∈ A.1
    · simp only [hmem, if_true]
      unfold sparseSignalWeight
      by_cases hi : i.1 < n'
      · simp only [if_pos hi, hread]
      · simp only [if_neg hi]
    · simp [hmem]

/-- Exact feedback-parameter displacement caused by one cell sign flip. -/
theorem sparseFeedbackParameter_hiddenTableCellNeg_sub
    {B n n' k q c0 : Nat} (eta : Real) (hn' : n' <= n)
    (b : Fin B) (j : Fin n') (table : SparseHiddenTable B n)
    (t : Nat) (h : History n k t) (A : MSetAction n k) :
    sparseFeedbackParameter eta n' q c0
        (sparseHiddenTableU
          (sparseHiddenTableCellNegEquiv B n b
            (sparseSignalCoordinate hn' j) table)) t h A -
      sparseFeedbackParameter eta n' q c0
        (sparseHiddenTableU table) t h A =
      2 * eta / (k : Real) *
        sparseHiddenTableU table b.1 (sparseSignalCoordinate hn' j) *
          (if t / q = b.1 then sparsePullIndicator hn' q c0 j t h A else 0) := by
  unfold sparseFeedbackParameter
  rw [sparseActionScore_hiddenTableCellNeg hn' b j table t h A]
  ring

/-- The squared one-round parameter energy is the squared cell amplitude
times its `0/1` active-pull indicator. -/
theorem sparseHiddenTableCellNeg_roundEnergy_eq
    {B n n' k q c0 t : Nat} (hk : 1 <= k)
    (eta : Real) (heta0 : 0 <= eta) (heta : eta <= (1 : Real) / 16)
    (hn' : n' <= n) (b : Fin B) (j : Fin n')
    (table : SparseHiddenTable B n) (h : History n k t)
    (A : MSetAction n k) :
    sparseRoundEnergy
        ((sparseHiddenTableParameterFamily hk eta heta0 heta n' q c0 B).at
          table)
        ((sparseHiddenTableParameterFamily hk eta heta0 heta n' q c0 B).at
          (sparseHiddenTableCellNegEquiv B n b
            (sparseSignalCoordinate hn' j) table)) t (h, A) =
      (2 * eta / (k : Real)) ^ 2 *
        sparseHiddenTableU table b.1 (sparseSignalCoordinate hn' j) ^ 2 *
          (if t / q = b.1 then sparsePullIndicator hn' q c0 j t h A else 0) := by
  have hdelta := sparseFeedbackParameter_hiddenTableCellNeg_sub
    (q := q) (c0 := c0) eta hn' b j table t h A
  unfold sparseRoundEnergy
  change (sparseFeedbackParameter eta n' q c0
      (sparseHiddenTableU table) t h A -
    sparseFeedbackParameter eta n' q c0
      (sparseHiddenTableU
        (sparseHiddenTableCellNegEquiv B n b
          (sparseSignalCoordinate hn' j) table)) t h A) ^ 2 = _
  rw [show sparseFeedbackParameter eta n' q c0
        (sparseHiddenTableU table) t h A -
      sparseFeedbackParameter eta n' q c0
        (sparseHiddenTableU
          (sparseHiddenTableCellNegEquiv B n b
            (sparseSignalCoordinate hn' j) table)) t h A =
      -(sparseFeedbackParameter eta n' q c0
          (sparseHiddenTableU
            (sparseHiddenTableCellNegEquiv B n b
              (sparseSignalCoordinate hn' j) table)) t h A -
        sparseFeedbackParameter eta n' q c0
          (sparseHiddenTableU table) t h A) by ring,
    hdelta]
  rw [sparsePullIndicator_eq_indicator]
  by_cases hblock : t / q = b.1 <;>
    by_cases hpull : j ∈ sparseActiveSelectedSignals hn' q c0 t h A <;>
    simp [hblock, hpull] <;> ring

/-- Cumulative cellwise energy is bounded pathwise by the literal block
budget `c0`. -/
theorem sparseHiddenTableCellNeg_cumulativeEnergy_le
    {B n n' k q c0 : Nat} (hk : 1 <= k)
    (eta : Real) (heta0 : 0 <= eta) (heta : eta <= (1 : Real) / 16)
    (hn' : n' <= n) (b : Fin B) (j : Fin n')
    (table : SparseHiddenTable B n) : forall T (h : History n k T),
    sparseCumulativeEnergy
        ((sparseHiddenTableParameterFamily hk eta heta0 heta n' q c0 B).at
          table)
        ((sparseHiddenTableParameterFamily hk eta heta0 heta n' q c0 B).at
          (sparseHiddenTableCellNegEquiv B n b
            (sparseSignalCoordinate hn' j) table)) T h <=
      (2 * eta / (k : Real)) ^ 2 *
        sparseHiddenTableU table b.1 (sparseSignalCoordinate hn' j) ^ 2 *
          (c0 : Real) := by
  intro T h
  have heq : sparseCumulativeEnergy
        ((sparseHiddenTableParameterFamily hk eta heta0 heta n' q c0 B).at
          table)
        ((sparseHiddenTableParameterFamily hk eta heta0 heta n' q c0 B).at
          (sparseHiddenTableCellNegEquiv B n b
            (sparseSignalCoordinate hn' j) table)) T h =
      (2 * eta / (k : Real)) ^ 2 *
        sparseHiddenTableU table b.1 (sparseSignalCoordinate hn' j) ^ 2 *
          sparseObservableCellPullCount hn' q c0 b.1 j T h := by
    induction T with
    | zero => simp [sparseCumulativeEnergy]
    | succ t ih =>
        rw [sparseCumulativeEnergy, sparseObservableCellPullCount_succ,
          ih h.1,
          sparseHiddenTableCellNeg_roundEnergy_eq
            hk eta heta0 heta hn' b j table h.1 h.2.1]
        ring
  rw [heq]
  exact mul_le_mul_of_nonneg_left
    (sparseObservableCellPullCount_le hn' b.1 j T h)
    (mul_nonneg (sq_nonneg _) (sq_nonneg _))

/-! ## Expected predictable cell energy -/

def sparseCellPullENN {n n' k : Nat} (hn' : n' <= n)
    (q c0 b : Nat) (j : Fin n') (t : Nat)
    (ha : History n k t × MSetAction n k) : ENNReal :=
  ENNReal.ofReal
    (if t / q = b then sparsePullIndicator hn' q c0 j t ha.1 ha.2 else 0)

theorem measurable_sparseCellPullENN
    {n n' k q c0 b : Nat} (hn' : n' <= n) (j : Fin n') (t : Nat) :
    Measurable (sparseCellPullENN (k := k) hn' q c0 b j t) := by
  unfold sparseCellPullENN
  apply Measurable.ennreal_ofReal
  split
  · exact measurable_sparsePullIndicator_joint hn' j
  · exact measurable_const

theorem sparseObservableCellPullCount_nonneg
    {n n' k q c0 b : Nat} (hn' : n' <= n) (j : Fin n') :
    forall T (h : History n k T),
      0 <= sparseObservableCellPullCount hn' q c0 b j T h := by
  intro T
  induction T with
  | zero => intro h; rfl
  | succ t ih =>
      intro h
      rw [sparseObservableCellPullCount_succ]
      exact add_nonneg (ih h.1) <| by
        split
        · exact sparsePullIndicator_mem_Icc hn' j h.1 h.2.1 |>.1
        · norm_num

theorem ofReal_sparseObservableCellPullCount_succ
    {n n' k q c0 b t : Nat} (hn' : n' <= n) (j : Fin n')
    (h : History n k (t + 1)) :
    ENNReal.ofReal (sparseObservableCellPullCount hn' q c0 b j (t + 1) h) =
      ENNReal.ofReal (sparseObservableCellPullCount hn' q c0 b j t h.1) +
        sparseCellPullENN hn' q c0 b j t (h.1, h.2.1) := by
  have hinc : 0 <=
      (if t / q = b then sparsePullIndicator hn' q c0 j t h.1 h.2.1 else 0) := by
    by_cases htb : t / q = b
    · simp only [if_pos htb]
      exact (sparsePullIndicator_mem_Icc hn' j h.1 h.2.1).1
    · simp [htb]
  rw [sparseObservableCellPullCount_succ,
    ENNReal.ofReal_add (sparseObservableCellPullCount_nonneg hn' j t h.1) hinc]
  rfl

/-- The action marginal of the scalar-feedback round kernel is the original
adaptive policy kernel. -/
theorem sparseAdaptiveRoundKernel_fst
    {n k : Nat} (P : Policy n k) (V : SparseAdaptiveParameters n k)
    (t : Nat) :
    Kernel.fst (sparseAdaptiveRoundKernel P V t) = P.kernel t := by
  letI : IsMarkovKernel (sparseParamFeedbackKernel
      (fun ha : History n k t × MSetAction n k => V.value t ha.1 ha.2)) :=
    sparseParamFeedbackKernel_isMarkov _ (V.measurable_value t)
      (fun ha => V.abs_le t ha.1 ha.2)
  unfold sparseAdaptiveRoundKernel
  exact Kernel.fst_compProd _ _

/-- Projecting the next feedback history to its prefix and action recovers
the prefix-law--policy composition. -/
theorem sparseAdaptive_law_succ_map_historyAction
    {n k : Nat} (P : Policy n k) (V : SparseAdaptiveParameters n k)
    (t : Nat) :
    ((sparseAdaptiveProcess P V).law (t + 1)).map
        (fun h : History n k (t + 1) => (h.1, h.2.1)) =
      (sparseAdaptiveProcess P V).law t ⊗ₘ P.kernel t := by
  letI : IsMarkovKernel (sparseAdaptiveRoundKernel P V t) :=
    sparseAdaptiveRoundKernel_isMarkov P V t
  rw [HistoryKernelProcess.law_succ]
  change (((sparseAdaptiveProcess P V).law t ⊗ₘ
    sparseAdaptiveRoundKernel P V t).map (Prod.map id Prod.fst)) = _
  rw [← Measure.compProd_map measurable_fst]
  rw [← Kernel.fst_eq, sparseAdaptiveRoundKernel_fst]

theorem lintegral_sparseObservableCellPullCount_succ
    {n n' k q c0 b : Nat} (P : Policy n k)
    (V : SparseAdaptiveParameters n k) (hn' : n' <= n)
    (j : Fin n') (t : Nat) :
    (∫⁻ h, ENNReal.ofReal
        (sparseObservableCellPullCount hn' q c0 b j (t + 1) h)
      ∂(sparseAdaptiveProcess P V).law (t + 1)) =
      (∫⁻ h, ENNReal.ofReal
          (sparseObservableCellPullCount hn' q c0 b j t h)
        ∂(sparseAdaptiveProcess P V).law t) +
      ∫⁻ ha, sparseCellPullENN hn' q c0 b j t ha
        ∂((sparseAdaptiveProcess P V).law t ⊗ₘ P.kernel t) := by
  let F : History n k t × MSetAction n k -> ENNReal := fun ha =>
    ENNReal.ofReal (sparseObservableCellPullCount hn' q c0 b j t ha.1) +
      sparseCellPullENN hn' q c0 b j t ha
  have hF : Measurable F :=
    ((ENNReal.measurable_ofReal.comp
      (measurable_sparseObservableCellPullCount hn' j t)).comp
        measurable_fst).add (measurable_sparseCellPullENN hn' j t)
  have hproj : Measurable
      (fun h : History n k (t + 1) => (h.1, h.2.1)) := by fun_prop
  calc
    (∫⁻ h, ENNReal.ofReal
        (sparseObservableCellPullCount hn' q c0 b j (t + 1) h)
      ∂(sparseAdaptiveProcess P V).law (t + 1)) =
        ∫⁻ h, F (h.1, h.2.1)
          ∂(sparseAdaptiveProcess P V).law (t + 1) := by
      apply lintegral_congr
      intro h
      exact ofReal_sparseObservableCellPullCount_succ hn' j h
    _ = ∫⁻ ha, F ha ∂(((sparseAdaptiveProcess P V).law (t + 1)).map
        (fun h : History n k (t + 1) => (h.1, h.2.1))) := by
      symm
      exact MeasureTheory.lintegral_map hF hproj
    _ = ∫⁻ ha, F ha
        ∂((sparseAdaptiveProcess P V).law t ⊗ₘ P.kernel t) := by
      rw [sparseAdaptive_law_succ_map_historyAction]
    _ = (∫⁻ ha, ENNReal.ofReal
          (sparseObservableCellPullCount hn' q c0 b j t ha.1)
          ∂((sparseAdaptiveProcess P V).law t ⊗ₘ P.kernel t)) +
        ∫⁻ ha, sparseCellPullENN hn' q c0 b j t ha
          ∂((sparseAdaptiveProcess P V).law t ⊗ₘ P.kernel t) := by
      exact lintegral_add_left
        ((ENNReal.measurable_ofReal.comp
          (measurable_sparseObservableCellPullCount hn' j t)).comp
            measurable_fst) _
    _ = (∫⁻ h, ENNReal.ofReal
          (sparseObservableCellPullCount hn' q c0 b j t h)
          ∂(sparseAdaptiveProcess P V).law t) +
        ∫⁻ ha, sparseCellPullENN hn' q c0 b j t ha
          ∂((sparseAdaptiveProcess P V).law t ⊗ₘ P.kernel t) := by
      congr 1
      calc
        (∫⁻ ha, ENNReal.ofReal
            (sparseObservableCellPullCount hn' q c0 b j t ha.1)
            ∂((sparseAdaptiveProcess P V).law t ⊗ₘ P.kernel t)) =
          ∫⁻ h, ∫⁻ _A, ENNReal.ofReal
              (sparseObservableCellPullCount hn' q c0 b j t h)
            ∂P.kernel t h ∂(sparseAdaptiveProcess P V).law t := by
          simpa only [Function.comp_apply] using
            (Measure.lintegral_compProd
              ((ENNReal.measurable_ofReal.comp
                (measurable_sparseObservableCellPullCount hn' j t)).comp
                  measurable_fst) : _)
        _ = ∫⁻ h, ENNReal.ofReal
              (sparseObservableCellPullCount hn' q c0 b j t h)
            ∂(sparseAdaptiveProcess P V).law t := by simp

/-- The sum of predictable active-pull probabilities is exactly the final
expected stopped cell count. -/
theorem lintegral_sparseObservableCellPullCount_eq_sum
    {n n' k q c0 b : Nat} (P : Policy n k)
    (V : SparseAdaptiveParameters n k) (hn' : n' <= n)
    (j : Fin n') : forall T,
    (∫⁻ h, ENNReal.ofReal
        (sparseObservableCellPullCount hn' q c0 b j T h)
      ∂(sparseAdaptiveProcess P V).law T) =
      ∑ t ∈ Finset.range T,
        ∫⁻ ha, sparseCellPullENN hn' q c0 b j t ha
          ∂((sparseAdaptiveProcess P V).law t ⊗ₘ P.kernel t) := by
  intro T
  induction T with
  | zero => simp [HistoryKernelProcess.law]
  | succ T ih =>
      rw [lintegral_sparseObservableCellPullCount_succ P V hn' j T,
        ih, Finset.sum_range_succ]

/-- Concrete expected parameter-energy budget for one genuine hidden-table
cell.  No expected-pull or KL premise remains. -/
theorem sparseHiddenTableCellNeg_parameterEnergy_le
    {B n n' k q c0 T : Nat} (P : Policy n k) (hk : 1 <= k)
    (eta : Real) (heta0 : 0 <= eta) (heta : eta <= (1 : Real) / 16)
    (hn' : n' <= n) (b : Fin B) (j : Fin n')
    (table : SparseHiddenTable B n) :
    ∑ t ∈ Finset.range T,
        ∫⁻ ha, sparseParameterEnergy
          ((sparseHiddenTableParameterFamily hk eta heta0 heta
            n' q c0 B).at table)
          ((sparseHiddenTableParameterFamily hk eta heta0 heta
            n' q c0 B).at
            (sparseHiddenTableCellNegEquiv B n b
              (sparseSignalCoordinate hn' j) table)) t ha
          ∂((sparseAdaptiveProcess P
            ((sparseHiddenTableParameterFamily hk eta heta0 heta
              n' q c0 B).at table)).law t ⊗ₘ P.kernel t) <=
      ENNReal.ofReal
        ((2 * eta / (k : Real)) ^ 2 *
          sparseHiddenTableU table b.1 (sparseSignalCoordinate hn' j) ^ 2 *
            (c0 : Real)) := by
  let V := (sparseHiddenTableParameterFamily hk eta heta0 heta
    n' q c0 B).at table
  let W := (sparseHiddenTableParameterFamily hk eta heta0 heta
    n' q c0 B).at
      (sparseHiddenTableCellNegEquiv B n b
        (sparseSignalCoordinate hn' j) table)
  let C : Real := (2 * eta / (k : Real)) ^ 2 *
    sparseHiddenTableU table b.1 (sparseSignalCoordinate hn' j) ^ 2
  have hC : 0 <= C := mul_nonneg (sq_nonneg _) (sq_nonneg _)
  have hpoint : forall t (ha : History n k t × MSetAction n k),
      sparseParameterEnergy V W t ha =
        ENNReal.ofReal C * sparseCellPullENN hn' q c0 b.1 j t ha := by
    intro t ha
    unfold sparseParameterEnergy sparseCellPullENN V W C
    have hround := sparseHiddenTableCellNeg_roundEnergy_eq
      (q := q) (c0 := c0) hk eta heta0 heta hn' b j table ha.1 ha.2
    unfold sparseRoundEnergy at hround
    rw [hround]
    rw [ENNReal.ofReal_mul hC]
  calc
    (∑ t ∈ Finset.range T,
        ∫⁻ ha, sparseParameterEnergy V W t ha
          ∂((sparseAdaptiveProcess P V).law t ⊗ₘ P.kernel t)) =
      ∑ t ∈ Finset.range T,
        ENNReal.ofReal C *
          ∫⁻ ha, sparseCellPullENN hn' q c0 b.1 j t ha
            ∂((sparseAdaptiveProcess P V).law t ⊗ₘ P.kernel t) := by
      apply Finset.sum_congr rfl
      intro t ht
      simp_rw [hpoint t]
      exact lintegral_const_mul _ (measurable_sparseCellPullENN hn' j t)
    _ = ENNReal.ofReal C *
        ∑ t ∈ Finset.range T,
          ∫⁻ ha, sparseCellPullENN hn' q c0 b.1 j t ha
            ∂((sparseAdaptiveProcess P V).law t ⊗ₘ P.kernel t) := by
      rw [Finset.mul_sum]
    _ = ENNReal.ofReal C *
        (∫⁻ h, ENNReal.ofReal
          (sparseObservableCellPullCount hn' q c0 b.1 j T h)
            ∂(sparseAdaptiveProcess P V).law T) := by
      rw [lintegral_sparseObservableCellPullCount_eq_sum P V hn' j T]
    _ <= ENNReal.ofReal C * ENNReal.ofReal (c0 : Real) := by
      gcongr
      calc
        (∫⁻ h, ENNReal.ofReal
            (sparseObservableCellPullCount hn' q c0 b.1 j T h)
              ∂(sparseAdaptiveProcess P V).law T) <=
          ∫⁻ _h, ENNReal.ofReal (c0 : Real)
              ∂(sparseAdaptiveProcess P V).law T := by
            exact lintegral_mono fun h => ENNReal.ofReal_le_ofReal
              (sparseObservableCellPullCount_le hn' b.1 j T h)
        _ = ENNReal.ofReal (c0 : Real) := by simp
    _ = ENNReal.ofReal (C * (c0 : Real)) := by
      rw [ENNReal.ofReal_mul hC]
    _ = _ := rfl

/-! ## Cellwise sign comparison on the true table -/

/-- The manuscript's conditional sign comparison for a literal table cell.
The only arithmetic premise identifies `rho` with its construction value;
the predictable energy and KL bounds are proved above. -/
theorem lower_score_bias_hiddenTableCell_conditional
    {B n n' k q c0 T : Nat} (P : Policy n k) (hk : 1 <= k)
    (eta : Real) (heta0 : 0 <= eta) (heta : eta <= (1 : Real) / 16)
    (hn' : n' <= n) (b : Fin B) (j : Fin n')
    (table : SparseHiddenTable B n) {rho M : Real}
    (hrho : 0 <= rho)
    (hrhoeq : rho = eta ^ 2 * (c0 : Real) / (k : Real) ^ 2)
    (hM : 0 <= M) (Vobs : History n k T -> Real)
    (hV : Measurable Vobs) (hVM : forall h, Vobs h ∈ Icc (0 : Real) M) :
    let F : SparseAdaptiveParameterFamily (SparseHiddenTable B n) n k :=
      sparseHiddenTableParameterFamily hk eta heta0 heta n' q c0 B
    let e := sparseHiddenTableCellNegEquiv B n b
      (sparseSignalCoordinate hn' j)
    let u := sparseHiddenTableU table b.1 (sparseSignalCoordinate hn' j)
    |u / 2 *
        ((∫ h, Vobs h ∂(sparseAdaptiveProcess P (F.at table)).law T) -
          ∫ h, Vobs h ∂(sparseAdaptiveProcess P (F.at (e table))).law T)| <=
      8 * M * u ^ 2 * Real.sqrt rho := by
  dsimp only
  let F : SparseAdaptiveParameterFamily (SparseHiddenTable B n) n k :=
    sparseHiddenTableParameterFamily hk eta heta0 heta n' q c0 B
  let e := sparseHiddenTableCellNegEquiv B n b
    (sparseSignalCoordinate hn' j)
  let u := sparseHiddenTableU table b.1 (sparseSignalCoordinate hn' j)
  let uabs := |u|
  have hu : uabs ∈ Icc (0 : Real) 1 := by
    exact ⟨abs_nonneg _, by
      simpa [uabs, u] using sparseHiddenTableU_abs_le_one table b.1
        (sparseSignalCoordinate hn' j)⟩
  have hkpos : 0 < (k : Real) := by exact_mod_cast hk
  have henergyRaw := sparseHiddenTableCellNeg_parameterEnergy_le
    (q := q) (c0 := c0) (T := T) P hk eta heta0 heta hn' b j table
  have hreal :
      128 * ((2 * eta / (k : Real)) ^ 2 * u ^ 2 * (c0 : Real)) =
        512 * rho * uabs ^ 2 := by
    rw [hrhoeq]
    have huabs : uabs ^ 2 = u ^ 2 := sq_abs u
    rw [huabs]
    field_simp [ne_of_gt hkpos]
    ring
  have henergy : ENNReal.ofReal 128 *
      ∑ t ∈ Finset.range T,
        ∫⁻ ha, sparseParameterEnergy (F.at table) (F.at (e table)) t ha
          ∂((sparseAdaptiveProcess P (F.at table)).law t ⊗ₘ P.kernel t) <=
      ENNReal.ofReal (512 * rho * uabs ^ 2) := by
    calc
      ENNReal.ofReal 128 *
          ∑ t ∈ Finset.range T,
            ∫⁻ ha, sparseParameterEnergy (F.at table) (F.at (e table)) t ha
              ∂((sparseAdaptiveProcess P (F.at table)).law t ⊗ₘ P.kernel t) <=
        ENNReal.ofReal 128 * ENNReal.ofReal
          ((2 * eta / (k : Real)) ^ 2 * u ^ 2 * (c0 : Real)) := by
            exact mul_le_mul_right (by simpa [F, e, u] using henergyRaw) _
      _ = ENNReal.ofReal
          (128 * ((2 * eta / (k : Real)) ^ 2 * u ^ 2 * (c0 : Real))) := by
            rw [ENNReal.ofReal_mul (by norm_num : (0 : Real) <= 128)]
      _ = ENNReal.ofReal (512 * rho * uabs ^ 2) := by rw [hreal]
  have hsign := lower_score_bias_conditional_sign_of_parameterEnergy
    P (F.at table) (F.at (e table)) hrho hu hM Vobs hV hVM henergy
  simpa [uabs, u, F, e, abs_mul, abs_div, sq_abs] using hsign

/-- Conditional expectations of a bounded observable are themselves in the
same interval. -/
theorem sparseFamilyExpectation_mem_Icc
    {Omega : Type*} [MeasurableSpace Omega] {n k T : Nat}
    (P : Policy n k) (F : SparseAdaptiveParameterFamily Omega n k)
    {M : Real} (hM : 0 <= M) (Vobs : History n k T -> Real)
    (hV : Measurable Vobs) (hVM : forall h, Vobs h ∈ Icc (0 : Real) M)
    (omega : Omega) :
    (∫ h, Vobs h ∂(sparseAdaptiveProcess P (F.at omega)).law T) ∈
      Icc (0 : Real) M := by
  letI : IsProbabilityMeasure
      ((sparseAdaptiveProcess P (F.at omega)).law T) := inferInstance
  have hint : Integrable Vobs
      ((sparseAdaptiveProcess P (F.at omega)).law T) :=
    Integrable.of_bound hV.aestronglyMeasurable M
      (ae_of_all _ fun h => by
        rw [Real.norm_eq_abs, abs_of_nonneg (hVM h).1]
        exact (hVM h).2)
  constructor
  · exact integral_nonneg fun h => (hVM h).1
  · calc
      (∫ h, Vobs h ∂(sparseAdaptiveProcess P (F.at omega)).law T) <=
          ∫ _h, M ∂(sparseAdaptiveProcess P (F.at omega)).law T :=
        integral_mono hint (integrable_const _) fun h => (hVM h).2
      _ = M := by simp

/-- The conditional expectation is measurable as a function of the hidden
table, because it is an integral against the family Markov kernel. -/
theorem measurable_sparseFamilyExpectation
    {Omega : Type*} [MeasurableSpace Omega] {n k T : Nat}
    (P : Policy n k) (F : SparseAdaptiveParameterFamily Omega n k)
    (Vobs : History n k T -> Real) (hV : Measurable Vobs) :
    Measurable (fun omega =>
      ∫ h, Vobs h ∂(sparseAdaptiveProcess P (F.at omega)).law T) := by
  have hstrong : StronglyMeasurable (fun omega =>
      ∫ h, Vobs h ∂sparseFamilyLawKernel P F T omega) :=
    hV.stronglyMeasurable.integral_kernel
  simpa only [sparseFamilyLawKernel_apply P F T] using hstrong.measurable

/-- Global cell sign bound under the genuine full-table joint law.  The
hidden cell is not assumed independent of the learner's past; the proof
pairs every table with its measure-preserving sign flip. -/
theorem lower_score_bias_hiddenTableCell_jointLaw
    {B n n' k q c0 T : Nat} (P : Policy n k) (hk : 1 <= k)
    (eta : Real) (heta0 : 0 <= eta) (heta : eta <= (1 : Real) / 16)
    (hn' : n' <= n) (b : Fin B) (j : Fin n') {rho M : Real}
    (hrho : 0 <= rho)
    (hrhoeq : rho = eta ^ 2 * (c0 : Real) / (k : Real) ^ 2)
    (hM : 0 <= M) (Vobs : History n k T -> Real)
    (hV : Measurable Vobs) (hVM : forall h, Vobs h ∈ Icc (0 : Real) M) :
    let F : SparseAdaptiveParameterFamily (SparseHiddenTable B n) n k :=
      sparseHiddenTableParameterFamily hk eta heta0 heta n' q c0 B
    |∫ z, sparseHiddenTableU z.1 b.1 (sparseSignalCoordinate hn' j) *
          Vobs z.2
        ∂sparseJointLaw (sparseHiddenTableMeasure B n) P F T| <=
      8 * M * Real.sqrt rho := by
  dsimp only
  let mu : Measure (SparseHiddenTable B n) := sparseHiddenTableMeasure B n
  let F : SparseAdaptiveParameterFamily (SparseHiddenTable B n) n k :=
    sparseHiddenTableParameterFamily hk eta heta0 heta n' q c0 B
  let e := sparseHiddenTableCellNegEquiv B n b
    (sparseSignalCoordinate hn' j)
  let Ucell : SparseHiddenTable B n -> Real := fun table =>
    sparseHiddenTableU table b.1 (sparseSignalCoordinate hn' j)
  let EV : SparseHiddenTable B n -> Real := fun table =>
    ∫ h, Vobs h ∂(sparseAdaptiveProcess P (F.at table)).law T
  have hEVmeas : Measurable EV := by
    exact measurable_sparseFamilyExpectation P F Vobs hV
  have hEVrange : forall table, EV table ∈ Icc (0 : Real) M := by
    intro table
    exact sparseFamilyExpectation_mem_Icc P F hM Vobs hV hVM table
  have hUmeas : Measurable Ucell :=
    measurable_sparseHiddenTableU B n b.1 (sparseSignalCoordinate hn' j)
  have hUabs : forall table, |Ucell table| <= 1 := by
    intro table
    exact sparseHiddenTableU_abs_le_one table b.1
      (sparseSignalCoordinate hn' j)
  have hEVint : Integrable EV mu :=
    Integrable.of_mem_Icc 0 M hEVmeas.aemeasurable (ae_of_all _ hEVrange)
  have hUEVint : Integrable (fun table => Ucell table * EV table) mu := by
    apply Integrable.of_bound (hUmeas.mul hEVmeas).aestronglyMeasurable M
    apply ae_of_all
    intro table
    change |Ucell table * EV table| <= M
    rw [abs_mul, abs_of_nonneg (hEVrange table).1]
    calc
      |Ucell table| * EV table <= 1 * M :=
        mul_le_mul (hUabs table) (hEVrange table).2
          (hEVrange table).1 (by norm_num)
      _ = M := one_mul _
  have hUEVeint : Integrable (fun table => Ucell table * EV (e table)) mu := by
    apply Integrable.of_bound
      (hUmeas.mul (hEVmeas.comp e.measurable)).aestronglyMeasurable M
    apply ae_of_all
    intro table
    change |Ucell table * EV (e table)| <= M
    rw [abs_mul, abs_of_nonneg (hEVrange (e table)).1]
    calc
      |Ucell table| * EV (e table) <= 1 * M :=
        mul_le_mul (hUabs table) (hEVrange (e table)).2
          (hEVrange (e table)).1 (by norm_num)
      _ = M := one_mul _
  have hpair : (∫ table, Ucell table * EV table ∂mu) =
      -(∫ table, Ucell table * EV (e table) ∂mu) := by
    have hmp := sparseHiddenTableCellNeg_measurePreserving B n b
      (sparseSignalCoordinate hn' j)
    have hchange := hmp.integral_comp'
      (fun table => Ucell table * EV table)
    rw [show (fun table => Ucell (e table) * EV (e table)) =
        fun table => -(Ucell table * EV (e table)) by
      funext table
      simp [Ucell, e]] at hchange
    rw [integral_neg] at hchange
    exact hchange.symm
  have hpoint : forall table,
      |Ucell table / 2 * (EV table - EV (e table))| <=
        8 * M * Real.sqrt rho := by
    intro table
    have hcond := lower_score_bias_hiddenTableCell_conditional
      (q := q) (c0 := c0) (T := T)
      P hk eta heta0 heta hn' b j table hrho hrhoeq hM Vobs hV hVM
    have huSq : Ucell table ^ 2 <= 1 := by
      have huBounds := (abs_le).1 (hUabs table)
      have hplus : 0 <= 1 + Ucell table := by linarith [huBounds.1]
      have hminus : 0 <= 1 - Ucell table := by linarith [huBounds.2]
      nlinarith [mul_nonneg hplus hminus]
    have hsqrt0 := Real.sqrt_nonneg rho
    calc
      |Ucell table / 2 * (EV table - EV (e table))| <=
          8 * M * Ucell table ^ 2 * Real.sqrt rho := by
        simpa [F, e, Ucell, EV] using hcond
      _ <= 8 * M * 1 * Real.sqrt rho := by
        exact mul_le_mul_of_nonneg_right
          (mul_le_mul_of_nonneg_left huSq (mul_nonneg (by norm_num) hM))
          hsqrt0
      _ = 8 * M * Real.sqrt rho := by ring
  have hdiffInt : Integrable
      (fun table => Ucell table / 2 * (EV table - EV (e table))) mu := by
    apply Integrable.of_bound
      (((hUmeas.div_const 2).mul
        (hEVmeas.sub (hEVmeas.comp e.measurable))).aestronglyMeasurable)
      (8 * M * Real.sqrt rho)
    exact ae_of_all _ hpoint
  have hrepr : (∫ table, Ucell table * EV table ∂mu) =
      ∫ table, Ucell table / 2 * (EV table - EV (e table)) ∂mu := by
    rw [show (fun table => Ucell table / 2 * (EV table - EV (e table))) =
        fun table => (1 / 2 : Real) *
          ((Ucell table * EV table) - (Ucell table * EV (e table))) by
      funext table
      ring]
    rw [integral_const_mul, integral_sub hUEVint hUEVeint, hpair]
    ring
  have hjointInt : Integrable
      (fun z : SparseHiddenTable B n × History n k T =>
        Ucell z.1 * Vobs z.2) (sparseJointLaw mu P F T) := by
    letI : IsProbabilityMeasure (sparseJointLaw mu P F T) := by
      unfold sparseJointLaw
      infer_instance
    apply Integrable.of_bound
      (((hUmeas.comp measurable_fst).mul
        (hV.comp measurable_snd)).aestronglyMeasurable) M
    apply ae_of_all
    intro z
    change |Ucell z.1 * Vobs z.2| <= M
    rw [abs_mul, abs_of_nonneg (hVM z.2).1]
    calc
      |Ucell z.1| * Vobs z.2 <= 1 * M :=
        mul_le_mul (hUabs z.1) (hVM z.2).2 (hVM z.2).1 (by norm_num)
      _ = M := one_mul _
  have hFubini :
      (∫ z, Ucell z.1 * Vobs z.2 ∂sparseJointLaw mu P F T) =
        ∫ table, Ucell table * EV table ∂mu := by
    unfold sparseJointLaw at hjointInt ⊢
    rw [Measure.integral_compProd hjointInt]
    apply integral_congr_ae
    apply ae_of_all
    intro table
    change (∫ b, Ucell table * Vobs b
        ∂sparseFamilyLawKernel P F T table) = Ucell table * EV table
    rw [integral_const_mul, sparseFamilyLawKernel_apply]
  rw [show sparseJointLaw (sparseHiddenTableMeasure B n) P F T =
      sparseJointLaw mu P F T by rfl]
  change |∫ z, Ucell z.1 * Vobs z.2 ∂sparseJointLaw mu P F T| <= _
  rw [hFubini, hrepr]
  calc
    |∫ table, Ucell table / 2 * (EV table - EV (e table)) ∂mu| <=
        ∫ table, |Ucell table / 2 * (EV table - EV (e table))| ∂mu :=
      abs_integral_le_integral_abs
    _ <= ∫ _table, 8 * M * Real.sqrt rho ∂mu :=
      integral_mono hdiffInt.abs (integrable_const _) hpoint
    _ = 8 * M * Real.sqrt rho := by simp

end

end MsetsLower.Lower.Sparse
