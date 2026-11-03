import CoefficientOne.RectangleDeterminants
import CoefficientOne.JacobiTrudiPadding
import CoefficientOne.CompleteDeletion

/-!
# The row expansion behind deletion from a rectangle

This formalizes the multilinear argument in the manuscript's
`lem:rect-deletion`: choosing a shifted row followed by an unshifted row
creates equal adjacent rows, so only terminal blocks survive.
-/

noncomputable section

namespace CoefficientOne.RectangleDeletion

open Finset Matrix

variable {R : Type*} [CommRing R] {k : ℕ}

def terminalSet (t : Fin (k + 1)) : Finset (Fin k) :=
  Finset.univ.filter (fun i => t.val ≤ i.val)

@[simp] theorem mem_terminalSet (t : Fin (k + 1)) (i : Fin k) :
    i ∈ terminalSet t ↔ t.val ≤ i.val := by
  simp [terminalSet]

theorem terminalSet_card (t : Fin (k + 1)) :
    (terminalSet t).card = k - t.val := by
  by_cases ht : t.val < k
  · have heq : terminalSet t = Finset.Ici (⟨t.val, ht⟩ : Fin k) := by
      ext i
      simp [Fin.le_def]
    rw [heq, Fin.card_Ici]
  · have heq : terminalSet t = ∅ := by
      ext i
      simp only [mem_terminalSet, Finset.notMem_empty, iff_false]
      omega
    simp only [heq, Finset.card_empty]
    omega

theorem terminalSet_injective : Function.Injective (@terminalSet k) := by
  intro t u heq
  apply Fin.ext
  have hc := congrArg Finset.card heq
  rw [terminalSet_card, terminalSet_card] at hc
  have ht := t.isLt
  have hu := u.isLt
  omega

theorem mem_of_closed_upward (S : Finset (Fin k))
    (hclosed : ∀ (i : Fin k) (hi : i.val + 1 < k),
      i ∈ S → (⟨i.val + 1, hi⟩ : Fin k) ∈ S)
    (i : Fin k) (hi : i ∈ S) (j : Fin k) (hij : i.val ≤ j.val) : j ∈ S := by
  have hp : ∀ t, i.val ≤ t → ∀ ht : t < k, (⟨t, ht⟩ : Fin k) ∈ S := by
    intro t hit
    induction t, hit using Nat.le_induction with
    | base =>
        intro ht
        simpa using hi
    | succ t hit ih =>
        intro ht
        exact hclosed ⟨t, by omega⟩ ht (ih (by omega))
  exact hp j.val hij j.isLt

theorem exists_terminalSet_of_closed (S : Finset (Fin k))
    (hclosed : ∀ (i : Fin k) (hi : i.val + 1 < k),
      i ∈ S → (⟨i.val + 1, hi⟩ : Fin k) ∈ S) :
    ∃ t : Fin (k + 1), S = terminalSet t := by
  by_cases hS : S.Nonempty
  · let i := S.min' hS
    refine ⟨⟨i.val, by omega⟩, ?_⟩
    ext j
    simp only [mem_terminalSet]
    constructor
    · intro hj
      exact S.min'_le j hj
    · intro hij
      exact mem_of_closed_upward S hclosed i (Finset.min'_mem S hS) j hij
  · refine ⟨Fin.last k, ?_⟩
    ext i
    simp only [Finset.not_nonempty_iff_eq_empty.mp hS, Finset.notMem_empty,
      mem_terminalSet, Fin.val_last, false_iff]
    omega

def selectedRows (U : Fin (k + 1) → Fin k → R) (S : Finset (Fin k)) :
    Matrix (Fin k) (Fin k) R :=
  fun i => if i ∈ S then U i.succ else U i.castSucc

theorem selectedRows_det_eq_zero_of_not_terminal
    (U : Fin (k + 1) → Fin k → R) (S : Finset (Fin k))
    (hS : ¬ ∃ t, S = terminalSet t) : (selectedRows U S).det = 0 := by
  have hbad : ¬ ∀ (i : Fin k) (hi : i.val + 1 < k),
      i ∈ S → (⟨i.val + 1, hi⟩ : Fin k) ∈ S := by
    intro hclosed
    exact hS (exists_terminalSet_of_closed S hclosed)
  push Not at hbad
  obtain ⟨i, hi, hiS, hjS⟩ := hbad
  let j : Fin k := ⟨i.val + 1, hi⟩
  have hij : i ≠ j := by
    intro heq
    have hv := congrArg Fin.val heq
    dsimp [j] at hv
    omega
  change j ∉ S at hjS
  apply Matrix.det_zero_of_row_eq hij
  simp only [selectedRows, if_pos hiS, if_neg hjS]
  congr 1

theorem shifted_row_expansion (U : Fin (k + 1) → Fin k → R) (x : R) :
    Matrix.det (fun i : Fin k => U i.castSucc - x • U i.succ) =
      ∑ S : Finset (Fin k), (-x) ^ S.card * (selectedRows U S).det := by
  have hadd := (Matrix.detRowAlternating : (Fin k → R) [⋀^Fin k]→ₗ[R] R).toMultilinearMap.map_add_univ (fun i => (-x) • U i.succ) (fun i => U i.castSucc)
  have hmat : (fun i : Fin k => U i.castSucc - x • U i.succ) =
      (fun i => (-x) • U i.succ) + (fun i => U i.castSucc) := by
    ext i j
    simp [sub_eq_add_neg, add_comm]
  rw [hmat]
  change Matrix.det ((fun i => (-x) • U i.succ) + (fun i => U i.castSucc)) =
    ∑ S : Finset (Fin k), Matrix.det
      (S.piecewise (fun i => (-x) • U i.succ) (fun i => U i.castSucc)) at hadd
  erw [hadd]
  apply Finset.sum_congr rfl
  intro S _
  have hterm : S.piecewise (fun i => (-x) • U i.succ) (fun i => U i.castSucc) =
      (fun i j => (if i ∈ S then -x else 1) * selectedRows U S i j) := by
    ext i j
    by_cases hi : i ∈ S <;> simp [Finset.piecewise, selectedRows, hi]
  change Matrix.det _ = _
  erw [hterm, Matrix.det_mul_column]
  congr 1
  simp

/-- The complete row expansion reduces to terminal choices; every discarded
summand has the adjacent pair of equal rows exhibited above. -/
theorem shifted_row_terminal_expansion (U : Fin (k + 1) → Fin k → R) (x : R) :
    Matrix.det (fun i : Fin k => U i.castSucc - x • U i.succ) =
      ∑ t : Fin (k + 1), (-x) ^ (k - t.val) *
        (selectedRows U (terminalSet t)).det := by
  rw [shifted_row_expansion]
  let f : Finset (Fin k) → R := fun S => (-x) ^ S.card * (selectedRows U S).det
  change ∑ S, f S = _
  calc
    ∑ S, f S = ∑ S ∈ Finset.univ.image terminalSet, f S := by
      symm
      apply Finset.sum_subset (Finset.subset_univ _)
      intro S _ hnot
      have hbad : ¬ ∃ t, S = terminalSet t := by
        rintro ⟨t, rfl⟩
        exact hnot (Finset.mem_image.mpr ⟨t, Finset.mem_univ _, rfl⟩)
      simp only [f, selectedRows_det_eq_zero_of_not_terminal U S hbad, mul_zero]
    _ = ∑ t : Fin (k + 1), f (terminalSet t) :=
      Finset.sum_image (fun _ _ _ _ heq => terminalSet_injective heq)
    _ = _ := by simp only [f, terminalSet_card]

/-- Indexing the terminal block by its length gives exactly the powers
`(-x)^j` appearing in the manuscript. -/
theorem shifted_row_terminal_expansion_by_length
    (U : Fin (k + 1) → Fin k → R) (x : R) :
    Matrix.det (fun i : Fin k => U i.castSucc - x • U i.succ) =
      ∑ j : Fin (k + 1), (-x) ^ j.val *
        (selectedRows U (terminalSet j.rev)).det := by
  rw [shifted_row_terminal_expansion]
  apply Fintype.sum_equiv Fin.revPerm
  intro t
  change _ = (-x) ^ t.rev.val * (selectedRows U (terminalSet t.rev.rev)).det
  simp [Fin.val_rev]

variable {N : ℕ}

/-- The partition `(q^(k-j),(q-1)^j)`, with its full zero tail. -/
def deletionShape (N q k j : ℕ) : Fin N → ℕ :=
  fun i => if i.val < k - j then q else if i.val < k then q - 1 else 0

theorem deletionShape_isPartition (N q k j : ℕ) :
    AlgebraicCombinatorics.IsNPartition (deletionShape N q k j) := by
  intro i l hil
  dsimp [deletionShape]
  split_ifs <;> omega

theorem deletionShape_zero_tail (q k j : ℕ) (i : Fin N) (hi : k ≤ i.val) :
    deletionShape N q k j i = 0 := by
  have hfirst : ¬ i.val < k - j := by omega
  simp [deletionShape, hfirst, not_lt.mpr hi]

open RectangleDeterminants

/-- The `k+1` rows denoted by U in the manuscript. -/
def completeRows (a : Fin N → ℝ) (q k : ℕ) : Fin (k + 1) → Fin k → ℝ :=
  fun i l => completeInt a ((q : ℤ) - (i.val : ℤ) + (l.val : ℤ))

/-- The terminal choice is precisely the Jacobi–Trudi determinant for the
claimed partition, with zero rows removed by the proved padding identity. -/
theorem terminal_determinant_eq_schurValue (a : Fin N → ℝ)
    (q k : ℕ) (hq : 1 ≤ q) (hk : k ≤ N) (j : Fin (k + 1)) :
    (selectedRows (completeRows a q k) (terminalSet j.rev)).det =
      schurValue (deletionShape N q k j.val) a := by
  rw [JacobiTrudiPadding.schurValue_eq_det_of_zero_tail a _
    (deletionShape_isPartition N q k j.val) k hk
    (fun i hi => deletionShape_zero_tail q k j.val i hi)]
  apply congrArg Matrix.det
  ext i l
  change selectedRows (completeRows a q k) (terminalSet j.rev) i l =
    completeInt a ((deletionShape N q k j.val (Fin.castLE hk i) : ℤ) - i.val + l.val)
  by_cases hi : i.val < k - j.val
  · have hnot : i ∉ terminalSet j.rev := by
      simp only [mem_terminalSet, Fin.val_rev]
      omega
    have hpart : deletionShape N q k j.val (Fin.castLE hk i) = q := by
      simp only [deletionShape, Fin.val_castLE, hi, if_true]
    simp only [selectedRows, if_neg hnot, completeRows, Fin.val_castSucc, hpart]
  · have hmem : i ∈ terminalSet j.rev := by
      simp only [mem_terminalSet, Fin.val_rev]
      omega
    have hpart : deletionShape N q k j.val (Fin.castLE hk i) = q - 1 := by
      simp only [deletionShape, Fin.val_castLE, hi, if_false, i.isLt, if_true]
    simp only [selectedRows, if_pos hmem, completeRows, Fin.val_succ, hpart]
    apply congrArg (completeInt a)
    omega

/-- Substitution `h_d[a-x] = h_d(a)-x*h_(d-1)(a)` in the rectangular
Jacobi–Trudi determinant. This definition does not assume x is an alphabet letter. -/
def deletedRectangle (a : Fin N → ℝ) (x : ℝ) (q k : ℕ) : ℝ :=
  (toeplitz (fun d => completeInt a d - x * completeInt a (d - 1)) q k).det

theorem rectangle_deletion (a : Fin N → ℝ) (x : ℝ)
    (q k : ℕ) (hq : 1 ≤ q) (hk : k ≤ N) :
    deletedRectangle a x q k =
      ∑ j : Fin (k + 1), (-x) ^ j.val *
        schurValue (deletionShape N q k j.val) a := by
  have hrows : toeplitz (fun d => completeInt a d - x * completeInt a (d - 1)) q k =
      (fun i : Fin k => completeRows a q k i.castSucc - x • completeRows a q k i.succ) := by
    ext i l
    simp only [toeplitz, completeRows, Pi.sub_apply, Pi.smul_apply, smul_eq_mul,
      Fin.val_castSucc, Fin.val_succ, Nat.cast_add, Nat.cast_one]
    have hidx : (q : ℤ) - i.val + l.val - 1 = q - (i.val + 1) + l.val := by ring
    rw [hidx]
  unfold deletedRectangle
  rw [hrows, shifted_row_terminal_expansion_by_length]
  apply Finset.sum_congr rfl
  intro j _
  rw [terminal_determinant_eq_schurValue a q k hq hk j]

/-- Setting an actual letter to zero realizes the formal subtraction of that
letter in every entry of Jacobi–Trudi. -/
theorem rectangleSchur_update_eq_deletedRectangle (a : Fin N → ℝ)
    (i : Fin N) (q k : ℕ) (hk : k ≤ N) :
    rectangleSchur (Function.update a i 0) q k = deletedRectangle a (a i) q k := by
  rw [rectangleSchur_eq_completeDet _ q k hk]
  unfold deletedRectangle
  apply congrArg Matrix.det
  ext r l
  exact CompleteDeletion.completeInt_update_zero a i _

/-- Deletion of an actual alphabet letter, proved with the same row expansion. -/
theorem rectangle_deletion_actual (a : Fin N → ℝ) (i : Fin N)
    (q k : ℕ) (hq : 1 ≤ q) (hk : k ≤ N) :
    rectangleSchur (Function.update a i 0) q k =
      ∑ j : Fin (k + 1), (-a i) ^ j.val *
        schurValue (deletionShape N q k j.val) a := by
  rw [rectangleSchur_update_eq_deletedRectangle a i q k hk,
    rectangle_deletion a (a i) q k hq hk]

/-- The load formed by deleting each letter and weighting by its square. -/
def rectangleLoad (a : Fin N → ℝ) (q k : ℕ) : ℝ :=
  ∑ i, a i ^ 2 * rectangleSchur (Function.update a i 0) q k

/-- Equation `eq:load-power-sums`, generalized to any rectangle width q.
This is obtained by the actual deletion formula followed by interchanging
finite sums, so its left side is the concrete load rather than an assumed
power-sum representation. -/
theorem rectangleLoad_eq_power_sums (a : Fin N → ℝ)
    (q k : ℕ) (hq : 1 ≤ q) (hk : k ≤ N) :
    rectangleLoad a q k =
      ∑ j : Fin (k + 1), (-1 : ℝ) ^ j.val *
        AlternantIdentities.powerSum a (j.val + 2) *
        schurValue (deletionShape N q k j.val) a := by
  unfold rectangleLoad
  simp_rw [rectangle_deletion_actual a _ q k hq hk, Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro j _
  unfold AlternantIdentities.powerSum
  simp only [Finset.mul_sum, Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro i _
  rw [neg_pow, pow_add]
  ring

end CoefficientOne.RectangleDeletion
