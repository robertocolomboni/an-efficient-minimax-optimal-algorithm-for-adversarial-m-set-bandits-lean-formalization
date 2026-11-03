import EffectiveResistance.FiniteLaw
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Tactic.Ext
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Order
import Mathlib.Tactic.Ring

/-!
# Occupancy counting between adjacent ranks

The key combinatorial operation moves one element from the first member of
an ordered rank-`q+1` pair to the second.  It gives a weight-preserving
bijection with marked ordered pairs of ranks `q` and `q+2`.
-/

open scoped BigOperators

namespace EffectiveResistance

noncomputable section

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- A marked ordered pair of rank-`q+1` sets, where the mark belongs only to
the first set. -/
@[ext]
structure BalancedMove (ι : Type*) [Fintype ι] [DecidableEq ι] (q : ℕ) where
  left : RankSubset ι (q + 1)
  right : RankSubset ι (q + 1)
  moved : ι
  moved_mem_left : moved ∈ left.1
  moved_not_mem_right : moved ∉ right.1

/-- A marked ordered pair of ranks `q` and `q+2`, where the mark belongs only
to the second set. -/
@[ext]
structure UnbalancedMove (ι : Type*) [Fintype ι] [DecidableEq ι] (q : ℕ) where
  lower : RankSubset ι q
  upper : RankSubset ι (q + 2)
  moved : ι
  moved_mem_upper : moved ∈ upper.1
  moved_not_mem_lower : moved ∉ lower.1

abbrev BalancedMoveSigma (ι : Type*) [Fintype ι] [DecidableEq ι] (q : ℕ) :=
  Σ A : RankSubset ι (q + 1),
    Σ B : RankSubset ι (q + 1), {x : ι // x ∈ A.1 \ B.1}

abbrev UnbalancedMoveSigma (ι : Type*) [Fintype ι] [DecidableEq ι] (q : ℕ) :=
  Σ C : RankSubset ι q,
    Σ D : RankSubset ι (q + 2), {x : ι // x ∈ D.1 \ C.1}

def balancedMoveSigmaEquiv (q : ℕ) :
    BalancedMoveSigma ι q ≃ BalancedMove ι q where
  toFun M := ⟨M.1, M.2.1, M.2.2.1,
    (Finset.mem_sdiff.mp M.2.2.2).1,
    (Finset.mem_sdiff.mp M.2.2.2).2⟩
  invFun M := ⟨M.left, ⟨M.right, ⟨M.moved,
    Finset.mem_sdiff.mpr ⟨M.moved_mem_left, M.moved_not_mem_right⟩⟩⟩⟩
  left_inv M := by
    rcases M with ⟨A, B, x⟩
    rfl
  right_inv M := by
    ext <;> rfl

def unbalancedMoveSigmaEquiv (q : ℕ) :
    UnbalancedMoveSigma ι q ≃ UnbalancedMove ι q where
  toFun M := ⟨M.1, M.2.1, M.2.2.1,
    (Finset.mem_sdiff.mp M.2.2.2).1,
    (Finset.mem_sdiff.mp M.2.2.2).2⟩
  invFun M := ⟨M.lower, ⟨M.upper, ⟨M.moved,
    Finset.mem_sdiff.mpr ⟨M.moved_mem_upper, M.moved_not_mem_lower⟩⟩⟩⟩
  left_inv M := by
    rcases M with ⟨C, D, x⟩
    rfl
  right_inv M := by
    ext <;> rfl

noncomputable instance (q : ℕ) : Fintype (BalancedMove ι q) :=
  Fintype.ofEquiv (BalancedMoveSigma ι q) (balancedMoveSigmaEquiv q)

noncomputable instance (q : ℕ) : Fintype (UnbalancedMove ι q) :=
  Fintype.ofEquiv (UnbalancedMoveSigma ι q) (unbalancedMoveSigmaEquiv q)

def occupancy (A B : Finset ι) (k : ι) : ℕ :=
  (if k ∈ A then 1 else 0) + (if k ∈ B then 1 else 0)

def moveDownUp (q : ℕ) : BalancedMove ι q → UnbalancedMove ι q :=
  fun M =>
    let A := M.left
    let B := M.right
    let x := M.moved
    have hxA : x ∈ A.1 := M.moved_mem_left
    have hxB : x ∉ B.1 := M.moved_not_mem_right
    let Cset := A.1.erase x
    let Dset := insert x B.1
    have hC : Cset.card = q := by
      simp only [Cset, Finset.card_erase_of_mem hxA, A.2]
      omega
    have hD : Dset.card = q + 2 := by
      simp only [Dset, Finset.card_insert_of_notMem hxB, B.2]
    ⟨⟨Cset, hC⟩, ⟨Dset, hD⟩, x, by simp [Dset], by simp [Cset]⟩

def moveUpDown (q : ℕ) : UnbalancedMove ι q → BalancedMove ι q :=
  fun M =>
    let C := M.lower
    let D := M.upper
    let x := M.moved
    have hxD : x ∈ D.1 := M.moved_mem_upper
    have hxC : x ∉ C.1 := M.moved_not_mem_lower
    let Aset := insert x C.1
    let Bset := D.1.erase x
    have hA : Aset.card = q + 1 := by
      simp only [Aset, Finset.card_insert_of_notMem hxC, C.2]
    have hB : Bset.card = q + 1 := by
      simp only [Bset, Finset.card_erase_of_mem hxD, D.2]
      omega
    ⟨⟨Aset, hA⟩, ⟨Bset, hB⟩, x, by simp [Aset], by simp [Bset]⟩

theorem moveUpDown_moveDownUp (q : ℕ) (M : BalancedMove ι q) :
    moveUpDown q (moveDownUp q M) = M := by
  apply BalancedMove.ext
  · apply Subtype.ext
    exact Finset.insert_erase M.moved_mem_left
  · apply Subtype.ext
    exact Finset.erase_insert M.moved_not_mem_right
  · rfl

theorem moveDownUp_moveUpDown (q : ℕ) (M : UnbalancedMove ι q) :
    moveDownUp q (moveUpDown q M) = M := by
  apply UnbalancedMove.ext
  · apply Subtype.ext
    exact Finset.erase_insert M.moved_not_mem_lower
  · apply Subtype.ext
    exact Finset.insert_erase M.moved_mem_upper
  · rfl

/-- The element-moving bijection. -/
def moveEquiv (q : ℕ) : BalancedMove ι q ≃ UnbalancedMove ι q where
  toFun := moveDownUp q
  invFun := moveUpDown q
  left_inv := moveUpDown_moveDownUp q
  right_inv := moveDownUp_moveUpDown q

theorem occupancy_moveDownUp (q : ℕ) (M : BalancedMove ι q) :
    occupancy (moveDownUp q M).lower.1 (moveDownUp q M).upper.1 =
      occupancy M.left.1 M.right.1 := by
  funext k
  by_cases hk : k = M.moved
  · subst k
    simp [moveDownUp, occupancy, M.moved_mem_left, M.moved_not_mem_right]
  · simp [moveDownUp, occupancy, hk]

theorem subsetWeight_moveDownUp (w : ι → ℝ) (q : ℕ)
    (M : BalancedMove ι q) :
    subsetWeight w (moveDownUp q M).lower.1 *
        subsetWeight w (moveDownUp q M).upper.1 =
      subsetWeight w M.left.1 * subsetWeight w M.right.1 := by
  let A := M.left
  let B := M.right
  let x := M.moved
  have hxA : x ∈ A.1 := M.moved_mem_left
  have hxB : x ∉ B.1 := M.moved_not_mem_right
  simp only [moveDownUp, subsetWeight]
  rw [Finset.prod_insert hxB]
  calc
    (∏ i ∈ A.1.erase x, w i) *
        (w x * ∏ i ∈ B.1, w i) =
      ((∏ i ∈ A.1.erase x, w i) * w x) *
        (∏ i ∈ B.1, w i) := by ring
    _ = (∏ i ∈ A.1, w i) * ∏ i ∈ B.1, w i := by
      rw [Finset.prod_erase_mul A.1 w hxA]

theorem moved_sdiff_card (q : ℕ) (M : BalancedMove ι q) :
    ((moveDownUp q M).upper.1 \ (moveDownUp q M).lower.1).card =
      (M.left.1 \ M.right.1).card + 1 := by
  let A := M.left
  let B := M.right
  let x := M.moved
  have hxA : x ∈ A.1 := M.moved_mem_left
  have hxB : x ∉ B.1 := M.moved_not_mem_right
  have hset :
      (insert x B.1 \ A.1.erase x) = insert x (B.1 \ A.1) := by
    ext y
    by_cases hy : y = x
    · subst y
      simp [hxA, hxB]
    · simp [hy]
  simp only [moveDownUp]
  rw [hset, Finset.card_insert_of_notMem]
  · have hcard : (B.1 \ A.1).card = (A.1 \ B.1).card := by
      apply Finset.card_sdiff_comm
      rw [A.2, B.2]
    rw [hcard]
  · simp [hxB]

def balancedOccupancyMoment (w : ι → ℝ) (q : ℕ)
    (F : (ι → ℕ) → ℝ) : ℝ :=
  ∑ A : RankSubset ι (q + 1), ∑ B : RankSubset ι (q + 1),
    subsetWeight w A.1 * subsetWeight w B.1 *
      (((A.1 \ B.1).card : ℝ) / ((A.1 \ B.1).card + 1)) *
        F (occupancy A.1 B.1)

def unbalancedOccupancyMoment (w : ι → ℝ) (q : ℕ)
    (F : (ι → ℕ) → ℝ) : ℝ :=
  ∑ C : RankSubset ι q, ∑ D : RankSubset ι (q + 2),
    subsetWeight w C.1 * subsetWeight w D.1 * F (occupancy C.1 D.1)

def balancedMoveTerm (w : ι → ℝ) (q : ℕ) (F : (ι → ℕ) → ℝ)
    (M : BalancedMove ι q) : ℝ :=
  subsetWeight w M.left.1 * subsetWeight w M.right.1 /
      (((M.left.1 \ M.right.1).card : ℝ) + 1) *
    F (occupancy M.left.1 M.right.1)

def unbalancedMoveTerm (w : ι → ℝ) (q : ℕ) (F : (ι → ℕ) → ℝ)
    (M : UnbalancedMove ι q) : ℝ :=
  subsetWeight w M.lower.1 * subsetWeight w M.upper.1 /
      ((M.upper.1 \ M.lower.1).card : ℝ) *
    F (occupancy M.lower.1 M.upper.1)

theorem sum_balancedMoveTerm (w : ι → ℝ) (q : ℕ)
    (F : (ι → ℕ) → ℝ) :
    ∑ M : BalancedMove ι q, balancedMoveTerm w q F M =
      balancedOccupancyMoment w q F := by
  rw [← (balancedMoveSigmaEquiv (ι := ι) q).sum_comp]
  simp only [Fintype.sum_sigma]
  unfold balancedMoveTerm balancedOccupancyMoment
  apply Finset.sum_congr rfl
  intro A _
  apply Finset.sum_congr rfl
  intro B _
  change (∑ _x : {x : ι // x ∈ A.1 \ B.1},
      subsetWeight w A.1 * subsetWeight w B.1 /
          (((A.1 \ B.1).card : ℝ) + 1) *
        F (occupancy A.1 B.1)) = _
  rw [Finset.sum_const]
  simp only [Finset.card_univ, Fintype.card_coe, nsmul_eq_mul]
  field_simp

theorem unbalanced_sdiff_card_pos (C : RankSubset ι q)
    (D : RankSubset ι (q + 2)) : 0 < (D.1 \ C.1).card := by
  have hle := Finset.card_le_card_sdiff_add_card (s := D.1) (t := C.1)
  rw [C.2, D.2] at hle
  omega

theorem sum_unbalancedMoveTerm (w : ι → ℝ) (q : ℕ)
    (F : (ι → ℕ) → ℝ) :
    ∑ M : UnbalancedMove ι q, unbalancedMoveTerm w q F M =
      unbalancedOccupancyMoment w q F := by
  rw [← (unbalancedMoveSigmaEquiv (ι := ι) q).sum_comp]
  simp only [Fintype.sum_sigma]
  unfold unbalancedMoveTerm unbalancedOccupancyMoment
  apply Finset.sum_congr rfl
  intro C _
  apply Finset.sum_congr rfl
  intro D _
  change (∑ _x : {x : ι // x ∈ D.1 \ C.1},
      subsetWeight w C.1 * subsetWeight w D.1 /
          ((D.1 \ C.1).card : ℝ) *
        F (occupancy C.1 D.1)) = _
  rw [Finset.sum_const]
  simp only [Finset.card_univ, Fintype.card_coe, nsmul_eq_mul]
  have hcard : ((D.1 \ C.1).card : ℝ) ≠ 0 := by
    exact_mod_cast (ne_of_gt (unbalanced_sdiff_card_pos C D))
  field_simp [hcard]

theorem moveTerm_preserved (w : ι → ℝ) (q : ℕ)
    (F : (ι → ℕ) → ℝ) (M : BalancedMove ι q) :
    unbalancedMoveTerm w q F (moveDownUp q M) =
      balancedMoveTerm w q F M := by
  unfold unbalancedMoveTerm balancedMoveTerm
  rw [subsetWeight_moveDownUp, occupancy_moveDownUp, moved_sdiff_card]
  simp only [Nat.cast_add, Nat.cast_one]

/-- Unnormalized likelihood-ratio identity for every statistic depending only
on the occupancy vector. -/
theorem occupancy_counting_identity (w : ι → ℝ) (q : ℕ)
    (F : (ι → ℕ) → ℝ) :
    balancedOccupancyMoment w q F = unbalancedOccupancyMoment w q F := by
  rw [← sum_balancedMoveTerm, ← sum_unbalancedMoveTerm]
  rw [← (moveEquiv (ι := ι) q).sum_comp]
  apply Finset.sum_congr rfl
  intro M _
  exact (moveTerm_preserved w q F M).symm

def rawRankPairMoment (w : ι → ℝ) (r s : ℕ)
    (G : RankSubset ι r → RankSubset ι s → ℝ) : ℝ :=
  ∑ A : RankSubset ι r, ∑ B : RankSubset ι s,
    subsetWeight w A.1 * subsetWeight w B.1 * G A B

def rankPairExpectation (w : ι → ℝ) (r s : ℕ)
    (G : RankSubset ι r → RankSubset ι s → ℝ) : ℝ :=
  ∑ A : RankSubset ι r, ∑ B : RankSubset ι s,
    subsetProbability w r A * subsetProbability w s B * G A B

theorem rankPairExpectation_eq_raw_div (w : ι → ℝ) (r s : ℕ)
    (G : RankSubset ι r → RankSubset ι s → ℝ) :
    rankPairExpectation w r s G =
      rawRankPairMoment w r s G / (elementarySum w r * elementarySum w s) := by
  unfold rankPairExpectation rawRankPairMoment subsetProbability
  calc
    (∑ A : RankSubset ι r, ∑ B : RankSubset ι s,
      subsetWeight w A.1 / elementarySum w r *
        (subsetWeight w B.1 / elementarySum w s) * G A B) =
      ∑ A : RankSubset ι r, ∑ B : RankSubset ι s,
        (subsetWeight w A.1 * subsetWeight w B.1 * G A B) /
          (elementarySum w r * elementarySum w s) := by
      apply Finset.sum_congr rfl
      intro A _
      apply Finset.sum_congr rfl
      intro B _
      ring
    _ = _ := by
      rw [Finset.sum_div]
      apply Finset.sum_congr rfl
      intro A _
      rw [Finset.sum_div]

def occupancyTilt (A B : Finset ι) : ℝ :=
  (A \ B).card / ((A \ B).card + 1)

def adjacentTheta (w : ι → ℝ) (q : ℕ) : ℝ :=
  elementarySum w q * elementarySum w (q + 2) /
    elementarySum w (q + 1) ^ 2

theorem occupancyTilt_nonnegative (A B : Finset ι) :
    0 ≤ occupancyTilt A B := by
  unfold occupancyTilt
  positivity

theorem occupancyTilt_le_one (A B : Finset ι) :
    occupancyTilt A B ≤ 1 := by
  unfold occupancyTilt
  apply (div_le_one₀ (by positivity : 0 < ((A \ B).card : ℝ) + 1)).2
  norm_num

theorem occupancyTilt_lt_one (A B : Finset ι) :
    occupancyTilt A B < 1 := by
  unfold occupancyTilt
  apply (div_lt_one (by positivity : 0 < ((A \ B).card : ℝ) + 1)).2
  norm_num

theorem rankPairExpectation_one
    (w : ι → ℝ) (hw : ∀ i, 0 < w i) (r s : ℕ)
    (hr : r ≤ Fintype.card ι) (hs : s ≤ Fintype.card ι) :
    rankPairExpectation w r s (fun _ _ => 1) = 1 := by
  unfold rankPairExpectation
  calc
    (∑ A : RankSubset ι r, ∑ B : RankSubset ι s,
      subsetProbability w r A * subsetProbability w s B * 1) =
        ∑ A : RankSubset ι r,
          subsetProbability w r A *
            (∑ B : RankSubset ι s, subsetProbability w s B) := by
      apply Finset.sum_congr rfl
      intro A _
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro B _
      ring
    _ = ∑ A : RankSubset ι r, subsetProbability w r A := by
      rw [sum_subsetProbability w hw hs]
      simp
    _ = 1 := sum_subsetProbability w hw hr

theorem normalize_adjacent_moment
    {E0 E1 E2 U : ℝ} (hE0 : E0 ≠ 0) (hE1 : E1 ≠ 0) (hE2 : E2 ≠ 0) :
    U / (E1 * E1) = (E0 * E2 / E1 ^ 2) * (U / (E0 * E2)) := by
  field_simp [hE0, hE1, hE2]

/-- Normalized occupancy likelihood-ratio identity.  This is the rigorous
finite-sum version of `dQ/dP = (H/(H+1))/θ`. -/
theorem occupancy_likelihood_ratio
    (w : ι → ℝ) (hw : ∀ i, 0 < w i) (q : ℕ)
    (hq : q + 2 ≤ Fintype.card ι) (F : (ι → ℕ) → ℝ) :
    rankPairExpectation w (q + 1) (q + 1)
        (fun A B => occupancyTilt A.1 B.1 * F (occupancy A.1 B.1)) =
      adjacentTheta w q *
        rankPairExpectation w q (q + 2)
          (fun C D => F (occupancy C.1 D.1)) := by
  rw [rankPairExpectation_eq_raw_div, rankPairExpectation_eq_raw_div]
  have hbalanced :
      rawRankPairMoment w (q + 1) (q + 1)
          (fun A B => occupancyTilt A.1 B.1 * F (occupancy A.1 B.1)) =
        balancedOccupancyMoment w q F := by
    unfold rawRankPairMoment balancedOccupancyMoment occupancyTilt
    apply Finset.sum_congr rfl
    intro A _
    apply Finset.sum_congr rfl
    intro B _
    ring
  have hunbalanced :
      rawRankPairMoment w q (q + 2)
          (fun C D => F (occupancy C.1 D.1)) =
        unbalancedOccupancyMoment w q F := by
    rfl
  rw [hbalanced, hunbalanced]
  rw [occupancy_counting_identity]
  unfold adjacentTheta
  have hq0 : q ≤ Fintype.card ι := by omega
  have hq1 : q + 1 ≤ Fintype.card ι := by omega
  have hE0 : elementarySum w q ≠ 0 :=
    ne_of_gt (elementarySum_pos w hw hq0)
  have hE1 : elementarySum w (q + 1) ≠ 0 :=
    ne_of_gt (elementarySum_pos w hw hq1)
  have hE2 : elementarySum w (q + 2) ≠ 0 :=
    ne_of_gt (elementarySum_pos w hw hq)
  exact normalize_adjacent_moment hE0 hE1 hE2

end

end EffectiveResistance
