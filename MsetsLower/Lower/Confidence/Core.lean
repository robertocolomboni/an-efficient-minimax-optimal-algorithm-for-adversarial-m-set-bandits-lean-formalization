import MsetsLower.Core.Protocol
import Mathlib.Data.Finset.Card

/-!
# Core and candidate coordinates for the confidence construction

This is the finite combinatorics at lines 5456--5463 of the manuscript.  A
fixed `(k-1)`-set is the core, its complement is the candidate set, and every
exact `k`-set contains between one and `k` candidate coordinates.
-/

namespace MsetsLower.Lower.Confidence

noncomputable section

/-- A fixed core with exactly `k-1` coordinates. -/
def confidenceCore (n k : Nat) (hkn : k ≤ n) : Finset (Fin n) :=
  (Classical.choice (nonempty_MSetAction (d := n) (m := k - 1) (by omega))).1

@[simp] theorem card_confidenceCore
    {n k : Nat} (hkn : k ≤ n) :
    (confidenceCore n k hkn).card = k - 1 := by
  exact (Classical.choice
    (nonempty_MSetAction (d := n) (m := k - 1) (by omega))).2

/-- Coordinates outside the fixed core. -/
def confidenceCandidates (n k : Nat) (hkn : k ≤ n) : Finset (Fin n) :=
  Finset.univ \ confidenceCore n k hkn

theorem card_confidenceCandidates
    {n k : Nat} (hk : 1 ≤ k) (hkn : k ≤ n) :
    (confidenceCandidates n k hkn).card = n - k + 1 := by
  rw [confidenceCandidates, Finset.card_sdiff_of_subset (Finset.subset_univ _)]
  simp only [Finset.card_univ, Fintype.card_fin, card_confidenceCore]
  omega

theorem half_dimension_le_card_confidenceCandidates
    {n k : Nat} (hk : 1 ≤ k) (hhalf : k ≤ n / 2) :
    n / 2 ≤ (confidenceCandidates n k (hhalf.trans (Nat.div_le_self n 2))).card := by
  rw [card_confidenceCandidates hk (hhalf.trans (Nat.div_le_self n 2))]
  omega

/-- The number `h_t` of candidate coordinates in an action. -/
def candidateCount {n k : Nat} (hkn : k ≤ n) (a : MSetAction n k) : Nat :=
  (a.1 ∩ confidenceCandidates n k hkn).card

theorem candidateCount_pos
    {n k : Nat} (hk : 1 ≤ k) (hkn : k ≤ n) (a : MSetAction n k) :
    1 ≤ candidateCount hkn a := by
  have hdiff := Finset.le_card_sdiff (confidenceCore n k hkn) a.1
  rw [a.2, card_confidenceCore] at hdiff
  have hone : 1 ≤ (a.1 \ confidenceCore n k hkn).card := by omega
  have heq : a.1 ∩ confidenceCandidates n k hkn =
      a.1 \ confidenceCore n k hkn := by
    ext x
    simp [confidenceCandidates]
  rw [candidateCount, heq]
  exact hone

theorem candidateCount_le
    {n k : Nat} (hkn : k ≤ n) (a : MSetAction n k) :
    candidateCount hkn a ≤ k := by
  calc
    candidateCount hkn a ≤ a.1.card :=
      Finset.card_mono Finset.inter_subset_left
    _ = k := a.2

/-- The comparator formed by the core together with a candidate coordinate. -/
def coreComparator
    {n k : Nat} (hk : 1 ≤ k) (hkn : k ≤ n)
    (i : Fin n) (hi : i ∈ confidenceCandidates n k hkn) : MSetAction n k := by
  refine ⟨insert i (confidenceCore n k hkn), ?_⟩
  have hnot : i ∉ confidenceCore n k hkn := by
    simpa [confidenceCandidates] using hi
  rw [Finset.card_insert_of_notMem hnot, card_confidenceCore]
  omega

@[simp] theorem coreComparator_val
    {n k : Nat} (hk : 1 ≤ k) (hkn : k ≤ n)
    (i : Fin n) (hi : i ∈ confidenceCandidates n k hkn) :
    (coreComparator hk hkn i hi).1 = insert i (confidenceCore n k hkn) := rfl

@[simp] theorem candidateCount_coreComparator
    {n k : Nat} (hk : 1 ≤ k) (hkn : k ≤ n)
    (i : Fin n) (hi : i ∈ confidenceCandidates n k hkn) :
    candidateCount hkn (coreComparator hk hkn i hi) = 1 := by
  have hnot : i ∉ confidenceCore n k hkn := by
    simpa [confidenceCandidates] using hi
  simp [candidateCount, confidenceCandidates, coreComparator, hnot]

end

end MsetsLower.Lower.Confidence
