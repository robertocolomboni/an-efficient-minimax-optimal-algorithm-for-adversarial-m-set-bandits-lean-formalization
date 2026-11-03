import MsetsPaper.Upper.WeightedLaw
import Mathlib.RingTheory.MvPolynomial.Symmetric.Defs

/-!
# Elementary symmetric sums for the actual weighted action law

These are specifications, expressed as finite subset sums. The separate
`ESPDP` module implements the non-enumerative dynamic program and proves its
agreement with this specification. Negative degrees are explicitly zero.
-/

noncomputable section
open scoped BigOperators
open MsetsLower MsetsLower.History

namespace MsetsPaper.Upper

variable {ι : Type*}

def esp (w : ι → ℝ) (R : Finset ι) (k : ℕ) : ℝ :=
  ∑ S ∈ R.powersetCard k, ∏ i ∈ S, w i

def espInt (w : ι → ℝ) (R : Finset ι) (k : ℤ) : ℝ :=
  if 0 ≤ k then esp w R k.toNat else 0

@[simp] theorem esp_zero (w : ι → ℝ) (R : Finset ι) : esp w R 0 = 1 := by
  simp [esp, Finset.powersetCard_zero]

@[simp] theorem esp_empty_succ (w : ι → ℝ) (k : ℕ) : esp w ∅ (k + 1) = 0 := by
  simp [esp, Finset.powersetCard_eq_empty.mpr (show (∅ : Finset ι).card < k + 1 by simp)]

theorem esp_eq_zero_of_card_lt (w : ι → ℝ) (R : Finset ι) (k : ℕ)
    (hk : R.card < k) : esp w R k = 0 := by
  simp [esp, Finset.powersetCard_eq_empty.mpr hk]

theorem esp_nonneg (w : ι → ℝ) (hw : ∀ i, 0 ≤ w i) (R : Finset ι) (k : ℕ) :
    0 ≤ esp w R k :=
  Finset.sum_nonneg fun _ _ => Finset.prod_nonneg fun i _ => hw i

theorem esp_pos (w : ι → ℝ) (hw : ∀ i, 0 < w i) (R : Finset ι) (k : ℕ)
    (hk : k ≤ R.card) : 0 < esp w R k :=
  Finset.sum_pos (fun _ _ => Finset.prod_pos fun i _ => hw i)
    (Finset.powersetCard_nonempty.mpr hk)

theorem esp_eq_multiset (w : ι → ℝ) (R : Finset ι) (k : ℕ) :
    esp w R k = (R.val.map w).esymm k := (Finset.esymm_map_val w R k).symm

theorem esp_insert_succ [DecidableEq ι] (w : ι → ℝ) (R : Finset ι) (i : ι) (hi : i ∉ R) (k : ℕ) :
    esp w (insert i R) (k + 1) = esp w R (k + 1) + w i * esp w R k := by
  simp only [esp_eq_multiset, Finset.insert_val_of_notMem hi, Multiset.map_cons]
  simp [Multiset.esymm, Multiset.powersetCard_cons, Multiset.map_map,
    Multiset.sum_map_mul_left]

theorem esp_delete [DecidableEq ι] (w : ι → ℝ) (R : Finset ι) (i : ι) (hi : i ∈ R)
    (k : ℕ) (hk : 0 < k) :
    esp w R k = esp w (R.erase i) k + w i * esp w (R.erase i) (k - 1) := by
  simpa only [Finset.insert_erase hi, Nat.sub_add_cancel hk] using
    esp_insert_succ w (R.erase i) i (Finset.notMem_erase _ _) (k - 1)

@[simp] theorem espInt_nat (w : ι → ℝ) (R : Finset ι) (k : ℕ) :
    espInt w R k = esp w R k := by simp [espInt]

theorem espInt_neg (w : ι → ℝ) (R : Finset ι) (k : ℤ) (hk : k < 0) :
    espInt w R k = 0 := by simp [espInt, not_le.mpr hk]

/-- Removing an arbitrary prescribed set from each action gives exactly the
remaining elementary sum. The proof is the literal subset bijection. -/
theorem esp_containing [DecidableEq ι] (w : ι → ℝ) (R J : Finset ι) (hJR : J ⊆ R)
    (k : ℕ) (hJk : J.card ≤ k) :
    (∑ S ∈ R.powersetCard k, if J ⊆ S then ∏ i ∈ S, w i else 0) =
      (∏ i ∈ J, w i) * esp w (R \ J) (k - J.card) := by
  rw [← Finset.sum_filter, Finset.filter_powersetCard_subset J R k hJR hJk]
  have hd (S : Finset ι) (hS : S ∈ (R \ J).powersetCard (k - J.card)) :
      Disjoint S J :=
    Finset.disjoint_of_subset_left (Finset.mem_powersetCard.mp hS).1
      Finset.sdiff_disjoint
  rw [Finset.sum_image]
  · rw [esp, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro S hS
    rw [Finset.prod_union (hd S hS), mul_comm]
  · intro S hS T hT hST
    have heq := congrArg (fun X : Finset ι => X \ J) hST
    simpa only [Finset.union_sdiff_cancel_right (hd S hS),
      Finset.union_sdiff_cancel_right (hd T hT)] using heq

variable {d m : ℕ}

/-- Reindexing actual actions by the cardinality-restricted powerset. -/
theorem sum_actions_eq_powerset (f : Finset (Fin d) → ℝ) :
    (∑ a : Action d m, f a.val) = ∑ S ∈ (Finset.univ : Finset (Fin d)).powersetCard m, f S := by
  symm
  apply Finset.sum_subtype
  intro S
  simp

theorem partition_eq_esp (theta : Fin d → ℝ) :
    partition (m := m) theta = esp (fun i => Real.exp (theta i)) Finset.univ m := by
  simp only [partition, actionLoss_eq_finset_sum, Real.exp_sum]
  exact sum_actions_eq_powerset (fun S => ∏ i ∈ S, Real.exp (theta i))

theorem weightedLaw_eq_esp (theta : Fin d → ℝ) (a : Action d m) :
    weightedLaw theta a =
      (∏ i ∈ a.val, Real.exp (theta i)) /
        esp (fun i => Real.exp (theta i)) Finset.univ m := by
  simp only [weightedLaw, partition_eq_esp, actionLoss_eq_finset_sum, Real.exp_sum]

end MsetsPaper.Upper
