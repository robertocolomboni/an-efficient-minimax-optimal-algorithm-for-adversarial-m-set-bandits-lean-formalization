import MsetsLower.Lower.Confidence.Core
import MsetsLower.Feedback.Inverse

/-!
# Item losses in the confidence construction

This file formalizes the reference and planted item-loss formulas from
`eq:lower-confidence-planted-loss`, together with their exact aggregate action
losses and normalization.  The adaptive stopping rule and random-table fixing
are layered on top of these pointwise identities elsewhere.
-/

namespace MsetsLower.Lower.Confidence

open MsetsLower Feedback
open scoped BigOperators

noncomputable section

/-- Indicator of the candidate set `V`. -/
def candidateIndicator
    {n k : Nat} (hkn : k ≤ n) (j : Fin n) : Real :=
  if j ∈ confidenceCandidates n k hkn then 1 else 0

theorem actionLoss_candidateIndicator
    {n k : Nat} (hkn : k ≤ n) (A : MSetAction n k) :
    actionLoss A (candidateIndicator hkn) = (candidateCount hkn A : Real) := by
  classical
  rw [actionLoss_eq_finset_sum]
  simp [candidateIndicator, candidateCount]

private theorem actionLoss_const
    {n k : Nat} (A : MSetAction n k) (c : Real) :
    actionLoss A (fun _ => c) = (k : Real) * c := by
  rw [actionLoss_eq_finset_sum]
  simp [A.2]

private theorem actionLoss_mul_left
    {n k : Nat} (A : MSetAction n k) (c : Real) (f : Fin n → Real) :
    actionLoss A (fun j => c * f j) = c * actionLoss A f := by
  rw [actionLoss_eq_finset_sum, actionLoss_eq_finset_sum, Finset.mul_sum]

private theorem actionLoss_sub
    {n k : Nat} (A : MSetAction n k) (f g : Fin n → Real) :
    actionLoss A (fun j => f j - g j) = actionLoss A f - actionLoss A g := by
  rw [actionLoss_eq_finset_sum, actionLoss_eq_finset_sum,
    actionLoss_eq_finset_sum, Finset.sum_sub_distrib]

private theorem actionLoss_pointIndicator
    {n k : Nat} (A : MSetAction n k) (c : Real) (i : Fin n) :
    actionLoss A (fun j => c * (if j = i then 1 else 0)) =
      c * (if i ∈ A.1 then 1 else 0) := by
  classical
  rw [actionLoss_eq_finset_sum]
  by_cases hi : i ∈ A.1 <;> simp [hi]

/-- Reference item loss `ℓ⁽⁰⁾_{t,j}` for a fixed noise value `z`. -/
def referenceItemLoss
    {n k : Nat} (hkn : k ≤ n) (z : Real) (j : Fin n) : Real :=
  ((1 : Real) / 4 + z / 8) / (k : Real)
    + (1 / (8 * (k : Real))) * candidateIndicator hkn j

/-- Exact aggregate reference loss at lines 5519--5523. -/
theorem actionLoss_referenceItemLoss
    {n k : Nat} (hk : 1 ≤ k) (hkn : k ≤ n)
    (z : Real) (A : MSetAction n k) :
    actionLoss A (referenceItemLoss hkn z) =
      (1 : Real) / 4 + z / 8 + (candidateCount hkn A : Real) / (8 * k) := by
  classical
  have hk0 : (k : Real) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt hk)
  change actionLoss A (fun j =>
      ((1 : Real) / 4 + z / 8) / (k : Real) +
        (1 / (8 * (k : Real))) * candidateIndicator hkn j) = _
  rw [actionLoss_add, actionLoss_const, actionLoss_mul_left,
    actionLoss_candidateIndicator]
  field_simp

/-- The reference aggregate loss has the sharper range displayed in the
manuscript. -/
theorem actionLoss_referenceItemLoss_mem_Icc
    {n k : Nat} (hk : 1 ≤ k) (hkn : k ≤ n)
    {z : Real} (hz : z ∈ Set.Icc (-1 : Real) 1)
    (A : MSetAction n k) :
    actionLoss A (referenceItemLoss hkn z) ∈
      Set.Icc ((1 : Real) / 8 + 1 / (8 * k)) (1 / 2 : Real) := by
  rw [actionLoss_referenceItemLoss hk hkn]
  have hkpos : (0 : Real) < k := by exact_mod_cast hk
  have hhposNat := candidateCount_pos hk hkn A
  have hhleNat := candidateCount_le hkn A
  have hhpos : (1 : Real) ≤ candidateCount hkn A := by exact_mod_cast hhposNat
  have hhle : (candidateCount hkn A : Real) ≤ k := by exact_mod_cast hhleNat
  constructor
  · have hdiv : 1 / (8 * (k : Real)) ≤
        (candidateCount hkn A : Real) / (8 * k) :=
      (div_le_div_iff_of_pos_right (mul_pos (by norm_num) hkpos)).2 hhpos
    norm_num at hz hdiv ⊢
    linarith
  · have hdiv : (candidateCount hkn A : Real) / (8 * k) ≤ 1 / 8 := by
      apply (div_le_iff₀ (mul_pos (by norm_num) hkpos)).2
      nlinarith
    norm_num at hz hdiv ⊢
    linarith

/-- Planted item loss for candidate `i`; this is
`eq:lower-confidence-planted-loss` with the activity indicator supplied as a
real scalar. -/
def plantedItemLoss
    {n k : Nat} (hkn : k ≤ n) (z Delta active : Real)
    (i : Fin n) (j : Fin n) : Real :=
  referenceItemLoss hkn z j -
    Delta * shape z * active * (if j = i then 1 else 0)

/-- Exact aggregate planted loss. -/
theorem actionLoss_plantedItemLoss
    {n k : Nat} (hk : 1 ≤ k) (hkn : k ≤ n)
    (z Delta active : Real) (i : Fin n) (A : MSetAction n k) :
    actionLoss A (plantedItemLoss hkn z Delta active i) =
      (1 : Real) / 4 + z / 8 + (candidateCount hkn A : Real) / (8 * k)
        - Delta * shape z * active * (if i ∈ A.1 then 1 else 0) := by
  classical
  change actionLoss A (fun j => referenceItemLoss hkn z j -
    (Delta * shape z * active) * (if j = i then 1 else 0)) = _
  rw [actionLoss_sub, actionLoss_referenceItemLoss hk hkn,
    actionLoss_pointIndicator]

/-- Under the paper's small-gap condition, every planted action loss belongs
to `[0,1]`.  The stronger assumption is exactly `k Δ ≤ 2⁻¹³` from
`eq:lower-confidence-delta-small`. -/
theorem actionLoss_plantedItemLoss_mem_Icc
    {n k : Nat} (hk : 1 ≤ k) (hkn : k ≤ n)
    {z Delta active : Real} (hz : z ∈ Set.Icc (-1 : Real) 1)
    (hDelta : 0 ≤ Delta) (hsmall : (k : Real) * Delta ≤ 1 / (2 : Real) ^ 13)
    (hactive : active ∈ Set.Icc (0 : Real) 1)
    (i : Fin n) (A : MSetAction n k) :
    actionLoss A (plantedItemLoss hkn z Delta active i) ∈ Set.Icc (0 : Real) 1 := by
  rw [actionLoss_plantedItemLoss hk hkn]
  have href := actionLoss_referenceItemLoss_mem_Icc hk hkn hz A
  rw [actionLoss_referenceItemLoss hk hkn] at href
  have hkpos : (0 : Real) < k := by exact_mod_cast hk
  have hshape := shape_mem_Icc hz
  by_cases hi : i ∈ A.1
  · simp only [if_pos hi]
    have hpert_nonneg : 0 ≤ Delta * shape z * active :=
      mul_nonneg (mul_nonneg hDelta hshape.1) hactive.1
    have hpert_le : Delta * shape z * active ≤ 1 / (8 * (k : Real)) := by
      have hDelta_le : Delta ≤ 1 / (8 * (k : Real)) := by
        apply (le_div_iff₀ (mul_pos (by norm_num) hkpos)).2
        calc
          Delta * (8 * k) = 8 * (k * Delta) := by ring
          _ ≤ 8 * (1 / (2 : Real) ^ 13) :=
            mul_le_mul_of_nonneg_left hsmall (by norm_num)
          _ ≤ 1 := by norm_num
      calc
        Delta * shape z * active ≤ Delta * 1 * active :=
          mul_le_mul_of_nonneg_right
            (mul_le_mul_of_nonneg_left hshape.2 hDelta) hactive.1
        _ ≤ Delta * 1 * 1 :=
          mul_le_mul_of_nonneg_left hactive.2 (mul_nonneg hDelta (by norm_num))
        _ ≤ 1 / (8 * (k : Real)) := by simpa using hDelta_le
    constructor
    · simp only [mul_one]
      nlinarith [href.1]
    · simp only [mul_one]
      nlinarith [href.2]
  · simp only [if_neg hi, mul_zero, sub_zero]
    constructor
    · exact (by positivity : (0 : Real) ≤ 1 / 8 + 1 / (8 * (k : Real))).trans href.1
    · exact href.2.trans (by norm_num)

end

end MsetsLower.Lower.Confidence
