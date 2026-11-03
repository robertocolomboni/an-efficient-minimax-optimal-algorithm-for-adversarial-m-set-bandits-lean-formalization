import CoefficientOne.Sampling.NewtonElementary

/-! # Quota monotonicity, including the two forced thresholds -/

open scoped BigOperators
open EffectiveResistance

namespace CoefficientOne.Sampling
noncomputable section

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- The manuscript's E_(r-1), with E_(-1)=0. -/
def elementaryPredecessor (w : ι → ℝ) (R : Finset ι) (r : ℕ) : ℝ :=
  if r = 0 then 0 else restrictedElementary w R (r - 1)

@[simp] theorem elementaryPredecessor_zero (w : ι → ℝ) (R : Finset ι) :
    elementaryPredecessor w R 0 = 0 := by simp [elementaryPredecessor]

@[simp] theorem elementaryPredecessor_succ (w : ι → ℝ) (R : Finset ι) (r : ℕ) :
    elementaryPredecessor w R (r + 1) = restrictedElementary w R r := by
  simp [elementaryPredecessor]

theorem restrictedElementary_turan (w : ι → ℝ) (hw : ∀ i, 0 < w i)
    (R : Finset ι) (r : ℕ) (hr : r ≤ R.card) :
    elementaryPredecessor w R r * restrictedElementary w R (r + 1) ≤
      restrictedElementary w R r ^ 2 := by
  cases r with
  | zero => simp
  | succ r =>
    rw [elementaryPredecessor_succ]
    by_cases hi : r + 2 ≤ R.card
    · exact restrictedElementary_logConcave w hw R r hi
    · rw [restrictedElementary_eq_zero_of_card_lt w R (r + 1 + 1) (by omega)]
      simpa using sq_nonneg (restrictedElementary w R (r + 1))

/-- The forced rejection at zero is distinguished from testing U≤0, so this
threshold is used only for comparing probabilities, not to change the recursion. -/
def quotaThreshold (w : ι → ℝ) (R : Finset ι) (r : ℕ) (i : ι) : ℝ :=
  if r = 0 then 0 else if r = R.card then 1 else sequentialThreshold w R r i

@[simp] theorem quotaThreshold_zero (w : ι → ℝ) (R : Finset ι) (i : ι) :
    quotaThreshold w R 0 i = 0 := by simp [quotaThreshold]

theorem sequentialThreshold_full (w : ι → ℝ) (hw : ∀ i, 0 < w i)
    (R : Finset ι) (i : ι) (hi : i ∈ R) : sequentialThreshold w R R.card i = 1 := by
  have hp : 0 < R.card := Finset.card_pos.mpr ⟨i, hi⟩
  have h := one_sub_sequentialThreshold w hw R R.card hp (le_refl _) i hi
  rw [restrictedElementary_eq_zero_of_card_lt w (R.erase i) R.card
    (by rw [Finset.card_erase_of_mem hi]; omega), zero_div] at h
  linarith

theorem quotaThreshold_eq_sequentialThreshold (w : ι → ℝ) (hw : ∀ i, 0 < w i)
    (R : Finset ι) (r : ℕ) (hr : 0 < r) (hR : r ≤ R.card) (i : ι) (hi : i ∈ R) :
    quotaThreshold w R r i = sequentialThreshold w R r i := by
  unfold quotaThreshold
  rw [if_neg (by omega)]
  split_ifs with h
  · subst r
    exact (sequentialThreshold_full w hw R i hi).symm
  · rfl

theorem restrictedElementary_delete_with_predecessor (w : ι → ℝ) (R : Finset ι)
    (r : ℕ) (i : ι) (hi : i ∈ R) :
    restrictedElementary w R r = restrictedElementary w (R.erase i) r +
      w i * elementaryPredecessor w (R.erase i) r := by
  cases r with
  | zero => simp
  | succ r =>
    simpa [elementaryPredecessor] using restrictedElementary_delete w R i hi (r + 1) (by omega)

theorem quotaThreshold_quotient (w : ι → ℝ) (hw : ∀ i, 0 < w i)
    (R : Finset ι) (r : ℕ) (hr : r ≤ R.card) (i : ι) (hi : i ∈ R) :
    quotaThreshold w R r i =
      w i * elementaryPredecessor w (R.erase i) r /
        (restrictedElementary w (R.erase i) r + w i * elementaryPredecessor w (R.erase i) r) := by
  cases r with
  | zero => simp
  | succ r =>
    rw [quotaThreshold_eq_sequentialThreshold w hw R (r + 1) (by omega) hr i hi]
    unfold sequentialThreshold
    rw [restrictedElementary_delete_with_predecessor w R (r + 1) i hi]
    simp

/-- The displayed difference formula, valid at r=0 and r=|R|-1, including |R|=1. -/
theorem quotaThreshold_succ_sub (w : ι → ℝ) (hw : ∀ i, 0 < w i)
    (R : Finset ι) (r : ℕ) (hr : r < R.card) (i : ι) (hi : i ∈ R) :
    quotaThreshold w R (r + 1) i - quotaThreshold w R r i =
      w i * (restrictedElementary w (R.erase i) r ^ 2 -
        elementaryPredecessor w (R.erase i) r * restrictedElementary w (R.erase i) (r + 1)) /
      ((restrictedElementary w (R.erase i) (r + 1) + w i * restrictedElementary w (R.erase i) r) *
       (restrictedElementary w (R.erase i) r + w i * elementaryPredecessor w (R.erase i) r)) := by
  have hden0 : 0 < restrictedElementary w (R.erase i) r +
      w i * elementaryPredecessor w (R.erase i) r := by
    rw [← restrictedElementary_delete_with_predecessor w R r i hi]
    exact restrictedElementary_pos w hw R r hr.le
  have hden1 : 0 < restrictedElementary w (R.erase i) (r + 1) +
      w i * restrictedElementary w (R.erase i) r := by
    rw [← elementaryPredecessor_succ w (R.erase i) r,
      ← restrictedElementary_delete_with_predecessor w R (r + 1) i hi]
    exact restrictedElementary_pos w hw R (r + 1) (by omega)
  rw [quotaThreshold_quotient w hw R (r + 1) (by omega) i hi,
    quotaThreshold_quotient w hw R r hr.le i hi, elementaryPredecessor_succ]
  field_simp [hden0.ne', hden1.ne']
  <;> ring

theorem quotaThreshold_le_succ (w : ι → ℝ) (hw : ∀ i, 0 < w i)
    (R : Finset ι) (r : ℕ) (hr : r < R.card) (i : ι) (hi : i ∈ R) :
    quotaThreshold w R r i ≤ quotaThreshold w R (r + 1) i := by
  apply sub_nonneg.mp
  rw [quotaThreshold_succ_sub w hw R r hr i hi]
  apply div_nonneg
  · apply mul_nonneg (hw i).le
    apply sub_nonneg.mpr
    apply restrictedElementary_turan w hw
    rw [Finset.card_erase_of_mem hi]
    omega
  · apply mul_nonneg
    · exact add_nonneg (restrictedElementary_nonneg w (fun i => (hw i).le) _ _)
        (mul_nonneg (hw i).le (restrictedElementary_nonneg w (fun i => (hw i).le) _ _))
    · rw [← restrictedElementary_delete_with_predecessor w R r i hi]
      exact (restrictedElementary_pos w hw R r hr.le).le

theorem quotaThreshold_mono (w : ι → ℝ) (hw : ∀ i, 0 < w i)
    (R : Finset ι) (r s : ℕ) (hrs : r ≤ s) (hs : s ≤ R.card) (i : ι) (hi : i ∈ R) :
    quotaThreshold w R r i ≤ quotaThreshold w R s i := by
  induction s generalizing r with
  | zero =>
    have hr : r = 0 := by omega
    subst r
    exact le_refl _
  | succ s ih =>
    by_cases heq : r = s + 1
    · subst r
      exact le_refl _
    · exact (ih r (by omega) (by omega)).trans
        (quotaThreshold_le_succ w hw R s (by omega) i hi)

end
end CoefficientOne.Sampling
