import MsetsLower.Lower.Confidence.EventAverage
import MsetsLower.Lower.Confidence.Stopping
import MsetsLower.Probability.Selection

/-!
# Selecting the planted confidence candidate

This module formalizes `eq:lower-confidence-selected-candidate`.  It combines
the averaged event probability with the pathwise active-pull accounting and
the already certified simultaneous selection lemma.
-/

namespace MsetsLower.Lower.Confidence

open MsetsLower MeasureTheory Set
open scoped BigOperators

noncomputable section

theorem activeSelectedCount_nonneg
    {n k : Nat} (hkn : k ≤ n) (B : Real) (i : Fin n) :
    ∀ (t : Nat) (h : History n k t), 0 ≤ activeSelectedCount hkn B i t h := by
  intro t
  induction t with
  | zero => intro h; simp
  | succ t ih =>
      intro h
      rw [activeSelectedCount_succ]
      exact add_nonneg (ih h.1)
        (mul_nonneg (activeIndicator_mem_Icc hkn B t h.1).1
          (History.selectedIndicator_mem_Icc i h.2.1).1)

theorem activeSelectedCount_le_time
    {n k : Nat} (hkn : k ≤ n) (B : Real) (i : Fin n) :
    ∀ (t : Nat) (h : History n k t),
      activeSelectedCount hkn B i t h ≤ t := by
  intro t
  induction t with
  | zero => intro h; simp
  | succ t ih =>
      intro h
      rw [activeSelectedCount_succ]
      have hactive := activeIndicator_mem_Icc hkn B t h.1
      have hselected := History.selectedIndicator_mem_Icc i h.2.1
      have hincrement :
          activeIndicator hkn B t h.1 * History.selectedIndicator i h.2.1 ≤ 1 := by
        calc
          activeIndicator hkn B t h.1 * History.selectedIndicator i h.2.1 ≤
              1 * History.selectedIndicator i h.2.1 :=
            mul_le_mul_of_nonneg_right hactive.2 hselected.1
          _ ≤ 1 := by simpa using hselected.2
      have hprev := ih h.1
      push_cast
      linarith

theorem integrable_activeSelectedCount
    {n k t : Nat} (P : Measure (History n k t)) [IsFiniteMeasure P]
    (hkn : k ≤ n) (B : Real) (i : Fin n) :
    Integrable (activeSelectedCount hkn B i t) P := by
  apply Integrable.of_bound
    (measurable_activeSelectedCount hkn B i t).aestronglyMeasurable (t : Real)
  apply ae_of_all
  intro h
  rw [Real.norm_eq_abs, abs_of_nonneg (activeSelectedCount_nonneg hkn B i t h)]
  exact activeSelectedCount_le_time hkn B i t h

/-- Integrating `eq:lower-confidence-total-pulls` gives the exact total
expectation budget used by the selection lemma. -/
theorem sum_expected_activeSelectedCount_le
    {n k T : Nat} (hk : 1 ≤ k) (hkn : k ≤ n)
    {B : Real} (hB : 0 ≤ B)
    (P : Measure (History n k T)) [IsProbabilityMeasure P] :
    ∑ i ∈ confidenceCandidates n k hkn,
        ∫ h, activeSelectedCount hkn B i T h ∂P ≤
      (T : Real) + 8 * (k : Real) * B + (k : Real) := by
  let total : History n k T → Real := fun h =>
    ∑ i ∈ confidenceCandidates n k hkn,
      activeSelectedCount hkn B i T h
  have htotal_integrable : Integrable total P := by
    dsimp [total]
    exact integrable_finsetSum _ fun i _ =>
      integrable_activeSelectedCount P hkn B i
  have hconstant_integrable : Integrable
      (fun _h : History n k T =>
        (T : Real) + 8 * (k : Real) * B + (k : Real)) P :=
    integrable_const _
  have hmono : (∫ h, total h ∂P) ≤
      ∫ _h : History n k T,
        ((T : Real) + 8 * (k : Real) * B + (k : Real)) ∂P := by
    apply integral_mono htotal_integrable hconstant_integrable
    intro h
    exact lower_confidence_total_pulls hk hkn hB h
  rw [show (∫ h, total h ∂P) =
      ∑ i ∈ confidenceCandidates n k hkn,
        ∫ h, activeSelectedCount hkn B i T h ∂P by
      dsimp [total]
      exact integral_finsetSum _ fun i _ =>
        integrable_activeSelectedCount P hkn B i] at hmono
  simpa using hmono

/-- Equation `eq:lower-confidence-selected-candidate`. -/
theorem lower_confidence_selected_candidate
    {n k T : Nat} (hk : 1 ≤ k) (hkn : k ≤ n)
    (hN : 2 ≤ (confidenceCandidates n k hkn).card)
    (noise : Nat → Real) (Delta : Real) {B : Real} (hB : 0 ≤ B)
    (P : Measure (History n k T)) [IsProbabilityMeasure P]
    (hprob_average : (1 : Real) / 8 ≤
      (∑ i ∈ confidenceCandidates n k hkn,
        P.real (confidenceScoreEvent hkn noise Delta B i)) /
          (confidenceCandidates n k hkn).card) :
    ∃ i ∈ confidenceCandidates n k hkn,
      (1 : Real) / 16 ≤
          P.real (confidenceScoreEvent hkn noise Delta B i) ∧
      (∫ h, activeSelectedCount hkn B i T h ∂P) ≤
        (16 / (confidenceCandidates n k hkn).card : Real) *
          ((T : Real) + 8 * (k : Real) * B + (k : Real)) := by
  let candidates := confidenceCandidates n k hkn
  let events : Fin n → Set (History n k T) :=
    fun i => confidenceScoreEvent hkn noise Delta B i
  let pulls : Fin n → History n k T → Real :=
    fun i => activeSelectedCount hkn B i T
  let budget : Real := (T : Real) + 8 * (k : Real) * B + (k : Real)
  have hcandidates : candidates.Nonempty := by
    exact Finset.card_pos.mp (lt_of_lt_of_le (by omega : 0 < 2) hN)
  have hNpos : (0 : Real) < candidates.card := by
    exact_mod_cast hcandidates.card_pos
  have hprob_sum : (candidates.card : Real) * ((1 : Real) / 8) ≤
      ∑ i ∈ candidates, P.real (events i) := by
    have hscaled := (le_div_iff₀ hNpos).mp
      (show (1 : Real) / 8 ≤
          (∑ i ∈ candidates, P.real (events i)) / candidates.card by
        simpa [candidates, events] using hprob_average)
    simpa [mul_comm] using hscaled
  have hpulls_sum :
      ∑ i ∈ candidates, ∫ h, pulls i h ∂P ≤
        (candidates.card : Real) * (budget / candidates.card) := by
    have hraw := sum_expected_activeSelectedCount_le hk hkn hB P
    have hbudget : budget =
        (T : Real) + 8 * (k : Real) * B + (k : Real) := rfl
    rw [show (candidates.card : Real) * (budget / candidates.card) = budget by
      field_simp]
    simpa [candidates, pulls, hbudget] using hraw
  obtain ⟨i, hi, hiprob, hipulls⟩ :=
    Probability.select_good_index_finset P candidates hcandidates events pulls
      (fun i hi => measurableSet_confidenceScoreEvent hkn noise Delta B i)
      (fun i hi => ae_of_all P fun h => activeSelectedCount_nonneg hkn B i T h)
      (p := (1 : Real) / 8) (w := budget / candidates.card)
      (by norm_num) (by norm_num) hprob_sum hpulls_sum
  refine ⟨i, ?_, ?_, ?_⟩
  · simpa [candidates] using hi
  · norm_num at hiprob ⊢
    exact hiprob
  · dsimp [candidates, pulls, budget] at hipulls ⊢
    norm_num [div_eq_mul_inv] at hipulls ⊢
    ring_nf at hipulls ⊢
    exact hipulls

end

end MsetsLower.Lower.Confidence

#print axioms MsetsLower.Lower.Confidence.sum_expected_activeSelectedCount_le
#print axioms MsetsLower.Lower.Confidence.lower_confidence_selected_candidate
