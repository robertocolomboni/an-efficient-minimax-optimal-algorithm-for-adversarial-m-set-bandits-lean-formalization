import CoefficientOne.Sampling.PrefixObservableOperations

/-! # The first disagreement of two concrete samplers using the same seed -/

open MeasureTheory Set

namespace CoefficientOne.Sampling
noncomputable section

def firstDisagreement {n : ℕ} (w v : Fin n → ℝ) (k : ℕ) (ω : Seed n) : WithTop ℕ :=
  if h : ∃ ℓ, ℓ ≤ n ∧ historySelected w k ℓ ω ≠ historySelected v k ℓ ω
  then (Nat.find h : WithTop ℕ) else ⊤

theorem firstDisagreement_eq_coe_iff {n : ℕ} (w v : Fin n → ℝ) (k ℓ : ℕ) (ω : Seed n) :
    firstDisagreement w v k ω = (ℓ : WithTop ℕ) ↔
      ℓ ≤ n ∧ historySelected w k ℓ ω ≠ historySelected v k ℓ ω ∧
        ∀ j < ℓ, historySelected w k j ω = historySelected v k j ω := by
  classical
  unfold firstDisagreement
  split_ifs with hex
  · constructor
    · intro he0
      have he : Nat.find hex = ℓ := by exact_mod_cast he0
      have hs := Nat.find_spec hex
      refine ⟨he ▸ hs.1, he ▸ hs.2, ?_⟩
      intro j hj
      by_contra hne
      have hjn : j ≤ n := le_trans (Nat.le_of_lt hj) (he ▸ hs.1)
      have hmin := Nat.find_min hex (he ▸ hj)
      exact hmin ⟨hjn, hne⟩
    · rintro ⟨hℓn, hne, hprev⟩
      have he : Nat.find hex = ℓ := by
        apply le_antisymm (Nat.find_min' hex ⟨hℓn, hne⟩)
        by_contra hlt
        exact (Nat.find_spec hex).2 (hprev (Nat.find hex) (by omega))
      exact_mod_cast he
  · constructor
    · intro h
      exact False.elim (WithTop.top_ne_coe h)
    · rintro ⟨hℓn, hne, _⟩
      exact False.elim (hex ⟨ℓ, hℓn, hne⟩)

theorem firstDisagreement_eq_top_iff {n : ℕ} (w v : Fin n → ℝ) (k : ℕ) (ω : Seed n) :
    firstDisagreement w v k ω = ⊤ ↔
      ∀ ℓ ≤ n, historySelected w k ℓ ω = historySelected v k ℓ ω := by
  classical
  simp only [firstDisagreement]
  split_ifs with hex
  · constructor
    · intro h
      exact False.elim (WithTop.coe_ne_top h)
    · intro h
      obtain ⟨ℓ, hℓ, hne⟩ := hex
      exact False.elim (hne (h ℓ hℓ))
  · constructor
    · intro _ ℓ hℓ
      by_contra hne
      exact hex ⟨ℓ, hℓ, hne⟩
    · intro _
      rfl

theorem firstDisagreement_le_dimension {n : ℕ} (w v : Fin n → ℝ) (k : ℕ) (ω : Seed n)
    (h : firstDisagreement w v k ω ≠ ⊤) : firstDisagreement w v k ω ≤ (n : WithTop ℕ) := by
  obtain ⟨ℓ, hℓ⟩ := WithTop.ne_top_iff_exists.mp h
  have hs := (firstDisagreement_eq_coe_iff w v k ℓ ω).mp hℓ.symm
  rw [← hℓ]
  exact WithTop.coe_le_coe.mpr hs.1

theorem firstDisagreement_ne_zero {n : ℕ} (w v : Fin n → ℝ) (k : ℕ) (ω : Seed n) :
    firstDisagreement w v k ω ≠ 0 := by
  intro h
  have hs := (firstDisagreement_eq_coe_iff w v k 0 ω).mp h
  exact hs.2.1 (by simp [historySelected])

theorem historySelected_dimension {n : ℕ} (w : Fin n → ℝ) (k : ℕ) (ω : Seed n) :
    historySelected w k n ω = sequentialSampler w k ω := by
  rw [historySelected_eq_output_inter, List.take_of_length_le (by simp), permutation_order_toFinset]
  exact Finset.inter_univ _

theorem firstDisagreement_eq_top_iff_output_eq {n : ℕ} (w v : Fin n → ℝ) (k : ℕ) (ω : Seed n) :
    firstDisagreement w v k ω = ⊤ ↔ sequentialSampler w k ω = sequentialSampler v k ω := by
  rw [firstDisagreement_eq_top_iff]
  constructor
  · intro h
    simpa only [historySelected_dimension] using h n le_rfl
  · intro h ℓ _
    simp only [historySelected_eq_output_inter, h]

theorem firstDisagreement_fiber_prefixObservable {n : ℕ} (w v : Fin n → ℝ) (k ℓ : ℕ) :
    PrefixObservableEvent ℓ {ω | firstDisagreement w v k ω = (ℓ : WithTop ℕ)} := by
  classical
  by_cases hℓ : ℓ ≤ n
  · have hprev := PrefixObservableEvent.iInter (fun j : Fin ℓ =>
      (historyAgreement_prefixObservable w v k j.val).mono (Nat.le_of_lt j.isLt))
    have h := (historyDisagreement_prefixObservable w v k ℓ).inter hprev
    have he : {ω | firstDisagreement w v k ω = (ℓ : WithTop ℕ)} =
        {ω | historySelected w k ℓ ω ≠ historySelected v k ℓ ω} ∩
          ⋂ j : Fin ℓ, {ω | historySelected w k j.val ω = historySelected v k j.val ω} := by
      ext ω
      simp only [mem_setOf_eq, firstDisagreement_eq_coe_iff, hℓ, true_and,
        mem_inter_iff, mem_iInter]
      exact and_congr_right fun _ => ⟨fun h j => h j.val j.isLt, fun h j hj => h ⟨j, hj⟩⟩
    rwa [he]
  · have he : {ω : Seed n | firstDisagreement w v k ω = (ℓ : WithTop ℕ)} = ∅ := by
      ext ω
      simp [firstDisagreement_eq_coe_iff, hℓ]
    rw [he]
    exact prefixObservableEvent_empty n ℓ

theorem firstDisagreement_stoppingTime {n : ℕ} (w v : Fin n → ℝ) (k : ℕ) :
    StoppedObservableEvent (firstDisagreement w v k) Set.univ := by
  intro t
  simpa only [Set.univ_inter] using firstDisagreement_fiber_prefixObservable w v k t.val

theorem firstDisagreement_event_stoppedObservable {n : ℕ} (w v : Fin n → ℝ) (k : ℕ) :
    StoppedObservableEvent (firstDisagreement w v k) {ω | firstDisagreement w v k ω ≠ ⊤} := by
  intro t
  have he : {ω | firstDisagreement w v k ω ≠ ⊤} ∩
      {ω | firstDisagreement w v k ω = (t.val : WithTop ℕ)} =
      {ω | firstDisagreement w v k ω = (t.val : WithTop ℕ)} := by
    ext ω
    simp only [mem_inter_iff, mem_setOf_eq]
    exact ⟨fun h => h.2, fun h => ⟨h ▸ WithTop.coe_ne_top, h⟩⟩
  rw [he]
  exact firstDisagreement_fiber_prefixObservable w v k t.val

end
end CoefficientOne.Sampling
