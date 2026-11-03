import CoefficientOne.Sampling.SequentialHistory

/-! # Boolean operations and monotonicity of the revealed-prefix sigma-algebra -/

open MeasureTheory Set

namespace CoefficientOne.Sampling
noncomputable section

theorem PrefixObservableEvent.compl {n ℓ : ℕ} {E : Set (Seed n)}
    (hE : PrefixObservableEvent ℓ E) : PrefixObservableEvent ℓ Eᶜ := by
  intro ρ
  obtain ⟨B, hB, hBE⟩ := hE ρ
  exact ⟨Bᶜ, hB.compl, fun ω hω => not_congr (hBE ω hω)⟩

theorem PrefixObservableEvent.union {n ℓ : ℕ} {E F : Set (Seed n)}
    (hE : PrefixObservableEvent ℓ E) (hF : PrefixObservableEvent ℓ F) :
    PrefixObservableEvent ℓ (E ∪ F) := by
  intro ρ
  obtain ⟨B, hB, hBE⟩ := hE ρ
  obtain ⟨C, hC, hCF⟩ := hF ρ
  exact ⟨B ∪ C, hB.union hC, fun ω hω => or_congr (hBE ω hω) (hCF ω hω)⟩

theorem prefixObservableEvent_empty (n ℓ : ℕ) :
    PrefixObservableEvent ℓ (∅ : Set (Seed n)) := by
  simpa using (prefixObservableEvent_univ n ℓ).compl

theorem PrefixObservableEvent.iUnion {n ℓ : ℕ} {α : Type*} [Countable α]
    {E : α → Set (Seed n)} (hE : ∀ a, PrefixObservableEvent ℓ (E a)) :
    PrefixObservableEvent ℓ (⋃ a, E a) := by
  intro ρ
  refine ⟨⋃ a, prefixPastSection (hE a) ρ,
    MeasurableSet.iUnion (fun a => measurableSet_prefixPastSection (hE a) ρ), ?_⟩
  intro ω hω
  simp only [mem_iUnion]
  exact exists_congr fun a => prefixPastSection_spec (hE a) ρ ω hω

theorem PrefixObservableEvent.iInter {n ℓ : ℕ} {α : Type*} [Countable α]
    {E : α → Set (Seed n)} (hE : ∀ a, PrefixObservableEvent ℓ (E a)) :
    PrefixObservableEvent ℓ (⋂ a, E a) := by
  intro ρ
  refine ⟨⋂ a, prefixPastSection (hE a) ρ,
    MeasurableSet.iInter (fun a => measurableSet_prefixPastSection (hE a) ρ), ?_⟩
  intro ω hω
  simp only [mem_iInter]
  exact forall_congr' fun a => prefixPastSection_spec (hE a) ρ ω hω

def restrictPastUniforms {n ℓ m : ℕ} (hℓm : ℓ ≤ m) (ρ : Equiv.Perm (Fin n)) :
    PastUniforms m ρ → PastUniforms ℓ ρ :=
  fun v i => v ⟨i.val, lt_of_lt_of_le i.property hℓm⟩

theorem measurable_restrictPastUniforms {n ℓ m : ℕ} (hℓm : ℓ ≤ m)
    (ρ : Equiv.Perm (Fin n)) : Measurable (restrictPastUniforms hℓm ρ) := by
  exact measurable_pi_iff.mpr fun i => measurable_pi_apply _

theorem PrefixObservableEvent.mono {n ℓ m : ℕ} {E : Set (Seed n)}
    (hE : PrefixObservableEvent ℓ E) (hℓm : ℓ ≤ m) : PrefixObservableEvent m E := by
  intro ρ
  obtain ⟨B, hB, hBE⟩ := hE ρ
  refine ⟨restrictPastUniforms hℓm ρ ⁻¹' B,
    hB.preimage (measurable_restrictPastUniforms hℓm ρ), ?_⟩
  intro ω hω
  have hsmall : PrefixMatches ℓ ρ ω.1 := fun j hj => hω j (lt_of_lt_of_le hj hℓm)
  exact hBE ω hsmall

theorem historyAgreement_prefixObservable {n : ℕ} (w v : Fin n → ℝ) (k ℓ : ℕ) :
    PrefixObservableEvent ℓ {ω | historySelected w k ℓ ω = historySelected v k ℓ ω} := by
  have h := PrefixObservableEvent.iUnion (fun A : Finset (Fin n) =>
    (historySelected_prefixObservable w k ℓ A).inter (historySelected_prefixObservable v k ℓ A))
  have he : (⋃ A : Finset (Fin n),
      {ω | historySelected w k ℓ ω = A} ∩ {ω | historySelected v k ℓ ω = A}) =
      {ω | historySelected w k ℓ ω = historySelected v k ℓ ω} := by
    ext ω
    simp only [mem_iUnion, mem_inter_iff, mem_setOf_eq]
    constructor
    · rintro ⟨A, hA, hB⟩
      exact hA.trans hB.symm
    · intro h
      exact ⟨historySelected v k ℓ ω, h, rfl⟩
  rwa [he] at h

theorem historyDisagreement_prefixObservable {n : ℕ} (w v : Fin n → ℝ) (k ℓ : ℕ) :
    PrefixObservableEvent ℓ {ω | historySelected w k ℓ ω ≠ historySelected v k ℓ ω} :=
  (historyAgreement_prefixObservable w v k ℓ).compl

end
end CoefficientOne.Sampling
