import CoefficientOne.Sampling.VariationDefinition
import CoefficientOne.Sampling.PrefixIntegration
import CoefficientOne.Sampling.ResidualVarianceDrop

/-! # The actual one-step update of the revealed state -/
open scoped BigOperators
open EffectiveResistance Matrix MeasureTheory
namespace CoefficientOne.Sampling
noncomputable section

theorem historyRemaining_succ {n : ℕ} (ℓ : ℕ) (hℓ : ℓ < n) (ω : Seed n) :
    historyRemaining (ℓ + 1) ω = (historyRemaining ℓ ω).erase (ω.1 ⟨ℓ, hℓ⟩) := by
  have ho : (List.ofFn ω.1).drop ℓ =
      ω.1 ⟨ℓ, hℓ⟩ :: (List.ofFn ω.1).drop (ℓ + 1) := by
    rw [List.drop_eq_getElem_cons (l := List.ofFn ω.1) (i := ℓ) (by simpa using hℓ),
      List.getElem_ofFn]
  have hn := nodup_drop (List.ofFn ω.1) (List.nodup_ofFn.mpr ω.1.injective) ℓ
  rw [ho] at hn
  have hi : ω.1 ⟨ℓ, hℓ⟩ ∉ ((List.ofFn ω.1).drop (ℓ + 1)).toFinset := by
    simpa using (List.nodup_cons.mp hn).1
  simp only [historyRemaining, ho, List.toFinset_cons, Finset.erase_insert hi]

theorem nextIndex_mem_historyRemaining {n : ℕ} (ℓ : ℕ) (hℓ : ℓ < n) (ω : Seed n) :
    ω.1 ⟨ℓ, hℓ⟩ ∈ historyRemaining ℓ ω := by
  rw [historyRemaining, permutation_drop_toFinset]
  simp [remainingSet, Revealed]

theorem nextIndex_notMem_revealed {n : ℕ} (ℓ : ℕ) (hℓ : ℓ < n) (ω : Seed n) :
    ω.1 ⟨ℓ, hℓ⟩ ∉ ((List.ofFn ω.1).take ℓ).toFinset := by
  simpa only [List.mem_toFinset, mem_permutation_take_iff, Revealed, Equiv.symm_apply_apply]
    using (Nat.lt_irrefl ℓ)

theorem revealedSet_succ {n : ℕ} (ℓ : ℕ) (hℓ : ℓ < n) (ω : Seed n) :
    ((List.ofFn ω.1).take (ℓ + 1)).toFinset =
      insert (ω.1 ⟨ℓ, hℓ⟩) ((List.ofFn ω.1).take ℓ).toFinset := by
  rw [List.take_succ_eq_append_getElem (by simpa using hℓ), List.getElem_ofFn]
  simp [Finset.union_comm]

theorem historySelected_succ {n : ℕ} (w : Fin n → ℝ) (k ℓ : ℕ) (hℓ : ℓ < n) (ω : Seed n) :
    historySelected w k (ℓ + 1) ω =
      if ω.1 ⟨ℓ, hℓ⟩ ∈ sequentialSampler w k ω then
        insert (ω.1 ⟨ℓ, hℓ⟩) (historySelected w k ℓ ω)
      else historySelected w k ℓ ω := by
  simp only [historySelected_eq_output_inter, revealedSet_succ ℓ hℓ ω]
  by_cases hi : ω.1 ⟨ℓ, hℓ⟩ ∈ sequentialSampler w k ω
  · rw [if_pos hi, Finset.inter_insert_of_mem hi]
  · rw [if_neg hi, Finset.inter_insert_of_notMem hi]

theorem historyQuota_succ {n : ℕ} (w : Fin n → ℝ) (k ℓ : ℕ) (hℓ : ℓ < n) (ω : Seed n) :
    historyQuota w k (ℓ + 1) ω =
      if ω.1 ⟨ℓ, hℓ⟩ ∈ sequentialSampler w k ω then historyQuota w k ℓ ω - 1
      else historyQuota w k ℓ ω := by
  have hi : ω.1 ⟨ℓ, hℓ⟩ ∉ historySelected w k ℓ ω := by
    rw [historySelected_eq_output_inter]
    exact fun h => nextIndex_notMem_revealed ℓ hℓ ω (Finset.mem_inter.mp h).2
  unfold historyQuota
  rw [historySelected_succ w k ℓ hℓ ω]
  split_ifs
  · rw [Finset.card_insert_of_notMem hi]
    omega
  · rfl

theorem samplerCovariance_next_forced {n : ℕ} (w : Fin n → ℝ) (hw : ∀ i, 0 < w i)
    (k ℓ : ℕ) (hk : k ≤ n) (hℓ : ℓ < n) (ω : Seed n)
    (ht : historyQuota w k ℓ ω = 0 ∨ historyQuota w k ℓ ω = (historyRemaining ℓ ω).card) :
    samplerCovariance w k (ℓ + 1) ω = 0 := by
  apply samplerCovariance_terminal w hw k (ℓ + 1) ω
  have hq := historyQuota_succ w k ℓ hℓ ω
  have hn := historyQuota_le_remaining_card w k (ℓ + 1) hk ω
  have hc : (historyRemaining (ℓ + 1) ω).card = (historyRemaining ℓ ω).card - 1 := by
    rw [historyRemaining_succ ℓ hℓ ω, Finset.card_erase_of_mem (nextIndex_mem_historyRemaining ℓ hℓ ω)]
  rcases ht with h0 | hf
  · left
    rw [h0] at hq
    split_ifs at hq <;> omega
  · right
    rw [hf] at hq
    split_ifs at hq <;> omega

theorem samplerHistoryState_on_historyEvent {n : ℕ} (w : Fin n → ℝ) (k ℓ : ℕ)
    (ρ : Equiv.Perm (Fin n)) (A : Finset (Fin n)) (ω : Seed n)
    (hω : ω ∈ historyEvent w k ℓ ρ A) :
    samplerHistoryState w k ℓ ω = (remainingSet ℓ ρ, k - A.card) := by
  rcases hω with ⟨hπ, hA⟩
  simp only [samplerHistoryState, historyRemaining, permutation_drop_toFinset,
    prefixMatches_remainingSet hπ, historyQuota, hA]

def actualNextDecision {n : ℕ} (w : Fin n → ℝ) (k ℓ : ℕ) (hℓ : ℓ < n)
    (ω : Seed n) : Fin n × Bool :=
  (ω.1 ⟨ℓ, hℓ⟩, decide (ω.1 ⟨ℓ, hℓ⟩ ∈ sequentialSampler w k ω))

theorem measurable_actualNextDecision {n : ℕ} (w : Fin n → ℝ) (k ℓ : ℕ) (hℓ : ℓ < n) :
    Measurable (actualNextDecision w k ℓ hℓ) := by
  have hf : Measurable (fun z : Equiv.Perm (Fin n) × Finset (Fin n) =>
    (z.1 ⟨ℓ, hℓ⟩, decide (z.1 ⟨ℓ, hℓ⟩ ∈ z.2))) := measurable_of_finite _
  exact fun _ hs => measurable_samplerOrderOutput w k (hf hs)

theorem nextIndex_mem_output_iff_continuation {n : ℕ} (w : Fin n → ℝ)
    (k ℓ : ℕ) (hℓ : ℓ < n) (ω : Seed n) :
    ω.1 ⟨ℓ, hℓ⟩ ∈ sequentialSampler w k ω ↔
      ω.1 ⟨ℓ, hℓ⟩ ∈ historyContinuation w k ℓ ω := by
  have hi : ω.1 ⟨ℓ, hℓ⟩ ∉ historySelected w k ℓ ω := by
    rw [historySelected_eq_output_inter]
    exact fun h => nextIndex_notMem_revealed ℓ hℓ ω (Finset.mem_inter.mp h).2
  rw [sequentialSampler_eq_history_union_continuation w k ℓ ω]
  simp only [Finset.mem_union, hi, false_or, historyContinuation]

theorem actualNextDecision_assemble {n : ℕ} (w : Fin n → ℝ) (hw : ∀ i, 0 < w i)
    (k ℓ : ℕ) (hℓ : ℓ < n) (ρ : Equiv.Perm (Fin n)) (A : Finset (Fin n))
    (hr0 : 0 < k - A.card) (hrtop : k - A.card < (remainingSet ℓ ρ).card)
    (z : SplitPrefixSeed ℓ ρ) (hz : z.2.1 ∈ historyPastSection w k ℓ ρ A) :
    actualNextDecision w k ℓ hℓ (assemblePrefixSeed ℓ ρ z) =
      let b := nextRevealBit ℓ ρ ⟨⟨ℓ, hℓ⟩, Nat.lt_irrefl ℓ⟩
        (residualThreshold w hw ℓ ρ (k - A.card) hr0 hrtop) (z.1, z.2.2)
      (b.1.val, b.2) := by
  apply Prod.ext
  · rfl
  · apply Bool.eq_iff_iff.mpr
    change decide ((assemblePrefixSeed ℓ ρ z).1 ⟨ℓ, hℓ⟩ ∈
      sequentialSampler w k (assemblePrefixSeed ℓ ρ z)) = true ↔ _
    rw [decide_eq_true_eq, nextIndex_mem_output_iff_continuation w k ℓ hℓ,
      historyContinuation_assemble w k ℓ ρ A z hz]
    exact (nextRevealBit_selects_iff w hw ℓ hℓ ρ (k - A.card) hr0 hrtop (z.1, z.2.2)).symm

theorem samplerCovariance_succ_on_history {n : ℕ} (w : Fin n → ℝ) (k ℓ : ℕ)
    (hℓ : ℓ < n) (ρ : Equiv.Perm (Fin n)) (A : Finset (Fin n)) (ω : Seed n)
    (hω : ω ∈ historyEvent w k ℓ ρ A) :
    samplerCovariance w k (ℓ + 1) ω =
      residualCovariance w ((remainingSet ℓ ρ).erase (actualNextDecision w k ℓ hℓ ω).1)
        (if (actualNextDecision w k ℓ hℓ ω).2 then k - A.card - 1 else k - A.card) := by
  have hs := samplerHistoryState_on_historyEvent w k ℓ ρ A ω hω
  have hR : historyRemaining ℓ ω = remainingSet ℓ ρ := congrArg Prod.fst hs
  have hr : historyQuota w k ℓ ω = k - A.card := congrArg Prod.snd hs
  unfold samplerCovariance
  rw [historyRemaining_succ ℓ hℓ ω, historyQuota_succ w k ℓ hℓ ω, hR, hr]
  simp [actualNextDecision]

end
end CoefficientOne.Sampling
