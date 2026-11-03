import CoefficientOne.Sampling.Variation

/-! # The first forced state and the stopped variation sum -/
open scoped BigOperators
open EffectiveResistance Matrix MeasureTheory
namespace CoefficientOne.Sampling
noncomputable section

def HistoryTerminal {n : ℕ} (w : Fin n → ℝ) (k ℓ : ℕ) (ω : Seed n) : Prop :=
  historyQuota w k ℓ ω = 0 ∨ historyQuota w k ℓ ω = (historyRemaining ℓ ω).card

instance historyTerminal_decidable {n : ℕ} (w : Fin n → ℝ) (k ℓ : ℕ) (ω : Seed n) :
    Decidable (HistoryTerminal w k ℓ ω) := by
  unfold HistoryTerminal
  infer_instance

theorem historyTerminal_last {n : ℕ} (w : Fin n → ℝ) (k : ℕ) (hk : k ≤ n) (ω : Seed n) :
    HistoryTerminal w k n ω := by
  have hR : historyRemaining n ω = ∅ := by simp [historyRemaining]
  have hq := historyQuota_le_remaining_card w k n hk ω
  rw [hR, Finset.card_empty] at hq
  exact Or.inl (Nat.eq_zero_of_le_zero hq)

theorem historyTerminal_succ {n : ℕ} (w : Fin n → ℝ) (k ℓ : ℕ) (hk : k ≤ n)
    (hℓ : ℓ < n) (ω : Seed n) (ht : HistoryTerminal w k ℓ ω) :
    HistoryTerminal w k (ℓ + 1) ω := by
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

theorem historyTerminal_mono {n : ℕ} (w : Fin n → ℝ) (k : ℕ) (hk : k ≤ n)
    (ω : Seed n) (t ℓ : ℕ) (htℓ : t ≤ ℓ) (hℓ : ℓ ≤ n)
    (ht : HistoryTerminal w k t ω) : HistoryTerminal w k ℓ ω := by
  induction ℓ, htℓ using Nat.le_induction with
  | base => exact ht
  | succ ℓ htℓ ih =>
    exact historyTerminal_succ w k ℓ hk (by omega) ω (ih (by omega))

def samplerTerminalTime {n : ℕ} (w : Fin n → ℝ) (k : ℕ) (hk : k ≤ n) (ω : Seed n) : ℕ :=
  Nat.find (show ∃ ℓ, HistoryTerminal w k ℓ ω from ⟨n, historyTerminal_last w k hk ω⟩)

theorem samplerTerminalTime_terminal {n : ℕ} (w : Fin n → ℝ) (k : ℕ) (hk : k ≤ n) (ω : Seed n) :
    HistoryTerminal w k (samplerTerminalTime w k hk ω) ω := by
  unfold samplerTerminalTime
  exact Nat.find_spec (p := fun ℓ => HistoryTerminal w k ℓ ω)
    ⟨n, historyTerminal_last w k hk ω⟩

theorem samplerTerminalTime_le {n : ℕ} (w : Fin n → ℝ) (k : ℕ) (hk : k ≤ n) (ω : Seed n) :
    samplerTerminalTime w k hk ω ≤ n := Nat.find_min' _ (historyTerminal_last w k hk ω)

theorem samplerTerminalTime_le_iff {n : ℕ} (w : Fin n → ℝ) (k : ℕ) (hk : k ≤ n)
    (ω : Seed n) (ℓ : ℕ) (hℓ : ℓ ≤ n) :
    samplerTerminalTime w k hk ω ≤ ℓ ↔ HistoryTerminal w k ℓ ω := by
  constructor
  · intro h
    exact historyTerminal_mono w k hk ω _ ℓ h hℓ (samplerTerminalTime_terminal w k hk ω)
  · exact fun h => Nat.find_min' _ h

theorem stopped_sum_eq_full_sum {n : ℕ} (w : Fin n → ℝ) (k : ℕ) (hk : k ≤ n)
    (ω : Seed n) (f : ℕ → ℝ) (hf : ∀ ℓ < n, HistoryTerminal w k ℓ ω → f ℓ = 0) :
    (∑ ℓ ∈ Finset.range (samplerTerminalTime w k hk ω), f ℓ) = ∑ ℓ ∈ Finset.range n, f ℓ := by
  apply Finset.sum_subset (Finset.range_mono (samplerTerminalTime_le w k hk ω))
  intro ℓ hn ht
  have hℓ : ℓ < n := Finset.mem_range.mp hn
  have hT : samplerTerminalTime w k hk ω ≤ ℓ := Nat.le_of_not_gt (by simpa using ht)
  exact hf ℓ hℓ ((samplerTerminalTime_le_iff w k hk ω ℓ hℓ.le).mp hT)

/-- Exact equality with the stopped sum written in the manuscript. -/
theorem samplerVariation_eq_stopped {n : ℕ} (w : Fin n → ℝ) (hw : ∀ i, 0 < w i)
    (k : ℕ) (hk : k ≤ n) (a : Fin n → ℝ) :
    samplerVariation w k a = ∫ ω,
      ∑ ℓ ∈ Finset.range (samplerTerminalTime w k hk ω), variationContribution w k ℓ a ω ∂seedMeasure n := by
  unfold samplerVariation
  apply integral_congr_ae
  exact Filter.Eventually.of_forall fun ω =>
    (stopped_sum_eq_full_sum w k hk ω (fun ℓ => variationContribution w k ℓ a ω)
      (fun ℓ _ ht => variationContribution_terminal w hw k ℓ a ω ht)).symm

theorem sampler_cut_telescope_stopped {n : ℕ} (w : Fin n → ℝ) (hw : ∀ i, 0 < w i)
    (k : ℕ) (hk : k ≤ n) (a : Fin n → ℝ) (s : ℝ) :
    (∫ ω, ∑ ℓ ∈ Finset.range (samplerTerminalTime w k hk ω),
      samplerCutVariance w k ℓ a s ω / (historyRemaining ℓ ω).card ∂seedMeasure n) ≤
      quadraticForm (covarianceMatrix w k) (cutVector a s) := by
  have he (ω : Seed n) :
      (∑ ℓ ∈ Finset.range (samplerTerminalTime w k hk ω),
        samplerCutVariance w k ℓ a s ω / (historyRemaining ℓ ω).card) =
      ∑ ℓ ∈ Finset.range n, samplerCutVariance w k ℓ a s ω / (historyRemaining ℓ ω).card := by
    apply stopped_sum_eq_full_sum w k hk ω
    intro ℓ _ ht
    simp [samplerCutVariance, samplerCovariance_terminal w hw k ℓ ω ht, quadraticForm]
  simp_rw [he]
  exact sampler_variance_telescope w hw k hk (cutVector a s)

end
end CoefficientOne.Sampling
