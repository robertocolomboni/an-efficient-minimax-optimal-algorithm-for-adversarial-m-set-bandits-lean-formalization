import CoefficientOne.Sampling.JointHistoryMeasurability

/-! Explicit nonterminal-state properties of the first terminal time. -/
namespace CoefficientOne.Sampling
noncomputable section

theorem samplerTerminalTime_before_nonterminal {n : ℕ} (w : Fin n → ℝ)
    (k : ℕ) (hk : k ≤ n) (ω : Seed n) (ℓ : ℕ)
    (hℓ : ℓ < samplerTerminalTime w k hk ω) :
    0 < historyQuota w k ℓ ω ∧
      historyQuota w k ℓ ω < (historyRemaining ℓ ω).card ∧
      2 ≤ (historyRemaining ℓ ω).card := by
  have hT := samplerTerminalTime_le w k hk ω
  have hq := historyQuota_le_remaining_card w k ℓ hk ω
  have hnt : ¬ HistoryTerminal w k ℓ ω := by
    intro ht
    have he := (samplerTerminalTime_le_iff w k hk ω ℓ (by omega)).mpr ht
    omega
  unfold HistoryTerminal at hnt
  omega

end
end CoefficientOne.Sampling
