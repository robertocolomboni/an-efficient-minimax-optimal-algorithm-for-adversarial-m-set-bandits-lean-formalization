import MsetsPaper.Alignment.LowerDefinitive
import MsetsPaper.Lower.OrdinaryTransport

/-! # C1 on the native `Fin K` bandit protocol

These interfaces preserve the constants and horizon of the definitive
manuscript.  The proof specializes the verified T2/T3 at m=1 and transports
the whole interaction law and regret, not merely the action-level formula.
-/

namespace MsetsPaper.Alignment.OrdinaryDefinitive

open MsetsPaper.Lower MeasureTheory Set

noncomputable section

theorem corollary_ordinary_bandits_explicit {K T : ℕ} (hK : 2 ≤ K)
    {δ : ℝ} (hδ : 0 < δ) (hsmall : δ ≤ (2 : ℝ) ^ (-36 : ℤ))
    (hT : Nat.ceil (64 * (K : ℝ) ^ 2 + 4 * (K : ℝ) * Real.log (1 / δ)) ≤ T) :
    ∀ P : Ordinary.Policy K, ∃ L : Ordinary.LossProcess K,
      (∀ t (h : Ordinary.History K t) i, L.loss t h i ∈ Icc (0 : ℝ) 1) ∧
      δ ≤ (Ordinary.runLaw P L T).real
        {h | (2 : ℝ) ^ (-43 : ℤ) * Real.sqrt ((K : ℝ) * T *
          (Real.log (K : ℝ) + Real.log (1 / δ))) ≤ Ordinary.pathRegret L T h} := by
  intro P
  obtain ⟨G, _hG, htail⟩ := LowerDefinitive.corollary_ordinary_bandits_explicit
    hK hδ hsmall hT (Ordinary.toMsetPolicy P)
  refine ⟨Ordinary.fromMsetLoss G, (Ordinary.fromMsetLoss G).loss_mem_Icc, ?_⟩
  rw [Ordinary.regret_tail_transport (by omega)]
  exact htail

/-- Literal ordinary-arm C1, with the same chosen horizon τ(K,1,δ) as T2. -/
theorem corollary_ordinary_bandits :
    ∃ (c δ₀ : ℝ) (τ : ℕ → ℝ → ℕ),
      0 < c ∧ δ₀ ∈ Ioo (0 : ℝ) 1 ∧
      (∀ K δ, τ K δ = NewRoute.horizon K 1 δ) ∧
      (∀ K δ, 2 ≤ K → 0 < δ → δ ≤ δ₀ →
        (τ K δ : ℝ) ≤ 1 + 64 * (K : ℝ) ^ 2 + 4 * (K : ℝ) * Real.log (1 / δ)) ∧
      (∀ K T δ, 2 ≤ K → 0 < δ → δ ≤ δ₀ → τ K δ ≤ T →
        ∀ P : Ordinary.Policy K, ∃ L : Ordinary.LossProcess K,
          (∀ t (h : Ordinary.History K t) i, L.loss t h i ∈ Icc (0 : ℝ) 1) ∧
          δ ≤ (Ordinary.runLaw P L T).real {h | c * Real.sqrt ((K : ℝ) * T *
            (Real.log (K : ℝ) + Real.log (1 / δ))) ≤ Ordinary.pathRegret L T h}) := by
  obtain ⟨c, δ₀, τ, hc, hδ₀, hτ, hpoly, hmain⟩ :=
    LowerDefinitive.corollary_ordinary_bandits
  refine ⟨c, δ₀, τ, hc, hδ₀, hτ, hpoly, ?_⟩
  intro K T δ hK hδ hsmall hT P
  obtain ⟨G, _hG, htail⟩ := hmain K T δ hK hδ hsmall hT (Ordinary.toMsetPolicy P)
  refine ⟨Ordinary.fromMsetLoss G, (Ordinary.fromMsetLoss G).loss_mem_Icc, ?_⟩
  rw [Ordinary.regret_tail_transport (by omega)]
  exact htail

end
end MsetsPaper.Alignment.OrdinaryDefinitive
