import MsetsPaper.Probability.AmbientHistoryLaw
import MsetsPaper.Upper.Algorithm

/-! # Reusable ambient law of the concrete algorithm

This shared interface supports T1 and the individual upper lemmas. The
canonical law is derived from the stochastic protocol premises and the
feedback-only algorithmic choice rule.
-/

namespace MsetsPaper.Probability.AmbientHistory

open MeasureTheory ProbabilityTheory MsetsLower MsetsPaper.Upper

noncomputable section

variable {Ω : Type*} [MeasurableSpace Ω] {d m : ℕ}

theorem exists_mainAlgorithm_ambient_law
    (μ : Measure Ω) [IsProbabilityMeasure μ]
    (X : ℕ → Ω → Action d m) (ell : ℕ → Ω → Fin d → ℝ)
    (p : ℕ → Ω → Action d m → ℝ) (hmd : m ≤ d) (T : ℕ) (delta : ℝ)
    (hX : ∀ t < T, Measurable (X t))
    (hell : ∀ t < T, Measurable[historySigma X ell t] (ell t))
    (hp : ∀ t < T, Measurable[historySigma X ell t] (p t))
    (hnorm : ∀ t < T, ∀ᵐ ω ∂μ, ∀ a : Action d m, |actionLoss a (ell t ω)| ≤ 1)
    (halgorithm : ∀ t < T, ∀ᵐ ω ∂μ,
      p t ω = weightedLaw (m := m)
        (ellipsoidAlgorithmParameters
          (mainLearningRate d T (Nat.choose d m) delta) T t (history X ell t ω)))
    (hsample : letI : Nonempty (Action d m) := nonempty_MSetAction hmd
      ∀ t < T, ∀ᵐ ω ∂μ,
        condDistrib (X t) (history X ell t) μ (history X ell t ω) =
          finiteAtomicMeasure (p t ω) id) :
    ∃ L : SignedLossProcess d m,
      (∀ t < T, ∀ᵐ ω ∂μ, L.itemLoss t (history X ell t ω) = ell t ω) ∧
      ∀ t ≤ T, μ.map (history X ell t) = signedRunLaw (mainAlgorithm T delta hmd) L t := by
  letI : Nonempty (Action d m) := nonempty_MSetAction hmd
  have hvalid : ∀ t < T, ∀ᵐ ω ∂μ, IsDistribution (p t ω) := by
    intro t ht
    filter_upwards [halgorithm t ht] with ω hω
    rw [hω]
    exact ⟨fun a ↦ (weightedLaw_pos _ hmd a).le, sum_weightedLaw _ hmd⟩
  obtain ⟨P, L, hP, hL, hlaw⟩ := exists_canonical_protocol μ hmd X ell p T
    hX hell hp hnorm hvalid hsample
  have hH := measurable_history_upto X ell T hX hell
  have hsame : ∀ t < T, ∀ᵐ ω ∂μ,
      P.kernel t (history X ell t ω) = (mainAlgorithm T delta hmd).kernel t (history X ell t ω) := by
    intro t ht
    filter_upwards [hP t ht, halgorithm t ht] with ω hq ha
    rw [hq, ha]
    rfl
  exact ⟨L, hL, history_law_change_policy μ X ell T hH P
    (mainAlgorithm T delta hmd) L hlaw hsame⟩

end
end MsetsPaper.Probability.AmbientHistory
