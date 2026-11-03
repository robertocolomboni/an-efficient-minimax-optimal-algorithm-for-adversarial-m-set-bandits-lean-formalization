import MsetsPaper.Alignment.UpperAmbientOMD

/-! Simultaneous pathwise L4. One reconstruction event, independent of q,
supports all comparator distributions. No uncountable intersection of
almost-sure statements is taken. -/

namespace MsetsPaper.Alignment

open MeasureTheory ProbabilityTheory MsetsLower MsetsPaper.Upper
open MsetsPaper.Probability MsetsPaper.Probability.AmbientHistory
open scoped BigOperators

noncomputable section
variable {Ω : Type*} [MeasurableSpace Ω] {d m : ℕ}

theorem upper_omd_stability_observable_uniform
    (L : SignedLossProcess d m) (hmpos : 1 ≤ m) (hmtop : m ≤ d - 1)
    (T : ℕ) (hT : 0 < T) {delta : ℝ} (hdelta0 : 0 < delta) (hdelta1 : delta < 1) :
    let eta := mainLearningRate d T (Nat.choose d m) delta
    let theta := ellipsoidAlgorithmParameters (d := d) (m := m) eta T
    ∀ᵐ h ∂signedRunLaw (mainAlgorithm T delta (by omega)) L T,
      ∀ q : Action d m → ℝ, (∀ a, 0 ≤ q a) → (∑ a, q a = 1) →
      (∀ i, 128 * eta * d * ((m : ℝ) / d) ≤ marginal q i ∧
        marginal q i ≤ 1 - 128 * eta * d * (1 - (m : ℝ) / d)) →
      observablePathSum (observableSurrogateDifference theta L eta q) T h ≤
        (paperKL q (weightedLaw (m := m) (0 : Fin d → ℝ))).toReal / eta + 1 +
          2 * eta * observablePathSum (observableSurrogateSecondMoment theta L eta) T h := by
  let eta := mainLearningRate d T (Nat.choose d m) delta
  let theta := ellipsoidAlgorithmParameters (d := d) (m := m) eta T
  have hreconstruct := signedRunLaw_ae_history_reconstruction theta
    (measurable_ellipsoidAlgorithmParameters eta T) (show m ≤ d by omega) L T
  filter_upwards [hreconstruct] with h hh
  intro q hq hqsum hqbox
  have hb := upper_omd_stability L hmpos hmtop T hT hdelta0 hdelta1
    q hq hqsum hqbox (actionsOfHistory T h)
  change observablePathSum (observableSurrogateDifference theta L eta q) T h ≤ _
  rw [paperKL_toReal q _ hq hqsum (weightedLaw_pos _ (by omega))
    (sum_weightedLaw _ (by omega))]
  rw [← hh]
  simp only [observablePathSum_historyOfActions]
  exact hb

/-- A single ambient probability-one event supports L4 for every admissible
q simultaneously. The event is independent of q, even though q ranges over
an uncountable simplex. -/
theorem upper_omd_stability_ambient_uniform
    (μ : Measure Ω) [IsProbabilityMeasure μ]
    (X : ℕ → Ω → Action d m) (ell : ℕ → Ω → Fin d → ℝ)
    (p : ℕ → Ω → Action d m → ℝ)
    (hmpos : 1 ≤ m) (hmtop : m ≤ d - 1) (T : ℕ) (hT : 0 < T)
    {delta : ℝ} (hdelta0 : 0 < delta) (hdelta1 : delta < 1)
    (hX : ∀ t < T, Measurable (X t))
    (hell : ∀ t < T, Measurable[historySigma X ell t] (ell t))
    (hp : ∀ t < T, Measurable[historySigma X ell t] (p t))
    (hnorm : ∀ t < T, ∀ᵐ ω ∂μ, ∀ a : Action d m, |actionLoss a (ell t ω)| ≤ 1)
    (halgorithm : ∀ t < T, ∀ᵐ ω ∂μ,
      p t ω = weightedLaw (m := m) (ellipsoidAlgorithmParameters
        (mainLearningRate d T (Nat.choose d m) delta) T t (history X ell t ω)))
    (hsample : letI : Nonempty (Action d m) := nonempty_MSetAction (show m ≤ d by omega)
      ∀ t < T, ∀ᵐ ω ∂μ,
        condDistrib (X t) (history X ell t) μ (history X ell t ω) =
          finiteAtomicMeasure (p t ω) id) :
    let eta := mainLearningRate d T (Nat.choose d m) delta
    ∀ᵐ ω ∂μ, ∀ q : Action d m → ℝ, (∀ a, 0 ≤ q a) → (∑ a, q a = 1) →
      (∀ i, 128 * eta * d * ((m : ℝ) / d) ≤ marginal q i ∧
        marginal q i ≤ 1 - 128 * eta * d * (1 - (m : ℝ) / d)) →
      ambientSurrogateDifference X ell p eta T q ω ≤
        (paperKL q (weightedLaw (m := m) (0 : Fin d → ℝ))).toReal / eta + 1 +
          2 * eta * ambientSurrogateSecondMoment X ell p eta T ω := by
  have hmd : m ≤ d := by omega
  letI : Nonempty (Action d m) := nonempty_MSetAction hmd
  let eta := mainLearningRate d T (Nat.choose d m) delta
  let theta := ellipsoidAlgorithmParameters (d := d) (m := m) eta T
  obtain ⟨L, hL, hlaw⟩ := exists_mainAlgorithm_ambient_law μ X ell p hmd T delta
    hX hell hp hnorm halgorithm hsample
  have hb := upper_omd_stability_observable_uniform L hmpos hmtop T hT hdelta0 hdelta1
  rw [← hlaw T le_rfl] at hb
  have hb' := ae_of_ae_map (measurable_history_upto X ell T hX hell T le_rfl).aemeasurable hb
  have hLa : ∀ᵐ ω ∂μ, ∀ t < T, L.itemLoss t (history X ell t ω) = ell t ω := by
    simpa only [ae_all_iff] using hL
  have hpa : ∀ᵐ ω ∂μ, ∀ t < T,
      p t ω = weightedLaw (theta t (history X ell t ω)) := by
    simpa only [ae_all_iff] using halgorithm
  filter_upwards [hb', hLa, hpa] with ω hbω hLω hpω
  intro q hq hqsum hqbox
  have hbound := hbω q hq hqsum hqbox
  have hd : observablePathSum (observableSurrogateDifference theta L eta q) T
      (history X ell T ω) = ambientSurrogateDifference X ell p eta T q ω := by
    rw [observablePathSum_history]
    apply Finset.sum_congr rfl
    intro t ht
    simp only [observableSurrogateDifference,
      hLω t (Finset.mem_range.mp ht), hpω t (Finset.mem_range.mp ht)]
    rfl
  have hv : observablePathSum (observableSurrogateSecondMoment theta L eta) T
      (history X ell T ω) = ambientSurrogateSecondMoment X ell p eta T ω := by
    rw [observablePathSum_history]
    apply Finset.sum_congr rfl
    intro t ht
    simp only [observableSurrogateSecondMoment,
      hLω t (Finset.mem_range.mp ht), hpω t (Finset.mem_range.mp ht)]
    rfl
  change observablePathSum (observableSurrogateDifference theta L eta q) T
    (history X ell T ω) ≤ (paperKL q (weightedLaw (m := m) (0 : Fin d → ℝ))).toReal / eta + 1 +
      2 * eta * observablePathSum (observableSurrogateSecondMoment theta L eta) T
        (history X ell T ω) at hbound
  rw [hd, hv] at hbound
  exact hbound

end
end MsetsPaper.Alignment
