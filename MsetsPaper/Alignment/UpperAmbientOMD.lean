import MsetsPaper.Alignment.UpperAmbient
import MsetsPaper.Alignment.ExtendedKL

/-! L4 on the paper's ambient probability space. The losses and probabilities
in the two finite sums are the actual random variables, and the entropy is
the genuine extended-valued KL (proved finite at the uniform reference).
-/

namespace MsetsPaper.Alignment

open MeasureTheory ProbabilityTheory MsetsLower MsetsPaper.Upper
open MsetsPaper.Probability MsetsPaper.Probability.AmbientHistory
open scoped BigOperators

noncomputable section
variable {Ω : Type*} [MeasurableSpace Ω] {d m : ℕ}

def ambientSurrogateDifference
    (X : ℕ → Ω → Action d m) (ell : ℕ → Ω → Fin d → ℝ)
    (p : ℕ → Ω → Action d m → ℝ) (eta : ℝ) (T : ℕ)
    (q : Action d m → ℝ) (ω : Ω) : ℝ :=
  ∑ t ∈ Finset.range T,
    let z := surrogate (ellipsoidAlgorithmParameters eta T t (history X ell t ω))
      (ell t ω) eta (X t ω)
    finiteExpectation (p t ω) z - finiteExpectation q z

def ambientSurrogateSecondMoment
    (X : ℕ → Ω → Action d m) (ell : ℕ → Ω → Fin d → ℝ)
    (p : ℕ → Ω → Action d m → ℝ) (eta : ℝ) (T : ℕ) (ω : Ω) : ℝ :=
  ∑ t ∈ Finset.range T,
    finiteExpectation (p t ω) (fun b ↦
      (surrogate (ellipsoidAlgorithmParameters eta T t (history X ell t ω))
        (ell t ω) eta (X t ω) b) ^ 2)

/-- The pathwise OMD inequality holds almost surely for the actual sampled
process. No positivity or global support condition is imposed on q. -/
theorem upper_omd_stability_ambient
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
          finiteAtomicMeasure (p t ω) id)
    (q : Action d m → ℝ) (hq : ∀ a, 0 ≤ q a) (hqsum : ∑ a, q a = 1)
    (hqbox : ∀ i,
      128 * mainLearningRate d T (Nat.choose d m) delta * d * ((m : ℝ) / d) ≤ marginal q i ∧
      marginal q i ≤ 1 - 128 * mainLearningRate d T (Nat.choose d m) delta * d *
        (1 - (m : ℝ) / d)) :
    let eta := mainLearningRate d T (Nat.choose d m) delta
    ∀ᵐ ω ∂μ, ambientSurrogateDifference X ell p eta T q ω ≤
      (paperKL q (weightedLaw (m := m) (0 : Fin d → ℝ))).toReal / eta + 1 +
        2 * eta * ambientSurrogateSecondMoment X ell p eta T ω := by
  have hmd : m ≤ d := by omega
  letI : Nonempty (Action d m) := nonempty_MSetAction hmd
  let eta := mainLearningRate d T (Nat.choose d m) delta
  let theta := ellipsoidAlgorithmParameters (d := d) (m := m) eta T
  obtain ⟨L, hL, hlaw⟩ := exists_mainAlgorithm_ambient_law μ X ell p hmd T delta
    hX hell hp hnorm halgorithm hsample
  have hb := upper_omd_stability_extendedKL L hmpos hmtop T hT hdelta0 hdelta1
    q hq hqsum hqbox
  rw [← hlaw T le_rfl] at hb
  have hb' := ae_of_ae_map (measurable_history_upto X ell T hX hell T le_rfl).aemeasurable hb
  have hLa : ∀ᵐ ω ∂μ, ∀ t < T, L.itemLoss t (history X ell t ω) = ell t ω := by
    simpa only [ae_all_iff] using hL
  have hpa : ∀ᵐ ω ∂μ, ∀ t < T,
      p t ω = weightedLaw (theta t (history X ell t ω)) := by
    simpa only [ae_all_iff] using halgorithm
  filter_upwards [hb', hLa, hpa] with ω hbω hLω hpω
  have hd : observablePathSum (observableSurrogateDifference theta L eta q) T
      (history X ell T ω) = ambientSurrogateDifference X ell p eta T q ω := by
    rw [observablePathSum_history]
    apply Finset.sum_congr rfl
    intro t ht
    simp only [observableSurrogateDifference, ambientSurrogateDifference,
      hLω t (Finset.mem_range.mp ht), hpω t (Finset.mem_range.mp ht)]
    rfl
  have hv : observablePathSum (observableSurrogateSecondMoment theta L eta) T
      (history X ell T ω) = ambientSurrogateSecondMoment X ell p eta T ω := by
    rw [observablePathSum_history]
    apply Finset.sum_congr rfl
    intro t ht
    simp only [observableSurrogateSecondMoment, ambientSurrogateSecondMoment,
      hLω t (Finset.mem_range.mp ht), hpω t (Finset.mem_range.mp ht)]
    rfl
  change ambientSurrogateDifference X ell p eta T q ω ≤ _
  change observablePathSum (observableSurrogateDifference theta L eta q) T
    (history X ell T ω) ≤ (paperKL q (weightedLaw (m := m) (0 : Fin d → ℝ))).toReal / eta + 1 +
      2 * eta * observablePathSum (observableSurrogateSecondMoment theta L eta) T
        (history X ell T ω) at hbω
  rw [hd, hv] at hbω
  exact hbω

end
end MsetsPaper.Alignment
