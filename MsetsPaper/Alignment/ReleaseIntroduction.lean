import MsetsPaper.Alignment.UpperAmbient
import MsetsPaper.Alignment.ImplementationCosts

/-! The introduction's single algorithm has both the ambient-probability
regret guarantee and the certified real-RAM execution bounds. Resource
bounds are uniform over every supplied feedback stream and seed stream;
the auxiliary zero loss process below is used only to instantiate that
loss-independent part of P1. -/

noncomputable section
namespace MsetsPaper.Alignment
open MeasureTheory ProbabilityTheory MsetsLower MsetsPaper.Upper
open MsetsPaper.Probability MsetsPaper.Probability.AmbientHistory
open MsetsPaper.Upper.RoundProgram MsetsPaper.Upper.SchurSolver
open scoped ProbabilityTheory

variable {Ω : Type*} [MeasurableSpace Ω] {d m : ℕ}

/-- I1: the same operational algorithm satisfies T1 on an arbitrary ambient
space and P1's work, live-space, and intermediate-operation bounds. -/
theorem efficiency_and_regret_ambient
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
      p t ω = weightedLaw (m := m)
        (ellipsoidAlgorithmParameters
          (mainLearningRate d T (Nat.choose d m) delta) T t (history X ell t ω)))
    (hsample : ∀ t < T, ∀ a : Action d m,
      μ⟦(X t) ⁻¹' {a} | historySigma X ell t⟧ =ᵐ[μ] fun ω ↦ p t ω a) :
    operationalMainPolicy T delta (by omega : m ≤ d) =
      mainAlgorithm T delta (by omega : m ≤ d) ∧
    (1 - delta ≤ μ.real {ω | regret X ell T ω ≤
      160 * Real.sqrt ((d : ℝ) * T *
        (Real.log (Nat.choose d m) + Real.log (1 / delta)))}) ∧
    (∀ (u : ℕ → Fin d → unitInterval) (Y : ℕ → ℝ),
      ((algorithmArena d m T delta (by omega) u Y).1.work : ℝ) ≤
        (T : ℝ) * (roundTimePolynomial d m T + 7 * (m : ℝ) + 2 * d + 29) ∧
      (algorithmArena d m T delta (by omega) u Y).2 ≤ algorithmSpace d m) ∧
    Implementation.PaperIntermediateCosts d m := by
  let L : SignedLossProcess d m := {
    itemLoss := fun _ _ _ ↦ 0
    measurable_itemLoss := fun _ ↦ measurable_const
    action_abs_le_one := by intros; simp [actionLoss] }
  obtain ⟨⟨hpolicy, _, _, hresources⟩, hcosts⟩ :=
    Implementation.efficient_implementation_with_subcosts
      L hmpos hmtop T hT delta hdelta0 hdelta1.le
  exact ⟨hpolicy,
    upper_main_regret_ambient_of_conditional_expectations μ X ell p
      hmpos hmtop T hT hdelta0 hdelta1 hX hell hp hnorm halgorithm hsample,
    (fun u Y ↦ (hresources u Y).2), hcosts⟩

end MsetsPaper.Alignment
