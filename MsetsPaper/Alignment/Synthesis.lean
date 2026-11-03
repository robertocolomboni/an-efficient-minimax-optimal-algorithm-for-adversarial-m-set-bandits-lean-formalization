import MsetsPaper.Alignment.UpperAlgorithm
import MsetsPaper.Alignment.ImplementationAlgorithm
import MsetsPaper.Alignment.LowerDefinitive
import MsetsPaper.RateSynthesis

/-!
The unnumbered conclusion of the definitive paper uses the SAME operational
algorithm for efficiency and regret, and the definitive lower assembly.
The lower tail is evaluated at 2*delta before comparing it with an upper tail
of delta. Thus equality at a single confidence level is not mistaken for a
contradiction. This adds no assumption to any numbered paper result.
-/

noncomputable section
open MsetsLower MsetsLower.Lower MeasureTheory
open MsetsPaper.Upper MsetsPaper.Upper.RoundProgram MsetsPaper.Upper.SchurSolver

namespace MsetsPaper.Alignment

/-- P1 and T1 concern the same feedback-only policy and streaming program. -/
theorem efficiency_and_regret {d m : ℕ} (L : SignedLossProcess d m)
    (hm : 1 ≤ m) (hmtop : m ≤ d - 1) (T : ℕ) (hT : 0 < T)
    {delta : ℝ} (hdelta : 0 < delta) (hdelta1 : delta < 1) :
    operationalMainPolicy T delta (by omega : m ≤ d) =
      mainAlgorithm T delta (by omega : m ≤ d) ∧
    (1 - delta ≤ (signedRunLaw (mainAlgorithm T delta (by omega)) L T).real
      {h | observableSignedRegret L T h ≤ 160 * regretRate d m T delta}) ∧
    (∀ (u : ℕ → Fin d → unitInterval) (Y : ℕ → ℝ),
      ((algorithmArena d m T delta (by omega) u Y).1.work : ℝ) ≤
        (T : ℝ) * (roundTimePolynomial d m T + 7 * (m : ℝ) + 2 * d + 29) ∧
      (algorithmArena d m T delta (by omega) u Y).2 ≤ algorithmSpace d m) := by
  obtain ⟨hpolicy, _, _, hresources⟩ := Implementation.efficient_implementation
    L hm hmtop T hT delta hdelta hdelta1.le
  exact ⟨hpolicy, upper_main_regret L hm hmtop T hT hdelta hdelta1,
    fun u Y => (hresources u Y).2⟩

/-- The final rates with strictly separated tail probabilities, using the
definitive last-step-complementation proof rather than the legacy endpoint. -/
theorem matching_high_probability_rates {d m T : ℕ}
    (hm : 1 ≤ m) (hmtop : m ≤ d - 1) (hTpos : 0 < T)
    {delta : ℝ} (hdelta : 0 < delta) (hsmall : delta ≤ (2 : ℝ) ^ (-37 : ℤ))
    (hT : MsetsPaper.Lower.NewRoute.horizon d m delta ≤ T) :
    (∃ P : Policy d m, ∀ L : SignedLossProcess d m,
      1 - delta ≤ (signedRunLaw P L T).real
        {h | observableSignedRegret L T h ≤ 160 * regretRate d m T delta}) ∧
    (∀ P : Policy d m, ∃ L : LossProcess d m,
      delta < (runLaw P L T).real
        {h | (2 : ℝ) ^ (-44 : ℤ) * regretRate d m T delta ≤ pathRegret L T h}) := by
  have hmd : m ≤ d := by omega
  have hsmall1 : delta < 1 := hsmall.trans_lt (by norm_num)
  have hsmall4 : delta ≤ 1 / 4 := hsmall.trans (by norm_num)
  have hsmall2 : 2 * delta ≤ (2 : ℝ) ^ (-36 : ℤ) := by
    norm_num at hsmall ⊢
    linarith
  constructor
  · refine ⟨mainAlgorithm T delta hmd, ?_⟩
    intro L
    exact upper_main_regret L hm hmtop T hTpos hdelta hsmall1
  · intro P
    obtain ⟨L, _hact, htail⟩ := LowerDefinitive.theorem_lower_bound_explicit
      (by omega : 2 ≤ d) hm hmtop (by positivity : 0 < 2 * delta) hsmall2
      ((doubled_confidence_horizon_le d m hdelta).trans hT) P
    refine ⟨L, (show delta < 2 * delta by linarith).trans_le (htail.trans ?_)⟩
    apply ENNReal.toReal_mono (measure_ne_top _ _)
    apply measure_mono
    intro h hh
    exact (doubled_confidence_rate_comparison hmd hdelta hsmall4).trans hh

end MsetsPaper.Alignment
