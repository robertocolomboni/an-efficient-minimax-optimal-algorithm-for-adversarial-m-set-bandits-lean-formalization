import MsetsPaper.Alignment.ImplementationProjection
import MsetsPaper.Alignment.ImplementationESP
import MsetsPaper.Upper.OperationalPolicy

/-! Definitive P1. Lean round t is paper round t+1. Every transition is
certified on every action history of every signed nonanticipating adversary.
Resource statements describe the feedback-only streaming program, with no
stored history and no bit-complexity claim. -/

noncomputable section
open scoped BigOperators
open MsetsLower MsetsPaper.Probability MsetsPaper.Upper
open MsetsPaper.Upper.RoundProgram MsetsPaper.Upper.SchurSolver

namespace MsetsPaper.Alignment.Implementation

variable {d m : ℕ}

def ProjectionTransition (L : SignedLossProcess d m) (eta : ℝ) (T t : ℕ)
    (h : ActionTree (Action d m) t) (a : Action d m) : Prop :=
  let theta := parametersOnActions (ellipsoidAlgorithmParameters eta T) L t h
  let next := parametersOnActions (ellipsoidAlgorithmParameters eta T) L (t + 1) (h, a)
  let tilde := theta - eta • surrogateVector theta (lossesOnActions L t h) eta a
  SmoothingPolytope ((128 * eta * d) / 2) (weightedLaw (m := m) next) ∧
  ∀ q : Action d m → ℝ, SmoothingPolytope (128 * eta * d) q →
    finiteKL q (weightedLaw (m := m) next) +
      finiteKL (weightedLaw (m := m) next) (weightedLaw tilde) ≤
        finiteKL q (weightedLaw tilde) + eta / T

/-- The full approximate Pythagorean statement for each actual transition.
The input-KL hypothesis of L8 is derived from the conditional increment
lemma and the preceding invariant, rather than postulated. -/
theorem algorithm_projection_transition (L : SignedLossProcess d m)
    (hm : 1 ≤ m) (hmtop : m ≤ d - 1) (T : ℕ) (hT : 0 < T)
    {eta : ℝ} (heta : 0 < eta) (hcap : eta ≤ 1 / (256 * (d : ℝ)))
    (t : ℕ) (ht : t < T) (h : ActionTree (Action d m) t) (a : Action d m) :
    ProjectionTransition L eta T t h a := by
  have hd : (1 : ℝ) ≤ d := by exact_mod_cast (show 1 ≤ d by omega)
  have hsmall : eta ≤ 1 / 64 := hcap.trans
    (one_div_le_one_div_of_le (by norm_num) (by linarith))
  obtain ⟨hbox, hKL⟩ := ellipsoid_algorithm_invariant L hm hmtop T hT heta hcap t ht.le h
  have hstep := unprojected_uniform_KL_le
    (parametersOnActions (ellipsoidAlgorithmParameters eta T) L t h)
    (lossesOnActions L t h) hm hmtop heta hsmall
    (fun i => (hbox i).1) (fun i => (hbox i).2) a
    (fun b => L.action_abs_le_one t (historyOfActions L t h) b)
  have htcast : (t : ℝ) + 1 ≤ T := by exact_mod_cast (show t + 1 ≤ T by omega)
  have hinput : finiteKL (weightedLaw (m := m) (0 : Fin d → ℝ))
      (weightedLaw (parametersOnActions (ellipsoidAlgorithmParameters eta T) L t h -
        eta • surrogateVector (parametersOnActions (ellipsoidAlgorithmParameters eta T) L t h)
          (lossesOnActions L t h) eta a)) ≤ T := by linarith
  have hcorrect := ellipsoid_projection_correct _ hm hmtop eta T heta hcap
    (by exact_mod_cast hT) hinput
  unfold ProjectionTransition
  dsimp only
  rw [ellipsoidAlgorithmParameters_tree_step]
  exact ⟨⟨weightedLaw_probability _ (by omega), hcorrect.1⟩,
    fun q hq => hcorrect.2 q hq.1.1 hq.1.2 hq.2⟩

/-- P1 with the chosen learning rate: the same operational policy, complete
round contracts, exact parameter realization and explicit total/peak
resource bounds. In particular the peak bound has no T or delta argument. -/
theorem efficient_implementation (L : SignedLossProcess d m)
    (hm : 1 ≤ m) (hmtop : m ≤ d - 1) (T : ℕ) (hT : 1 ≤ T)
    (delta : ℝ) (hdelta0 : 0 < delta) (hdelta1 : delta ≤ 1) :
    let eta := mainLearningRate d T (Nat.choose d m) delta
    operationalMainPolicy T delta (by omega : m ≤ d) =
      mainAlgorithm T delta (by omega : m ≤ d) ∧
    (∀ t ≤ T, ∀ h : ActionTree (Action d m) t,
      SmoothingPolytope ((128 * eta * d) / 2)
        (weightedLaw (m := m) (parametersOnActions (ellipsoidAlgorithmParameters eta T) L t h)) ∧
      finiteKL (weightedLaw (m := m) (0 : Fin d → ℝ))
        (weightedLaw (parametersOnActions (ellipsoidAlgorithmParameters eta T) L t h)) ≤ t) ∧
    (∀ t < T, ∀ (h : ActionTree (Action d m) t) (a : Action d m),
      ProjectionTransition L eta T t h a) ∧
    (∀ (u : ℕ → Fin d → unitInterval) (Y : ℕ → ℝ),
      storedVector (algorithmArena d m T delta (by omega) u Y).1.value =
        ellipsoidAlgorithmParameters eta T T
          (roundHistory eta T (by omega : m ≤ d) u Y T) ∧
      ((algorithmArena d m T delta (by omega) u Y).1.work : ℝ) ≤
        (T : ℝ) * (roundTimePolynomial d m T + 7 * (m : ℝ) + 2 * d + 29) ∧
      (algorithmArena d m T delta (by omega) u Y).2 ≤ algorithmSpace d m) := by
  dsimp only
  have hd : (0 : ℝ) < d := by exact_mod_cast (show 0 < d by omega)
  have hTr : (0 : ℝ) < T := by exact_mod_cast (show 0 < T by omega)
  have hK : (2 : ℝ) ≤ Nat.choose d m := by exact_mod_cast action_count_ge_two hm hmtop
  have heta := mainLearningRate_pos hd hTr hK hdelta0 hdelta1
  have hcap := mainLearningRate_le_cap (d : ℝ) (T : ℝ) (Nat.choose d m : ℝ) delta
  refine ⟨operationalMainPolicy_eq_main T delta (by omega), ?_, ?_, ?_⟩
  · intro t ht h
    obtain ⟨hbox, hKL⟩ := ellipsoid_algorithm_invariant L hm hmtop T (by omega)
      heta hcap t ht h
    exact ⟨⟨weightedLaw_probability _ (by omega), hbox⟩, hKL⟩
  · exact fun t ht h a => algorithm_projection_transition L hm hmtop T (by omega)
      heta hcap t ht h a
  · intro u Y
    exact ⟨algorithmArena_parameters d m T delta hm hmtop u Y,
      algorithmArena_polynomial_work d m T delta hm hmtop hT hdelta0 hdelta1 u Y,
      algorithmArena_peak d m T delta (by omega) u Y⟩

end MsetsPaper.Alignment.Implementation
