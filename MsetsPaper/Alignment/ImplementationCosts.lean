import MsetsPaper.Alignment.ImplementationAlgorithm

/-! The final P1 program and every intermediate running-time bound are
certified together. These are the routines called by startRoundResource and
finishRoundResource, including charged input copies and RAM accesses. -/

noncomputable section
open scoped BigOperators
open MsetsLower MsetsPaper.Probability MsetsPaper.Upper
open MsetsPaper.Upper.RoundProgram MsetsPaper.Upper.SchurSolver
open MsetsPaper.Upper.VectorProgram

namespace MsetsPaper.Alignment.Implementation

variable {d m : ℕ}

/-- Literal intermediate operation counts for the very same round program. -/
def PaperIntermediateCosts (d m : ℕ) : Prop :=
  (∀ theta : StoredVector d, (prepareMomentsResource theta m).work ≤ 550*d^3*m) ∧
  (∀ (theta : StoredVector d) (hmd : m ≤ d) (u : Fin d → unitInterval),
    (sampleResource theta hmd u).work ≤ 230*d*m) ∧
  (∀ (A : StoredMatrix d) (b : StoredVector d),
    (profiledSolve d A b).1.work ≤ 200*(d+1)^3 ∧
    (profiledSolve d A b).1.allocated ≤ 200*(d+1)^3) ∧
  (∀ mu : StoredVector d, (resourceCorrection m mu).work ≤ 16*d+6) ∧
  (∀ (eta : ℝ) (theta estimate c : StoredVector d),
    (resourceUpdateStored eta theta estimate c).work = 9*d+5)

theorem paper_intermediate_costs (hd : 1 ≤ d) (hm : 1 ≤ m) :
    PaperIntermediateCosts d m := by
  refine ⟨fun theta => prepareMomentsResource_cubic theta hd hm, ?_,
    fun A b => profiledSolve_total_cubic d A b,
    fun mu => (resourceCorrection_bounds m mu).1,
    fun eta theta estimate c => (resourceUpdateStored_counts eta theta estimate c).1⟩
  intro theta hmd u
  exact (sampleResource_linear theta hmd hd hm u).1

/-- Final implementation theorem, augmented with the paper's subcosts for its
actual moment preparation, sampler, solver, correction and vector update. -/
theorem efficient_implementation_with_subcosts (L : SignedLossProcess d m)
    (hm : 1 ≤ m) (hmtop : m ≤ d - 1) (T : ℕ) (hT : 1 ≤ T)
    (delta : ℝ) (hdelta0 : 0 < delta) (hdelta1 : delta ≤ 1) :
    (
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
      (algorithmArena d m T delta (by omega) u Y).2 ≤ algorithmSpace d m)
    ) ∧ PaperIntermediateCosts d m := by
  exact ⟨efficient_implementation L hm hmtop T hT delta hdelta0 hdelta1,
    paper_intermediate_costs (by omega) hm⟩

end MsetsPaper.Alignment.Implementation
