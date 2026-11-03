import MsetsPaper.Alignment.UpperAmbient

/-! The leverage lemma on an arbitrary ambient probability space, with the
same predictable observable-history protocol as the main theorem. Both the
displayed exponential coefficient and the final relaxed constants are kept. -/

namespace MsetsPaper.Alignment

open MeasureTheory ProbabilityTheory MsetsLower MsetsLower.History MsetsPaper.Upper
open MsetsPaper.Probability MsetsPaper.Probability.AmbientHistory
open scoped BigOperators

noncomputable section
variable {Ω : Type*} [MeasurableSpace Ω] {d m : ℕ}

theorem measurable_actual_phi (theta : Ω → Fin d → ℝ) (htheta : Measurable theta)
    (a : Action d m) : Measurable (fun ω ↦
      phi (weightedMarginal (m := m) (theta ω)) (fun i ↦ selectedIndicator i a)) := by
  have hmu (i : Fin d) : Measurable (fun ω ↦ weightedMarginal (m := m) (theta ω) i) :=
    (measurable_pi_apply i).comp (measurable_actual_marginal (m := m) theta htheta)
  unfold phi
  exact (Finset.measurable_sum _ (fun i _ ↦
    ((hmu i).const_sub _).pow_const 2 |>.div ((hmu i).mul ((hmu i).const_sub 1)))).const_add 1

def ambientPhi (X : ℕ → Ω → Action d m) (ell : ℕ → Ω → Fin d → ℝ)
    (eta : ℝ) (T : ℕ) (ω : Ω) : ℝ :=
  ∑ t ∈ Finset.range T, phi (weightedMarginal (m := m)
    (ellipsoidAlgorithmParameters eta T t (history X ell t ω)))
      (fun i ↦ selectedIndicator i (X t ω))

theorem ambientPhi_event_transport
    (μ : Measure Ω) (X : ℕ → Ω → Action d m) (ell : ℕ → Ω → Fin d → ℝ)
    (P : Policy d m) (L : SignedLossProcess d m) (eta : ℝ) (T : ℕ)
    (hH : Measurable (history X ell T))
    (hlaw : μ.map (history X ell T) = signedRunLaw P L T) (b : ℝ) :
    μ.real {ω | ambientPhi X ell eta T ω ≤ b} =
      (signedRunLaw P L T).real {h |
        observablePathSum (observablePhi (ellipsoidAlgorithmParameters eta T)) T h ≤ b} := by
  let theta := ellipsoidAlgorithmParameters (d := d) (m := m) eta T
  let E : Set (History d m T) := {h | observablePathSum (observablePhi theta) T h ≤ b}
  have hE : MeasurableSet E := measurableSet_le
    (measurable_observablePathSum _ (fun t a ↦ measurable_actual_phi (theta t)
      (measurable_ellipsoidAlgorithmParameters eta T t) a) T) measurable_const
  have heq : {ω | ambientPhi X ell eta T ω ≤ b} = (history X ell T) ⁻¹' E := by
    ext ω
    simp only [Set.mem_setOf_eq, Set.mem_preimage, E, observablePathSum_history,
      observablePhi, ambientPhi, theta]
  change (μ {ω | ambientPhi X ell eta T ω ≤ b}).toReal = _
  rw [heq, ← Measure.map_apply hH hE, hlaw]
  rfl

/-- The sharper intermediate coefficient on the concrete canonical run.
The invariant is discharged only on the action histories reached by that run. -/
theorem upper_leverage_sharp_concentration
    (L : SignedLossProcess d m) (hmpos : 1 ≤ m) (hmtop : m ≤ d - 1)
    (T : ℕ) (hT : 0 < T) {delta : ℝ} (hdelta0 : 0 < delta) (hdelta1 : delta < 1)
    {rho : ℝ} (hrho0 : 0 < rho) :
    let eta := mainLearningRate d T (Nat.choose d m) delta
    let theta := ellipsoidAlgorithmParameters (d := d) (m := m) eta T
    1 - rho ≤ (signedRunLaw (mainAlgorithm T delta (by omega)) L T).real
      {h | observablePathSum (observablePhi theta) T h ≤
        (Real.exp 1 - 1) * ((d : ℝ) + 1) * T +
          (1 + 4 * d / (128 * eta * d)) * Real.log (1 / rho)} := by
  let eta := mainLearningRate d T (Nat.choose d m) delta
  let theta := ellipsoidAlgorithmParameters (d := d) (m := m) eta T
  have hd : (1 : ℝ) ≤ d := by exact_mod_cast (show 1 ≤ d by omega)
  have hTr : (1 : ℝ) ≤ T := by exact_mod_cast hT
  have hK : (2 : ℝ) ≤ Nat.choose d m := by exact_mod_cast action_count_ge_two hmpos hmtop
  obtain ⟨heta, _, hlam, _, _⟩ :=
    mainLearningRate_parameter_constraints hd hTr hK hdelta0 hdelta1.le
  have hinv := ellipsoid_algorithm_invariant L hmpos hmtop T hT heta
    (mainLearningRate_le_cap _ _ _ _)
  dsimp only
  unfold mainAlgorithm
  rw [signedRunLaw_probability_eq_tree_all_sets]
  simp only [Set.mem_setOf_eq, observablePathSum_historyOfActions]
  apply nonnegative_bounded_sum_sharp_high_probability_upto
    (weightedBranchingLaw (parametersOnActions theta L) (show m ≤ d by omega))
    (adaptivePhi (parametersOnActions theta L)) T (show 0 < 1 + 4 * (d : ℝ) /
      (128 * eta * d) by positivity)
  · intro t ht h a
    exact adaptivePhi_range _ hmpos hmtop hlam t h
      (fun i ↦ ((hinv t (by omega) h).1 i).1)
      (fun i ↦ ((hinv t (by omega) h).1 i).2) a
  · intro t _ h
    exact adaptivePhi_mean _ hmpos hmtop t h
  · exact hrho0

/-- L6's displayed sharper inequality on an arbitrary ambient experiment. -/
theorem upper_leverage_sharp_concentration_ambient
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
    {rho : ℝ} (hrho0 : 0 < rho) :
    let eta := mainLearningRate d T (Nat.choose d m) delta
    1 - rho ≤ μ.real {ω | ambientPhi X ell eta T ω ≤
      (Real.exp 1 - 1) * ((d : ℝ) + 1) * T +
        (1 + 4 * d / (128 * eta * d)) * Real.log (1 / rho)} := by
  classical
  have hmd : m ≤ d := by omega
  letI : Nonempty (Action d m) := nonempty_MSetAction hmd
  obtain ⟨L, _, hlaw⟩ := exists_mainAlgorithm_ambient_law μ X ell p hmd T delta
    hX hell hp hnorm halgorithm hsample
  dsimp only
  rw [ambientPhi_event_transport μ X ell (mainAlgorithm T delta hmd) L _ T
    (measurable_history_upto X ell T hX hell T le_rfl) (hlaw T le_rfl)]
  exact upper_leverage_sharp_concentration L hmpos hmtop T hT hdelta0 hdelta1 hrho0

/-- L6 with precisely the two final factors of 2, on the same ambient model. -/
theorem upper_leverage_concentration_ambient
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
    {rho : ℝ} (hrho0 : 0 < rho) (hrho1 : rho < 1) :
    let eta := mainLearningRate d T (Nat.choose d m) delta
    1 - rho ≤ μ.real {ω | ambientPhi X ell eta T ω ≤
      2 * ((d : ℝ) + 1) * T +
        2 * (1 + 4 * d / (128 * eta * d)) * Real.log (1 / rho)} := by
  classical
  have hmd : m ≤ d := by omega
  letI : Nonempty (Action d m) := nonempty_MSetAction hmd
  obtain ⟨L, _, hlaw⟩ := exists_mainAlgorithm_ambient_law μ X ell p hmd T delta
    hX hell hp hnorm halgorithm hsample
  dsimp only
  rw [ambientPhi_event_transport μ X ell (mainAlgorithm T delta hmd) L _ T
    (measurable_history_upto X ell T hX hell T le_rfl) (hlaw T le_rfl)]
  exact upper_leverage_concentration L hmpos hmtop T hT hdelta0 hdelta1 hrho0 hrho1

end
end MsetsPaper.Alignment
