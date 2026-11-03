import MsetsPaper.Upper.Algorithm
import MsetsPaper.Upper.AdaptiveOMD

/-!
# Upper lemmas instantiated on the definitive manuscript's actual algorithm

No marginal or projection invariant is an input to the public concentration
or stability results below. They are proved for the concrete ellipsoid update.
The finite action-tree representation reconstructs the REAL feedback history
under the given deterministic, history-dependent, non-anticipating adversary.
Lean time t corresponds to manuscript round t+1.
-/

noncomputable section

open MeasureTheory MsetsLower MsetsLower.History MsetsPaper.Probability MsetsPaper.Upper
open scoped BigOperators

namespace MsetsPaper.Alignment

variable {d m : ℕ}

/-- The projection guarantee needed by OMD, for EVERY admissible comparator
distribution, discharged on each reachable history of the actual algorithm. -/
theorem upper_algorithm_projection_for_comparator
    (L : SignedLossProcess d m) (hmpos : 1 ≤ m) (hmtop : m ≤ d - 1)
    (T : ℕ) (hT : 0 < T) {eta : ℝ}
    (heta : 0 < eta) (hcap : eta ≤ 1 / (256 * (d : ℝ)))
    (q : Action d m → ℝ) (hq : ∀ a, 0 ≤ q a) (hqsum : ∑ a, q a = 1)
    (hqbox : ∀ i, 128 * eta * d * ((m : ℝ) / d) ≤ marginal q i ∧
      marginal q i ≤ 1 - 128 * eta * d * (1 - (m : ℝ) / d))
    (t : ℕ) (ht : t < T) (h : ActionTree (Action d m) t) (a : Action d m) :
    let theta := parametersOnActions (ellipsoidAlgorithmParameters eta T) L
    let next := weightedLaw (m := m) (theta (t + 1) (h, a))
    let unprojected := weightedLaw (m := m)
      (theta t h - eta • surrogateVector (theta t h) (lossesOnActions L t h) eta a)
    finiteKL q next ≤ finiteKL q unprojected - finiteKL next unprojected + eta / T := by
  let theta := parametersOnActions (ellipsoidAlgorithmParameters eta T) L
  have hd : (1 : ℝ) ≤ d := by exact_mod_cast (show 1 ≤ d by omega)
  have hTr : (1 : ℝ) ≤ T := by exact_mod_cast hT
  have hsmall : eta ≤ 1 / 64 := hcap.trans
    (one_div_le_one_div_of_le (by norm_num) (by linarith))
  obtain ⟨hbox, hKL⟩ := ellipsoid_algorithm_invariant L hmpos hmtop T hT heta hcap
    t (by omega) h
  have hstep := unprojected_uniform_KL_le (theta t h) (lossesOnActions L t h)
    hmpos hmtop heta hsmall (fun i ↦ (hbox i).1) (fun i ↦ (hbox i).2) a
    (fun b ↦ L.action_abs_le_one t (historyOfActions L t h) b)
  have htcast : (t : ℝ) + 1 ≤ T := by exact_mod_cast (show t + 1 ≤ T by omega)
  have hinput : finiteKL (weightedLaw (m := m) (0 : Fin d → ℝ))
      (weightedLaw (theta t h - eta • surrogateVector (theta t h) (lossesOnActions L t h) eta a)) ≤ T := by
    change finiteKL _ (weightedLaw (m := m) (theta t h)) ≤ (t : ℝ) at hKL
    linarith
  have hpyth := (ellipsoid_projection_correct
    (theta t h - eta • surrogateVector (theta t h) (lossesOnActions L t h) eta a)
    hmpos hmtop eta T heta hcap hTr hinput).2 q hq hqsum hqbox
  have hnext : theta (t + 1) (h, a) = ellipsoidProjection (m := m)
      (theta t h - eta • surrogateVector (theta t h) (lossesOnActions L t h) eta a) eta T := rfl
  change finiteKL q (weightedLaw (m := m) (theta (t + 1) (h, a))) ≤
    finiteKL q (weightedLaw (m := m)
      (theta t h - eta • surrogateVector (theta t h) (lossesOnActions L t h) eta a)) -
    finiteKL (weightedLaw (m := m) (theta (t + 1) (h, a)))
      (weightedLaw (m := m)
        (theta t h - eta • surrogateVector (theta t h) (lossesOnActions L t h) eta a)) + eta / T
  rw [hnext]
  linarith

/-- `lem:omd-stability` on every actual action trajectory of Algorithm 1.
There is no assumed increment bound, invariant, or projection contract. -/
theorem upper_omd_stability
    (L : SignedLossProcess d m) (hmpos : 1 ≤ m) (hmtop : m ≤ d - 1)
    (T : ℕ) (hT : 0 < T) {delta : ℝ} (hdelta0 : 0 < delta) (hdelta1 : delta < 1)
    (q : Action d m → ℝ) (hq : ∀ a, 0 ≤ q a) (hqsum : ∑ a, q a = 1)
    (hqbox : ∀ i,
      128 * mainLearningRate d T (Nat.choose d m) delta * d * ((m : ℝ) / d) ≤ marginal q i ∧
      marginal q i ≤ 1 - 128 * mainLearningRate d T (Nat.choose d m) delta * d *
        (1 - (m : ℝ) / d)) (h : ActionTree (Action d m) T) :
    let eta := mainLearningRate d T (Nat.choose d m) delta
    let theta := parametersOnActions (ellipsoidAlgorithmParameters eta T) L
    pathSum (adaptiveSurrogateDifference theta (lossesOnActions L) eta q) T h ≤
      finiteKL q (weightedLaw (m := m) (0 : Fin d → ℝ)) / eta + 1 +
      2 * eta * pathSum (adaptiveSurrogateSecondMoment theta (lossesOnActions L) eta) T h := by
  let eta := mainLearningRate d T (Nat.choose d m) delta
  let theta := parametersOnActions (ellipsoidAlgorithmParameters eta T) L
  have hd : (1 : ℝ) ≤ d := by exact_mod_cast (show 1 ≤ d by omega)
  have hTr : (1 : ℝ) ≤ T := by exact_mod_cast hT
  have hK : (2 : ℝ) ≤ Nat.choose d m := by exact_mod_cast action_count_ge_two hmpos hmtop
  obtain ⟨heta, hsmall, _, _, _⟩ :=
    mainLearningRate_parameter_constraints hd hTr hK hdelta0 hdelta1.le
  have hcap : eta ≤ 1 / (256 * (d : ℝ)) := mainLearningRate_le_cap _ _ _ _
  have hinv := ellipsoid_algorithm_invariant L hmpos hmtop T hT heta hcap
  apply adaptive_omd_stability_of_projection theta (lossesOnActions L) q T hT
    hmpos hmtop eta heta hsmall hq hqsum
    (fun t _ h a ↦ L.action_abs_le_one t (historyOfActions L t h) a)
    (fun t ht h i ↦ ((hinv t (by omega) h).1 i).1)
    (fun t ht h i ↦ ((hinv t (by omega) h).1 i).2)
  intro t ht h a
  exact upper_algorithm_projection_for_comparator L hmpos hmtop T hT heta hcap
    q hq hqsum hqbox t ht h a

/-- `lem:kw-concentration` for the concrete algorithm and a history-predictable
sequence of comparator distributions. All invariants are discharged here.
Measurability is the paper's predictability requirement in history form. -/
theorem upper_kw_concentration
    (L : SignedLossProcess d m) (hmpos : 1 ≤ m) (hmtop : m ≤ d - 1)
    (T : ℕ) (hT : 0 < T) {delta : ℝ} (hdelta0 : 0 < delta) (hdelta1 : delta < 1)
    (q : (t : ℕ) → History d m t → Action d m → ℝ)
    (_hqmeas : ∀ t, Measurable (q t))
    (hq : ∀ t < T, ∀ h a, 0 ≤ q t h a)
    (hqsum : ∀ t < T, ∀ h, ∑ a, q t h a = 1)
    {rho : ℝ} (hrho0 : 0 < rho) (_hrho1 : rho < 1) :
    let eta := mainLearningRate d T (Nat.choose d m) delta
    let theta := ellipsoidAlgorithmParameters (d := d) (m := m) eta T
    1 - rho ≤ (signedRunLaw (mainAlgorithm T delta (by omega)) L T).real
      {h | |observablePathSum (observableComparatorDelta theta q L) T h| ≤
        eta / 4 * observablePathSum (observableComparatorV theta q) T h +
          Real.log (2 / rho) / eta} := by
  let eta := mainLearningRate d T (Nat.choose d m) delta
  let theta := ellipsoidAlgorithmParameters (d := d) (m := m) eta T
  have hd : (1 : ℝ) ≤ d := by exact_mod_cast (show 1 ≤ d by omega)
  have hTr : (1 : ℝ) ≤ T := by exact_mod_cast hT
  have hK : (2 : ℝ) ≤ Nat.choose d m := by exact_mod_cast action_count_ge_two hmpos hmtop
  obtain ⟨heta, hsmall, _, _, _⟩ :=
    mainLearningRate_parameter_constraints hd hTr hK hdelta0 hdelta1.le
  have hinv := ellipsoid_algorithm_invariant L hmpos hmtop T hT heta
    (mainLearningRate_le_cap _ _ _ _)
  dsimp only
  unfold mainAlgorithm
  rw [signedRunLaw_probability_eq_tree_all_sets]
  simp only [Set.mem_setOf_eq, observablePathSum_historyOfActions]
  exact adaptive_comparator_high_probability (parametersOnActions theta L)
    (comparatorsOnActions q L) (lossesOnActions L) hmpos hmtop T heta hsmall
    (fun t ht h a ↦ hq t ht (historyOfActions L t h) a)
    (fun t ht h ↦ hqsum t ht (historyOfActions L t h))
    (fun t ht h i ↦ ((hinv t (by omega) h).1 i).1)
    (fun t ht h i ↦ ((hinv t (by omega) h).1 i).2)
    (fun t _ h a ↦ L.action_abs_le_one t (historyOfActions L t h) a) hrho0

/-- `lem:leverage` under the law of the actual algorithm, with the two factors
of 2 in its stated bound and lambda=128 eta d. -/
theorem upper_leverage_concentration
    (L : SignedLossProcess d m) (hmpos : 1 ≤ m) (hmtop : m ≤ d - 1)
    (T : ℕ) (hT : 0 < T) {delta : ℝ} (hdelta0 : 0 < delta) (hdelta1 : delta < 1)
    {rho : ℝ} (hrho0 : 0 < rho) (hrho1 : rho < 1) :
    let eta := mainLearningRate d T (Nat.choose d m) delta
    let theta := ellipsoidAlgorithmParameters (d := d) (m := m) eta T
    1 - rho ≤ (signedRunLaw (mainAlgorithm T delta (by omega)) L T).real
      {h | observablePathSum (observablePhi theta) T h ≤
        2 * ((d : ℝ) + 1) * T +
          2 * (1 + 4 * d / (128 * eta * d)) * Real.log (1 / rho)} := by
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
  exact adaptive_leverage_high_probability (parametersOnActions theta L) hmpos hmtop T hlam
    (fun t ht h i ↦ ((hinv t (by omega) h).1 i).1)
    (fun t ht h i ↦ ((hinv t (by omega) h).1 i).2) hrho0 hrho1.le

/-- `thm:main` with the definitive manuscript's open confidence interval and
constant C=160. This uses the concrete feedback-only algorithm. -/
theorem upper_main_regret
    (L : SignedLossProcess d m) (hmpos : 1 ≤ m) (hmtop : m ≤ d - 1)
    (T : ℕ) (hT : 0 < T) {delta : ℝ} (hdelta0 : 0 < delta) (hdelta1 : delta < 1) :
    1 - delta ≤ (signedRunLaw (mainAlgorithm T delta (by omega)) L T).real
      {h | observableSignedRegret L T h ≤
        160 * Real.sqrt ((d : ℝ) * T *
          (Real.log (Nat.choose d m) + Real.log (1 / delta)))} :=
  main_algorithm_regret_high_probability L hmpos hmtop T hT hdelta0 hdelta1.le

end MsetsPaper.Alignment
