import MsetsPaper.Upper.ProjectionEllipsoidMeasurable
import MsetsPaper.Upper.AlgorithmInvariant
import MsetsPaper.Upper.MainObservableBound
import MsetsPaper.Upper.AlgorithmParameters

/-! # The concrete observable algorithm and its main regret guarantee

The projection is the fixed-budget ellipsoid search. Its local guarantee
is instantiated before the invariant induction; no global marginal bound,
projection success, or regret bound is assumed of the algorithm.
-/

noncomputable section
open MeasureTheory MsetsLower MsetsLower.History MsetsPaper.Probability
open scoped BigOperators

namespace MsetsPaper.Upper

variable {d m : ℕ}

def ellipsoidAlgorithmParameters (eta : ℝ) (T : ℕ) :
    (t : ℕ) → History d m t → Fin d → ℝ :=
  algorithmParameters (fun z ↦ ellipsoidProjection (m := m) z eta T) eta

theorem measurable_ellipsoidAlgorithmParameters (eta : ℝ) (T t : ℕ) :
    Measurable (ellipsoidAlgorithmParameters (d := d) (m := m) eta T t) :=
  measurable_algorithmParameters _ (measurable_ellipsoidProjection eta T) eta t

theorem ellipsoidAlgorithmParameters_tree_step (L : SignedLossProcess d m)
    (eta : ℝ) (T t : ℕ) (h : ActionTree (Action d m) t) (a : Action d m) :
    parametersOnActions (ellipsoidAlgorithmParameters eta T) L (t + 1) (h, a) =
      ellipsoidProjection (m := m)
        (parametersOnActions (ellipsoidAlgorithmParameters eta T) L t h -
          eta • surrogateVector (parametersOnActions (ellipsoidAlgorithmParameters eta T) L t h)
            (lossesOnActions L t h) eta a) eta T := rfl

theorem ellipsoid_algorithm_invariant (L : SignedLossProcess d m)
    (hmpos : 1 ≤ m) (hmtop : m ≤ d - 1) (T : ℕ) (hT : 0 < T)
    {eta : ℝ} (heta : 0 < eta) (hcap : eta ≤ 1 / (256 * (d : ℝ))) :
    ∀ t ≤ T, ∀ h,
      (∀ i, (128 * eta * d / 2) * ((m : ℝ) / d) ≤
          weightedMarginal (m := m)
            (parametersOnActions (ellipsoidAlgorithmParameters eta T) L t h) i ∧
        weightedMarginal (m := m)
            (parametersOnActions (ellipsoidAlgorithmParameters eta T) L t h) i ≤
          1 - (128 * eta * d / 2) * (1 - (m : ℝ) / d)) ∧
      finiteKL (weightedLaw (m := m) (0 : Fin d → ℝ))
        (weightedLaw (parametersOnActions (ellipsoidAlgorithmParameters eta T) L t h)) ≤ t := by
  have hd : (1 : ℝ) ≤ d := by exact_mod_cast (show 1 ≤ d by omega)
  have hTr : (1 : ℝ) ≤ T := by exact_mod_cast hT
  have hsmall : eta ≤ 1 / 64 := hcap.trans
    (one_div_le_one_div_of_le (by norm_num) (by linarith))
  have hprod := (le_div_iff₀ (show 0 < 256 * (d : ℝ) by positivity)).mp hcap
  have hlam : 128 * eta * d ≤ 1 / 2 := by nlinarith
  apply algorithm_invariant_of_projection_contract
    (parametersOnActions (ellipsoidAlgorithmParameters eta T) L) (lossesOnActions L)
    hmpos hmtop T hT heta hsmall hlam rfl
    (fun t _ h a ↦ L.action_abs_le_one t (historyOfActions L t h) a)
  intro t ht h a
  dsimp only
  intro hKL
  rw [ellipsoidAlgorithmParameters_tree_step]
  obtain ⟨hbox, hpyth⟩ := ellipsoid_projection_correct _ hmpos hmtop eta T heta hcap hTr hKL
  refine ⟨hbox, ?_⟩
  intro q hq hqsum hqbox
  have hh := hpyth q hq hqsum hqbox
  linarith

def mainAlgorithm (T : ℕ) (delta : ℝ) (hmd : m ≤ d) : Policy d m :=
  observableWeightedPolicy
    (ellipsoidAlgorithmParameters (mainLearningRate d T (Nat.choose d m) delta) T)
    (measurable_ellipsoidAlgorithmParameters _ T) hmd

/-- T1: the probability guarantee for the concrete feedback-only algorithm.
Only the paper's dimension, horizon, confidence and action-loss hypotheses
remain. The computational-resource theorem is a separate obligation. -/
theorem main_algorithm_regret_high_probability (L : SignedLossProcess d m)
    (hmpos : 1 ≤ m) (hmtop : m ≤ d - 1) (T : ℕ) (hT : 0 < T)
    {delta : ℝ} (hdelta0 : 0 < delta) (hdelta1 : delta ≤ 1) :
    1 - delta ≤ (signedRunLaw (mainAlgorithm T delta (by omega)) L T).real
      {h | observableSignedRegret L T h ≤
        160 * Real.sqrt ((d : ℝ) * T * (Real.log (Nat.choose d m) + Real.log (1 / delta)))} := by
  let eta := mainLearningRate d T (Nat.choose d m) delta
  let theta := parametersOnActions (ellipsoidAlgorithmParameters eta T) L
  have hd : (1 : ℝ) ≤ d := by exact_mod_cast (show 1 ≤ d by omega)
  have hTr : (1 : ℝ) ≤ T := by exact_mod_cast hT
  have hK : (2 : ℝ) ≤ Nat.choose d m := by exact_mod_cast action_count_ge_two hmpos hmtop
  obtain ⟨heta, hsmall, hlam0, hlam, _⟩ :=
    mainLearningRate_parameter_constraints hd hTr hK hdelta0 hdelta1
  have hcap : eta ≤ 1 / (256 * (d : ℝ)) := mainLearningRate_le_cap _ _ _ _
  have hinv := ellipsoid_algorithm_invariant L hmpos hmtop T hT heta hcap
  unfold mainAlgorithm
  rw [signedRunLaw_probability_eq_tree_all_sets]
  simp only [Set.mem_setOf_eq, observableSignedRegret_historyOfActions]
  apply main_regret_high_probability_of_projection theta (lossesOnActions L)
    hmpos hmtop T hT hdelta0 hdelta1 rfl
    (fun t _ h a ↦ L.action_abs_le_one t (historyOfActions L t h) a)
  · intro t ht h i
    exact ((hinv t (by omega) h).1 i).1
  · intro t ht h i
    exact ((hinv t (by omega) h).1 i).2
  · intro x t ht h a
    dsimp only
    change finiteKL (smoothedComparator (128 * eta * d) x)
        (weightedLaw (m := m) (theta (t + 1) (h, a))) ≤
      finiteKL (smoothedComparator (128 * eta * d) x)
        (weightedLaw (m := m) (theta t h - eta • surrogateVector (theta t h) (lossesOnActions L t h) eta a)) -
      finiteKL (weightedLaw (m := m) (theta (t + 1) (h, a)))
        (weightedLaw (m := m) (theta t h - eta • surrogateVector (theta t h) (lossesOnActions L t h) eta a)) + eta / T
    obtain ⟨hbox, hKL⟩ := hinv t (by omega) h
    have hstep := unprojected_uniform_KL_le (theta t h) (lossesOnActions L t h)
      hmpos hmtop heta hsmall (fun i ↦ (hbox i).1) (fun i ↦ (hbox i).2) a
      (fun b ↦ L.action_abs_le_one t (historyOfActions L t h) b)
    have htcast : (t : ℝ) + 1 ≤ T := by exact_mod_cast (show t + 1 ≤ T by omega)
    have hinput : finiteKL (weightedLaw (m := m) (0 : Fin d → ℝ))
        (weightedLaw (theta t h - eta • surrogateVector (theta t h) (lossesOnActions L t h) eta a)) ≤ T := by
      change finiteKL _ (weightedLaw (theta t h)) ≤ (t : ℝ) at hKL
      linarith
    have hpyth := (ellipsoid_projection_correct
      (theta t h - eta • surrogateVector (theta t h) (lossesOnActions L t h) eta a)
      hmpos hmtop eta T heta hcap hTr hinput).2
      (smoothedComparator (128 * eta * d) x)
      (smoothedComparator_nonneg (by dsimp [eta]; linarith) (by dsimp [eta]; linarith) x)
      (sum_smoothedComparator _ x)
      (smoothedComparator_marginal_mem _ x hmpos hmtop (by dsimp [eta]; linarith))
    have hnext : theta (t + 1) (h, a) = ellipsoidProjection (m := m)
        (theta t h - eta • surrogateVector (theta t h) (lossesOnActions L t h) eta a) eta T := rfl
    rw [hnext]
    linarith

end MsetsPaper.Upper
