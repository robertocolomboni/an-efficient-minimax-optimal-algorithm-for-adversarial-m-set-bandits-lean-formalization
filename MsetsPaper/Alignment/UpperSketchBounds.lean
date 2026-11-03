import MsetsPaper.Alignment.UpperObservable
import MsetsPaper.Upper.AlgorithmParameters
import MsetsPaper.Upper.MainAdaptiveEstimated
import MsetsPaper.Upper.MainGoodEvent

/-!
# Explicit constants in the main upper-bound sketch

The O(1) projection term is exactly 1. The correction bounds have constants
20 and 160. The concentration and estimated-loss O-terms below have constant
544, uniformly for 0 < delta < 1, including delta arbitrarily close to one.
The latter absorption uses the actual learning rate and T >= 1, K >= 2.
The public algorithmic endpoint assumes neither a marginal invariant nor a
projection certificate: both are discharged by the proved concrete update.
-/

noncomputable section

open MsetsLower MsetsLower.History MsetsPaper.Probability MsetsPaper.Upper
open scoped BigOperators

namespace MsetsPaper.Alignment.UpperSketch

variable {d m : ℕ}

/-- The pointwise correction bound underlying the sketch's maximum. -/
theorem correction_uniform_bound (theta : Fin d → ℝ)
    (hmpos : 1 ≤ m) (hmtop : m ≤ d - 1) {lam : ℝ}
    (hlam : 0 < lam) (hlamd : lam ≤ d)
    (hlo : ∀ i, (lam / 2) * ((m : ℝ) / d) ≤ weightedMarginal (m := m) theta i)
    (hhi : ∀ i, weightedMarginal (m := m) theta i ≤
      1 - (lam / 2) * (1 - (m : ℝ) / d)) (a : Action d m) :
    0 ≤ actionLoss a (correction (m : ℝ) (weightedMarginal (m := m) theta)) ∧
      actionLoss a (correction (m : ℝ) (weightedMarginal (m := m) theta)) ≤
        20 * d / lam := by
  have hr := weightedLaw_phi_range theta hmpos hmtop
    (show 0 < lam / 2 by positivity) hlo hhi a
  rw [actionLoss_correction theta hmpos hmtop]
  have hratio : (1 : ℝ) ≤ d / lam := (le_div_iff₀ hlam).mpr (by simpa using hlamd)
  have hid : 1 + 2 * (d : ℝ) / (lam / 2) = 1 + 4 * d / lam := by ring
  rw [hid] at hr
  constructor
  · exact mul_nonneg (by norm_num) hr.1
  · calc
      _ ≤ 4 * (1 + 4 * d / lam) := mul_le_mul_of_nonneg_left hr.2 (by norm_num)
      _ ≤ _ := by ring_nf at hratio ⊢; linarith

/-- Max-times-mean with the literal mean 4(d+1), then d+1 <= 2d. -/
theorem correction_squared_bound (theta : Fin d → ℝ)
    (hmpos : 1 ≤ m) (hmtop : m ≤ d - 1) {lam : ℝ}
    (hlam : 0 < lam) (hlamd : lam ≤ d)
    (hlo : ∀ i, (lam / 2) * ((m : ℝ) / d) ≤ weightedMarginal (m := m) theta i)
    (hhi : ∀ i, weightedMarginal (m := m) theta i ≤
      1 - (lam / 2) * (1 - (m : ℝ) / d)) :
    finiteExpectation (weightedLaw theta)
      (fun a : Action d m ↦
        (actionLoss a (correction (m : ℝ) (weightedMarginal (m := m) theta))) ^ 2) ≤
      160 * (d : ℝ) ^ 2 / lam := by
  have hd : (1 : ℝ) ≤ d := by exact_mod_cast (show 1 ≤ d by omega)
  have hp (a : Action d m) := correction_uniform_bound theta hmpos hmtop hlam hlamd hlo hhi a
  have hs := Finset.sum_le_sum (s := Finset.univ) (fun a _ ↦
    mul_le_mul_of_nonneg_left
      (show (actionLoss a (correction (m : ℝ) (weightedMarginal (m := m) theta))) ^ 2 ≤
          (20 * d / lam) * actionLoss a
            (correction (m : ℝ) (weightedMarginal (m := m) theta)) by
        nlinarith [mul_nonneg (hp a).1 (sub_nonneg.mpr (hp a).2)])
      (weightedLaw_pos theta (show m ≤ d by omega) a).le)
  have heq : (∑ a : Action d m, weightedLaw theta a *
      ((20 * d / lam) * actionLoss a
        (correction (m : ℝ) (weightedMarginal (m := m) theta)))) =
      (20 * d / lam) * finiteExpectation (weightedLaw theta)
        (fun a : Action d m ↦ actionLoss a
          (correction (m : ℝ) (weightedMarginal (m := m) theta))) := by
    simp only [finiteExpectation, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro a _
    ring
  rw [heq, correction_mean theta hmpos hmtop] at hs
  change finiteExpectation (weightedLaw theta) _ ≤ _ at hs
  have hb := mul_le_mul_of_nonneg_left (show (d : ℝ) + 1 ≤ 2 * d by linarith)
    (show 0 ≤ 80 * (d : ℝ) / lam by positivity)
  have hfinal : (20 * (d : ℝ) / lam) * (4 * (d + 1)) ≤ 160 * d ^ 2 / lam := by
    convert hb using 1 <;> ring
  exact hs.trans hfinal

/-- Both O-bounds instantiated on each actual round, with no box premise. -/
theorem algorithm_correction_bounds
    (L : SignedLossProcess d m) (hmpos : 1 ≤ m) (hmtop : m ≤ d - 1)
    (T : ℕ) (hT : 0 < T) {delta : ℝ} (hdelta0 : 0 < delta) (hdelta1 : delta < 1)
    (t : ℕ) (ht : t < T) (h : ActionTree (Action d m) t) :
    let eta := mainLearningRate d T (Nat.choose d m) delta
    let lam := 128 * eta * d
    let theta := parametersOnActions (ellipsoidAlgorithmParameters eta T) L t h
    finiteExpectation (weightedLaw theta)
        (fun a : Action d m ↦ actionLoss a (correction (m : ℝ) (weightedMarginal (m := m) theta))) =
      4 * ((d : ℝ) + 1) ∧
    (∀ a : Action d m, actionLoss a (correction (m : ℝ) (weightedMarginal (m := m) theta)) ≤
      20 * d / lam) ∧
    finiteExpectation (weightedLaw theta)
        (fun a : Action d m ↦ (actionLoss a (correction (m : ℝ) (weightedMarginal (m := m) theta))) ^ 2) ≤
      160 * (d : ℝ) ^ 2 / lam := by
  let eta := mainLearningRate d T (Nat.choose d m) delta
  have hd : (1 : ℝ) ≤ d := by exact_mod_cast (show 1 ≤ d by omega)
  have hTr : (1 : ℝ) ≤ T := by exact_mod_cast hT
  have hK : (2 : ℝ) ≤ Nat.choose d m := by exact_mod_cast action_count_ge_two hmpos hmtop
  obtain ⟨heta, _, hlam, hlamhalf, _⟩ :=
    mainLearningRate_parameter_constraints hd hTr hK hdelta0 hdelta1.le
  have hinv := (ellipsoid_algorithm_invariant L hmpos hmtop T hT heta
    (mainLearningRate_le_cap _ _ _ _) t (by omega) h).1
  dsimp only
  refine ⟨correction_mean _ hmpos hmtop, ?_, ?_⟩
  · intro a
    exact (correction_uniform_bound _ hmpos hmtop hlam (by linarith)
      (fun i ↦ (hinv i).1) (fun i ↦ (hinv i).2) a).2
  · exact correction_squared_bound _ hmpos hmtop hlam (by linarith)
      (fun i ↦ (hinv i).1) (fun i ↦ (hinv i).2)

/-- The first sketch display has exactly +1, before the second-moment bound. -/
theorem estimated_loss_before_concentration
    (L : SignedLossProcess d m) (hmpos : 1 ≤ m) (hmtop : m ≤ d - 1)
    (T : ℕ) (hT : 0 < T) {delta : ℝ} (hdelta0 : 0 < delta) (hdelta1 : delta < 1)
    (x : Action d m) (h : ActionTree (Action d m) T) :
    let eta := mainLearningRate d T (Nat.choose d m) delta
    let theta := parametersOnActions (ellipsoidAlgorithmParameters eta T) L
    let q := smoothedComparator (128 * eta * d) x
    pathSum (adaptiveEstimatedDifference theta (lossesOnActions L) q) T h ≤
      Real.log (Nat.choose d m) / eta + 1 +
        2 * eta * pathSum (adaptiveSurrogateSecondMoment theta (lossesOnActions L) eta) T h +
        4 * eta * ((d : ℝ) + 1) * T -
        eta * pathSum (fun t h (_ : Action d m) ↦ comparatorV (theta t h) q) T h := by
  let eta := mainLearningRate d T (Nat.choose d m) delta
  let theta := parametersOnActions (ellipsoidAlgorithmParameters eta T) L
  let q := smoothedComparator (128 * eta * d) x
  have hd : (1 : ℝ) ≤ d := by exact_mod_cast (show 1 ≤ d by omega)
  have hTr : (1 : ℝ) ≤ T := by exact_mod_cast hT
  have hK : (2 : ℝ) ≤ Nat.choose d m := by exact_mod_cast action_count_ge_two hmpos hmtop
  obtain ⟨heta, _, hlam, hlamhalf, _⟩ :=
    mainLearningRate_parameter_constraints hd hTr hK hdelta0 hdelta1.le
  have hlam1 : 128 * eta * d ≤ 1 := by linarith
  have homd := upper_omd_stability L hmpos hmtop T hT hdelta0 hdelta1 q
    (smoothedComparator_nonneg hlam.le hlam1 x) (sum_smoothedComparator _ x)
    (smoothedComparator_marginal_mem _ x hmpos hmtop hlam1) h
  have hKL := div_le_div_of_nonneg_right
    (smoothedComparator_initialKL_le_log_card hlam.le hlam1 x) heta.le
  have hpoint : ∀ t < T, ∀ h a,
      adaptiveSurrogateDifference theta (lossesOnActions L) eta q t h a =
        (adaptiveEstimatedDifference theta (lossesOnActions L) q t h a -
          4 * eta * ((d : ℝ) + 1)) + eta * comparatorV (theta t h) q := by
    intro t _ h a
    dsimp [adaptiveSurrogateDifference]
    rw [mean_learner_surrogate _ _ _ hmpos hmtop, mean_surrogate]
    dsimp [adaptiveEstimatedDifference]
    ring
  have heq := pathSum_congr_upto _ _ T hpoint h
  rw [pathSum_add, pathSum_sub, pathSum_const, pathSum_mul] at heq
  change pathSum (adaptiveSurrogateDifference theta (lossesOnActions L) eta q) T h ≤ _ at homd
  rw [heq] at homd
  dsimp only
  change finiteKL q _ / eta ≤ _ at hKL
  linarith

/-- The three separate terms in the first second-order O-display. -/
theorem second_order_three_terms {d T eta delta S Z : ℝ}
    (hd : 1 ≤ d) (hT : 0 ≤ T) (heta : 0 < eta)
    (hlamd : 128 * eta * d ≤ d)
    (hdelta0 : 0 < delta) (hdelta1 : delta ≤ 1)
    (hmoment : 2 * eta * Z ≤ 4 * eta * S + 3 * eta ^ 2 * (d + 1) * T)
    (hlev : S ≤ 2 * (d + 1) * T +
      2 * (1 + 4 * d / (128 * eta * d)) * Real.log (1 / (delta / 2))) :
    2 * eta * Z ≤ 16 * eta * d * T +
      40 * eta * d / (128 * eta * d) * Real.log (2 / delta) +
      768 * eta ^ 3 * d ^ 2 * T / (128 * eta * d) := by
  have hd0 : 0 < d := by linarith
  have hlam : 0 < 128 * eta * d := by positivity
  have hratio : (1 : ℝ) ≤ d / (128 * eta * d) :=
    (le_div_iff₀ hlam).mpr (by simpa using hlamd)
  have hB : 1 + 4 * d / (128 * eta * d) ≤ 5 * d / (128 * eta * d) := by
    ring_nf at hratio ⊢
    linarith
  have hlog : 0 ≤ Real.log (2 / delta) :=
    Real.log_nonneg ((le_div_iff₀ hdelta0).mpr (by linarith))
  rw [show (1 : ℝ) / (delta / 2) = 2 / delta by ring] at hlev
  have hs := mul_le_mul_of_nonneg_left hlev (show 0 ≤ 4 * eta by positivity)
  have hlin := mul_le_mul_of_nonneg_right (show d + 1 ≤ 2 * d by linarith)
    (show 0 ≤ 8 * eta * T by positivity)
  have hBmul := mul_le_mul_of_nonneg_right hB
    (show 0 ≤ 8 * eta * Real.log (2 / delta) by positivity)
  have hfirst : 4 * eta * S ≤ 16 * eta * d * T +
      40 * eta * d / (128 * eta * d) * Real.log (2 / delta) := by
    calc
      _ ≤ 8 * eta * (d + 1) * T +
          8 * eta * (1 + 4 * d / (128 * eta * d)) * Real.log (2 / delta) := by nlinarith
      _ ≤ _ := by convert add_le_add hlin hBmul using 1 <;> ring
  have hquad := mul_le_mul_of_nonneg_right (show d + 1 ≤ 2 * d by linarith)
    (show 0 ≤ 3 * eta ^ 2 * T by positivity)
  have hid : 768 * eta ^ 3 * d ^ 2 * T / (128 * eta * d) = 6 * eta ^ 2 * d * T := by
    field_simp
    ring
  rw [hid]
  nlinarith

/-- Arithmetic for the two second-order O-displays; its input is L6. -/
theorem second_order_on_leverage_event {d T K delta S Z : ℝ}
    (hd : 1 ≤ d) (hT : 1 ≤ T) (hK : 2 ≤ K)
    (hdelta0 : 0 < delta) (hdelta1 : delta ≤ 1)
    (hmoment : 2 * mainLearningRate d T K delta * Z ≤
      4 * mainLearningRate d T K delta * S +
        3 * (mainLearningRate d T K delta) ^ 2 * (d + 1) * T)
    (hlev : 4 * mainLearningRate d T K delta * S ≤
      8 * mainLearningRate d T K delta * (d + 1) * T + Real.log (2 / delta)) :
    2 * mainLearningRate d T K delta * Z ≤
      22 * mainLearningRate d T K delta * d * T + Real.log (2 / delta) ∧
    1 + 2 * mainLearningRate d T K delta * Z +
        4 * mainLearningRate d T K delta * (d + 1) * T ≤
      544 * mainLearningRate d T K delta * d * T + Real.log (1 / delta) := by
  let eta := mainLearningRate d T K delta
  obtain ⟨heta, hsmall, _, _, _⟩ :=
    mainLearningRate_parameter_constraints hd hT hK hdelta0 hdelta1
  have hdim : d + 1 ≤ 2 * d := by linarith
  have he2 : eta ^ 2 ≤ eta := by dsimp [eta]; nlinarith
  have hquad := mul_le_mul_of_nonneg_right he2 (show 0 ≤ 3 * (d + 1) * T by positivity)
  have hlinear := mul_le_mul_of_nonneg_right hdim (show 0 ≤ 11 * eta * T by positivity)
  have hsecond : 2 * eta * Z ≤ 22 * eta * d * T + Real.log (2 / delta) := by
    dsimp [eta] at *
    nlinarith
  have habsorb := main_sketch_constant_absorption hd hT hK hdelta0 hdelta1
  have hcorr := mul_le_mul_of_nonneg_right hdim (show 0 ≤ 4 * eta * T by positivity)
  constructor
  · exact hsecond
  · dsimp [eta] at *
    nlinarith [mul_nonneg heta.le (show 0 ≤ d * T by positivity)]

/-- Both sketch O-displays, simultaneously for all comparators, under the
actual algorithm's law. The common event has probability at least 1-delta/2. -/
theorem algorithm_sketch_estimated_loss_high_probability
    (L : SignedLossProcess d m) (hmpos : 1 ≤ m) (hmtop : m ≤ d - 1)
    (T : ℕ) (hT : 0 < T) {delta : ℝ} (hdelta0 : 0 < delta) (hdelta1 : delta < 1) :
    let eta := mainLearningRate d T (Nat.choose d m) delta
    let theta := parametersOnActions (ellipsoidAlgorithmParameters eta T) L
    1 - delta / 2 ≤ (weightedBranchingLaw theta (by omega)).probability T
      {h | (2 * eta * pathSum (adaptiveSurrogateSecondMoment theta (lossesOnActions L) eta) T h ≤
        16 * eta * d * T +
          40 * eta * d / (128 * eta * d) * Real.log (2 / delta) +
          768 * eta ^ 3 * (d : ℝ) ^ 2 * T / (128 * eta * d)) ∧
        (2 * eta * pathSum (adaptiveSurrogateSecondMoment theta (lossesOnActions L) eta) T h ≤
        544 * eta * d * T + Real.log (1 / delta)) ∧
        ∀ x : Action d m,
          pathSum (adaptiveEstimatedDifference theta (lossesOnActions L)
            (smoothedComparator (128 * eta * d) x)) T h ≤
          Real.log (Nat.choose d m) / eta -
            eta * pathSum (fun t h (_ : Action d m) ↦ comparatorV (theta t h)
              (smoothedComparator (128 * eta * d) x)) T h +
            544 * eta * d * T + Real.log (1 / delta)} := by
  let eta := mainLearningRate d T (Nat.choose d m) delta
  let theta := parametersOnActions (ellipsoidAlgorithmParameters eta T) L
  have hd : (1 : ℝ) ≤ d := by exact_mod_cast (show 1 ≤ d by omega)
  have hTr : (1 : ℝ) ≤ T := by exact_mod_cast hT
  have hK : (2 : ℝ) ≤ Nat.choose d m := by exact_mod_cast action_count_ge_two hmpos hmtop
  obtain ⟨heta, hsmall, hlam, hlamhalf, _⟩ :=
    mainLearningRate_parameter_constraints hd hTr hK hdelta0 hdelta1.le
  have hinv := ellipsoid_algorithm_invariant L hmpos hmtop T hT heta
    (mainLearningRate_le_cap _ _ _ _)
  have hlev := adaptive_leverage_high_probability theta hmpos hmtop T hlam
    (fun t ht h i ↦ ((hinv t (by omega) h).1 i).1)
    (fun t ht h i ↦ ((hinv t (by omega) h).1 i).2)
    (show 0 < delta / 2 by positivity) (show delta / 2 ≤ 1 by linarith)
  apply hlev.trans
  apply (weightedBranchingLaw theta (show m ≤ d by omega)).probability_mono
  intro h hh
  have hphi := main_leverage_simplification (show (0 : ℝ) < d by linarith)
    heta hsmall hdelta0 hdelta1.le hh
  have hmoment := pathSum_mono_upto
    (fun t h a ↦ 2 * eta * adaptiveSurrogateSecondMoment theta (lossesOnActions L) eta t h a)
    (fun t h a ↦ 4 * eta * adaptivePhi theta t h a + 3 * eta ^ 2 * ((d : ℝ) + 1)) T
    (fun t ht h a ↦ scaled_surrogate_secondMoment_le (theta t h) (lossesOnActions L t h)
      hmpos hmtop heta hsmall (fun i ↦ ((hinv t (by omega) h).1 i).1)
      (fun i ↦ ((hinv t (by omega) h).1 i).2) a
      (L.action_abs_le_one t (historyOfActions L t h) a)) h
  rw [pathSum_mul, pathSum_add, pathSum_mul, pathSum_const] at hmoment
  have hmoment' : 2 * eta * pathSum (adaptiveSurrogateSecondMoment theta (lossesOnActions L) eta) T h ≤
      4 * eta * pathSum (adaptivePhi theta) T h + 3 * eta ^ 2 * ((d : ℝ) + 1) * T := by
    nlinarith [hmoment]
  have hb := second_order_on_leverage_event hd hTr hK hdelta0 hdelta1.le hmoment' hphi
  have hthree := second_order_three_terms hd (show (0 : ℝ) ≤ T by positivity) heta
    (by linarith : 128 * eta * d ≤ d) hdelta0 hdelta1.le hmoment' hh
  have hcorr0 : 0 ≤ 4 * eta * ((d : ℝ) + 1) * T := by positivity
  refine ⟨hthree, ?_, ?_⟩
  · linarith [hb.2]
  · intro x
    have he := estimated_loss_before_concentration L hmpos hmtop T hT hdelta0 hdelta1 x h
    dsimp only at he ⊢
    linarith [hb.2]

def observableEstimatedDifference
    (theta : (t : ℕ) → History d m t → Fin d → ℝ)
    (L : SignedLossProcess d m) (q : Action d m → ℝ)
    (t : ℕ) (h : History d m t) (a : Action d m) : ℝ :=
  actionLoss a (L.itemLoss t h) - finiteExpectation q (estimateScalar (theta t h) a (L.itemLoss t h))

/-- The same simultaneous sketch bounds on the actual feedback-history run. -/
theorem algorithm_sketch_estimated_loss_observable
    (L : SignedLossProcess d m) (hmpos : 1 ≤ m) (hmtop : m ≤ d - 1)
    (T : ℕ) (hT : 0 < T) {delta : ℝ} (hdelta0 : 0 < delta) (hdelta1 : delta < 1) :
    let eta := mainLearningRate d T (Nat.choose d m) delta
    let theta := ellipsoidAlgorithmParameters (d := d) (m := m) eta T
    1 - delta / 2 ≤ (signedRunLaw (mainAlgorithm T delta (by omega)) L T).real
      {h | (2 * eta * observablePathSum (observableSurrogateSecondMoment theta L eta) T h ≤
        16 * eta * d * T +
          40 * eta * d / (128 * eta * d) * Real.log (2 / delta) +
          768 * eta ^ 3 * (d : ℝ) ^ 2 * T / (128 * eta * d)) ∧
        (2 * eta * observablePathSum (observableSurrogateSecondMoment theta L eta) T h ≤
          544 * eta * d * T + Real.log (1 / delta)) ∧
        ∀ x : Action d m,
          observablePathSum (observableEstimatedDifference theta L
            (smoothedComparator (128 * eta * d) x)) T h ≤
          Real.log (Nat.choose d m) / eta -
            eta * observablePathSum (observableComparatorV theta
              (fun _ _ ↦ smoothedComparator (128 * eta * d) x)) T h +
            544 * eta * d * T + Real.log (1 / delta)} := by
  dsimp only
  unfold mainAlgorithm
  rw [signedRunLaw_probability_eq_tree_all_sets]
  simp only [Set.mem_setOf_eq, observablePathSum_historyOfActions]
  exact algorithm_sketch_estimated_loss_high_probability L hmpos hmtop T hT hdelta0 hdelta1

end MsetsPaper.Alignment.UpperSketch
