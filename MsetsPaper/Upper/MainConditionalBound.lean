import MsetsPaper.Upper.AdaptiveRegret

/-! # T1 assembled from the projection and marginal invariants

This is deliberately a conditional theorem, not the completed algorithmic
claim: P1 must construct a measurable update and discharge the displayed
projection and marginal premises. All subsequent regret and probability
steps are derived here, with the manuscript's constants.
-/

noncomputable section
open MsetsLower MsetsPaper.Probability
open scoped BigOperators

namespace MsetsPaper.Upper

variable {d m : ℕ}

/-- The displayed combined inequality, before discarding its negative
correction. All inputs are the three preceding displayed inequalities. -/
theorem main_combined_arithmetic {E D S V A B eta n T l : ℝ}
    (hest : E ≤ A / eta + 1 + 4 * eta * S + 3 * eta ^ 2 * n * T +
      4 * eta * n * T - eta * V)
    (hlev : 4 * eta * S ≤ 8 * eta * n * T + l)
    (hconc : D ≤ eta / 4 * V + B / eta) :
    E + D ≤ (A + B) / eta + 1 + 12 * eta * n * T +
      3 * eta ^ 2 * n * T + l - 3 * eta / 4 * V := by
  rw [add_div]
  linarith

theorem main_regret_on_good_event
    (theta ell : (t : ℕ) → ActionTree (Action d m) t → Fin d → ℝ)
    (hmpos : 1 ≤ m) (hmtop : m ≤ d - 1) (T : ℕ) (hT : 0 < T)
    {eta delta : ℝ} (heta : 0 < eta) (hsmall : eta ≤ 1 / 64)
    (hlam : 128 * eta * d ≤ 1) (hzero : theta 0 () = 0)
    (hloss : ∀ t < T, ∀ h (a : Action d m), |actionLoss a (ell t h)| ≤ 1)
    (hlo : ∀ t < T, ∀ h i, (128 * eta * d / 2) * ((m : ℝ) / d) ≤
      weightedMarginal (m := m) (theta t h) i)
    (hhi : ∀ t < T, ∀ h i, weightedMarginal (m := m) (theta t h) i ≤
      1 - (128 * eta * d / 2) * (1 - (m : ℝ) / d))
    (hprojection : ∀ (x : Action d m) t, t < T → ∀ h a,
      finiteKL (smoothedComparator (128 * eta * d) x)
        (weightedLaw (m := m) (theta (t + 1) (h, a))) ≤
      finiteKL (smoothedComparator (128 * eta * d) x)
        (weightedLaw (m := m)
          (theta t h - eta • surrogateVector (theta t h) (ell t h) eta a)) -
      finiteKL (weightedLaw (m := m) (theta (t + 1) (h, a)))
        (weightedLaw (m := m)
          (theta t h - eta • surrogateVector (theta t h) (ell t h) eta a)) + eta / T)
    (h : ActionTree (Action d m) T) (hgood : h ∈ mainGoodEvent theta ell T eta delta) :
    adaptiveRegret ell T h ≤
      (Real.log (Nat.choose d m) + Real.log (4 * (Nat.choose d m : ℝ) / delta)) / eta +
        1 + 286 * eta * d * T + Real.log (2 / delta) := by
  have hd : (1 : ℝ) ≤ d := by exact_mod_cast (show 1 ≤ d by omega)
  have hlam0 : 0 ≤ 128 * eta * d := by positivity
  have heta1 : eta ≤ 1 := by linarith
  apply adaptiveRegret_le_of_forall ell (by omega) T h
  intro x
  let q := smoothedComparator (128 * eta * d) x
  let V := fun t h (_ : Action d m) ↦ comparatorV (theta t h) q
  let e := adaptiveEstimatedDifference theta ell q
  let D := adaptiveComparatorDelta theta (fun _ _ ↦ q) ell
  let g := fun t h (a : Action d m) ↦ actionLoss a (ell t h) - comparatorTrue q (ell t h)
  have hq := smoothedComparator_nonneg hlam0 hlam x
  have hest := adaptive_estimated_regret_le_of_projection theta ell q T hT hmpos hmtop
    eta heta hsmall hq (sum_smoothedComparator _ x) hloss hlo hhi (hprojection x) h
  rw [hzero] at hest
  have hKL := div_le_div_of_nonneg_right
    (smoothedComparator_initialKL_le_log_card hlam0 hlam x) heta.le
  have hlev := hgood.1
  simp only [Set.mem_setOf_eq] at hlev
  have hconc := hgood.2 x
  change pathSum D T h ≤ eta / 4 * pathSum V T h + _ at hconc
  change pathSum e T h ≤ _ at hest
  have hdecomp : pathSum g T h = pathSum e T h + pathSum D T h := by
    rw [← pathSum_add]
    apply pathSum_congr_upto
    intro t ht h a
    dsimp [g, e, D, adaptiveEstimatedDifference, adaptiveComparatorDelta,
      comparatorDelta, comparatorEstimate]
    ring
  have hv : 0 ≤ pathSum V T h := by
    have hp := pathSum_mono_upto (fun _ _ _ ↦ (0 : ℝ)) V T
      (fun t _ h _ ↦ comparatorV_nonneg (theta t h) q hq hmpos hmtop) h
    simpa only [pathSum_const, mul_zero] using hp
  have hnegative : 0 ≤ 3 * eta / 4 * pathSum V T h := by positivity
  have hquad : 3 * eta ^ 2 * ((d : ℝ) + 1) * T ≤
      3 * eta * ((d : ℝ) + 1) * T := by
    have he : eta ^ 2 ≤ eta := by nlinarith
    have hp := mul_le_mul_of_nonneg_right he (show 0 ≤ 3 * ((d : ℝ) + 1) * T by positivity)
    nlinarith
  have hsmoothed : pathSum g T h ≤
      (Real.log (Nat.choose d m) + Real.log (4 * (Nat.choose d m : ℝ) / delta)) / eta +
        1 + 15 * eta * ((d : ℝ) + 1) * T + Real.log (2 / delta) := by
    change pathSum e T h ≤ finiteKL q _ / eta + 1 +
      4 * eta * pathSum (adaptivePhi theta) T h + 3 * eta ^ 2 * ((d : ℝ) + 1) * T +
      4 * eta * ((d : ℝ) + 1) * T - eta * pathSum V T h at hest
    change finiteKL q _ / eta ≤ _ at hKL
    have hest' : pathSum e T h ≤ Real.log (Nat.choose d m) / eta + 1 +
        4 * eta * pathSum (adaptivePhi theta) T h + 3 * eta ^ 2 * ((d : ℝ) + 1) * T +
        4 * eta * ((d : ℝ) + 1) * T - eta * pathSum V T h := by linarith
    have hcombined := main_combined_arithmetic hest' hlev hconc
    rw [hdecomp]
    linarith
  have hpure := adaptive_smoothed_to_pure ell T hlam0 hloss x h
  have hdim : 15 * eta * ((d : ℝ) + 1) * T + 2 * (128 * eta * d) * T ≤
      286 * eta * d * T := by
    have hp := mul_le_mul_of_nonneg_right (show (d : ℝ) + 1 ≤ 2 * d by linarith)
      (show 0 ≤ 15 * eta * T by positivity)
    nlinarith
  change _ ≤ pathSum g T h + _ at hpure
  linarith

theorem main_regret_high_probability_of_projection
    (theta ell : (t : ℕ) → ActionTree (Action d m) t → Fin d → ℝ)
    (hmpos : 1 ≤ m) (hmtop : m ≤ d - 1) (T : ℕ) (hT : 0 < T)
    {delta : ℝ} (hdelta0 : 0 < delta) (hdelta1 : delta ≤ 1)
    (hzero : theta 0 () = 0)
    (hloss : ∀ t < T, ∀ h (a : Action d m), |actionLoss a (ell t h)| ≤ 1)
    (hlo : ∀ t < T, ∀ h i,
      (128 * mainLearningRate d T (Nat.choose d m) delta * d / 2) * ((m : ℝ) / d) ≤
      weightedMarginal (m := m) (theta t h) i)
    (hhi : ∀ t < T, ∀ h i, weightedMarginal (m := m) (theta t h) i ≤
      1 - (128 * mainLearningRate d T (Nat.choose d m) delta * d / 2) * (1 - (m : ℝ) / d))
    (hprojection : ∀ (x : Action d m) t, t < T → ∀ h a,
      let eta := mainLearningRate d T (Nat.choose d m) delta
      finiteKL (smoothedComparator (128 * eta * d) x)
        (weightedLaw (m := m) (theta (t + 1) (h, a))) ≤
      finiteKL (smoothedComparator (128 * eta * d) x)
        (weightedLaw (m := m)
          (theta t h - eta • surrogateVector (theta t h) (ell t h) eta a)) -
      finiteKL (weightedLaw (m := m) (theta (t + 1) (h, a)))
        (weightedLaw (m := m)
          (theta t h - eta • surrogateVector (theta t h) (ell t h) eta a)) + eta / T) :
    1 - delta ≤ (weightedBranchingLaw theta (by omega)).probability T
      {h | adaptiveRegret ell T h ≤
        160 * Real.sqrt ((d : ℝ) * T * (Real.log (Nat.choose d m) + Real.log (1 / delta)))} := by
  let eta := mainLearningRate d T (Nat.choose d m) delta
  have hd : (1 : ℝ) ≤ d := by exact_mod_cast (show 1 ≤ d by omega)
  have hTr : (1 : ℝ) ≤ T := by exact_mod_cast hT
  have hK : (2 : ℝ) ≤ Nat.choose d m := by exact_mod_cast action_count_ge_two hmpos hmtop
  obtain ⟨heta, hsmall, hlam0, hlam, heps⟩ :=
    mainLearningRate_parameter_constraints hd hTr hK hdelta0 hdelta1
  have hprob := main_good_event_probability theta ell hmpos hmtop T heta hsmall
    (show 128 * eta * d ≤ 1 by dsimp [eta]; linarith) hdelta0 hdelta1 hlo hhi hloss
  apply hprob.trans
  apply BranchingLaw.probability_mono
  intro h hh
  have hraw := main_regret_on_good_event theta ell hmpos hmtop T hT heta hsmall
    (show 128 * eta * d ≤ 1 by dsimp [eta]; linarith) hzero hloss hlo hhi hprojection h hh
  have hmaster := main_master_simplification (by positivity : (0 : ℝ) ≤ d)
    (by positivity : (0 : ℝ) ≤ T) hK hdelta0 hdelta1 heta
    (show eta ≤ 1 by dsimp [eta]; linarith) hraw
  exact mainLearningRate_regret_constant (by linarith) (by linarith) hK hdelta0 hdelta1
    (adaptiveRegret_trivial ell (by omega) T hloss h) hmaster

end MsetsPaper.Upper
