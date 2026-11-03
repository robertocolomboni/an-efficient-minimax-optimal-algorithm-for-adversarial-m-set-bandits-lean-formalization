import MsetsPaper.Upper.AdaptiveOMD
import MsetsPaper.Upper.MainEstimatedRegret
import MsetsPaper.Upper.AdaptiveConcentration

/-! # T1's estimated-loss bound along a genuinely adaptive action prefix -/

noncomputable section
open MsetsLower MsetsPaper.Probability
open scoped BigOperators

namespace MsetsPaper.Upper

variable {d m : ℕ}

def adaptiveEstimatedDifference
    (theta ell : (t : ℕ) → ActionTree (Action d m) t → Fin d → ℝ)
    (q : Action d m → ℝ) (t : ℕ) (h : ActionTree (Action d m) t) (a : Action d m) : ℝ :=
  actionLoss a (ell t h) - finiteExpectation q (estimateScalar (theta t h) a (ell t h))

theorem adaptive_estimated_regret_le_of_projection
    (theta ell : (t : ℕ) → ActionTree (Action d m) t → Fin d → ℝ)
    (q : Action d m → ℝ) (T : ℕ) (hT : 0 < T)
    (hmpos : 1 ≤ m) (hmtop : m ≤ d - 1)
    (eta : ℝ) (heta : 0 < eta) (hsmall : eta ≤ 1 / 64)
    (hq : ∀ b, 0 ≤ q b) (hqsum : ∑ b, q b = 1)
    (hloss : ∀ t < T, ∀ h (b : Action d m), |actionLoss b (ell t h)| ≤ 1)
    (hlo : ∀ t < T, ∀ h i, (128 * eta * d / 2) * ((m : ℝ) / d) ≤
      weightedMarginal (m := m) (theta t h) i)
    (hhi : ∀ t < T, ∀ h i, weightedMarginal (m := m) (theta t h) i ≤
      1 - (128 * eta * d / 2) * (1 - (m : ℝ) / d))
    (hprojection : ∀ t < T, ∀ h a,
      finiteKL q (weightedLaw (m := m) (theta (t + 1) (h, a))) ≤
        finiteKL q (weightedLaw (m := m)
          (theta t h - eta • surrogateVector (theta t h) (ell t h) eta a)) -
        finiteKL (weightedLaw (m := m) (theta (t + 1) (h, a)))
          (weightedLaw (m := m) (theta t h - eta • surrogateVector (theta t h) (ell t h) eta a)) +
        eta / (T : ℝ)) (h : ActionTree (Action d m) T) :
    pathSum (adaptiveEstimatedDifference theta ell q) T h ≤
      finiteKL q (weightedLaw (m := m) (theta 0 ())) / eta + 1 +
        4 * eta * pathSum (adaptivePhi theta) T h + 3 * eta ^ 2 * ((d : ℝ) + 1) * T +
        4 * eta * ((d : ℝ) + 1) * T -
        eta * pathSum (fun t h (_ : Action d m) ↦ comparatorV (theta t h) q) T h := by
  let g := adaptiveSurrogateDifference theta ell eta q
  let z := adaptiveSurrogateSecondMoment theta ell eta
  let e := adaptiveEstimatedDifference theta ell q
  let C := fun t h (_ : Action d m) ↦ comparatorV (theta t h) q
  have homd := adaptive_omd_stability_of_projection theta ell q T hT hmpos hmtop
    eta heta hsmall hq hqsum hloss hlo hhi hprojection h
  have hpoint : ∀ t < T, ∀ h a, g t h a =
      (e t h a - 4 * eta * ((d : ℝ) + 1)) + eta * C t h a := by
    intro t ht h a
    dsimp [g, adaptiveSurrogateDifference]
    rw [mean_learner_surrogate _ _ _ hmpos hmtop, mean_surrogate]
    dsimp [e, adaptiveEstimatedDifference, C]
    ring
  have hleft := pathSum_congr_upto g
    (fun t h a ↦ (e t h a - 4 * eta * ((d : ℝ) + 1)) + eta * C t h a) T hpoint h
  rw [pathSum_add, pathSum_sub, pathSum_const, pathSum_mul] at hleft
  have hsecond := pathSum_mono_upto (fun t h a ↦ 2 * eta * z t h a)
    (fun t h a ↦ 4 * eta * adaptivePhi theta t h a + 3 * eta ^ 2 * ((d : ℝ) + 1)) T
    (fun t ht h a ↦ scaled_surrogate_secondMoment_le (theta t h) (ell t h) hmpos hmtop
      heta hsmall (hlo t ht h) (hhi t ht h) a (hloss t ht h a)) h
  rw [pathSum_mul, pathSum_add, pathSum_mul, pathSum_const] at hsecond
  change pathSum g T h ≤ _ at homd
  rw [hleft] at homd
  change pathSum e T h ≤ _
  change 2 * eta * pathSum (adaptiveSurrogateSecondMoment theta ell eta) T h ≤ _ at hsecond
  dsimp [C] at homd
  linarith

end MsetsPaper.Upper
