import MsetsPaper.Probability.FinitePotential
import MsetsPaper.Upper.OMD

/-!
# L4 on actual action-prefix dependent parameters

This is the same KL telescoping, now indexed by a whole realized adaptive
path. P1 must supply the explicitly stated projection and marginal invariants.
-/

noncomputable section

open MsetsLower MsetsPaper.Probability
open scoped BigOperators

namespace MsetsPaper.Upper

variable {d m : ℕ}

def adaptiveSurrogateDifference
    (theta ell : (t : ℕ) → ActionTree (Action d m) t → Fin d → ℝ)
    (eta : ℝ) (q : Action d m → ℝ)
    (t : ℕ) (h : ActionTree (Action d m) t) (a : Action d m) : ℝ :=
  finiteExpectation (weightedLaw (theta t h)) (surrogate (theta t h) (ell t h) eta a) -
    finiteExpectation q (surrogate (theta t h) (ell t h) eta a)

def adaptiveSurrogateSecondMoment
    (theta ell : (t : ℕ) → ActionTree (Action d m) t → Fin d → ℝ)
    (eta : ℝ) (t : ℕ) (h : ActionTree (Action d m) t) (a : Action d m) : ℝ :=
  finiteExpectation (weightedLaw (theta t h)) (fun b ↦ (surrogate (theta t h) (ell t h) eta a b) ^ 2)

theorem adaptive_omd_stability_of_projection
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
    pathSum (adaptiveSurrogateDifference theta ell eta q) T h ≤
      finiteKL q (weightedLaw (m := m) (theta 0 ())) / eta + 1 +
        2 * eta * pathSum (adaptiveSurrogateSecondMoment theta ell eta) T h := by
  let g := adaptiveSurrogateDifference theta ell eta q
  let z := adaptiveSurrogateSecondMoment theta ell eta
  let V := fun t h ↦ finiteKL q (weightedLaw (m := m) (theta t h))
  have hstep : ∀ t < T, ∀ h a, eta * g t h a ≤
      V t h - V (t + 1) (h, a) + (2 * eta ^ 2 * z t h a + eta / (T : ℝ)) := by
    intro t ht h a
    rw [← add_assoc]
    apply omd_one_step q (weightedLaw (theta t h))
      (weightedLaw (theta (t + 1) (h, a))) (surrogate (theta t h) (ell t h) eta a)
      eta (eta / (T : ℝ)) hqsum
      (weightedLaw_pos _ (by omega)) (sum_weightedLaw _ (by omega))
      (weightedLaw_pos _ (by omega)) (sum_weightedLaw _ (by omega))
    · intro b
      rw [abs_mul, abs_of_pos heta]
      exact bounded_increments (theta t h) (ell t h) hmpos hmtop heta hsmall
        (hloss t ht h) (hlo t ht h) (hhi t ht h) a b
    · simpa only [mwUpdate_surrogate_weightedLaw _ _ _ (show m ≤ d by omega)] using
        hprojection t ht h a
  have hsum := pathSum_le_potential_drop (fun t h a ↦ eta * g t h a)
    (fun t h a ↦ 2 * eta ^ 2 * z t h a + eta / (T : ℝ)) V T hstep h
  rw [pathSum_mul, pathSum_add, pathSum_mul, pathSum_const] at hsum
  have hTne : (T : ℝ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt hT)
  have hcancel : (T : ℝ) * (eta / (T : ℝ)) = eta := by field_simp
  rw [hcancel] at hsum
  have hlast : 0 ≤ V T h := finiteKL_nonneg q _ hq hqsum
    (weightedLaw_pos _ (by omega)) (sum_weightedLaw _ (by omega))
  have hdiv : eta * (finiteKL q (weightedLaw (m := m) (theta 0 ())) / eta) =
      finiteKL q (weightedLaw (m := m) (theta 0 ())) := by field_simp
  dsimp [V] at hsum hlast
  change pathSum g T h ≤ _
  apply (mul_le_mul_iff_right₀ heta).mp
  nlinarith

end MsetsPaper.Upper
