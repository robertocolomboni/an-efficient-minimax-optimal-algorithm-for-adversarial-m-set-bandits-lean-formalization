import MsetsPaper.Upper.AdaptiveConcentration
import MsetsPaper.Upper.SmoothedComparator
import MsetsPaper.Upper.MainParameters

/-! # T1: simultaneous comparator concentration and the leverage event

The event is uniform over all actual m-sets, hence also covers an action
chosen in hindsight. No probability estimate for that random choice is
assumed. Projection invariants remain explicit upstream obligations.
-/

noncomputable section
open MsetsLower MsetsPaper.Probability
open scoped BigOperators

namespace MsetsPaper.Upper

variable {d m : ℕ}

def mainGoodEvent
    (theta ell : (t : ℕ) → ActionTree (Action d m) t → Fin d → ℝ)
    (T : ℕ) (eta delta : ℝ) : Set (ActionTree (Action d m) T) :=
  {h | 4 * eta * pathSum (adaptivePhi theta) T h ≤
        8 * eta * ((d : ℝ) + 1) * T + Real.log (2 / delta)} ∩
  {h | ∀ x : Action d m,
    pathSum (adaptiveComparatorDelta theta
      (fun _ _ ↦ smoothedComparator (128 * eta * d) x) ell) T h ≤
    eta / 4 * pathSum (fun t h _ ↦ comparatorV (theta t h)
      (smoothedComparator (128 * eta * d) x)) T h +
      Real.log (4 * (Nat.choose d m : ℝ) / delta) / eta}

theorem main_leverage_simplification {d eta delta S : ℝ} {T : ℕ}
    (hd : 0 < d) (heta : 0 < eta) (hsmall : eta ≤ 1 / 64)
    (hdelta0 : 0 < delta) (hdelta1 : delta ≤ 1)
    (hS : S ≤ 2 * (d + 1) * T +
      2 * (1 + 4 * d / (128 * eta * d)) * Real.log (1 / (delta / 2))) :
    4 * eta * S ≤ 8 * eta * (d + 1) * T + Real.log (2 / delta) := by
  have hlog : 0 ≤ Real.log (2 / delta) := by
    apply Real.log_nonneg
    apply (le_div_iff₀ hdelta0).mpr
    linarith
  have hr : 1 / (delta / 2) = 2 / delta := by ring
  rw [hr] at hS
  have hid : 4 * eta * (2 * (1 + 4 * d / (128 * eta * d))) =
      8 * eta + 1 / 4 := by field_simp; ring
  have h := mul_le_mul_of_nonneg_left hS (show 0 ≤ 4 * eta by positivity)
  rw [mul_add, ← mul_assoc (4 * eta) (2 * (1 + 4 * d / (128 * eta * d))), hid] at h
  have hcoeff : 8 * eta + 1 / 4 ≤ 1 := by linarith
  have hprod := mul_le_mul_of_nonneg_right hcoeff hlog
  nlinarith

theorem main_good_event_probability
    (theta ell : (t : ℕ) → ActionTree (Action d m) t → Fin d → ℝ)
    (hmpos : 1 ≤ m) (hmtop : m ≤ d - 1) (T : ℕ)
    {eta delta : ℝ} (heta : 0 < eta) (hsmall : eta ≤ 1 / 64)
    (hlam : 128 * eta * d ≤ 1) (hdelta0 : 0 < delta) (hdelta1 : delta ≤ 1)
    (hlo : ∀ t < T, ∀ h i, (128 * eta * d / 2) * ((m : ℝ) / d) ≤
      weightedMarginal (m := m) (theta t h) i)
    (hhi : ∀ t < T, ∀ h i, weightedMarginal (m := m) (theta t h) i ≤
      1 - (128 * eta * d / 2) * (1 - (m : ℝ) / d))
    (hloss : ∀ t < T, ∀ h (a : Action d m), |actionLoss a (ell t h)| ≤ 1) :
    1 - delta ≤ (weightedBranchingLaw theta (by omega)).probability T
      (mainGoodEvent theta ell T eta delta) := by
  classical
  let P := weightedBranchingLaw theta (show m ≤ d by omega)
  have hd : (0 : ℝ) < d := by exact_mod_cast (show 0 < d by omega)
  have hK : (0 : ℝ) < Nat.choose d m := by
    exact_mod_cast Nat.choose_pos (show m ≤ d by omega)
  have hlam0 : 0 < 128 * eta * d := by positivity
  have hlev := adaptive_leverage_high_probability theta hmpos hmtop T
    hlam0 hlo hhi (show 0 < delta / 2 by positivity) (show delta / 2 ≤ 1 by linarith)
  have hlev' : 1 - delta / 2 ≤ P.probability T
      {h | 4 * eta * pathSum (adaptivePhi theta) T h ≤
        8 * eta * ((d : ℝ) + 1) * T + Real.log (2 / delta)} := by
    apply hlev.trans
    apply P.probability_mono
    intro h hh
    exact main_leverage_simplification hd heta hsmall hdelta0 hdelta1 hh
  let E := fun x : Action d m ↦ {h : ActionTree (Action d m) T |
    pathSum (adaptiveComparatorDelta theta
      (fun _ _ ↦ smoothedComparator (128 * eta * d) x) ell) T h ≤
    eta / 4 * pathSum (fun t h _ ↦ comparatorV (theta t h)
      (smoothedComparator (128 * eta * d) x)) T h +
      Real.log (4 * (Nat.choose d m : ℝ) / delta) / eta}
  have heach : ∀ x, 1 - delta / (2 * (Nat.choose d m : ℝ)) ≤ P.probability T (E x) := by
    intro x
    have hc := adaptive_comparator_high_probability theta
      (fun _ _ ↦ smoothedComparator (128 * eta * d) x) ell hmpos hmtop T heta hsmall
      (fun _ _ _ b ↦ smoothedComparator_nonneg hlam0.le hlam x b)
      (fun _ _ _ ↦ sum_smoothedComparator _ x) hlo hhi hloss
      (show 0 < delta / (2 * (Nat.choose d m : ℝ)) by positivity)
    apply hc.trans
    apply P.probability_mono
    intro h hh
    have hlog : 2 / (delta / (2 * (Nat.choose d m : ℝ))) =
        4 * (Nat.choose d m : ℝ) / delta := by field_simp; ring
    simp only [Set.mem_setOf_eq] at hh
    have hb := (le_abs_self _).trans hh
    simpa only [hlog, adaptiveComparatorV, E, Set.mem_setOf_eq] using hb
  have hall := P.probability_forall_ge_of_each T E
    (fun _ ↦ delta / (2 * (Nat.choose d m : ℝ))) heach
  have hsum : (∑ _ : Action d m, delta / (2 * (Nat.choose d m : ℝ))) = delta / 2 := by
    simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, card_MSetAction]
    field_simp
  rw [hsum] at hall
  have hinter := P.probability_inter_ge T _ _ hlev' hall
  simpa only [mainGoodEvent, E, Set.mem_setOf_eq, add_halves] using hinter

end MsetsPaper.Upper
