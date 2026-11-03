import MsetsPaper.Alignment.UpperHistoricalMajorant
import MsetsPaper.Alignment.UpperAuditComparators
import Mathlib.Data.Nat.Choose.Central

/-! Small standalone mathematical claims in the setting and techniques prose.
The exponential-support example is an explicit finite bound, not a claim
about the bit complexity of representing real-valued parameters. -/

noncomputable section
open MsetsLower MsetsLower.History MsetsPaper.Upper
open scoped BigOperators
namespace MsetsPaper.Alignment

theorem marginal_diracWeights {d m : ℕ} (a : Action d m) (i : Fin d) :
    marginal (diracWeights a) i = selectedIndicator i a := by
  classical
  simp [marginal, diracWeights]

theorem dirac_not_inPaperMarginalSet {d m : ℕ} (a : Action d m)
    (hmpos : 1 ≤ m) (hmtop : m ≤ d - 1) {lam : ℝ} (hlam : 0 < lam) :
    ¬ InPaperMarginalSet (diracWeights a) lam := by
  intro hbox
  have hcard : 0 < a.val.card := by rw [a.property]; omega
  obtain ⟨i, hi⟩ := Finset.card_pos.mp hcard
  have hmR : (m : ℝ) < d := by exact_mod_cast (show m < d by omega)
  have hdR : (0 : ℝ) < d := by exact_mod_cast (show 0 < d by omega)
  have hpos : 0 < lam * (1 - (m : ℝ) / d) :=
    mul_pos hlam (sub_pos.mpr ((div_lt_one hdR).mpr hmR))
  have hu := (hbox i).2
  rw [marginal_diracWeights] at hu
  simp only [selectedIndicator, if_pos hi] at hu
  linarith

/-- At d=2n and m=n every finite parameter vector assigns positive mass to
at least 4^n/(2n+1) actions; the parameters still have only 2n coordinates. -/
theorem weighted_support_exponential (n : ℕ) (theta : Fin (2 * n) → ℝ) :
    4 ^ n ≤ (2 * n + 1) *
      ((Finset.univ : Finset (Action (2 * n) n)).filter
        (fun a ↦ 0 < weightedLaw theta a)).card := by
  classical
  have heq : ((Finset.univ : Finset (Action (2 * n) n)).filter
      (fun a ↦ 0 < weightedLaw theta a)) = Finset.univ := by
    apply Finset.filter_eq_self.mpr
    intro a _
    exact weightedLaw_pos theta (by omega) a
  rw [heq, Finset.card_univ, card_MSetAction]
  exact Nat.four_pow_le_two_mul_add_one_mul_centralBinom n

end MsetsPaper.Alignment
