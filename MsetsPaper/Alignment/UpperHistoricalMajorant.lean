import MsetsPaper.Alignment.UpperStructural

/-! The coefficient-two majorant in the attribution footnote of `paper/main.tex`.
These are mathematical identities and bounds, separate from any
claim about the authorship or publication history of the earlier result. -/

noncomputable section
open Matrix MsetsLower MsetsLower.History
open scoped BigOperators

namespace MsetsPaper.Upper

def phiOld {d : ℕ} (mu x : Fin d → ℝ) : ℝ :=
  1 + 2 * ∑ i, (x i - mu i) ^ 2 / (mu i * (1 - mu i))

theorem phiOld_eq_two_phi_sub_one {d : ℕ} (mu x : Fin d → ℝ) :
    phiOld mu x = 2 * phi mu x - 1 := by
  unfold phiOld phi
  ring

theorem one_le_phi {d : ℕ} (mu x : Fin d → ℝ)
    (hmu : ∀ i, 0 < mu i) (hmu1 : ∀ i, mu i < 1) :
    1 ≤ phi mu x := by
  unfold phi
  exact le_add_of_nonneg_right (Finset.sum_nonneg fun i _ ↦
    div_nonneg (sq_nonneg _) (mul_pos (hmu i) (sub_pos.mpr (hmu1 i))).le)

theorem phi_le_phiOld {d : ℕ} (mu x : Fin d → ℝ)
    (hmu : ∀ i, 0 < mu i) (hmu1 : ∀ i, mu i < 1) :
    phi mu x ≤ phiOld mu x := by
  rw [phiOld_eq_two_phi_sub_one]
  linarith [one_le_phi mu x hmu hmu1]

theorem weightedLaw_phiOld_mean {d m : ℕ} (theta : Fin d → ℝ)
    (hmpos : 1 ≤ m) (hmtop : m ≤ d - 1) :
    (∑ a : Action d m, weightedLaw theta a *
      phiOld (weightedMarginal (m := m) theta) (fun i ↦ selectedIndicator i a)) =
        2 * (d : ℝ) + 1 := by
  simp_rw [phiOld_eq_two_phi_sub_one, mul_sub, mul_one]
  rw [Finset.sum_sub_distrib, sum_weightedLaw theta (by omega)]
  have heq : (∑ a : Action d m, weightedLaw theta a *
      (2 * phi (weightedMarginal (m := m) theta) (fun i ↦ selectedIndicator i a))) =
      2 * ∑ a : Action d m, weightedLaw theta a *
        phi (weightedMarginal (m := m) theta) (fun i ↦ selectedIndicator i a) := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro a _
    ring
  rw [heq, weightedLaw_phi_mean theta hmpos hmtop]
  ring

theorem weightedLaw_phiOld_range {d m : ℕ} (theta : Fin d → ℝ)
    (hmpos : 1 ≤ m) (hmtop : m ≤ d - 1) {lam : ℝ} (hlam : 0 < lam)
    (hlo : ∀ i, lam * ((m : ℝ) / d) ≤ weightedMarginal (m := m) theta i)
    (hhi : ∀ i, weightedMarginal (m := m) theta i ≤ 1 - lam * (1 - (m : ℝ) / d))
    (a : Action d m) :
    0 ≤ phiOld (weightedMarginal (m := m) theta) (fun i ↦ selectedIndicator i a) ∧
      phiOld (weightedMarginal (m := m) theta) (fun i ↦ selectedIndicator i a) ≤
        1 + 4 * d / lam := by
  have hlow := one_le_phi (weightedMarginal (m := m) theta)
    (fun i ↦ selectedIndicator i a) (weightedMarginal_pos theta hmpos hmtop)
    (weightedMarginal_lt_one theta hmtop)
  have hu := (weightedLaw_phi_range theta hmpos hmtop hlam hlo hhi a).2
  rw [phiOld_eq_two_phi_sub_one]
  constructor
  · linarith
  · calc
      _ ≤ 2 * (1 + 2 * (d : ℝ) / lam) - 1 := by linarith
      _ = 1 + 4 * d / lam := by ring

end MsetsPaper.Upper

namespace MsetsPaper.Alignment
open MsetsPaper.Upper

/-- Distribution-facing mathematical content of the historical footnote.
The box is P_lambda itself; P_(lambda/2) would instead give 1+8d/lambda. -/
theorem upper_historical_majorant {d m : ℕ} (p : Action d m → ℝ)
    (hweighted : IsWeightedMSetLaw p) (hmpos : 1 ≤ m) (hmtop : m ≤ d - 1)
    {lam : ℝ} (hlam : 0 < lam) (hbox : InPaperMarginalSet p lam) :
    (∑ a : Action d m, p a * phiOld (marginal p) (fun i ↦ selectedIndicator i a)) =
        2 * (d : ℝ) + 1 ∧
    (∀ a : Action d m,
      0 ≤ phiOld (marginal p) (fun i ↦ selectedIndicator i a) ∧
      phiOld (marginal p) (fun i ↦ selectedIndicator i a) ≤ 1 + 4 * d / lam ∧
      (fun i ↦ selectedIndicator i a) ⬝ᵥ
        ((secondMoment p)⁻¹ *ᵥ (fun i ↦ selectedIndicator i a)) ≤
          phiOld (marginal p) (fun i ↦ selectedIndicator i a)) := by
  obtain ⟨theta, rfl⟩ := hweighted
  refine ⟨weightedLaw_phiOld_mean theta hmpos hmtop, ?_⟩
  intro a
  have hr := weightedLaw_phiOld_range theta hmpos hmtop hlam
    (fun i ↦ (hbox i).1) (fun i ↦ (hbox i).2) a
  refine ⟨hr.1, hr.2, (leverage_le_phi theta hmpos hmtop a).trans ?_⟩
  exact phi_le_phiOld _ _ (weightedMarginal_pos theta hmpos hmtop)
    (weightedMarginal_lt_one theta hmtop)

end MsetsPaper.Alignment
