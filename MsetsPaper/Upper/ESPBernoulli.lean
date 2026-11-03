import MsetsPaper.Upper.ESPAlgorithms

/-! # Conditioning the product Bernoulli masses on exact cardinality -/

noncomputable section
open scoped BigOperators

namespace MsetsPaper.Upper

variable {d m : ℕ}

/-- Product of the coordinate Bernoulli probabilities, with odds w_i. -/
def bernoulliSubsetMass (w : Fin d → ℝ) (S : Finset (Fin d)) : ℝ :=
  ∏ i, if i ∈ S then w i / (1 + w i) else 1 / (1 + w i)

theorem bernoulliSubsetMass_factor (w : Fin d → ℝ) (S : Finset (Fin d)) :
    bernoulliSubsetMass w S = (∏ i ∈ S, w i) / ∏ i, (1 + w i) := by
  unfold bernoulliSubsetMass
  have h (i : Fin d) : (if i ∈ S then w i / (1 + w i) else 1 / (1 + w i)) =
      (if i ∈ S then w i else 1) / (1 + w i) := by split_ifs <;> rfl
  simp_rw [h]
  rw [Finset.prod_div_distrib]
  simp

theorem bernoulliSubsetMass_nonneg (w : Fin d → ℝ) (hw : ∀ i, 0 < w i)
    (S : Finset (Fin d)) : 0 ≤ bernoulliSubsetMass w S := by
  rw [bernoulliSubsetMass_factor]
  exact div_nonneg (Finset.prod_nonneg fun i _ => (hw i).le)
    (Finset.prod_nonneg fun i _ => by linarith [hw i])

theorem sum_bernoulliSubsetMass (w : Fin d → ℝ) (hw : ∀ i, 0 < w i) :
    ∑ S : Finset (Fin d), bernoulliSubsetMass w S = 1 := by
  simp_rw [bernoulliSubsetMass_factor]
  rw [← Finset.sum_div]
  have hz : (∏ i, (1 + w i)) ≠ 0 :=
    ne_of_gt (Finset.prod_pos fun i _ => by linarith [hw i])
  have hs : (∑ S : Finset (Fin d), ∏ i ∈ S, w i) = ∏ i, (1 + w i) := by
    simpa [add_comm] using (Finset.prod_add w (fun _ => (1 : ℝ)) Finset.univ).symm
  rw [hs, div_self hz]

/-- Conditioning the normalized product mass on the rank event gives the
actual exponential law, not an abstract weighted-law assumption. -/
theorem conditionalBernoulli_eq_weightedLaw (theta : Fin d → ℝ) (a : Action d m) :
    bernoulliSubsetMass (fun i => Real.exp (theta i)) a.val /
      (∑ b : Action d m, bernoulliSubsetMass (fun i => Real.exp (theta i)) b.val) =
        weightedLaw theta a := by
  simp_rw [bernoulliSubsetMass_factor]
  rw [← Finset.sum_div, weightedLaw_product_form]
  have hz : (∏ i, (1 + Real.exp (theta i))) ≠ 0 :=
    ne_of_gt (Finset.prod_pos fun i _ => by linarith [Real.exp_pos (theta i)])
  exact div_div_div_cancel_right₀ hz _ _

end MsetsPaper.Upper
