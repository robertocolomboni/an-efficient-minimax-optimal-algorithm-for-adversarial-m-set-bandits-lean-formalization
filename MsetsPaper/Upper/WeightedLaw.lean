import MsetsPaper.Upper.SecondMoment
import MsetsPaper.Upper.Majorant
import Mathlib.Analysis.SpecialFunctions.Exp

/-!
# The concrete exponential fixed-cardinality law

The normalizing constant, full support, and strict marginal bounds are proved
from the finite action space.  The majorant identities are then instantiated
on this actual law; none of their conclusions is supplied as an input.
-/

noncomputable section

open scoped BigOperators
open Matrix MsetsLower MsetsLower.History

namespace MsetsPaper.Upper

variable {d m : ℕ}

/-- The finite partition function of the weighted m-set distribution. -/
def partition (theta : Fin d → ℝ) : ℝ :=
  ∑ a : Action d m, Real.exp (actionLoss a theta)

/-- The actual distribution used by the algorithm, represented by d parameters. -/
def weightedLaw (theta : Fin d → ℝ) (a : Action d m) : ℝ :=
  Real.exp (actionLoss a theta) / partition (m := m) theta

/-- Actual inclusion marginals, not independent Bernoulli parameters. -/
def weightedMarginal (theta : Fin d → ℝ) : Fin d → ℝ :=
  marginal (weightedLaw (m := m) theta)

theorem partition_pos (theta : Fin d → ℝ) (hmd : m ≤ d) :
    0 < partition (m := m) theta := by
  classical
  obtain ⟨a⟩ := nonempty_MSetAction hmd
  apply Finset.sum_pos'
  · intro b _
    exact (Real.exp_pos _).le
  · exact ⟨a, Finset.mem_univ _, Real.exp_pos _⟩

theorem weightedLaw_pos (theta : Fin d → ℝ) (hmd : m ≤ d) (a : Action d m) :
    0 < weightedLaw theta a :=
  div_pos (Real.exp_pos _) (partition_pos theta hmd)

theorem sum_weightedLaw (theta : Fin d → ℝ) (hmd : m ≤ d) :
    ∑ a : Action d m, weightedLaw theta a = 1 := by
  classical
  unfold weightedLaw
  rw [← Finset.sum_div]
  exact div_self (ne_of_gt (partition_pos theta hmd))

/-- Exponential parameters give exactly the product-of-positive-weights law. -/
theorem weightedLaw_product_form (theta : Fin d → ℝ) (a : Action d m) :
    weightedLaw theta a =
      (∏ i ∈ a.val, Real.exp (theta i)) /
        (∑ b : Action d m, ∏ i ∈ b.val, Real.exp (theta i)) := by
  classical
  simp only [weightedLaw, partition, actionLoss_eq_finset_sum, Real.exp_sum]

theorem selectedIndicator_binary (i : Fin d) (a : Action d m) :
    selectedIndicator i a = 0 ∨ selectedIndicator i a = 1 := by
  classical
  by_cases hi : i ∈ a.val <;> simp [selectedIndicator, hi]

/-- Every item can occur in an action when the requested rank is positive. -/
theorem exists_action_mem (hmpos : 1 ≤ m) (hmd : m ≤ d) (i : Fin d) :
    ∃ a : Action d m, i ∈ a.val := by
  classical
  have hcard : ((Finset.univ : Finset (Fin d)).erase i).card = d - 1 := by
    simp [Finset.card_erase_of_mem]
  obtain ⟨A, hA, hAc⟩ := Finset.exists_subset_card_eq
    (show m - 1 ≤ ((Finset.univ : Finset (Fin d)).erase i).card by rw [hcard]; omega)
  have hi : i ∉ A := by
    intro hh
    have := hA hh
    simp at this
  refine ⟨⟨insert i A, ?_⟩, by simp⟩
  rw [Finset.card_insert_of_notMem hi, hAc]
  omega

/-- Every item can be omitted at each non-top rank. -/
theorem exists_action_not_mem (hmtop : m ≤ d - 1) (i : Fin d) :
    ∃ a : Action d m, i ∉ a.val := by
  classical
  have hcard : ((Finset.univ : Finset (Fin d)).erase i).card = d - 1 := by
    simp [Finset.card_erase_of_mem]
  obtain ⟨A, hA, hAc⟩ := Finset.exists_subset_card_eq
    (show m ≤ ((Finset.univ : Finset (Fin d)).erase i).card by rw [hcard]; exact hmtop)
  refine ⟨⟨A, hAc⟩, ?_⟩
  intro hi
  have := hA hi
  simp at this

theorem marginal_pos_of_fullSupport (p : Action d m → ℝ) (hp : ∀ a, 0 < p a)
    (hmpos : 1 ≤ m) (hmd : m ≤ d) (i : Fin d) : 0 < marginal p i := by
  classical
  obtain ⟨a, ha⟩ := exists_action_mem hmpos hmd i
  unfold marginal
  apply Finset.sum_pos'
  · intro b _
    exact mul_nonneg (hp b).le (selectedIndicator_mem_Icc i b).1
  · refine ⟨a, Finset.mem_univ _, ?_⟩
    simpa [selectedIndicator, ha] using hp a

theorem marginal_lt_one_of_fullSupport (p : Action d m → ℝ) (hp : ∀ a, 0 < p a)
    (hsum : ∑ a, p a = 1) (hmtop : m ≤ d - 1) (i : Fin d) : marginal p i < 1 := by
  classical
  obtain ⟨a, ha⟩ := exists_action_not_mem hmtop i
  have hc : 0 < ∑ b : Action d m, p b * (1 - selectedIndicator i b) := by
    apply Finset.sum_pos'
    · intro b _
      exact mul_nonneg (hp b).le (sub_nonneg.mpr (selectedIndicator_mem_Icc i b).2)
    · refine ⟨a, Finset.mem_univ _, ?_⟩
      simpa [selectedIndicator, ha] using hp a
  have heq : (∑ b : Action d m, p b * (1 - selectedIndicator i b)) =
      1 - marginal p i := by
    simp [mul_sub, Finset.sum_sub_distrib, hsum, marginal]
  rw [heq] at hc
  exact sub_pos.mp hc

theorem weightedMarginal_pos (theta : Fin d → ℝ) (hmpos : 1 ≤ m)
    (hmtop : m ≤ d - 1) (i : Fin d) : 0 < weightedMarginal (m := m) theta i :=
  marginal_pos_of_fullSupport (weightedLaw theta)
    (weightedLaw_pos theta (by omega)) hmpos (by omega) i

theorem weightedMarginal_lt_one (theta : Fin d → ℝ)
    (hmtop : m ≤ d - 1) (i : Fin d) : weightedMarginal (m := m) theta i < 1 :=
  marginal_lt_one_of_fullSupport (weightedLaw theta)
    (weightedLaw_pos theta (by omega)) (sum_weightedLaw theta (by omega)) hmtop i

theorem sum_weightedMarginal (theta : Fin d → ℝ) (hmd : m ≤ d) :
    ∑ i, weightedMarginal (m := m) theta i = (m : ℝ) :=
  sum_marginal (weightedLaw theta) (sum_weightedLaw theta hmd)

/-- Concrete affine correction identity for each actual action. -/
theorem weightedLaw_correction_dot (theta : Fin d → ℝ) (hmpos : 1 ≤ m)
    (hmtop : m ≤ d - 1) (a : Action d m) :
    ∑ i, correction (m : ℝ) (weightedMarginal (m := m) theta) i * selectedIndicator i a =
      4 * phi (weightedMarginal (m := m) theta) (fun i => selectedIndicator i a) := by
  apply correction_dot (m : ℝ) (by exact_mod_cast (show m ≠ 0 by omega))
  · exact weightedMarginal_pos theta hmpos hmtop
  · exact weightedMarginal_lt_one theta hmtop
  · intro i
    exact selectedIndicator_binary i a
  · exact sum_selectedIndicator a

/-- The exact mean d+1 under the normalized exponential law. -/
theorem weightedLaw_phi_mean (theta : Fin d → ℝ) (hmpos : 1 ≤ m)
    (hmtop : m ≤ d - 1) :
    ∑ a : Action d m, weightedLaw theta a *
      phi (weightedMarginal (m := m) theta) (fun i => selectedIndicator i a) = (d : ℝ) + 1 := by
  apply phi_mean (weightedLaw theta) (fun a i => selectedIndicator i a)
    (sum_weightedLaw theta (by omega))
  · intro a i
    exact selectedIndicator_binary i a
  · exact weightedMarginal_pos theta hmpos hmtop
  · exact weightedMarginal_lt_one theta hmtop

/-- The paper's two actual marginal constraints yield its precise majorant range. -/
theorem weightedLaw_phi_range (theta : Fin d → ℝ) (hmpos : 1 ≤ m)
    (hmtop : m ≤ d - 1) {lam : ℝ} (hlam : 0 < lam)
    (hlo : ∀ i, lam * ((m : ℝ) / d) ≤ weightedMarginal (m := m) theta i)
    (hhi : ∀ i, weightedMarginal (m := m) theta i ≤ 1 - lam * (1 - (m : ℝ) / d))
    (a : Action d m) :
    0 ≤ phi (weightedMarginal (m := m) theta) (fun i => selectedIndicator i a) ∧
      phi (weightedMarginal (m := m) theta) (fun i => selectedIndicator i a) ≤ 1 + 2 * d / lam := by
  apply phi_range (by omega) (by omega) (weightedMarginal (m := m) theta)
    (fun i => selectedIndicator i a) hlam hlo
  · intro i
    linarith [hhi i]
  · intro i
    exact selectedIndicator_binary i a
  · exact sum_selectedIndicator a

/-- Lemma 2's positive-definiteness clause for the actual exponential law. -/
theorem weightedLaw_secondMoment_posDef (theta : Fin d → ℝ) (hmpos : 1 ≤ m)
    (hmtop : m ≤ d - 1) : (secondMoment (weightedLaw (m := m) theta)).PosDef :=
  secondMoment_posDef (weightedLaw theta) (weightedLaw_pos theta (by omega)) hmpos hmtop

/-- The actual exponential law also satisfies the inverse/mean identity. -/
theorem weightedLaw_inverse_marginal (theta : Fin d → ℝ) (hmpos : 1 ≤ m)
    (hmtop : m ≤ d - 1) :
    (secondMoment (weightedLaw (m := m) theta))⁻¹ *ᵥ weightedMarginal (m := m) theta =
      fun _ => (m : ℝ)⁻¹ :=
  secondMoment_inv_mulVec_marginal (weightedLaw theta)
    (weightedLaw_pos theta (by omega)) hmpos hmtop

end MsetsPaper.Upper
