import CoefficientOne.CovarianceEnergy

/-!
# The electrical interpretation of the actual covariance graph

The Laplacian equation specifies the injected current.  Its zero-mean
solution is unique, and the resistance is its endpoint voltage difference.
-/

open scoped BigOperators
open Matrix EffectiveResistance

namespace CoefficientOne

noncomputable section

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- The i-th coordinate of Σh is the sum of outgoing currents. -/
theorem covariance_current_formula
    (w : ι → ℝ) (hw : ∀ i, 0 < w i) (m : ℕ)
    (hmpos : 1 ≤ m) (hmtop : m ≤ Fintype.card ι - 1)
    (h : ι → ℝ) (i : ι) :
    (covarianceMatrix w m *ᵥ h) i =
      ∑ j, (-covarianceMatrix w m i j) * (h i - h j) := by
  have heq := (externalFieldCovarianceNetwork w hw m hmpos hmtop).laplacian_mulVec h i
  rw [externalFieldCovarianceNetwork_laplacian] at heq
  rw [heq]
  apply Finset.sum_congr rfl
  intro j _
  by_cases hij : i = j
  · subst j
    simp
  · simp [externalFieldCovarianceNetwork, covarianceNetwork, hij]

/-- The same formula with the zero diagonal term omitted, as in Appendix E.3. -/
theorem covariance_current_formula_offDiagonal
    (w : ι → ℝ) (hw : ∀ i, 0 < w i) (m : ℕ)
    (hmpos : 1 ≤ m) (hmtop : m ≤ Fintype.card ι - 1)
    (h : ι → ℝ) (i : ι) :
    (covarianceMatrix w m *ᵥ h) i =
      ∑ j ∈ Finset.univ.erase i, (-covarianceMatrix w m i j) * (h i - h j) := by
  rw [covariance_current_formula w hw m hmpos hmtop h i]
  have hh := Finset.sum_erase_add Finset.univ
    (fun j => (-covarianceMatrix w m i j) * (h i - h j)) (Finset.mem_univ i)
  simpa using hh.symm

/-- Adding a constant potential does not change the injected currents. -/
theorem covariance_current_add_constant
    (w : ι → ℝ) (hw : ∀ i, 0 < w i) (m : ℕ)
    (hmpos : 1 ≤ m) (hmtop : m ≤ Fintype.card ι - 1)
    (h : ι → ℝ) (c : ℝ) :
    covarianceMatrix w m *ᵥ (h + fun _ => c) = covarianceMatrix w m *ᵥ h := by
  rw [Matrix.mulVec_add,
    covariance_mulVec_eq_zero_of_constant w hw m (hmtop.trans (Nat.sub_le _ _))
      (fun _ => c) (fun _ _ => rfl), add_zero]

/-- Every injected current has sum zero, and every zero-sum demand is attained. -/
theorem covariance_range_eq_zeroSum
    (w : ι → ℝ) (hw : ∀ i, 0 < w i) (m : ℕ)
    (hmpos : 1 ≤ m) (hmtop : m ≤ Fintype.card ι - 1) :
    LinearMap.range (covarianceMatrix w m).toLin' = zeroSumSubmodule (ι := ι) := by
  ext y
  change (∃ x, covarianceMatrix w m *ᵥ x = y) ↔ IsZeroSum y
  constructor
  · rintro ⟨x, rfl⟩
    rw [← externalFieldCovarianceNetwork_laplacian w hw m hmpos hmtop]
    exact ConductanceNetwork.laplacian_mulVec_zeroSum _ x
  · intro hy
    exact ⟨externalFieldPseudoinverse w hw m hmpos hmtop *ᵥ y,
      externalField_pseudoinverse_solves_zeroSum w hw m hmpos hmtop y hy⟩

/-- Any zero-mean solution equals the canonical pseudoinverse potential. -/
theorem covariance_zeroSum_solution_unique
    (w : ι → ℝ) (hw : ∀ i, 0 < w i) (m : ℕ)
    (hmpos : 1 ≤ m) (hmtop : m ≤ Fintype.card ι - 1)
    (y : ι → ℝ) (hy : IsZeroSum y) (h : ι → ℝ) (hz : IsZeroSum h)
    (hsolve : covarianceMatrix w m *ᵥ h = y) :
    h = externalFieldPseudoinverse w hw m hmpos hmtop *ᵥ y := by
  have hcard : 0 < Fintype.card ι := by omega
  letI : Nonempty ι := Fintype.card_pos_iff.mp hcard
  let G := externalFieldCovarianceNetwork w hw m hmpos hmtop
  have hinj := G.laplacianOnZeroSum_injective
    (externalFieldCovarianceNetwork_strictlyComplete w hw m hmpos hmtop)
  have hzero := externalField_pseudoinverse_mulVec_zeroSum w hw m hmpos hmtop y
  have heq : G.laplacianOnZeroSum ⟨h, hz⟩ =
      G.laplacianOnZeroSum ⟨externalFieldPseudoinverse w hw m hmpos hmtop *ᵥ y, hzero⟩ := by
    apply Subtype.ext
    change G.laplacian *ᵥ h =
      G.laplacian *ᵥ (externalFieldPseudoinverse w hw m hmpos hmtop *ᵥ y)
    rw [show G.laplacian = covarianceMatrix w m from
      externalFieldCovarianceNetwork_laplacian w hw m hmpos hmtop,
      hsolve, externalField_pseudoinverse_solves_zeroSum w hw m hmpos hmtop y hy]
  exact congrArg Subtype.val (hinj heq)

/-- Existence and uniqueness on the actual zero-mean potential space. -/
theorem covariance_existsUnique_zeroSum_solution
    (w : ι → ℝ) (hw : ∀ i, 0 < w i) (m : ℕ)
    (hmpos : 1 ≤ m) (hmtop : m ≤ Fintype.card ι - 1)
    (y : ι → ℝ) (hy : IsZeroSum y) :
    ∃! h : ι → ℝ, IsZeroSum h ∧ covarianceMatrix w m *ᵥ h = y := by
  refine ⟨externalFieldPseudoinverse w hw m hmpos hmtop *ᵥ y,
    ⟨externalField_pseudoinverse_mulVec_zeroSum w hw m hmpos hmtop y,
      externalField_pseudoinverse_solves_zeroSum w hw m hmpos hmtop y hy⟩, ?_⟩
  intro h hh
  exact covariance_zeroSum_solution_unique w hw m hmpos hmtop y hy h hh.1 hh.2

/-- The pseudoinverse quadratic form is the voltage difference at the terminals. -/
theorem externalField_resistance_eq_voltage_difference
    (w : ι → ℝ) (hw : ∀ i, 0 < w i) (m : ℕ)
    (hmpos : 1 ≤ m) (hmtop : m ≤ Fintype.card ι - 1) (i j : ι) :
    quadraticForm (externalFieldPseudoinverse w hw m hmpos hmtop) (pairDemand i j) =
      (externalFieldPseudoinverse w hw m hmpos hmtop *ᵥ pairDemand i j) i -
      (externalFieldPseudoinverse w hw m hmpos hmtop *ᵥ pairDemand i j) j := by
  exact EffectiveResistance.pairDemand_dotProduct i j _

/-- Any zero-mean solution of the unit-current equation gives the same resistance. -/
theorem externalField_resistance_eq_voltage_of_solution
    (w : ι → ℝ) (hw : ∀ i, 0 < w i) (m : ℕ)
    (hmpos : 1 ≤ m) (hmtop : m ≤ Fintype.card ι - 1)
    (i j : ι) (hij : i ≠ j) (h : ι → ℝ) (hz : IsZeroSum h)
    (hsolve : covarianceMatrix w m *ᵥ h = pairDemand i j) :
    quadraticForm (externalFieldPseudoinverse w hw m hmpos hmtop) (pairDemand i j) =
      h i - h j := by
  rw [covariance_zeroSum_solution_unique w hw m hmpos hmtop (pairDemand i j)
    (pairDemand_zeroSum hij) h hz hsolve]
  exact externalField_resistance_eq_voltage_difference w hw m hmpos hmtop i j

end

end CoefficientOne
