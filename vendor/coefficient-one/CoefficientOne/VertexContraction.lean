import CoefficientOne.GraphExamples

/-!
# Contracting all vertices except one

Conductances between distinct blocks are the sums of the original
conductances across those blocks.  For the partition `{i}`, `{i}ᶜ`, this
construction is exactly the two-vertex network of conductance `degree i`.
-/

open scoped BigOperators
open Matrix EffectiveResistance

namespace CoefficientOne

noncomputable section

variable {ι κ : Type*} [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ]

/-- The explicit network obtained by identifying the fibers of q.
Internal edges become loops and are omitted from the zero-diagonal network. -/
def blockContraction (G : ConductanceNetwork ι) (q : ι → κ) : ConductanceNetwork κ where
  conductance a b := if a = b then 0 else
    ∑ u, ∑ v, if q u = a ∧ q v = b then G.conductance u v else 0
  symmetric := by
    apply Matrix.IsSymm.ext
    intro a b
    by_cases hab : a = b
    · subst b
      simp
    · simp only [hab, Ne.symm hab, if_false]
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro u _
      apply Finset.sum_congr rfl
      intro v _
      rw [G.conductance_comm]
      simp only [and_comm]
  nonnegative := by
    intro a b
    split_ifs
    · exact le_rfl
    · apply Finset.sum_nonneg
      intro u _
      apply Finset.sum_nonneg
      intro v _
      split_ifs
      · exact G.nonnegative u v
      · exact le_rfl
  diagonal_zero := by intro a; simp

/-- The singleton i is block zero; every other vertex is in block one. -/
def singletonBlock (i : ι) (j : ι) : Fin 2 := if j = i then 0 else 1

theorem singletonBlock_zero_iff (i j : ι) : singletonBlock i j = 0 ↔ j = i := by
  by_cases hij : j = i <;> simp [singletonBlock, hij]

theorem singletonBlock_one_iff (i j : ι) : singletonBlock i j = 1 ↔ j ≠ i := by
  by_cases hij : j = i <;> simp [singletonBlock, hij]

/-- Every edge incident to i contributes once to the inter-block conductance. -/
theorem singletonContraction_conductance (G : ConductanceNetwork ι) (i : ι) :
    (blockContraction G (singletonBlock i)).conductance 0 1 = G.degree i := by
  change (if (0 : Fin 2) = 1 then 0 else
    ∑ u, ∑ v, if singletonBlock i u = 0 ∧ singletonBlock i v = 1
      then G.conductance u v else 0) = G.degree i
  rw [if_neg (by decide : (0 : Fin 2) ≠ 1)]
  have hterm (u v : ι) :
      (if singletonBlock i u = 0 ∧ singletonBlock i v = 1
        then G.conductance u v else 0) = if u = i then G.conductance i v else 0 := by
    simp only [singletonBlock_zero_iff, singletonBlock_one_iff]
    by_cases hu : u = i
    · subst u
      by_cases hv : v = i
      · subst v
        simp [G.diagonal_zero]
      · simp [hv]
    · simp [hu]
  simp_rw [hterm]
  rw [Finset.sum_eq_single i]
  · simp [ConductanceNetwork.degree]
  · intro u _ hui
    simp [hui]
  · simp

theorem conductanceNetwork_eq_of_conductance_eq
    (G H : ConductanceNetwork ι) (h : G.conductance = H.conductance) : G = H := by
  cases G
  cases H
  cases h
  rfl

/-- Identification with the concrete two-vertex network, rather than an
assumption on the resulting matrix. -/
theorem singletonContraction_eq_twoVertexNetwork (G : ConductanceNetwork ι) (i : ι) :
    blockContraction G (singletonBlock i) =
      twoVertexNetwork (G.degree i) (Finset.sum_nonneg (fun j _ => G.nonnegative i j)) := by
  apply conductanceNetwork_eq_of_conductance_eq
  ext a b
  fin_cases a <;> fin_cases b
  · exact (blockContraction G (singletonBlock i)).diagonal_zero 0
  · exact singletonContraction_conductance G i
  · rw [(blockContraction G (singletonBlock i)).conductance_comm]
    exact singletonContraction_conductance G i
  · exact (blockContraction G (singletonBlock i)).diagonal_zero 1

/-- The explicit two-vertex Green kernel, now for the actual block contraction. -/
def singletonContractionGreenKernel (G : ConductanceNetwork ι) (i : ι)
    (hi : 0 < G.degree i) : GreenKernel (blockContraction G (singletonBlock i)) where
  kernel := (twoVertexGreenKernel (G.degree i) hi).kernel
  symmetric := (twoVertexGreenKernel (G.degree i) hi).symmetric
  solves_zeroSum y hy := by
    rw [singletonContraction_eq_twoVertexNetwork]
    exact (twoVertexGreenKernel (G.degree i) hi).solves_zeroSum y hy

/-- The resistance after the explicit vertex identification is 1/degree i. -/
theorem singletonContraction_effectiveResistance
    (G : ConductanceNetwork ι) (i : ι) (hi : 0 < G.degree i) :
    (singletonContractionGreenKernel G i hi).effectiveResistance 0 1 = 1 / G.degree i :=
  twoVertex_effectiveResistance (G.degree i) hi

/-- Appendix E.3 for the concrete covariance graph: contracting all other
vertices produces resistance exactly equal to the inverse coordinate variance. -/
theorem externalField_singletonContraction_resistance
    (w : ι → ℝ) (hw : ∀ i, 0 < w i) (m : ℕ)
    (hmpos : 1 ≤ m) (hmtop : m ≤ Fintype.card ι - 1) (i : ι) :
    (singletonContractionGreenKernel
      (externalFieldCovarianceNetwork w hw m hmpos hmtop) i
      (externalFieldCovarianceNetwork_degree_pos w hw m hmpos hmtop i)).effectiveResistance 0 1 =
        1 / covarianceVariance w m i := by
  rw [singletonContraction_effectiveResistance, externalFieldCovarianceNetwork_degree_eq]
  rfl

end

end CoefficientOne
