import EffectiveResistance.BoundaryRanks
import EffectiveResistance.MatrixCorollary
import EffectiveResistance.GreenKernelExistence
import EffectiveResistance.EdgeVariation

/-!
# The effective-resistance theorem at every nontrivial rank

This file joins the rank-one, interior-rank, and top-rank arguments into the
single statement used in the paper.
-/

open Matrix

namespace EffectiveResistance

noncomputable section

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- The main effective-resistance bound for every nontrivial rank. -/
theorem externalField_effectiveResistance_bound
    (w : ι → ℝ) (hw : ∀ k, 0 < w k)
    (m : ℕ) (hm_pos : 1 ≤ m) (hm_top : m ≤ Fintype.card ι - 1)
    (N : ConductanceNetwork ι) (G : GreenKernel N)
    (i j : ι) (hij : i ≠ j)
    (hL : N.laplacian = covarianceMatrix w m) :
    G.effectiveResistance i j ≤
      1 / covarianceMatrix w m i i + 1 / covarianceMatrix w m j j := by
  by_cases hm_one : m = 1
  · subst m
    exact externalField_effectiveResistance_bound_rankOne
      w hw N G i j hij hL
  by_cases hm_last : m = Fintype.card ι - 1
  · subst m
    exact externalField_effectiveResistance_bound_topRank
      w hw N G i j hij hL
  · let q := m - 2
    have hm_two : 2 ≤ m := by omega
    have hqm : q + 2 = m := by
      dsimp [q]
      omega
    have hm_interior : m ≤ Fintype.card ι - 2 := by omega
    have hm_card : m ≤ Fintype.card ι := by omega
    have hq_card : q + 2 ≤ Fintype.card ι := by omega
    have hq_complement : q + 2 ≤ Fintype.card (PairComplement i j) := by
      rw [card_pairComplement i j hij]
      omega
    have hbound := externalField_effectiveResistance_bound_interior
      w hw N G i j hij q hq_card hq_complement
        (by simpa [hqm] using hL)
    simpa [hqm] using hbound

/-- Distinct coordinates of a nontrivial fixed-rank external-field law have
strictly negative covariance. -/
theorem externalField_covariance_offDiagonal_neg
    (w : ι → ℝ) (hw : ∀ k, 0 < w k)
    (m : ℕ) (hm_pos : 1 ≤ m) (hm_top : m ≤ Fintype.card ι - 1)
    (i j : ι) (hij : i ≠ j) :
    covarianceMatrix w m i j < 0 := by
  by_cases hm_one : m = 1
  · subst m
    have hm_card : 1 ≤ Fintype.card ι := by omega
    rw [covariance_eq_pairCell11_sub_means w hw hm_card i j,
      pairCell11_rankOne_eq_zero w i j hij]
    simpa only [zero_sub] using neg_lt_zero.mpr
      (mul_pos (inclusionMean_rankOne_pos w hw i)
        (inclusionMean_rankOne_pos w hw j))
  by_cases hm_last : m = Fintype.card ι - 1
  · subst m
    have hm_card : Fintype.card ι - 1 ≤ Fintype.card ι := Nat.sub_le _ _
    rw [covariance_eq_pairCell00_sub_exclusion_means w hw
        (Fintype.card ι - 1) hm_card i j,
      pairCell00_topRank_eq_zero w i j hij]
    simpa only [zero_sub] using neg_lt_zero.mpr
      (mul_pos (exclusionMean_topRank_pos w hw i)
        (exclusionMean_topRank_pos w hw j))
  · let q := m - 2
    have hm_two : 2 ≤ m := by omega
    have hqm : q + 2 = m := by
      dsimp [q]
      omega
    have hm_card : q + 2 ≤ Fintype.card ι := by omega
    have hm_interior : q + 2 ≤ Fintype.card ι - 2 := by omega
    simpa [hqm] using externalField_covariance_offDiagonal_neg_interior
      w hw q hm_card hm_interior i j hij

/-- The canonical covariance conductance network at an arbitrary nontrivial
rank. -/
def externalFieldCovarianceNetwork
    (w : ι → ℝ) (hw : ∀ k, 0 < w k)
    (m : ℕ) (hm_pos : 1 ≤ m) (hm_top : m ≤ Fintype.card ι - 1) :
    ConductanceNetwork ι :=
  covarianceNetwork w m fun i j hij =>
    (externalField_covariance_offDiagonal_neg
      w hw m hm_pos hm_top i j hij).le

theorem externalFieldCovarianceNetwork_laplacian
    (w : ι → ℝ) (hw : ∀ k, 0 < w k)
    (m : ℕ) (hm_pos : 1 ≤ m) (hm_top : m ≤ Fintype.card ι - 1) :
    (externalFieldCovarianceNetwork w hw m hm_pos hm_top).laplacian =
      covarianceMatrix w m := by
  exact covarianceNetwork.laplacian_eq_covariance
    w hw m (hm_top.trans (Nat.sub_le _ _)) _

theorem externalFieldCovarianceNetwork_degree_eq
    (w : ι → ℝ) (hw : ∀ k, 0 < w k)
    (m : ℕ) (hm_pos : 1 ≤ m) (hm_top : m ≤ Fintype.card ι - 1)
    (i : ι) :
    (externalFieldCovarianceNetwork w hw m hm_pos hm_top).degree i =
      covarianceMatrix w m i i := by
  exact covarianceNetwork.degree_eq_covariance_diagonal
    w hw m (hm_top.trans (Nat.sub_le _ _)) _ i

theorem externalFieldCovarianceNetwork_degree_pos
    (w : ι → ℝ) (hw : ∀ k, 0 < w k)
    (m : ℕ) (hm_pos : 1 ≤ m) (hm_top : m ≤ Fintype.card ι - 1)
    (i : ι) :
    0 < (externalFieldCovarianceNetwork w hw m hm_pos hm_top).degree i := by
  let N := externalFieldCovarianceNetwork w hw m hm_pos hm_top
  have hcard : 1 < Fintype.card ι := by omega
  obtain ⟨j, hji⟩ := Fintype.exists_ne_of_one_lt_card hcard i
  have hij : i ≠ j := Ne.symm hji
  have hc : 0 < N.conductance i j := by
    change 0 < if i = j then 0 else -covarianceMatrix w m i j
    rw [if_neg hij]
    exact neg_pos.mpr
      (externalField_covariance_offDiagonal_neg
        w hw m hm_pos hm_top i j hij)
  have hle : N.conductance i j ≤ N.degree i := by
    unfold ConductanceNetwork.degree
    exact Finset.single_le_sum (fun k _ => N.nonnegative i k)
      (Finset.mem_univ j)
  exact lt_of_lt_of_le hc hle

theorem externalFieldCovarianceNetwork_strictlyComplete
    (w : ι → ℝ) (hw : ∀ k, 0 < w k)
    (m : ℕ) (hm_pos : 1 ≤ m) (hm_top : m ≤ Fintype.card ι - 1) :
    (externalFieldCovarianceNetwork w hw m hm_pos hm_top).IsStrictlyComplete := by
  intro i j hij
  change 0 < if i = j then 0 else -covarianceMatrix w m i j
  rw [if_neg hij]
  exact neg_pos.mpr
    (externalField_covariance_offDiagonal_neg
      w hw m hm_pos hm_top i j hij)

/-- The canonical zero-sum Green kernel of the external-field covariance
matrix.  Its matrix is the Moore--Penrose inverse of the covariance
Laplacian. -/
def externalFieldGreenKernel
    (w : ι → ℝ) (hw : ∀ k, 0 < w k)
    (m : ℕ) (hm_pos : 1 ≤ m) (hm_top : m ≤ Fintype.card ι - 1) :
    GreenKernel (externalFieldCovarianceNetwork w hw m hm_pos hm_top) := by
  have hcard_pos : 0 < Fintype.card ι := by omega
  letI : Nonempty ι := Fintype.card_pos_iff.mp hcard_pos
  exact ConductanceNetwork.canonicalGreenKernel
    (externalFieldCovarianceNetwork w hw m hm_pos hm_top)
    (externalFieldCovarianceNetwork_strictlyComplete
      w hw m hm_pos hm_top)

/-- The canonical covariance Green matrix (equivalently, the
Moore--Penrose pseudoinverse of the covariance Laplacian). -/
def externalFieldGreenMatrix
    (w : ι → ℝ) (hw : ∀ k, 0 < w k)
    (m : ℕ) (hm_pos : 1 ≤ m) (hm_top : m ≤ Fintype.card ι - 1) :
    Matrix ι ι ℝ :=
  (externalFieldGreenKernel w hw m hm_pos hm_top).kernel

/-- The Moore--Penrose pseudoinverse of the external-field covariance
matrix, realized by its canonical Green matrix. -/
abbrev externalFieldPseudoinverse
    (w : ι → ℝ) (hw : ∀ k, 0 < w k)
    (m : ℕ) (hm_pos : 1 ≤ m) (hm_top : m ≤ Fintype.card ι - 1) :
    Matrix ι ι ℝ :=
  externalFieldGreenMatrix w hw m hm_pos hm_top

theorem externalFieldPseudoinverse_isMoorePenroseInverse
    (w : ι → ℝ) (hw : ∀ k, 0 < w k)
    (m : ℕ) (hm_pos : 1 ≤ m) (hm_top : m ≤ Fintype.card ι - 1) :
    IsMoorePenroseInverse (covarianceMatrix w m)
      (externalFieldPseudoinverse w hw m hm_pos hm_top) := by
  have hcard_pos : 0 < Fintype.card ι := by omega
  letI : Nonempty ι := Fintype.card_pos_iff.mp hcard_pos
  let N := externalFieldCovarianceNetwork w hw m hm_pos hm_top
  have hMP := N.canonicalGreenMatrix_isMoorePenroseInverse
    (externalFieldCovarianceNetwork_strictlyComplete
      w hw m hm_pos hm_top)
  rw [externalFieldCovarianceNetwork_laplacian
    w hw m hm_pos hm_top] at hMP
  exact hMP

/-- The main theorem for the canonical covariance conductance network. -/
theorem externalFieldCovarianceNetwork_effectiveResistance_bound
    (w : ι → ℝ) (hw : ∀ k, 0 < w k)
    (m : ℕ) (hm_pos : 1 ≤ m) (hm_top : m ≤ Fintype.card ι - 1)
    (G : GreenKernel
      (externalFieldCovarianceNetwork w hw m hm_pos hm_top))
    (i j : ι) (hij : i ≠ j) :
    G.effectiveResistance i j ≤
      1 / covarianceMatrix w m i i + 1 / covarianceMatrix w m j j := by
  exact externalField_effectiveResistance_bound w hw m hm_pos hm_top
    (externalFieldCovarianceNetwork w hw m hm_pos hm_top) G i j hij
    (externalFieldCovarianceNetwork_laplacian
      w hw m hm_pos hm_top)

/-- The effective-resistance theorem stated directly for the canonical Green
matrix of the covariance Laplacian. -/
theorem externalField_effectiveResistance_bound_canonical
    (w : ι → ℝ) (hw : ∀ k, 0 < w k)
    (m : ℕ) (hm_pos : 1 ≤ m) (hm_top : m ≤ Fintype.card ι - 1)
    (i j : ι) (hij : i ≠ j) :
    quadraticForm
        (externalFieldGreenMatrix w hw m hm_pos hm_top)
        (pairDemand i j) ≤
      1 / covarianceMatrix w m i i + 1 / covarianceMatrix w m j j := by
  exact externalFieldCovarianceNetwork_effectiveResistance_bound
    w hw m hm_pos hm_top
    (externalFieldGreenKernel w hw m hm_pos hm_top) i j hij

/-- The main theorem in the paper's pseudoinverse notation. -/
theorem externalField_pseudoinverse_effectiveResistance_bound
    (w : ι → ℝ) (hw : ∀ k, 0 < w k)
    (m : ℕ) (hm_pos : 1 ≤ m) (hm_top : m ≤ Fintype.card ι - 1)
    (i j : ι) (hij : i ≠ j) :
    quadraticForm
        (externalFieldPseudoinverse w hw m hm_pos hm_top)
        (pairDemand i j) ≤
      1 / covarianceMatrix w m i i + 1 / covarianceMatrix w m j j :=
  externalField_effectiveResistance_bound_canonical
    w hw m hm_pos hm_top i j hij

/-- The constant-four weighted edge-variation estimate for the potential
generated by a unit pair demand in the external-field covariance network. -/
theorem externalField_edgeVariation_pairDemand_le_four
    (w : ι → ℝ) (hw : ∀ k, 0 < w k)
    (m : ℕ) (hm_pos : 1 ≤ m) (hm_top : m ≤ Fintype.card ι - 1)
    (a b : ι) :
    (externalFieldCovarianceNetwork w hw m hm_pos hm_top).edgeVariation
        ((externalFieldGreenKernel w hw m hm_pos hm_top).potential
          (pairDemand a b)) ≤ 4 := by
  let N := externalFieldCovarianceNetwork w hw m hm_pos hm_top
  let G := externalFieldGreenKernel w hw m hm_pos hm_top
  have hdeg : ∀ k, 0 < N.degree k := fun k =>
    externalFieldCovarianceNetwork_degree_pos w hw m hm_pos hm_top k
  have hER : G.SatisfiesEndpointBound := by
    intro i j hij
    have hbound := externalFieldCovarianceNetwork_effectiveResistance_bound
      w hw m hm_pos hm_top G i j hij
    rw [externalFieldCovarianceNetwork_degree_eq
        w hw m hm_pos hm_top i,
      externalFieldCovarianceNetwork_degree_eq
        w hw m hm_pos hm_top j]
    simpa [one_div] using hbound
  exact G.edgeVariation_potential_pairDemand_le_four hdeg hER a b

/-- The general edge-variation inequality for the external-field covariance
Laplacian: `Φ_Σ(h) ≤ 2 ‖Σh‖₁`. -/
theorem externalField_edgeVariation_le_two_l1_covariance
    (w : ι → ℝ) (hw : ∀ k, 0 < w k)
    (m : ℕ) (hm_pos : 1 ≤ m) (hm_top : m ≤ Fintype.card ι - 1)
    (h : ι → ℝ) :
    (externalFieldCovarianceNetwork w hw m hm_pos hm_top).edgeVariation h ≤
      2 * l1Norm (covarianceMatrix w m *ᵥ h) := by
  let N := externalFieldCovarianceNetwork w hw m hm_pos hm_top
  let G := externalFieldGreenKernel w hw m hm_pos hm_top
  have hdeg : ∀ k, 0 < N.degree k := fun k =>
    externalFieldCovarianceNetwork_degree_pos w hw m hm_pos hm_top k
  have hER : G.SatisfiesEndpointBound := by
    intro i j hij
    have hbound := externalFieldCovarianceNetwork_effectiveResistance_bound
      w hw m hm_pos hm_top G i j hij
    rw [externalFieldCovarianceNetwork_degree_eq
        w hw m hm_pos hm_top i,
      externalFieldCovarianceNetwork_degree_eq
        w hw m hm_pos hm_top j]
    simpa [one_div] using hbound
  have hgeneric := G.edgeVariation_le_two_l1_laplacian hdeg hER h
  rw [externalFieldCovarianceNetwork_laplacian
    w hw m hm_pos hm_top] at hgeneric
  exact hgeneric

/-- The dynamic half-operator estimate used by the correlated-sampling
reduction, in quadratic-form notation. -/
theorem externalField_half_operator_covariance
    (w : ι → ℝ) (hw : ∀ k, 0 < w k)
    (m : ℕ) (hm_pos : 1 ≤ m) (hm_top : m ≤ Fintype.card ι - 1)
    (h : ι → ℝ) :
    (2 : ℝ)⁻¹ * quadraticForm (covarianceMatrix w m) h ≤
      GreenKernel.reciprocalDegreeNorm
        (N := externalFieldCovarianceNetwork w hw m hm_pos hm_top)
        (covarianceMatrix w m *ᵥ h) := by
  let N := externalFieldCovarianceNetwork w hw m hm_pos hm_top
  let G := externalFieldGreenKernel w hw m hm_pos hm_top
  have hdeg : ∀ k, 0 < N.degree k := fun k =>
    externalFieldCovarianceNetwork_degree_pos w hw m hm_pos hm_top k
  have hER : G.SatisfiesEndpointBound := by
    intro i j hij
    have hbound := externalFieldCovarianceNetwork_effectiveResistance_bound
      w hw m hm_pos hm_top G i j hij
    rw [externalFieldCovarianceNetwork_degree_eq
        w hw m hm_pos hm_top i,
      externalFieldCovarianceNetwork_degree_eq
        w hw m hm_pos hm_top j]
    simpa [one_div] using hbound
  have hgeneric := G.half_operator_laplacian hdeg hER h
  rw [N.energy_eq_quadraticForm,
    externalFieldCovarianceNetwork_laplacian
      w hw m hm_pos hm_top] at hgeneric
  exact hgeneric

/-- The factor-two normalized covariance comparison for the external-field
law, conditional only on a Green kernel for its covariance Laplacian. -/
theorem externalField_half_normalized_covariance
    (w : ι → ℝ) (hw : ∀ k, 0 < w k)
    (m : ℕ) (hm_pos : 1 ≤ m) (hm_top : m ≤ Fintype.card ι - 1)
    (G : GreenKernel
      (externalFieldCovarianceNetwork w hw m hm_pos hm_top)) :
    LoewnerLE
      ((2 : ℝ)⁻¹ • comparisonMatrix (fun i => covarianceMatrix w m i i))
      (covarianceMatrix w m) := by
  have hcard_pos : 0 < Fintype.card ι := by omega
  letI : Nonempty ι := Fintype.card_pos_iff.mp hcard_pos
  let N := externalFieldCovarianceNetwork w hw m hm_pos hm_top
  have hdeg : ∀ k, 0 < N.degree k := fun k =>
    externalFieldCovarianceNetwork_degree_pos w hw m hm_pos hm_top k
  have hER : G.SatisfiesEndpointBound := by
    intro i j hij
    have hbound := externalFieldCovarianceNetwork_effectiveResistance_bound
      w hw m hm_pos hm_top G i j hij
    rw [externalFieldCovarianceNetwork_degree_eq
        w hw m hm_pos hm_top i,
      externalFieldCovarianceNetwork_degree_eq
        w hw m hm_pos hm_top j]
    simpa [one_div] using hbound
  have hmatrix := G.half_normalized_laplacian hdeg hER
  have hdegree : N.degree = fun i => covarianceMatrix w m i i := by
    funext i
    exact externalFieldCovarianceNetwork_degree_eq
      w hw m hm_pos hm_top i
  rw [hdegree,
    externalFieldCovarianceNetwork_laplacian w hw m hm_pos hm_top] at hmatrix
  exact hmatrix

/-- The unconditional factor-two normalized covariance comparison. -/
theorem externalField_half_normalized_covariance_unconditional
    (w : ι → ℝ) (hw : ∀ k, 0 < w k)
    (m : ℕ) (hm_pos : 1 ≤ m) (hm_top : m ≤ Fintype.card ι - 1) :
    LoewnerLE
      ((2 : ℝ)⁻¹ • comparisonMatrix (fun i => covarianceMatrix w m i i))
      (covarianceMatrix w m) := by
  exact externalField_half_normalized_covariance w hw m hm_pos hm_top
    (externalFieldGreenKernel w hw m hm_pos hm_top)

end

end EffectiveResistance
