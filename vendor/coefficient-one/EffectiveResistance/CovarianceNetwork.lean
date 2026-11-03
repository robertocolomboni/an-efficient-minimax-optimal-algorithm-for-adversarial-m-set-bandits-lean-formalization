import EffectiveResistance.PairCellFormulas
import EffectiveResistance.Network

/-!
# The covariance matrix as a conductance Laplacian
-/

open scoped BigOperators
open Matrix

namespace EffectiveResistance

noncomputable section

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- The conductance network associated with a covariance matrix whose
off-diagonal entries are nonpositive. -/
def covarianceNetwork
    (w : ι → ℝ) (m : ℕ)
    (hneg : ∀ i j, i ≠ j → covarianceMatrix w m i j ≤ 0) :
    ConductanceNetwork ι where
  conductance i j := if i = j then 0 else -covarianceMatrix w m i j
  symmetric := by
    apply Matrix.IsSymm.ext
    intro i j
    by_cases hij : i = j
    · subst j
      simp
    · simp [hij, Ne.symm hij, covariance_comm]
  nonnegative := by
    intro i j
    by_cases hij : i = j
    · simp [hij]
    · simp only [hij, if_false]
      exact neg_nonneg.mpr (hneg i j hij)
  diagonal_zero := by
    intro i
    simp

namespace covarianceNetwork

theorem degree_eq_covariance_diagonal
    (w : ι → ℝ) (hw : ∀ k, 0 < w k) (m : ℕ)
    (hm : m ≤ Fintype.card ι)
    (hneg : ∀ i j, i ≠ j → covarianceMatrix w m i j ≤ 0)
    (i : ι) :
    (covarianceNetwork w m hneg).degree i = covarianceMatrix w m i i := by
  have hrow := covariance_rowSum_zero w hw hm i
  unfold ConductanceNetwork.degree covarianceNetwork
  calc
    (∑ j, if i = j then 0 else -covarianceMatrix w m i j) =
        ∑ j, (-covarianceMatrix w m i j +
          if j = i then covarianceMatrix w m i i else 0) := by
            apply Finset.sum_congr rfl
            intro j _
            by_cases hij : i = j
            · subst j
              simp
            · simp [hij, Ne.symm hij]
    _ = -(∑ j, covarianceMatrix w m i j) + covarianceMatrix w m i i := by
      rw [Finset.sum_add_distrib, Finset.sum_neg_distrib]
      simp
    _ = covarianceMatrix w m i i := by
      rw [hrow]
      ring

theorem laplacian_eq_covariance
    (w : ι → ℝ) (hw : ∀ k, 0 < w k) (m : ℕ)
    (hm : m ≤ Fintype.card ι)
    (hneg : ∀ i j, i ≠ j → covarianceMatrix w m i j ≤ 0) :
    (covarianceNetwork w m hneg).laplacian = covarianceMatrix w m := by
  ext i j
  by_cases hij : i = j
  · subst j
    rw [ConductanceNetwork.laplacian_diagonal,
      degree_eq_covariance_diagonal w hw m hm hneg i]
  · rw [ConductanceNetwork.laplacian_offDiagonal _ hij]
    simp [covarianceNetwork, hij]

end covarianceNetwork

/-- Strict negative correlation of distinct coordinates in the rank range
`2 ≤ m ≤ card ι - 2`. -/
theorem externalField_covariance_offDiagonal_neg_interior
    (w : ι → ℝ) (hw : ∀ k, 0 < w k)
    (q : ℕ) (hm : q + 2 ≤ Fintype.card ι)
    (hinterior : q + 2 ≤ Fintype.card ι - 2)
    (i j : ι) (hij : i ≠ j) :
    covarianceMatrix w (q + 2) i j < 0 := by
  have hq : q + 2 ≤ Fintype.card (PairComplement i j) := by
    rw [card_pairComplement i j hij]
    exact hinterior
  have hω := pairCell_omega_pos w hw i j hij q hq
  have heq := externalFieldPairTable_omega_eq_neg_covariance
    w hw hm i j
  change 0 < (externalFieldPairTable w hw hm i j).ω at hω
  rw [heq] at hω
  linarith

/-- The covariance conductance network in the interior-rank range. -/
def externalFieldCovarianceNetworkInterior
    (w : ι → ℝ) (hw : ∀ k, 0 < w k)
    (q : ℕ) (hm : q + 2 ≤ Fintype.card ι)
    (hinterior : q + 2 ≤ Fintype.card ι - 2) :
    ConductanceNetwork ι :=
  covarianceNetwork w (q + 2) fun i j hij =>
    (externalField_covariance_offDiagonal_neg_interior
      w hw q hm hinterior i j hij).le

theorem externalFieldCovarianceNetworkInterior_laplacian
    (w : ι → ℝ) (hw : ∀ k, 0 < w k)
    (q : ℕ) (hm : q + 2 ≤ Fintype.card ι)
    (hinterior : q + 2 ≤ Fintype.card ι - 2) :
    (externalFieldCovarianceNetworkInterior w hw q hm hinterior).laplacian =
      covarianceMatrix w (q + 2) := by
  exact covarianceNetwork.laplacian_eq_covariance w hw (q + 2) hm _

end

end EffectiveResistance
