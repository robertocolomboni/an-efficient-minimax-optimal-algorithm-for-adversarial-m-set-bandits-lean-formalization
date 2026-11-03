import CoefficientOne.ElementaryBridge
import EffectiveResistance.AllRanks
import EffectiveResistance.PairCellFormulas
import Mathlib.LinearAlgebra.Matrix.PosDef
import Mathlib.Tactic

/-!
# From the actual fixed-rank covariance to the kernel matrix

This file proves the manuscript identities `eq:covariance-laplacian` and
`eq:covariance-congruence` from the original finite probability law. The
off-diagonal formula is derived from the four endpoint cells for ranks at
least two. Rank one is evaluated directly on singleton subsets.

The degree parameter in `kernelK` is an integer, implementing the manuscript's
zero convention for negative elementary symmetric degrees without truncated
natural-number subtraction.
-/

open scoped BigOperators
open Matrix EffectiveResistance

namespace CoefficientOne

noncomputable section

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- The rectangular elementary determinant `K_j = e_j² - e_(j-1)e_(j+1)`. -/
def kernelK (w : ι → ℝ) (j : ℤ) : ℝ :=
  elementaryInt w j ^ 2 - elementaryInt w (j - 1) * elementaryInt w (j + 1)

/-- The manuscript's zero-diagonal matrix with double-deleted entries. -/
def kernelMatrix (w : ι → ℝ) (j : ℤ) : Matrix ι ι ℝ :=
  fun i l => if i = l then 0 else kernelK (pairRestrictedWeight w i l) j

/-- Coordinate variances of the original finite-law covariance. -/
def covarianceVariance (w : ι → ℝ) (m : ℕ) : ι → ℝ :=
  fun i => covarianceMatrix w m i i

@[simp]
theorem kernelK_zero (w : ι → ℝ) : kernelK w 0 = 1 := by
  simp [kernelK, elementaryInt_zero, elementaryInt_of_neg]

theorem kernelK_succ_nat (w : ι → ℝ) (q : ℕ) :
    kernelK w (q + 1 : ℕ) = elementarySum w (q + 1) ^ 2 -
      elementarySum w q * elementarySum w (q + 2) := by
  unfold kernelK
  have hminus : ((q + 1 : ℕ) : ℤ) - 1 = q := by omega
  have hplus : ((q + 1 : ℕ) : ℤ) + 1 = (q + 2 : ℕ) := by omega
  rw [hminus, hplus, elementaryInt_nat, elementaryInt_nat, elementaryInt_nat]

/-- Direct evaluation of the categorical marginal on its only contributing
singleton. No rank-one probability formula is assumed. -/
theorem inclusionMean_rankOne_eq_weight (w : ι → ℝ) (i : ι) :
    inclusionMean w 1 i = w i / elementarySum w 1 := by
  let T : RankSubset ι 1 := ⟨{i}, Finset.card_singleton i⟩
  unfold inclusionMean expectation
  rw [Finset.sum_eq_single T]
  · simp [T, subsetProbability, subsetWeight, indicator]
  · intro S hS hST
    have hi : i ∉ S.1 := by
      intro hi
      obtain ⟨k, hk⟩ := Finset.card_eq_one.mp S.property
      have hik : i = k := by simpa [hk] using hi
      subst k
      apply hST
      exact Subtype.ext hk
    simp [indicator, hi]
  · intro hT
    exact False.elim (hT (Finset.mem_univ T))

/-- Off-diagonal covariance at rank one, obtained from the categorical law. -/
theorem neg_covariance_rankOne_eq_kernel
    (w : ι → ℝ) (hw : ∀ k, 0 < w k)
    (hm : 1 ≤ Fintype.card ι) (i l : ι) (hil : i ≠ l) :
    -covarianceMatrix w 1 i l =
      w i * w l * kernelK (pairRestrictedWeight w i l) 0 /
        elementarySum w 1 ^ 2 := by
  rw [covariance_eq_pairCell11_sub_means w hw hm i l,
    pairCell11_rankOne_eq_zero w i l hil,
    inclusionMean_rankOne_eq_weight, inclusionMean_rankOne_eq_weight, kernelK_zero]
  ring

/-- The four-cell determinant gives the off-diagonal covariance formula at
every rank `q+2`, including boundary cases where a background cell is empty. -/
theorem neg_covariance_succ_succ_eq_kernel
    (w : ι → ℝ) (hw : ∀ k, 0 < w k) (q : ℕ)
    (hm : q + 2 ≤ Fintype.card ι) (i l : ι) (hil : i ≠ l) :
    -covarianceMatrix w (q + 2) i l =
      w i * w l * kernelK (pairRestrictedWeight w i l) (q + 1 : ℕ) /
        elementarySum w (q + 2) ^ 2 := by
  rw [← externalFieldPairTable_omega_eq_neg_covariance w hw hm i l]
  change pairCell10 w (q + 2) i l * pairCell01 w (q + 2) i l -
      pairCell11 w (q + 2) i l * pairCell00 w (q + 2) i l = _
  rw [pairCell10_eq_elementarySums w i l hil q,
    pairCell01_eq_elementarySums w i l hil q,
    pairCell11_eq_elementarySums w i l hil q,
    pairCell00_eq_elementarySums w i l hil q,
    kernelK_succ_nat]
  ring

/-- Equation `eq:covariance-laplacian`, for the actual finite-law covariance.
The formula holds even at the full rank; nontriviality is needed only later
to obtain strict positivity. -/
theorem neg_covariance_offDiagonal_eq_kernel
    (w : ι → ℝ) (hw : ∀ k, 0 < w k) (m : ℕ)
    (hmpos : 1 ≤ m) (hmcard : m ≤ Fintype.card ι)
    (i l : ι) (hil : i ≠ l) :
    -covarianceMatrix w m i l =
      w i * w l * kernelK (pairRestrictedWeight w i l) ((m : ℤ) - 1) /
        elementarySum w m ^ 2 := by
  by_cases hmone : m = 1
  · subst m
    simpa using neg_covariance_rankOne_eq_kernel w hw hmcard i l hil
  · obtain ⟨q, hq⟩ : ∃ q : ℕ, m = q + 2 := ⟨m - 2, by omega⟩
    subst m
    have hindex : ((q + 2 : ℕ) : ℤ) - 1 = (q + 1 : ℕ) := by omega
    rw [hindex]
    exact neg_covariance_succ_succ_eq_kernel w hw q hmcard i l hil

/-- Equation `eq:covariance-congruence`, proved entry by entry from the
off-diagonal formula; the diagonal entries vanish on both sides. -/
theorem covariance_complement_eq_kernel_congruence
    (w : ι → ℝ) (hw : ∀ k, 0 < w k) (m : ℕ)
    (hmpos : 1 ≤ m) (hmcard : m ≤ Fintype.card ι) :
    Matrix.diagonal (covarianceVariance w m) - covarianceMatrix w m =
      (1 / elementarySum w m ^ 2) •
        (Matrix.diagonal w * kernelMatrix w ((m : ℤ) - 1) * Matrix.diagonal w) := by
  ext i l
  by_cases hil : i = l
  · subst l
    simp [covarianceVariance, kernelMatrix, Matrix.mul_diagonal, Matrix.diagonal_mul]
  · have hentry := neg_covariance_offDiagonal_eq_kernel w hw m hmpos hmcard i l hil
    simpa [covarianceVariance, kernelMatrix, hil, Matrix.mul_diagonal,
      Matrix.diagonal_mul, div_eq_mul_inv, mul_assoc, mul_left_comm, mul_comm] using hentry

/-- The row-sum identity of the original covariance, in matrix-vector form. -/
theorem covariance_mulVec_one_eq_zero
    (w : ι → ℝ) (hw : ∀ k, 0 < w k) (m : ℕ)
    (hmcard : m ≤ Fintype.card ι) :
    covarianceMatrix w m *ᵥ (fun _ => 1) = 0 := by
  ext i
  simpa [Matrix.mulVec, dotProduct] using covariance_rowSum_zero w hw hmcard i

/-- The complementary matrix has the variance vector as its row sums. -/
theorem covariance_complement_mulVec_one
    (w : ι → ℝ) (hw : ∀ k, 0 < w k) (m : ℕ)
    (hmcard : m ≤ Fintype.card ι) :
    (Matrix.diagonal (covarianceVariance w m) - covarianceMatrix w m) *ᵥ
      (fun _ => 1) = covarianceVariance w m := by
  rw [Matrix.sub_mulVec, covariance_mulVec_one_eq_zero w hw m hmcard, sub_zero]
  ext i
  simp [Matrix.mulVec_diagonal]

/-- Every variance is strictly positive at a nontrivial rank, using the
already-proved strictly positive covariance-network degree. -/
theorem covarianceVariance_pos
    (w : ι → ℝ) (hw : ∀ k, 0 < w k) (m : ℕ)
    (hmpos : 1 ≤ m) (hmtop : m ≤ Fintype.card ι - 1) (i : ι) :
    0 < covarianceVariance w m i := by
  have h := externalFieldCovarianceNetwork_degree_pos w hw m hmpos hmtop i
  rwa [externalFieldCovarianceNetwork_degree_eq] at h

/-- The total variance is positive at every nontrivial rank. -/
theorem covarianceVariance_sum_pos
    (w : ι → ℝ) (hw : ∀ k, 0 < w k) (m : ℕ)
    (hmpos : 1 ≤ m) (hmtop : m ≤ Fintype.card ι - 1) :
    0 < ∑ i, covarianceVariance w m i := by
  have hcard : 0 < Fintype.card ι := by omega
  haveI : Nonempty ι := Fintype.card_pos_iff.mp hcard
  exact Finset.sum_pos (fun i hi => covarianceVariance_pos w hw m hmpos hmtop i)
    Finset.univ_nonempty

/-- A constant vector is annihilated by the covariance, directly from its
zero row sums. The formulation also works for an empty index type. -/
theorem covariance_mulVec_eq_zero_of_constant
    (w : ι → ℝ) (hw : ∀ k, 0 < w k) (m : ℕ)
    (hmcard : m ≤ Fintype.card ι) (x : ι → ℝ)
    (hx : ∀ i l, x i = x l) : covarianceMatrix w m *ᵥ x = 0 := by
  ext i
  simp only [Matrix.mulVec, dotProduct, Pi.zero_apply]
  calc
    (∑ l, covarianceMatrix w m i l * x l) =
        (∑ l, covarianceMatrix w m i l) * x i := by
      rw [Finset.sum_mul]
      apply Finset.sum_congr rfl
      intro l hl
      rw [hx l i]
    _ = 0 := by rw [covariance_rowSum_zero w hw hmcard i, zero_mul]

/-- Zero covariance energy is equivalent to a constant vector at every
nontrivial rank. The forward argument uses the already-proved positive-edge
energy decomposition of the actual covariance network. -/
theorem covariance_quadraticForm_eq_zero_iff_constant
    (w : ι → ℝ) (hw : ∀ k, 0 < w k) (m : ℕ)
    (hmpos : 1 ≤ m) (hmtop : m ≤ Fintype.card ι - 1) (x : ι → ℝ) :
    quadraticForm (covarianceMatrix w m) x = 0 ↔ ∀ i l, x i = x l := by
  constructor
  · intro hzero
    let N := externalFieldCovarianceNetwork w hw m hmpos hmtop
    have henergy : N.energy x = 0 := by
      rw [N.energy_eq_quadraticForm]
      change quadraticForm
        (externalFieldCovarianceNetwork w hw m hmpos hmtop).laplacian x = 0
      rw [externalFieldCovarianceNetwork_laplacian]
      exact hzero
    exact N.eq_of_energy_eq_zero
      (externalFieldCovarianceNetwork_strictlyComplete w hw m hmpos hmtop) x henergy
  · intro hx
    have hker := covariance_mulVec_eq_zero_of_constant
      w hw m (hmtop.trans (Nat.sub_le _ _)) x hx
    simp [quadraticForm, hker]

/-- The exact covariance kernel: it consists precisely of the constant
vectors, i.e. the span of the all-ones vector at a nontrivial rank. -/
theorem covariance_mulVec_eq_zero_iff_constant
    (w : ι → ℝ) (hw : ∀ k, 0 < w k) (m : ℕ)
    (hmpos : 1 ≤ m) (hmtop : m ≤ Fintype.card ι - 1) (x : ι → ℝ) :
    covarianceMatrix w m *ᵥ x = 0 ↔ ∀ i l, x i = x l := by
  constructor
  · intro hzero
    apply (covariance_quadraticForm_eq_zero_iff_constant w hw m hmpos hmtop x).mp
    simp [quadraticForm, hzero]
  · exact covariance_mulVec_eq_zero_of_constant w hw m (hmtop.trans (Nat.sub_le _ _)) x

/-- Semidefiniteness packaged in mathlib's standard matrix predicate. -/
theorem covarianceMatrix_posSemidef
    (w : ι → ℝ) (hw : ∀ k, 0 < w k) (m : ℕ)
    (hmcard : m ≤ Fintype.card ι) : (covarianceMatrix w m).PosSemidef := by
  apply Matrix.posSemidef_iff_dotProduct_mulVec.mpr
  refine ⟨Matrix.isHermitian_iff_isSymm.mpr (covariance_isSymm w m), ?_⟩
  intro x
  simpa only [star_trivial, quadraticForm] using covariance_quadratic_nonnegative w hw hmcard x
end

end CoefficientOne
