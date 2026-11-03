import CoefficientOne.Main
import EffectiveResistance.AllRanks

/-!
# The direct quadratic identity for the pseudoinverse comparison

These lemmas prove the identity used in Appendix E.4.  The only estimate
specialized to the external-field law is the coefficient-one covariance theorem.
-/

noncomputable section

open Matrix EffectiveResistance
open scoped BigOperators

namespace CoefficientOne

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

theorem pseudoinverse_comparison_isSymm (v : ι → ℝ) :
    (comparisonMatrix v).IsSymm := by
  apply Matrix.IsSymm.ext
  intro i j
  simp [comparisonMatrix, Matrix.vecMulVec, mul_comm, Matrix.diagonal_apply]
  split_ifs <;> simp_all

/-- The diagonal inverse sends a zero-sum demand to a solution for P. -/
theorem comparison_div_mulVec (v y : ι → ℝ) (hv : ∀ i, v i ≠ 0)
    (hy : IsZeroSum y) :
    comparisonMatrix v *ᵥ (fun i => y i / v i) = y := by
  have hdot : v ⬝ᵥ (fun i => y i / v i) = 0 := by
    simpa [IsZeroSum, dotProduct, mul_div_cancel₀, hv] using hy
  rw [comparisonMatrix, Matrix.sub_mulVec, Matrix.smul_mulVec,
    Matrix.vecMulVec_mulVec, hdot]
  ext i
  simpa [Matrix.mulVec_diagonal] using mul_div_cancel₀ (y i) (hv i)

/-- The weighted-variance expression proves P is positive semidefinite. -/
theorem pseudoinverse_comparison_quadratic_nonneg (v x : ι → ℝ)
    (hv : ∀ i, 0 ≤ v i) (hV : totalWeight v ≠ 0) :
    0 ≤ quadraticForm (comparisonMatrix v) x := by
  let b := (∑ i, v i * x i) / totalWeight v
  have hexpand :
      (∑ i, v i * (x i - b) ^ 2) =
        (∑ i, v i * x i ^ 2) - 2 * b * (∑ i, v i * x i) +
          b ^ 2 * totalWeight v := by
    calc
      _ = ∑ i, (v i * x i ^ 2 - 2 * b * (v i * x i) + b ^ 2 * v i) := by
        apply Finset.sum_congr rfl
        intro i _
        ring
      _ = _ := by
        rw [Finset.sum_add_distrib, Finset.sum_sub_distrib,
          ← Finset.mul_sum, ← Finset.mul_sum]
        rfl
  have heq : quadraticForm (comparisonMatrix v) x =
      ∑ i, v i * (x i - b) ^ 2 := by
    rw [quadraticForm_comparisonMatrix, hexpand]
    dsimp [b]
    field_simp [hV]
    ring
  rw [heq]
  exact Finset.sum_nonneg (fun i _ => mul_nonneg (hv i) (sq_nonneg _))

theorem pseudoinverse_comparison_posSemidef (v : ι → ℝ)
    (hv : ∀ i, 0 ≤ v i) (hV : totalWeight v ≠ 0) :
    (comparisonMatrix v).PosSemidef := by
  apply Matrix.posSemidef_iff_dotProduct_mulVec.mpr
  refine ⟨Matrix.isHermitian_iff_isSymm.mpr (pseudoinverse_comparison_isSymm v), ?_⟩
  intro x
  simpa only [star_trivial, quadraticForm] using
    pseudoinverse_comparison_quadratic_nonneg v x hv hV

omit [DecidableEq ι] in
/-- The exact two-term identity in Appendix E.4, before using positivity. -/
theorem pseudoinverse_gap_identity (S P : Matrix ι ι ℝ) (hP : P.IsSymm)
    (y z h : ι → ℝ) (hPz : P *ᵥ z = y) (hSh : S *ᵥ h = y) :
    y ⬝ᵥ z - y ⬝ᵥ h =
      quadraticForm P (z - h) + quadraticForm (S - P) h := by
  have hswap := symmetric_bilinear_swap P hP z h
  rw [hPz] at hswap
  simp only [quadraticForm, Matrix.mulVec_sub, Matrix.sub_mulVec,
    dotProduct_sub, sub_dotProduct, hPz, hSh]
  rw [hswap, dotProduct_comm z y, dotProduct_comm h y]
  ring

/-- The existing canonical Moore-Penrose inverse solves every zero-sum demand. -/
theorem externalField_pseudoinverse_solves_zeroSum
    (w : ι → ℝ) (hw : ∀ i, 0 < w i) (m : ℕ)
    (hmpos : 1 ≤ m) (hmtop : m ≤ Fintype.card ι - 1)
    (y : ι → ℝ) (hy : IsZeroSum y) :
    covarianceMatrix w m *ᵥ
      (externalFieldPseudoinverse w hw m hmpos hmtop *ᵥ y) = y := by
  have hh := (externalFieldGreenKernel w hw m hmpos hmtop).solves_zeroSum y hy
  rw [externalFieldCovarianceNetwork_laplacian] at hh
  exact hh

/-- The canonical pseudoinverse always takes values in the zero-sum subspace. -/
theorem externalField_pseudoinverse_mulVec_zeroSum
    (w : ι → ℝ) (hw : ∀ i, 0 < w i) (m : ℕ)
    (hmpos : 1 ≤ m) (hmtop : m ≤ Fintype.card ι - 1) (y : ι → ℝ) :
    IsZeroSum (externalFieldPseudoinverse w hw m hmpos hmtop *ᵥ y) := by
  have hcard : 0 < Fintype.card ι := by omega
  letI : Nonempty ι := Fintype.card_pos_iff.mp hcard
  change IsZeroSum
    ((externalFieldCovarianceNetwork w hw m hmpos hmtop).canonicalGreenMatrix
      (externalFieldCovarianceNetwork_strictlyComplete w hw m hmpos hmtop) *ᵥ y)
  rw [ConductanceNetwork.canonicalGreenMatrix_mulVec]
  exact ConductanceNetwork.greenOperator_zeroSum _ _ y

theorem externalField_pseudoinverse_mulVec_ne_zero
    (w : ι → ℝ) (hw : ∀ i, 0 < w i) (m : ℕ)
    (hmpos : 1 ≤ m) (hmtop : m ≤ Fintype.card ι - 1)
    (y : ι → ℝ) (hy : IsZeroSum y) (hy0 : y ≠ 0) :
    externalFieldPseudoinverse w hw m hmpos hmtop *ᵥ y ≠ 0 := by
  intro hz
  have hh := externalField_pseudoinverse_solves_zeroSum w hw m hmpos hmtop y hy
  rw [hz, Matrix.mulVec_zero] at hh
  exact hy0 hh.symm

variable {n : ℕ}

/-- The manuscript's identity, with the actual covariance and pseudoinverse. -/
theorem externalField_pseudoinverse_gap_identity
    (w : Fin n → ℝ) (hw : ∀ i, 0 < w i) (m : ℕ)
    (hmpos : 1 ≤ m) (hmtop : m ≤ n - 1)
    (y : Fin n → ℝ) (hy : IsZeroSum y) :
    (∑ i, y i ^ 2 / covarianceVariance w m i) -
      quadraticForm (externalFieldPseudoinverse w hw m hmpos
        (by simpa using hmtop)) y =
      quadraticForm (comparisonMatrix (covarianceVariance w m))
        ((fun i => y i / covarianceVariance w m i) -
          externalFieldPseudoinverse w hw m hmpos (by simpa using hmtop) *ᵥ y) +
      quadraticForm (covarianceMatrix w m - comparisonMatrix (covarianceVariance w m))
        (externalFieldPseudoinverse w hw m hmpos (by simpa using hmtop) *ᵥ y) := by
  have hv := covarianceVariance_pos w hw m hmpos (by simpa using hmtop)
  have hh := pseudoinverse_gap_identity (covarianceMatrix w m)
    (comparisonMatrix (covarianceVariance w m))
    (pseudoinverse_comparison_isSymm _) y
    (fun i => y i / covarianceVariance w m i)
    (externalFieldPseudoinverse w hw m hmpos (by simpa using hmtop) *ᵥ y)
    (comparison_div_mulVec _ y (fun i => ne_of_gt (hv i)) hy)
    (externalField_pseudoinverse_solves_zeroSum w hw m hmpos
      (by simpa using hmtop) y hy)
  convert hh using 1
  simp only [quadraticForm, dotProduct, pow_two, mul_div_assoc]

/-- The coefficient-one inverse bound follows from the two nonnegative terms. -/
theorem externalField_pseudoinverse_bound
    (w : Fin n → ℝ) (hw : ∀ i, 0 < w i) (m : ℕ)
    (hmpos : 1 ≤ m) (hmtop : m ≤ n - 1)
    (y : Fin n → ℝ) (hy : IsZeroSum y) :
    quadraticForm (externalFieldPseudoinverse w hw m hmpos
      (by simpa using hmtop)) y ≤ ∑ i, y i ^ 2 / covarianceVariance w m i := by
  have hid := externalField_pseudoinverse_gap_identity w hw m hmpos hmtop y hy
  have hv := covarianceVariance_pos w hw m hmpos (by simpa using hmtop)
  have hV := covarianceVariance_sum_pos w hw m hmpos (by simpa using hmtop)
  have hfirst := pseudoinverse_comparison_quadratic_nonneg (covarianceVariance w m)
    ((fun i => y i / covarianceVariance w m i) -
      externalFieldPseudoinverse w hw m hmpos (by simpa using hmtop) *ᵥ y)
    (fun i => (hv i).le) (ne_of_gt hV)
  have hsecond := covariance_comparison_coefficient_one w hw m hmpos hmtop
    (externalFieldPseudoinverse w hw m hmpos (by simpa using hmtop) *ᵥ y)
  rw [quadraticForm_sub] at hid
  linarith

/-- The inverse energy of a nonzero zero-sum demand is strictly positive. -/
theorem externalField_pseudoinverse_quadratic_pos
    (w : Fin n → ℝ) (hw : ∀ i, 0 < w i) (m : ℕ)
    (hmpos : 1 ≤ m) (hmtop : m ≤ n - 1)
    (y : Fin n → ℝ) (hy : IsZeroSum y) (hy0 : y ≠ 0) :
    0 < quadraticForm (externalFieldPseudoinverse w hw m hmpos
      (by simpa using hmtop)) y := by
  let h := externalFieldPseudoinverse w hw m hmpos (by simpa using hmtop) *ᵥ y
  have hsolve : covarianceMatrix w m *ᵥ h = y :=
    externalField_pseudoinverse_solves_zeroSum w hw m hmpos
      (by simpa using hmtop) y hy
  have hnonconst : ¬ ∀ i j, h i = h j := by
    intro hc
    have hz := covariance_mulVec_eq_zero_of_constant w hw m
      (by simpa using (hmtop.trans (Nat.sub_le n 1))) h hc
    rw [hsolve] at hz
    exact hy0 hz
  have henergy : 0 < quadraticForm (covarianceMatrix w m) h := by
    apply lt_of_le_of_ne
    · exact covariance_quadratic_nonnegative w hw (by simpa using
        (hmtop.trans (Nat.sub_le n 1))) h
    · intro hz
      exact hnonconst ((covariance_quadraticForm_eq_zero_iff_constant
        w hw m hmpos (by simpa using hmtop) h).mp hz.symm)
  change 0 < y ⬝ᵥ h
  simpa only [quadraticForm, hsolve, dotProduct_comm h y] using henergy

end CoefficientOne
