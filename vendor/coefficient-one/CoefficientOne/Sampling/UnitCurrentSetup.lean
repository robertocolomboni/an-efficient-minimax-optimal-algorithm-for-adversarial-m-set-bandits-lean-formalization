import CoefficientOne.NormalizedSpectrum
import CoefficientOne.RegularizedGreenKernel
import EffectiveResistance.EdgeVariation

/-!
# Unit-current setup: normalization and the positive Gram matrix

The network is arbitrary: connectedness means that its Laplacian kernel consists
of constants. No external-field representation or strict completeness is assumed.
The normalized conductances below are exactly the manuscript's replacement C/s.
-/

open scoped BigOperators
open Matrix EffectiveResistance

namespace CoefficientOne.Sampling

noncomputable section

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

def degreeMass (N : ConductanceNetwork ι) : ℝ := ∑ i, N.degree i

def stationaryMass (N : ConductanceNetwork ι) (i : ι) : ℝ :=
  N.degree i / degreeMass N

def normalizedConductance (N : ConductanceNetwork ι) : Matrix ι ι ℝ :=
  fun i j => N.conductance i j / degreeMass N

def transitionMatrix (N : ConductanceNetwork ι) : Matrix ι ι ℝ :=
  fun i j => N.conductance i j / N.degree i

def currentGramMatrix (N : ConductanceNetwork ι) : Matrix ι ι ℝ :=
  Matrix.vecMulVec (stationaryMass N) (stationaryMass N) - normalizedConductance N

def HasConstantKernel (N : ConductanceNetwork ι) : Prop :=
  ∀ x : ι → ℝ, N.laplacian *ᵥ x = 0 ↔ ∀ i j, x i = x j

def HasNormalizedGapOne (N : ConductanceNetwork ι) : Prop :=
  ∀ i, (Matrix.isHermitian_iff_isSymm.mpr
    (normalizedMatrix_isSymm N.laplacian N.laplacian_isSymm)).eigenvalues i ≠ 0 →
    1 ≤ (Matrix.isHermitian_iff_isSymm.mpr
      (normalizedMatrix_isSymm N.laplacian N.laplacian_isSymm)).eigenvalues i

theorem degreeMass_pos [Nonempty ι] (N : ConductanceNetwork ι)
    (hd : ∀ i, 0 < N.degree i) : 0 < degreeMass N :=
  Finset.sum_pos (fun i _ => hd i) Finset.univ_nonempty

theorem stationaryMass_pos [Nonempty ι] (N : ConductanceNetwork ι)
    (hd : ∀ i, 0 < N.degree i) (i : ι) : 0 < stationaryMass N i :=
  div_pos (hd i) (degreeMass_pos N hd)

theorem sum_stationaryMass [Nonempty ι] (N : ConductanceNetwork ι)
    (hd : ∀ i, 0 < N.degree i) : ∑ i, stationaryMass N i = 1 := by
  simp only [stationaryMass, ← Finset.sum_div]
  exact div_self (degreeMass_pos N hd).ne'

theorem normalizedConductance_nonneg [Nonempty ι] (N : ConductanceNetwork ι)
    (hd : ∀ i, 0 < N.degree i) (i j : ι) : 0 ≤ normalizedConductance N i j :=
  div_nonneg (N.nonnegative i j) (degreeMass_pos N hd).le

theorem normalizedConductance_comm (N : ConductanceNetwork ι) (i j : ι) :
    normalizedConductance N i j = normalizedConductance N j i := by
  simp only [normalizedConductance, N.conductance_comm i j]

@[simp] theorem normalizedConductance_diagonal (N : ConductanceNetwork ι) (i : ι) :
    normalizedConductance N i i = 0 := by
  simp [normalizedConductance, N.diagonal_zero]

theorem normalizedConductance_rowSum (N : ConductanceNetwork ι) (i : ι) :
    ∑ j, normalizedConductance N i j = stationaryMass N i := by
  simp [normalizedConductance, stationaryMass, ← Finset.sum_div,
    ConductanceNetwork.degree]

theorem normalizedConductance_sum [Nonempty ι] (N : ConductanceNetwork ι)
    (hd : ∀ i, 0 < N.degree i) : ∑ i, ∑ j, normalizedConductance N i j = 1 := by
  simp_rw [normalizedConductance_rowSum]
  exact sum_stationaryMass N hd

theorem stationary_transition (N : ConductanceNetwork ι)
    (hd : ∀ i, 0 < N.degree i) (i j : ι) :
    stationaryMass N i * transitionMatrix N i j = normalizedConductance N i j := by
  simp only [stationaryMass, transitionMatrix, normalizedConductance]
  field_simp [(hd i).ne']

theorem transition_rowSum (N : ConductanceNetwork ι)
    (hd : ∀ i, 0 < N.degree i) (i : ι) : ∑ j, transitionMatrix N i j = 1 := by
  simp only [transitionMatrix, ← Finset.sum_div]
  exact div_self (hd i).ne'

@[simp] theorem transition_diagonal (N : ConductanceNetwork ι) (i : ι) :
    transitionMatrix N i i = 0 := by
  simp [transitionMatrix, N.diagonal_zero]

theorem stationary_transition_reversible (N : ConductanceNetwork ι)
    (hd : ∀ i, 0 < N.degree i) (i j : ι) :
    stationaryMass N i * transitionMatrix N i j =
      stationaryMass N j * transitionMatrix N j i := by
  rw [stationary_transition N hd, stationary_transition N hd,
    normalizedConductance_comm N i j]

theorem stationary_transition_columnSum (N : ConductanceNetwork ι)
    (hd : ∀ i, 0 < N.degree i) (j : ι) :
    ∑ i, stationaryMass N i * transitionMatrix N i j = stationaryMass N j := by
  simp_rw [stationary_transition N hd, normalizedConductance_comm N _ j]
  exact normalizedConductance_rowSum N j

theorem currentGramMatrix_isSymm (N : ConductanceNetwork ι) :
    (currentGramMatrix N).IsSymm := by
  apply Matrix.IsSymm.ext
  intro i j
  simp only [currentGramMatrix, Matrix.sub_apply, Matrix.vecMulVec_apply]
  rw [normalizedConductance_comm N i j, mul_comm]

theorem currentGramMatrix_diagonal (N : ConductanceNetwork ι) (i : ι) :
    currentGramMatrix N i i = (stationaryMass N i) ^ 2 := by
  simp [currentGramMatrix, Matrix.vecMulVec, pow_two]

theorem currentGramMatrix_mulVec_one [Nonempty ι] (N : ConductanceNetwork ι)
    (hd : ∀ i, 0 < N.degree i) : currentGramMatrix N *ᵥ (fun _ => 1) = 0 := by
  ext i
  simp only [Matrix.mulVec, dotProduct, currentGramMatrix, Matrix.sub_apply,
    Matrix.vecMulVec_apply, mul_one, Finset.sum_sub_distrib, ← Finset.mul_sum,
    sum_stationaryMass N hd, normalizedConductance_rowSum, mul_one, sub_self,
    Pi.zero_apply]

/-- Entrywise identification with the centered quadratic-form comparison.
This is Q=(C-comparisonMatrix d)/s, equivalent to ππᵀ-DP after normalization. -/
theorem currentGramMatrix_eq_scaled_defect (N : ConductanceNetwork ι) :
    currentGramMatrix N = (degreeMass N)⁻¹ •
      (N.laplacian - comparisonMatrix N.degree) := by
  ext i j
  simp only [currentGramMatrix, stationaryMass, normalizedConductance,
    Matrix.sub_apply, Matrix.vecMulVec_apply, ConductanceNetwork.laplacian,
    comparisonMatrix, Matrix.smul_apply, smul_eq_mul, totalWeight, degreeMass]
  simp only [div_eq_mul_inv]
  ring

theorem comparison_of_normalized_gap [Nonempty ι] (N : ConductanceNetwork ι)
    (hd : ∀ i, 0 < N.degree i) (hk : HasConstantKernel N)
    (hg : HasNormalizedGapOne N) :
    LoewnerLE (comparisonMatrix N.degree) N.laplacian := by
  have h := (covariance_comparison_iff_normalized_eigenvalue_gap N.laplacian
    N.laplacian_isSymm (fun i => by rw [N.laplacian_diagonal]; exact hd i) hk).mpr hg
  simpa only [N.laplacian_diagonal] using h

/-- The positive matrix Q in the manuscript, for an arbitrary connected network
with normalized gap one. The spectral comparison is generic, not a covariance assumption. -/
theorem currentGramMatrix_posSemidef [Nonempty ι] (N : ConductanceNetwork ι)
    (hd : ∀ i, 0 < N.degree i) (hk : HasConstantKernel N)
    (hg : HasNormalizedGapOne N) : (currentGramMatrix N).PosSemidef := by
  apply Matrix.posSemidef_iff_dotProduct_mulVec.mpr
  refine ⟨Matrix.isHermitian_iff_isSymm.mpr (currentGramMatrix_isSymm N), ?_⟩
  intro x
  simp only [star_trivial]
  change 0 ≤ quadraticForm (currentGramMatrix N) x
  rw [currentGramMatrix_eq_scaled_defect, quadraticForm_smul, quadraticForm_sub]
  exact mul_nonneg (inv_nonneg.mpr (degreeMass_pos N hd).le)
    (sub_nonneg.mpr (comparison_of_normalized_gap N hd hk hg x))

end
end CoefficientOne.Sampling
