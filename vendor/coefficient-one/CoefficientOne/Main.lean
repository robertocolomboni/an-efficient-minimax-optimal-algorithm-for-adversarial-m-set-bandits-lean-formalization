import CoefficientOne.StrictScalarPositivity
import CoefficientOne.ConcreteCertificate
import CoefficientOne.KernelBase
import CoefficientOne.KernelPositivity
import CoefficientOne.NormalizedSpectrum
import CoefficientOne.Sharpness

/-!
# Coefficient one: the complete covariance theorem

For a positive external field on the m-subsets of Fin N, with 1 ≤ m ≤ N-1,
the covariance dominates Diag(v) - vvᵀ / sum(v).  All scalar and certificate
inputs below are proved for the actual alphabet.  The proof follows the
manuscript: scalar bounds, weighted positive certificate, negative kernel
hyperplane, and the direct quadratic-form comparison.  The equivalent
normalized spectral statement and optimality are included.
-/

noncomputable section

namespace CoefficientOne

open Matrix EffectiveResistance AlphabetDeterminants ScalarReciprocity
open ScalarPositivity StrictScalarPositivity

variable {N : ℕ}

/-- The concrete matrix in the manuscript is positive definite. -/
theorem certificate_posDef (a : Fin N → ℝ) (ha : ∀ i, 0 < a i)
    (k : ℕ) (hkpos : 1 ≤ k) (hk : k + 2 ≤ N) :
    (ConcreteCertificate.R a k).PosDef := by
  apply ConcreteCertificate.R_posDef_of_scalar_bounds a ha k (by omega)
  · intro i
    exact scalarA_update_pos a ha k hkpos hk i
  · intro i
    exact scalarB_nonneg _ (zeroLetter_nonneg a (fun j => (ha j).le) i) k

/-- Strict negativity on the manuscript's explicitly constructed hyperplane. -/
theorem kernelMatrix_negative_hyperplane (a : Fin N → ℝ) (ha : ∀ i, 0 < a i)
    (k : ℕ) (hkpos : 1 ≤ k) (hk : k + 2 ≤ N)
    (z : Fin N → ℝ) (hz : z ≠ 0) (hbz : ConcreteCertificate.b a k ⬝ᵥ z = 0) :
    z ⬝ᵥ (kernelMatrix a k *ᵥ z) < 0 := by
  rw [ConcreteCertificate.kernelMatrix_eq_Hzeroed]
  apply ConcreteCertificate.Hzeroed_negative_hyperplane_of_scalar_bounds a ha k (by omega)
    ?_ ?_ z hz hbz
  · intro i
    exact scalarA_update_pos a ha k hkpos hk i
  · intro i
    exact scalarB_nonneg _ (zeroLetter_nonneg a (fun j => (ha j).le) i) k

/-- Both the elementary k=0 case and the certificate case, with no assumed
scalar inequalities or matrix identities left as hypotheses. -/
theorem kernelMatrix_exists_negative_hyperplane (a : Fin N → ℝ)
    (ha : ∀ i, 0 < a i) (k : ℕ) (hk : k + 2 ≤ N) :
    ∃ b : Fin N → ℝ, ∀ z, z ≠ 0 → b ⬝ᵥ z = 0 →
      z ⬝ᵥ (kernelMatrix a k *ᵥ z) < 0 := by
  by_cases hkzero : k = 0
  · subst k
    exact ⟨fun _ => 1, kernelMatrix_zero_neg_on_hyperplane a⟩
  · exact ⟨ConcreteCertificate.b a k,
      kernelMatrix_negative_hyperplane a ha k (by omega) hk⟩

/-- Lemma `lem:inertia`: exactly one positive eigenvalue and N-1 negative
eigenvalues, including multiplicities. -/
theorem kernelMatrix_inertia (a : Fin N → ℝ) (ha : ∀ i, 0 < a i)
    (k : ℕ) (hk : k + 2 ≤ N) :
    ∃ i, 0 < (Matrix.isHermitian_iff_isSymm.mpr (kernelMatrix_isSymm a k)).eigenvalues i ∧
      ∀ j, j ≠ i →
        (Matrix.isHermitian_iff_isSymm.mpr (kernelMatrix_isSymm a k)).eigenvalues j < 0 := by
  obtain ⟨b, hb⟩ := kernelMatrix_exists_negative_hyperplane a ha k hk
  exact kernelMatrix_inertia_of_negative_hyperplane a ha k
    (by simp only [Fintype.card_fin]; omega) (by simp only [Fintype.card_fin]; omega) b hb

/-- The main coefficient-one Loewner comparison for the actual finite law. -/
theorem covariance_comparison_coefficient_one (w : Fin N → ℝ)
    (hw : ∀ i, 0 < w i) (m : ℕ) (hmpos : 1 ≤ m) (hmtop : m ≤ N - 1) :
    LoewnerLE (comparisonMatrix (covarianceVariance w m)) (covarianceMatrix w m) := by
  obtain ⟨b, hb⟩ := kernelMatrix_exists_negative_hyperplane w hw (m - 1) (by omega)
  apply covariance_comparison_of_kernel_hyperplane w hw m hmpos
    (by simpa only [Fintype.card_fin] using hmtop) b
  intro z hz
  have hidx : (m : ℤ) - 1 = ((m - 1 : ℕ) : ℤ) := by omega
  rw [hidx]
  by_cases hz0 : z = 0
  · simp [hz0]
  · exact (hb z hz0 hz).le

/-- Every nonzero eigenvalue of the normalized covariance is at least one. -/
theorem normalized_covariance_eigenvalue_ge_one (w : Fin N → ℝ)
    (hw : ∀ i, 0 < w i) (m : ℕ) (hmpos : 1 ≤ m) (hmtop : m ≤ N - 1) :
    ∀ i, (Matrix.isHermitian_iff_isSymm.mpr
      (normalizedMatrix_isSymm (covarianceMatrix w m) (covariance_isSymm w m))).eigenvalues i ≠ 0 →
      1 ≤ (Matrix.isHermitian_iff_isSymm.mpr
        (normalizedMatrix_isSymm (covarianceMatrix w m) (covariance_isSymm w m))).eigenvalues i :=
  (externalField_comparison_iff_normalized_eigenvalue_gap w hw m hmpos
    (by simpa only [Fintype.card_fin] using hmtop)).mp
      (covariance_comparison_coefficient_one w hw m hmpos hmtop)

/-- Coefficient one holds uniformly, and every larger proposed coefficient
fails already for an explicit positive law on the singletons of Fin 3. -/
theorem covariance_comparison_coefficient_one_optimal :
    (∀ (n : ℕ) (w : Fin n → ℝ), (∀ i, 0 < w i) →
      ∀ m : ℕ, 1 ≤ m → m ≤ n - 1 →
        LoewnerLE (comparisonMatrix (covarianceVariance w m)) (covarianceMatrix w m)) ∧
    (∀ c : ℝ, 1 < c → ∃ w : Fin 3 → ℝ, (∀ i, 0 < w i) ∧
      ¬ LoewnerLE (c • comparisonMatrix (covarianceVariance w 1)) (covarianceMatrix w 1)) :=
  ⟨fun _ w hw m hm ht => covariance_comparison_coefficient_one w hw m hm ht,
    covariance_comparison_constant_one_is_sharp⟩

end CoefficientOne
