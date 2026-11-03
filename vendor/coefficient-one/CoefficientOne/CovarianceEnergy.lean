import CoefficientOne.PseudoinverseIdentity

/-!
# The covariance graph and the upper spectral endpoint

This is the edge-energy proof in Appendix E.1.  The upper bound two follows
from `(a-b)^2 ≤ 2(a^2+b^2)`, independently of the strict inertia/trace proof.
-/

open scoped BigOperators
open Matrix EffectiveResistance

namespace CoefficientOne

noncomputable section

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- The graph energy, with each edge counted once. -/
theorem network_energy_eq_sum_lt [LinearOrder ι]
    (G : ConductanceNetwork ι) (x : ι → ℝ) :
    quadraticForm G.laplacian x =
      ∑ i, ∑ j, if i < j then G.conductance i j * (x i - x j) ^ 2 else 0 := by
  rw [← G.energy_eq_quadraticForm, G.energy_eq_half_edgePairingSum]
  have hsum := sum_symmetric_eq_two_sum_lt
    (fun i j => G.conductance i j * (x i - x j) ^ 2)
    (fun i j => by rw [G.conductance_comm i j, sub_sq_comm])
    (fun i => by simp)
  unfold ConductanceNetwork.edgePairingSum
  rw [Fintype.sum_prod_type]
  simp_rw [mul_assoc, ← pow_two]
  rw [hsum]
  ring

/-- The upper energy estimate for every finite nonnegative conductance network. -/
theorem network_energy_le_two_degree (G : ConductanceNetwork ι) (x : ι → ℝ) :
    quadraticForm G.laplacian x ≤ 2 * ∑ i, G.degree i * x i ^ 2 := by
  rw [← G.energy_eq_quadraticForm, G.energy_eq_half_edgePairingSum]
  have hterm (i j : ι) :
      G.conductance i j * (x i - x j) ^ 2 ≤
        G.conductance i j * (2 * (x i ^ 2 + x j ^ 2)) := by
    apply mul_le_mul_of_nonneg_left _ (G.nonnegative i j)
    nlinarith [sq_nonneg (x i + x j)]
  have hleft : (∑ i, ∑ j, G.conductance i j * x i ^ 2) =
      ∑ i, G.degree i * x i ^ 2 := by
    simp only [ConductanceNetwork.degree, Finset.sum_mul]
  have hright : (∑ i, ∑ j, G.conductance i j * x j ^ 2) =
      ∑ i, G.degree i * x i ^ 2 := by
    rw [Finset.sum_comm]
    simp_rw [G.conductance_comm]
    exact hleft
  calc
    _ = (2 : ℝ)⁻¹ * ∑ i, ∑ j, G.conductance i j * (x i - x j) ^ 2 := by
      simp only [ConductanceNetwork.edgePairingSum, Fintype.sum_prod_type, pow_two, mul_assoc]
    _ ≤ (2 : ℝ)⁻¹ * ∑ i, ∑ j, G.conductance i j * (2 * (x i ^ 2 + x j ^ 2)) := by
      apply mul_le_mul_of_nonneg_left _ (by norm_num)
      exact Finset.sum_le_sum (fun i _ => Finset.sum_le_sum (fun j _ => hterm i j))
    _ = 2 * ∑ i, G.degree i * x i ^ 2 := by
      simp_rw [show ∀ i j, G.conductance i j * (2 * (x i ^ 2 + x j ^ 2)) =
        2 * (G.conductance i j * x i ^ 2) + 2 * (G.conductance i j * x j ^ 2) by
          intro i j; ring]
      simp only [Finset.sum_add_distrib, ← Finset.mul_sum]
      rw [hleft, hright]
      ring

/-- The actual fixed-rank covariance energy in the paper's i<j notation. -/
theorem covariance_energy_eq_sum_lt {n : ℕ}
    (w : Fin n → ℝ) (hw : ∀ i, 0 < w i) (m : ℕ)
    (hmpos : 1 ≤ m) (hmtop : m ≤ n - 1) (x : Fin n → ℝ) :
    quadraticForm (covarianceMatrix w m) x =
      ∑ i, ∑ j, if i < j then (-covarianceMatrix w m i j) * (x i - x j) ^ 2 else 0 := by
  have h := network_energy_eq_sum_lt
    (externalFieldCovarianceNetwork w hw m hmpos (by simpa using hmtop)) x
  rw [externalFieldCovarianceNetwork_laplacian] at h
  rw [h]
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  by_cases hij : i < j
  · simp [hij, externalFieldCovarianceNetwork, covarianceNetwork, ne_of_lt hij]
  · simp [hij]

/-- Appendix E.1: the covariance energy is at most twice the diagonal energy. -/
theorem covariance_energy_le_two_variance
    (w : ι → ℝ) (hw : ∀ i, 0 < w i) (m : ℕ)
    (hmpos : 1 ≤ m) (hmtop : m ≤ Fintype.card ι - 1) (x : ι → ℝ) :
    quadraticForm (covarianceMatrix w m) x ≤
      2 * ∑ i, covarianceVariance w m i * x i ^ 2 := by
  have h := network_energy_le_two_degree
    (externalFieldCovarianceNetwork w hw m hmpos hmtop) x
  simpa only [externalFieldCovarianceNetwork_laplacian,
    externalFieldCovarianceNetwork_degree_eq, covarianceVariance] using h

/-- Normalize the upper energy estimate by the square-root variances. -/
theorem normalized_covariance_energy_le_two
    (w : ι → ℝ) (hw : ∀ i, 0 < w i) (m : ℕ)
    (hmpos : 1 ≤ m) (hmtop : m ≤ Fintype.card ι - 1) (x : ι → ℝ) :
    quadraticForm (normalizedMatrix (covarianceMatrix w m)) x ≤ 2 * (x ⬝ᵥ x) := by
  rw [normalizedMatrix_quadraticForm]
  have h := covariance_energy_le_two_variance w hw m hmpos hmtop
    (x / diagonalSqrtVector (covarianceMatrix w m))
  have heq : (∑ i, covarianceVariance w m i *
      (x / diagonalSqrtVector (covarianceMatrix w m)) i ^ 2) = x ⬝ᵥ x := by
    unfold dotProduct
    apply Finset.sum_congr rfl
    intro i _
    have hv := covarianceVariance_pos w hw m hmpos hmtop i
    change 0 < covarianceMatrix w m i i at hv
    simp only [Pi.div_apply, diagonalSqrtVector, div_pow,
      Real.sq_sqrt hv.le, ← pow_two, covarianceVariance]
    field_simp [hv.ne']
  rwa [heq] at h

/-- The upper eigenvalue bound follows directly from the graph-energy estimate. -/
theorem normalized_covariance_eigenvector_le_two_from_energy
    (w : ι → ℝ) (hw : ∀ i, 0 < w i) (m : ℕ)
    (hmpos : 1 ≤ m) (hmtop : m ≤ Fintype.card ι - 1)
    (μ : ℝ) (x : ι → ℝ) (hx : x ≠ 0)
    (heig : normalizedMatrix (covarianceMatrix w m) *ᵥ x = μ • x) : μ ≤ 2 := by
  have hb := normalized_covariance_energy_le_two w hw m hmpos hmtop x
  have hnorm : 0 < x ⬝ᵥ x := by
    simpa only [star_trivial] using dotProduct_self_star_pos_iff.mpr hx
  rw [quadraticForm, heig, dotProduct_smul, smul_eq_mul] at hb
  nlinarith

theorem normalized_covariance_eigenvalue_le_two_from_energy {n : ℕ}
    (w : Fin n → ℝ) (hw : ∀ i, 0 < w i) (m : ℕ)
    (hmpos : 1 ≤ m) (hmtop : m ≤ n - 1) (i : Fin n) :
    (Matrix.isHermitian_iff_isSymm.mpr
      (normalizedMatrix_isSymm _ (covariance_isSymm w m))).eigenvalues i ≤ 2 := by
  let hN := Matrix.isHermitian_iff_isSymm.mpr
    (normalizedMatrix_isSymm _ (covariance_isSymm w m))
  exact normalized_covariance_eigenvector_le_two_from_energy w hw m hmpos
    (by simpa using hmtop) _ (⇑(hN.eigenvectorBasis i))
    ((WithLp.ofLp_eq_zero 2).ne.2 (hN.eigenvectorBasis.orthonormal.ne_zero i))
    (hN.mulVec_eigenvectorBasis i)

/-- The nonstrict spectral inclusion proved in Appendix E.1, by its energy route. -/
theorem normalized_covariance_spectrum_subset_from_energy {n : ℕ}
    (w : Fin n → ℝ) (hw : ∀ i, 0 < w i) (m : ℕ)
    (hmpos : 1 ≤ m) (hmtop : m ≤ n - 1) :
    spectrum ℝ (normalizedMatrix (covarianceMatrix w m)) ⊆
      ({0} : Set ℝ) ∪ Set.Icc 1 2 := by
  have hN := Matrix.isHermitian_iff_isSymm.mpr
    (normalizedMatrix_isSymm _ (covariance_isSymm w m))
  rw [hN.spectrum_real_eq_range_eigenvalues]
  rintro μ ⟨i, rfl⟩
  by_cases hi : hN.eigenvalues i = 0
  · exact Or.inl hi
  · exact Or.inr ⟨normalized_covariance_eigenvalue_ge_one w hw m hmpos hmtop i hi,
      normalized_covariance_eigenvalue_le_two_from_energy w hw m hmpos hmtop i⟩

end

end CoefficientOne
