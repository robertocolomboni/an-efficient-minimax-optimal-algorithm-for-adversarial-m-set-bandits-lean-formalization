import CoefficientOne.Strictness

/-!
# The strict normalized spectrum

The proof follows the manuscript's inertia-and-trace argument. The matrix
`I - N` is diagonally congruent to the deletion matrix and has exactly one
positive eigenvalue. Its square-root variance vector has eigenvalue one.
Consequently the other eigenvalues of `N` exceed one; its trace supplies the
strict upper endpoint in dimensions at least three.
-/

open scoped BigOperators
open Matrix EffectiveResistance

namespace CoefficientOne

noncomputable section

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- The diagonal congruence for `I - N`, expressed as an equality of forms. -/
theorem normalized_complement_quadraticForm
    (S : Matrix ι ι ℝ) (hdiag : ∀ i, 0 < S i i) (x : ι → ℝ) :
    quadraticForm (1 - normalizedMatrix S) x =
      quadraticForm (Matrix.diagonal (fun i => S i i) - S)
        (x / diagonalSqrtVector S) := by
  rw [quadraticForm_sub, quadraticForm_sub, normalizedMatrix_quadraticForm]
  congr 1
  rw [quadraticForm_diagonal]
  simp only [quadraticForm, Matrix.one_mulVec, dotProduct]
  apply Finset.sum_congr rfl
  intro i hi
  simp only [Pi.div_apply, diagonalSqrtVector, div_pow, Real.sq_sqrt (hdiag i).le]
  field_simp [(hdiag i).ne']

variable {n : ℕ}

theorem normalized_covariance_kernel_vector
    (w : Fin n → ℝ) (hw : ∀ i, 0 < w i) (m : ℕ)
    (hmpos : 1 ≤ m) (hmtop : m ≤ n - 1) :
    normalizedMatrix (covarianceMatrix w m) *ᵥ diagonalSqrtVector (covarianceMatrix w m) = 0 := by
  have hdiag : ∀ i, 0 < covarianceMatrix w m i i := covarianceVariance_pos w hw m hmpos
    (by simpa only [Fintype.card_fin] using hmtop)
  rw [normalizedMatrix_mulVec_eq_zero_iff _ hdiag]
  have hdiv : diagonalSqrtVector (covarianceMatrix w m) /
      diagonalSqrtVector (covarianceMatrix w m) = (fun _ => (1 : ℝ)) := by
    ext i
    exact div_self (diagonalSqrtVector_pos _ hdiag i).ne'
  rw [hdiv]
  exact covariance_mulVec_one_eq_zero w hw m
    (by simpa only [Fintype.card_fin] using hmtop.trans (Nat.sub_le _ _))

theorem normalized_covariance_kernel_vector_norm_pos
    (w : Fin n → ℝ) (hw : ∀ i, 0 < w i) (m : ℕ)
    (hmpos : 1 ≤ m) (hmtop : m ≤ n - 1) :
    0 < diagonalSqrtVector (covarianceMatrix w m) ⬝ᵥ
      diagonalSqrtVector (covarianceMatrix w m) := by
  have hdiag : ∀ i, 0 < covarianceMatrix w m i i := covarianceVariance_pos w hw m hmpos
    (by simpa only [Fintype.card_fin] using hmtop)
  rw [diagonalSqrtVector_dot_self _ hdiag]
  exact covarianceVariance_sum_pos w hw m hmpos
    (by simpa only [Fintype.card_fin] using hmtop)

/-- The strict negative hyperplane transports through the diagonal normalization. -/
theorem normalized_covariance_complement_negative_hyperplane
    (w : Fin n → ℝ) (hw : ∀ i, 0 < w i) (m : ℕ)
    (hmpos : 1 ≤ m) (hmtop : m ≤ n - 1) :
    ∃ b : Fin n → ℝ, ∀ z, z ≠ 0 → b ⬝ᵥ z = 0 →
      z ⬝ᵥ ((1 - normalizedMatrix (covarianceMatrix w m)) *ᵥ z) < 0 := by
  have hdiag : ∀ i, 0 < covarianceMatrix w m i i := covarianceVariance_pos w hw m hmpos
    (by simpa only [Fintype.card_fin] using hmtop)
  let u := diagonalSqrtVector (covarianceMatrix w m)
  obtain ⟨b, hb⟩ := covariance_complement_exists_negative_hyperplane w hw m hmpos hmtop
  refine ⟨b / u, ?_⟩
  intro z hz horth
  have hzne : z / u ≠ 0 := by
    intro hzero
    apply hz
    ext i
    have hi := congrFun hzero i
    exact (div_eq_zero_iff.mp hi).resolve_right (diagonalSqrtVector_pos _ hdiag i).ne'
  have horth' : b ⬝ᵥ (z / u) = 0 := by
    simpa only [dotProduct, Pi.div_apply, div_mul_eq_mul_div, mul_div_assoc] using horth
  change quadraticForm (1 - normalizedMatrix (covarianceMatrix w m)) z < 0
  rw [normalized_complement_quadraticForm _ hdiag]
  exact hb (z / u) hzne horth'

/-- The unique positive eigenvalue of `I - N` is one, and every other one is negative. -/
theorem normalized_covariance_complement_inertia
    (w : Fin n → ℝ) (hw : ∀ i, 0 < w i) (m : ℕ)
    (hmpos : 1 ≤ m) (hmtop : m ≤ n - 1) :
    let M := 1 - normalizedMatrix (covarianceMatrix w m)
    let hM : M.IsHermitian := Matrix.isHermitian_iff_isSymm.mpr
      (Matrix.isSymm_one.sub (normalizedMatrix_isSymm _ (covariance_isSymm w m)))
    ∃ i, hM.eigenvalues i = 1 ∧ ∀ j, j ≠ i → hM.eigenvalues j < 0 := by
  dsimp only
  let M := 1 - normalizedMatrix (covarianceMatrix w m)
  have hM : M.IsHermitian := Matrix.isHermitian_iff_isSymm.mpr
    (Matrix.isSymm_one.sub (normalizedMatrix_isSymm _ (covariance_isSymm w m)))
  let u := diagonalSqrtVector (covarianceMatrix w m)
  have hu : 0 < u ⬝ᵥ u := normalized_covariance_kernel_vector_norm_pos w hw m hmpos hmtop
  have hune : u ≠ 0 := by
    intro hz
    simp [hz] at hu
  have hMu : M *ᵥ u = u := by
    simp only [M, Matrix.sub_mulVec, Matrix.one_mulVec,
      normalized_covariance_kernel_vector w hw m hmpos hmtop, sub_zero, u]
  obtain ⟨b, hb⟩ := normalized_covariance_complement_negative_hyperplane w hw m hmpos hmtop
  obtain ⟨i, hi, hother⟩ := unique_positive_eigenvalue_of_negative_hyperplane
    M hM b u hb (by simpa only [hMu] using hu)
  obtain ⟨j, hj⟩ := eigenvalue_eq_indexed_of_mulVec M hM 1 u hune (by simpa using hMu)
  have hji : j = i := by
    by_contra hne
    have := hother j hne
    linarith
  exact ⟨i, by simpa only [hji] using hj, hother⟩

/-- A nonzero normalized eigenvalue is strictly greater than one. -/
theorem normalized_covariance_eigenvector_gt_one
    (w : Fin n → ℝ) (hw : ∀ i, 0 < w i) (m : ℕ)
    (hmpos : 1 ≤ m) (hmtop : m ≤ n - 1)
    (μ : ℝ) (hμ : μ ≠ 0) (x : Fin n → ℝ) (hx : x ≠ 0)
    (heig : normalizedMatrix (covarianceMatrix w m) *ᵥ x = μ • x) : 1 < μ := by
  let M := 1 - normalizedMatrix (covarianceMatrix w m)
  have hM : M.IsHermitian := Matrix.isHermitian_iff_isSymm.mpr
    (Matrix.isSymm_one.sub (normalizedMatrix_isSymm _ (covariance_isSymm w m)))
  obtain ⟨i, hi, hother⟩ := normalized_covariance_complement_inertia w hw m hmpos hmtop
  have hMx : M *ᵥ x = (1 - μ) • x := by
    simp only [M, Matrix.sub_mulVec, Matrix.one_mulVec, heig, sub_smul, one_smul]
  obtain ⟨j, hj⟩ := eigenvalue_eq_indexed_of_mulVec M hM (1 - μ) x hx hMx
  have hji : j ≠ i := by
    intro hji
    subst j
    apply hμ
    change hM.eigenvalues i = 1 at hi
    linarith
  have hneg := hother j hji
  change hM.eigenvalues j < 0 at hneg
  linarith

theorem normalized_covariance_eigenvalue_gt_one
    (w : Fin n → ℝ) (hw : ∀ i, 0 < w i) (m : ℕ)
    (hmpos : 1 ≤ m) (hmtop : m ≤ n - 1)
    (i : Fin n)
    (hi : (Matrix.isHermitian_iff_isSymm.mpr
      (normalizedMatrix_isSymm _ (covariance_isSymm w m))).eigenvalues i ≠ 0) :
    1 < (Matrix.isHermitian_iff_isSymm.mpr
      (normalizedMatrix_isSymm _ (covariance_isSymm w m))).eigenvalues i := by
  let N := normalizedMatrix (covarianceMatrix w m)
  have hN : N.IsHermitian := Matrix.isHermitian_iff_isSymm.mpr
    (normalizedMatrix_isSymm _ (covariance_isSymm w m))
  exact normalized_covariance_eigenvector_gt_one w hw m hmpos hmtop _ hi
    (⇑(hN.eigenvectorBasis i))
    ((WithLp.ofLp_eq_zero 2).ne.2 (hN.eigenvectorBasis.orthonormal.ne_zero i))
    (hN.mulVec_eigenvectorBasis i)

/-- An exact one-dimensional kernel gives exactly one zero in the indexed spectrum. -/
theorem unique_zero_eigenvalue_of_kernel_line
    (S : Matrix ι ι ℝ) (hS : S.IsHermitian) (u : ι → ℝ)
    (hu : 0 < u ⬝ᵥ u)
    (hker : ∀ x : ι → ℝ, S *ᵥ x = 0 ↔ ∃ c : ℝ, x = c • u) :
    ∃ i, hS.eigenvalues i = 0 ∧ ∀ j, j ≠ i → hS.eigenvalues j ≠ 0 := by
  have hune : u ≠ 0 := by
    intro hz
    simp [hz] at hu
  have hSu : S *ᵥ u = 0 := (hker u).mpr ⟨1, by simp⟩
  obtain ⟨i, hi⟩ := eigenvalue_eq_indexed_of_mulVec S hS 0 u hune (by simpa using hSu)
  refine ⟨i, hi, ?_⟩
  intro j hji hj
  let x : ι → ℝ := ⇑(hS.eigenvectorBasis i)
  let y : ι → ℝ := ⇑(hS.eigenvectorBasis j)
  have hx : x ≠ 0 :=
    (WithLp.ofLp_eq_zero 2).ne.2 (hS.eigenvectorBasis.orthonormal.ne_zero i)
  have hy : y ≠ 0 :=
    (WithLp.ofLp_eq_zero 2).ne.2 (hS.eigenvectorBasis.orthonormal.ne_zero j)
  obtain ⟨a, ha⟩ := (hker x).mp (by simpa [x, hi] using hS.mulVec_eigenvectorBasis i)
  obtain ⟨b, hb⟩ := (hker y).mp (by simpa [y, hj] using hS.mulVec_eigenvectorBasis j)
  have hane : a ≠ 0 := by
    intro hz
    apply hx
    simp [ha, hz]
  have hbne : b ≠ 0 := by
    intro hz
    apply hy
    simp [hb, hz]
  have horth : x ⬝ᵥ y = 0 := by
    simpa only [x, y, EuclideanSpace.inner_eq_star_dotProduct, star_trivial] using
      hS.eigenvectorBasis.inner_eq_zero hji
  rw [ha, hb, smul_dotProduct, dotProduct_smul] at horth
  exact (mul_ne_zero hane (mul_ne_zero hbne hu.ne')) horth

theorem normalized_covariance_unique_zero_eigenvalue
    (w : Fin n → ℝ) (hw : ∀ i, 0 < w i) (m : ℕ)
    (hmpos : 1 ≤ m) (hmtop : m ≤ n - 1) :
    let hN := Matrix.isHermitian_iff_isSymm.mpr
      (normalizedMatrix_isSymm _ (covariance_isSymm w m))
    ∃ i, hN.eigenvalues i = 0 ∧ ∀ j, j ≠ i → hN.eigenvalues j ≠ 0 := by
  haveI : Nonempty (Fin n) := ⟨⟨0, by omega⟩⟩
  apply unique_zero_eigenvalue_of_kernel_line _ _
    (diagonalSqrtVector (covarianceMatrix w m))
    (normalized_covariance_kernel_vector_norm_pos w hw m hmpos hmtop)
  exact normalizedMatrix_kernel_line _
    (covarianceVariance_pos w hw m hmpos (by simpa only [Fintype.card_fin] using hmtop))
    (covariance_mulVec_eq_zero_iff_constant w hw m hmpos
      (by simpa only [Fintype.card_fin] using hmtop))

/-- Trace of normalized covariance, with eigenvalue multiplicities retained. -/
theorem normalized_covariance_sum_eigenvalues
    (w : Fin n → ℝ) (hw : ∀ i, 0 < w i) (m : ℕ)
    (hmpos : 1 ≤ m) (hmtop : m ≤ n - 1) :
    ∑ i, (Matrix.isHermitian_iff_isSymm.mpr
      (normalizedMatrix_isSymm _ (covariance_isSymm w m))).eigenvalues i = (n : ℝ) := by
  let N := normalizedMatrix (covarianceMatrix w m)
  have hN : N.IsHermitian := Matrix.isHermitian_iff_isSymm.mpr
    (normalizedMatrix_isSymm _ (covariance_isSymm w m))
  change ∑ i, hN.eigenvalues i = (n : ℝ)
  have htrace : N.trace = ∑ i, hN.eigenvalues i := by
    simpa using hN.trace_eq_sum_eigenvalues
  rw [← htrace]
  have hdiag : ∀ i, N i i = 1 := fun i => normalizedMatrix_diagonal _ i
    (covarianceVariance_pos w hw m hmpos
      (by simpa only [Fintype.card_fin] using hmtop) i)
  simp [Matrix.trace, Matrix.diag, hdiag]

/-- Deleting the zero eigenvalue and a chosen eigenvalue leaves n-2 terms. -/
theorem trace_erase_two (l : Fin n → ℝ) (i₀ i : Fin n) (hi : i ≠ i₀)
    (hzero : l i₀ = 0) (htrace : ∑ j, l j = (n : ℝ)) :
    let s := (Finset.univ.erase i₀).erase i
    s.card = n - 2 ∧ (∑ j ∈ s, l j) + l i = (n : ℝ) := by
  let s := (Finset.univ.erase i₀).erase i
  have himem : i ∈ Finset.univ.erase i₀ := by simp [hi]
  have hcard : s.card = n - 2 := by
    dsimp [s]
    rw [Finset.card_erase_of_mem himem, Finset.card_erase_of_mem (Finset.mem_univ i₀)]
    simp only [Finset.card_univ, Fintype.card_fin]
    omega
  refine ⟨hcard, ?_⟩
  have hfirst := Finset.sum_erase_add Finset.univ l (Finset.mem_univ i₀)
  have hsecond := Finset.sum_erase_add (Finset.univ.erase i₀) l himem
  rw [hzero, add_zero, htrace] at hfirst
  exact hsecond.trans hfirst

/-- Trace n and the n-2 remaining strict lower bounds force an upper bound two. -/
theorem spectral_trace_lt_two (hn : 3 ≤ n) (l : Fin n → ℝ) (i₀ : Fin n)
    (hzero : l i₀ = 0) (htrace : ∑ j, l j = (n : ℝ))
    (hlower : ∀ j, j ≠ i₀ → 1 < l j) (i : Fin n) (hi : i ≠ i₀) : l i < 2 := by
  let s := (Finset.univ.erase i₀).erase i
  obtain ⟨hcard, hsum⟩ := trace_erase_two l i₀ i hi hzero htrace
  change s.card = n - 2 at hcard
  change (∑ j ∈ s, l j) + l i = (n : ℝ) at hsum
  have hsne : s.Nonempty := Finset.card_pos.mp (by omega)
  have hsumlower : (∑ j ∈ s, (1 : ℝ)) < ∑ j ∈ s, l j := by
    apply Finset.sum_lt_sum
    · intro j hj
      exact (hlower j (by simpa [s] using (Finset.mem_erase.mp hj).2)).le
    · obtain ⟨j, hj⟩ := hsne
      exact ⟨j, hj, hlower j (by simpa [s] using (Finset.mem_erase.mp hj).2)⟩
  have hones : (∑ j ∈ s, (1 : ℝ)) = (n : ℝ) - 2 := by
    simp only [Finset.sum_const, nsmul_eq_mul, mul_one, hcard]
    rw [Nat.cast_sub (by omega : 2 ≤ n)]
    norm_num
  rw [hones] at hsumlower
  linarith

theorem normalized_covariance_eigenvalue_lt_two
    (w : Fin n → ℝ) (hw : ∀ i, 0 < w i) (m : ℕ)
    (hmpos : 1 ≤ m) (hmtop : m ≤ n - 1) (hn : 3 ≤ n)
    (i : Fin n)
    (hi : (Matrix.isHermitian_iff_isSymm.mpr
      (normalizedMatrix_isSymm _ (covariance_isSymm w m))).eigenvalues i ≠ 0) :
    (Matrix.isHermitian_iff_isSymm.mpr
      (normalizedMatrix_isSymm _ (covariance_isSymm w m))).eigenvalues i < 2 := by
  let N := normalizedMatrix (covarianceMatrix w m)
  have hN : N.IsHermitian := Matrix.isHermitian_iff_isSymm.mpr
    (normalizedMatrix_isSymm _ (covariance_isSymm w m))
  obtain ⟨i₀, hzero, hother⟩ := normalized_covariance_unique_zero_eigenvalue w hw m hmpos hmtop
  exact spectral_trace_lt_two hn hN.eigenvalues i₀ hzero
    (normalized_covariance_sum_eigenvalues w hw m hmpos hmtop)
    (fun j hj => normalized_covariance_eigenvalue_gt_one w hw m hmpos hmtop j (hother j hj))
    i (by intro h; exact hi (h ▸ hzero))

/-- In dimension two, trace two and a simple zero leave the eigenvalue two. -/
theorem normalized_covariance_eigenvalue_eq_two_of_dimension_two
    (w : Fin 2 → ℝ) (hw : ∀ i, 0 < w i) (m : ℕ)
    (hmpos : 1 ≤ m) (hmtop : m ≤ 2 - 1) (i : Fin 2)
    (hi : (Matrix.isHermitian_iff_isSymm.mpr
      (normalizedMatrix_isSymm _ (covariance_isSymm w m))).eigenvalues i ≠ 0) :
    (Matrix.isHermitian_iff_isSymm.mpr
      (normalizedMatrix_isSymm _ (covariance_isSymm w m))).eigenvalues i = 2 := by
  let N := normalizedMatrix (covarianceMatrix w m)
  have hN : N.IsHermitian := Matrix.isHermitian_iff_isSymm.mpr
    (normalizedMatrix_isSymm _ (covariance_isSymm w m))
  obtain ⟨i₀, hzero, _⟩ := normalized_covariance_unique_zero_eigenvalue w hw m hmpos hmtop
  obtain ⟨hcard, hsum⟩ := trace_erase_two hN.eigenvalues i₀ i
    (by intro h; exact hi (h ▸ hzero)) hzero
    (normalized_covariance_sum_eigenvalues w hw m hmpos hmtop)
  have hempty : (Finset.univ.erase i₀).erase i = ∅ :=
    Finset.card_eq_zero.mp (by simpa using hcard)
  simpa [hempty] using hsum

/-- The strict spectral inclusion stated in the manuscript for dimensions at least three. -/
theorem normalized_covariance_spectrum_subset_strict
    (w : Fin n → ℝ) (hw : ∀ i, 0 < w i) (m : ℕ)
    (hmpos : 1 ≤ m) (hmtop : m ≤ n - 1) (hn : 3 ≤ n) :
    spectrum ℝ (normalizedMatrix (covarianceMatrix w m)) ⊆
      ({0} : Set ℝ) ∪ Set.Ioo 1 2 := by
  have hN := Matrix.isHermitian_iff_isSymm.mpr
    (normalizedMatrix_isSymm _ (covariance_isSymm w m))
  rw [hN.spectrum_real_eq_range_eigenvalues]
  rintro μ ⟨i, rfl⟩
  by_cases hi : hN.eigenvalues i = 0
  · exact Or.inl hi
  · exact Or.inr ⟨normalized_covariance_eigenvalue_gt_one w hw m hmpos hmtop i hi,
      normalized_covariance_eigenvalue_lt_two w hw m hmpos hmtop hn i hi⟩

/-- The dimension-two spectrum has exactly the two values zero and two. -/
theorem normalized_covariance_spectrum_dimension_two
    (w : Fin 2 → ℝ) (hw : ∀ i, 0 < w i) (m : ℕ)
    (hmpos : 1 ≤ m) (hmtop : m ≤ 2 - 1) :
    spectrum ℝ (normalizedMatrix (covarianceMatrix w m)) = ({0, 2} : Set ℝ) := by
  have hN := Matrix.isHermitian_iff_isSymm.mpr
    (normalizedMatrix_isSymm _ (covariance_isSymm w m))
  rw [hN.spectrum_real_eq_range_eigenvalues]
  obtain ⟨i₀, hzero, hother⟩ := normalized_covariance_unique_zero_eigenvalue w hw m hmpos hmtop
  ext μ
  constructor
  · rintro ⟨i, rfl⟩
    by_cases hi : hN.eigenvalues i = 0
    · simp [hi]
    · have htwo := normalized_covariance_eigenvalue_eq_two_of_dimension_two w hw m hmpos hmtop i hi
      simp [htwo]
  · intro hμ
    rcases (show μ = 0 ∨ μ = 2 from hμ) with rfl | rfl
    · exact ⟨i₀, hzero⟩
    · obtain ⟨j, hji⟩ := Fintype.exists_ne_of_one_lt_card
        (by simp : 1 < Fintype.card (Fin 2)) i₀
      exact ⟨j, normalized_covariance_eigenvalue_eq_two_of_dimension_two w hw m hmpos hmtop j
        (hother j hji)⟩

end

end CoefficientOne
