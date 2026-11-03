import CoefficientOne.Sampling.ConditionalGap
import CoefficientOne.Sampling.BinaryRegression

/-! # The coefficient-one operator inequality for conditional variances -/

open scoped BigOperators
open Matrix EffectiveResistance Unitary

namespace CoefficientOne.Sampling
noncomputable section

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- The spectral step in E.2: eigenvalues zero or at least one imply B² ≥ B. -/
theorem square_sub_self_posSemidef_of_gap (B : Matrix ι ι ℝ) (hB : B.IsHermitian)
    (hg : ∀ i, hB.eigenvalues i ≠ 0 → 1 ≤ hB.eigenvalues i) :
    (B * B - B).PosSemidef := by
  let f := conjStarAlgAut ℝ (Matrix ι ι ℝ) hB.eigenvectorUnitary
  have hs : B = f (Matrix.diagonal hB.eigenvalues) := by
    simpa [f, Function.comp_def] using hB.spectral_theorem
  have heq : B * B - B = f (Matrix.diagonal (fun i => (hB.eigenvalues i) ^ 2 - hB.eigenvalues i)) := by
    conv_lhs => rw [hs]
    rw [← map_mul, ← map_sub]
    congr 1
    rw [Matrix.diagonal_mul_diagonal, ← Matrix.diagonal_sub]
    congr 1
    ext i
    simp [pow_two]
  have hd : (Matrix.diagonal (fun i => (hB.eigenvalues i) ^ 2 - hB.eigenvalues i)).PosSemidef := by
    apply Matrix.posSemidef_diagonal_iff.mpr
    intro i
    by_cases hi : hB.eigenvalues i = 0
    · simp [hi]
    · have h := hg i hi
      nlinarith
  rw [heq]
  simpa [f, conjStarAlgAut_apply, Matrix.star_eq_conjTranspose] using
    hd.mul_mul_conjTranspose_same (hB.eigenvectorUnitary : Matrix ι ι ℝ)

theorem quadraticForm_square (B : Matrix ι ι ℝ) (hB : B.IsSymm) (x : ι → ℝ) :
    quadraticForm (B * B) x = (B *ᵥ x) ⬝ᵥ (B *ᵥ x) := by
  rw [quadraticForm, ← Matrix.mulVec_mulVec, dotProduct_mulVec]
  congr 1
  ext i
  simp only [Matrix.vecMul, Matrix.mulVec, dotProduct]
  apply Finset.sum_congr rfl
  intro j _
  rw [hB.apply i j]
  ring

/-- Coordinate form of CD⁻¹C ≥ C, obtained by the manuscript's diagonal
normalization and the spectral inequality B² ≥ B. -/
theorem covariance_operator_ge_one (w : ι → ℝ) (hw : ∀ i, 0 < w i)
    (k : ℕ) (hkpos : 1 ≤ k) (hktop : k ≤ Fintype.card ι - 1) (a : ι → ℝ) :
    quadraticForm (covarianceMatrix w k) a ≤
      ∑ i, ((covarianceMatrix w k *ᵥ a) i) ^ 2 / covarianceMatrix w k i i := by
  let C := covarianceMatrix w k
  let B := normalizedMatrix C
  let u := diagonalSqrtVector C
  have hd : ∀ i, 0 < C i i := covarianceVariance_pos w hw k hkpos hktop
  have hB : B.IsSymm := normalizedMatrix_isSymm C (covariance_isSymm w k)
  have hpos := square_sub_self_posSemidef_of_gap B (Matrix.isHermitian_iff_isSymm.mpr hB)
    (normalized_covariance_gap_fintype w hw k hkpos hktop)
  have he := hpos.dotProduct_mulVec_nonneg (u * a)
  simp only [star_trivial] at he
  change 0 ≤ quadraticForm (B * B - B) (u * a) at he
  rw [quadraticForm_sub, quadraticForm_square B hB] at he
  have hCa : B *ᵥ (u * a) = (C *ᵥ a) / u := by
    dsimp only [B, u]
    rw [normalizedMatrix_mulVec_eq, mul_diagonalSqrtVector_div_self C hd a]
  have hq : quadraticForm B (u * a) = quadraticForm C a := by
    dsimp only [B, u]
    rw [normalizedMatrix_quadraticForm, mul_diagonalSqrtVector_div_self C hd a]
  rw [hCa, hq] at he
  have hn : ((C *ᵥ a) / u) ⬝ᵥ ((C *ᵥ a) / u) =
      ∑ i, ((C *ᵥ a) i) ^ 2 / C i i := by
    unfold dotProduct
    apply Finset.sum_congr rfl
    intro i _
    simp only [Pi.div_apply, u, diagonalSqrtVector]
    rw [← pow_two, div_pow, Real.sq_sqrt (hd i).le]
  rw [hn] at he
  exact sub_nonneg.mp he

/-- The expected remaining variance after revealing coordinate i. -/
def coordinateRemainingVariance {k : ℕ} (p : FiniteLaw (RankSubset ι k))
    (a : ι → ℝ) (i : ι) (hv : 0 < lawCovariance p i i) : ℝ :=
  binaryMass p (rankIndicatorBit i) false *
    lawVariance (binaryConditionalLaw p (rankIndicatorBit i) false
      (binaryMass_indicator_pos p i hv false)) (lawLinearStatistic a) +
  binaryMass p (rankIndicatorBit i) true *
    lawVariance (binaryConditionalLaw p (rankIndicatorBit i) true
      (binaryMass_indicator_pos p i hv true)) (lawLinearStatistic a)

/-- Averaging the exact binary identity over a uniform coordinate. This is a
finite-law identity; its use at random histories requires the separate reveal-law bridge. -/
theorem uniform_coordinate_variance_drop [Nonempty ι] {k : ℕ}
    (p : FiniteLaw (RankSubset ι k)) (a : ι → ℝ)
    (hv : ∀ i, 0 < lawCovariance p i i) :
    lawVariance p (lawLinearStatistic a) - (Fintype.card ι : ℝ)⁻¹ *
      ∑ i, coordinateRemainingVariance p a i (hv i) =
    (Fintype.card ι : ℝ)⁻¹ * ∑ i, ((lawCovariance p *ᵥ a) i) ^ 2 / lawCovariance p i i := by
  have hsum : (Fintype.card ι : ℝ) * lawVariance p (lawLinearStatistic a) -
      (∑ i, coordinateRemainingVariance p a i (hv i)) =
      ∑ i, ((lawCovariance p *ᵥ a) i) ^ 2 / lawCovariance p i i := by
    have he := Finset.sum_congr (s₁ := Finset.univ) (s₂ := Finset.univ) rfl
      (fun i _ => binary_indicator_variance_drop p a i (hv i))
    simpa only [coordinateRemainingVariance, Finset.sum_sub_distrib,
      Finset.sum_const, Finset.card_univ, nsmul_eq_mul] using he
  have hn : (Fintype.card ι : ℝ) ≠ 0 := by exact_mod_cast Fintype.card_ne_zero
  calc
    _ = (Fintype.card ι : ℝ)⁻¹ * ((Fintype.card ι : ℝ) *
        lawVariance p (lawLinearStatistic a) - ∑ i, coordinateRemainingVariance p a i (hv i)) := by
      field_simp [hn]
    _ = _ := by rw [hsum]

/-- The full one-step inequality from the actual positive external-field law:
the average variance drop is at least one over the number of coordinates times
the current variance. No law of random sampler states is assumed here. -/
theorem externalField_uniform_variance_drop (w : ι → ℝ) (hw : ∀ i, 0 < w i)
    (k : ℕ) (hkpos : 1 ≤ k) (hktop : k ≤ Fintype.card ι - 1) (a : ι → ℝ) :
    let p := externalFieldLaw w hw (hktop.trans (Nat.sub_le _ _))
    let hv : ∀ i, 0 < lawCovariance p i i := covarianceVariance_pos w hw k hkpos hktop
    (Fintype.card ι : ℝ)⁻¹ * lawVariance p (lawLinearStatistic a) ≤
      lawVariance p (lawLinearStatistic a) - (Fintype.card ι : ℝ)⁻¹ *
        ∑ i, coordinateRemainingVariance p a i (hv i) := by
  dsimp only
  haveI : Nonempty ι := Fintype.card_pos_iff.mp (by omega)
  erw [uniform_coordinate_variance_drop, lawVariance_linearStatistic]
  exact mul_le_mul_of_nonneg_left (covariance_operator_ge_one w hw k hkpos hktop a)
    (inv_nonneg.mpr (Nat.cast_nonneg _))

end
end CoefficientOne.Sampling
