import CoefficientOne.UniformLaw
import CoefficientOne.EffectiveResistanceCorollary
import Mathlib.Analysis.SpecificLimits.Basic

/-!
# Effective resistance of uniform fixed-rank laws and sharpness

These are the computations in Appendix E.3. The matrix formula comes from the
actual uniform law in `UniformLaw`. Solving the pair-demand equation computes
its canonical Green resistance. Growing dimension at rank one proves that no
coefficient below one works uniformly, even just on pair demands.
-/

open scoped BigOperators
open Matrix EffectiveResistance Filter

namespace CoefficientOne
noncomputable section

theorem uniform_covariance_mulVec_zeroSum {n : ℕ} (hn : 2 ≤ n)
    (m : ℕ) (hm : m ≤ n) (y : Fin n → ℝ) (hy : IsZeroSum y) :
    covarianceMatrix (uniformWeights n) m *ᵥ y =
      ((n : ℝ) * uniformVariance n m / ((n : ℝ) - 1)) • y := by
  rw [uniform_covariance_matrix hn m hm, Matrix.smul_mulVec, Matrix.sub_mulVec,
    Matrix.one_mulVec, Matrix.smul_mulVec]
  have hzero : Matrix.vecMulVec (fun _ : Fin n => (1 : ℝ)) (fun _ => 1) *ᵥ y = 0 := by
    funext i
    simpa [Matrix.mulVec, Matrix.vecMulVec, dotProduct, IsZeroSum] using hy
  rw [hzero]
  simp

theorem uniform_effectiveResistance {n : ℕ} (m : ℕ)
    (hmpos : 1 ≤ m) (hmtop : m ≤ n - 1) (i j : Fin n) (hij : i ≠ j) :
    (externalFieldGreenKernel (uniformWeights n) (uniformWeights_pos n) m hmpos
      (by simpa using hmtop)).effectiveResistance i j =
      2 * ((n : ℝ) - 1) / ((n : ℝ) * uniformVariance n m) := by
  have hn : 2 ≤ n := by omega
  have hn0 : (n : ℝ) ≠ 0 := by exact_mod_cast (show n ≠ 0 by omega)
  have hv : uniformVariance n m ≠ 0 := (uniformVariance_pos hmpos hmtop).ne'
  have hn1 : (n : ℝ) - 1 ≠ 0 := by
    have : (2 : ℝ) ≤ n := by exact_mod_cast hn
    linarith
  let a : ℝ := (n : ℝ) * uniformVariance n m / ((n : ℝ) - 1)
  have ha : a ≠ 0 := div_ne_zero (mul_ne_zero hn0 hv) hn1
  let x := a⁻¹ • pairDemand i j
  have hx : covarianceMatrix (uniformWeights n) m *ᵥ x = pairDemand i j := by
    dsimp [x]
    rw [Matrix.mulVec_smul, uniform_covariance_mulVec_zeroSum hn m (by omega)
      (pairDemand i j) (pairDemand_zeroSum hij)]
    change a⁻¹ • (a • pairDemand i j) = _
    rw [smul_smul, inv_mul_cancel₀ ha, one_smul]
  have hdrop := (externalFieldGreenKernel (uniformWeights n) (uniformWeights_pos n)
    m hmpos (by simpa using hmtop)).effectiveResistance_eq_solution_drop hij x
      (by simpa only [externalFieldCovarianceNetwork_laplacian] using hx)
  rw [hdrop]
  simp only [x, Pi.smul_apply, smul_eq_mul, pairDemand_apply_left hij,
    pairDemand_apply_right hij]
  dsimp [a]
  field_simp
  ring

theorem uniform_pseudoinverse_pairDemand {n : ℕ} (m : ℕ)
    (hmpos : 1 ≤ m) (hmtop : m ≤ n - 1) (i j : Fin n) (hij : i ≠ j) :
    quadraticForm (externalFieldPseudoinverse (uniformWeights n) (uniformWeights_pos n)
      m hmpos (by simpa using hmtop)) (pairDemand i j) =
      2 * ((n : ℝ) - 1) / ((n : ℝ) * uniformVariance n m) :=
  uniform_effectiveResistance m hmpos hmtop i j hij

theorem uniform_resistance_ratio {n : ℕ} (m : ℕ)
    (hmpos : 1 ≤ m) (hmtop : m ≤ n - 1) (i j : Fin n) (hij : i ≠ j) :
    quadraticForm (externalFieldPseudoinverse (uniformWeights n) (uniformWeights_pos n)
      m hmpos (by simpa using hmtop)) (pairDemand i j) /
      (1 / covarianceMatrix (uniformWeights n) m i i +
        1 / covarianceMatrix (uniformWeights n) m j j) = ((n : ℝ) - 1) / n := by
  have hn : 0 < n := by omega
  have hn0 : (n : ℝ) ≠ 0 := by exact_mod_cast hn.ne'
  have hv : uniformVariance n m ≠ 0 := (uniformVariance_pos hmpos hmtop).ne'
  rw [uniform_pseudoinverse_pairDemand m hmpos hmtop i j hij,
    uniform_covariance_diagonal hn m (by omega), uniform_covariance_diagonal hn m (by omega)]
  field_simp
  ring

theorem uniform_resistance_ratio_limit :
    Tendsto (fun n : ℕ => ((n : ℝ) - 1) / n) atTop (nhds 1) := by
  have hi : Tendsto (fun n : ℕ => (n : ℝ)⁻¹) atTop (nhds 0) :=
    tendsto_inv_atTop_zero.comp tendsto_natCast_atTop_atTop
  have h : Tendsto (fun n : ℕ => 1 - (n : ℝ)⁻¹) atTop (nhds (1 - 0)) :=
    tendsto_const_nhds.sub hi
  simp only [sub_zero] at h
  apply h.congr'
  filter_upwards [eventually_ge_atTop 1] with n hn
  have hn0 : (n : ℝ) ≠ 0 := by exact_mod_cast (show n ≠ 0 by omega)
  field_simp

/-- The actual pair-resistance ratio for rank one in dimension `k + 2`. -/
def uniformRankOneResistanceRatio (k : ℕ) : ℝ :=
  let i : Fin (k + 2) := ⟨0, by omega⟩
  let j : Fin (k + 2) := ⟨1, by omega⟩
  quadraticForm (externalFieldPseudoinverse (uniformWeights (k + 2))
    (uniformWeights_pos (k + 2)) 1 (by omega) (by simp)) (pairDemand i j) /
    (1 / covarianceMatrix (uniformWeights (k + 2)) 1 i i +
      1 / covarianceMatrix (uniformWeights (k + 2)) 1 j j)

theorem uniformRankOneResistanceRatio_eq (k : ℕ) :
    uniformRankOneResistanceRatio k = (((k + 2 : ℕ) : ℝ) - 1) / (k + 2 : ℕ) := by
  apply uniform_resistance_ratio 1 (by omega) (by omega)
  intro h
  have := congrArg Fin.val h
  norm_num at this

theorem uniform_rankOne_resistance_ratio_limit :
    Tendsto uniformRankOneResistanceRatio atTop (nhds 1) := by
  have heq : uniformRankOneResistanceRatio =
      fun k => (((k + 2 : ℕ) : ℝ) - 1) / (k + 2 : ℕ) :=
    funext uniformRankOneResistanceRatio_eq
  rw [heq]
  exact uniform_resistance_ratio_limit.comp (tendsto_add_atTop_nat 2)

/-- Every proposed coefficient below one fails for an actual uniform rank-one
law, a fortiori for the class of all positive external fields. -/
theorem uniform_rankOne_resistance_constant_one_is_sharp (c : ℝ) (hc : c < 1) :
    ∃ (n : ℕ) (hn : 2 ≤ n) (i j : Fin n), i ≠ j ∧
      c * (1 / covarianceMatrix (uniformWeights n) 1 i i +
        1 / covarianceMatrix (uniformWeights n) 1 j j) <
      quadraticForm (externalFieldPseudoinverse (uniformWeights n) (uniformWeights_pos n)
        1 (by omega) (by simpa using (show 1 ≤ n - 1 by omega))) (pairDemand i j) := by
  obtain ⟨k, hk⟩ := exists_nat_gt (max 1 ((1 - c)⁻¹))
  have hk1 : (1 : ℝ) < k := lt_of_le_of_lt (le_max_left _ _) hk
  have hn : 2 ≤ k := by exact_mod_cast hk1
  have hkc : (1 - c)⁻¹ < (k : ℝ) := lt_of_le_of_lt (le_max_right _ _) hk
  have hk0 : (0 : ℝ) < k := by linarith
  have hc0 : 0 < 1 - c := by linarith
  have hratio : c < ((k : ℝ) - 1) / k := by
    have ht := (inv_lt_iff_one_lt_mul₀ hc0).mp hkc
    apply (lt_div_iff₀ hk0).mpr
    nlinarith
  let i : Fin k := ⟨0, by omega⟩
  let j : Fin k := ⟨1, by omega⟩
  have hij : i ≠ j := by intro h; have := congrArg Fin.val h; simp [i, j] at this
  have hv : 0 < uniformVariance k 1 := uniformVariance_pos (by omega) (by omega)
  have hden : 0 < 1 / covarianceMatrix (uniformWeights k) 1 i i +
      1 / covarianceMatrix (uniformWeights k) 1 j j := by
    rw [uniform_covariance_diagonal (by omega) 1 (by omega),
      uniform_covariance_diagonal (by omega) 1 (by omega)]
    positivity
  refine ⟨k, hn, i, j, hij, ?_⟩
  have hr := uniform_resistance_ratio 1 (by omega) (by omega : 1 ≤ k - 1) i j hij
  rw [← hr] at hratio
  exact (lt_div_iff₀ hden).mp hratio

theorem externalField_effectiveResistance_constant_one_is_sharp (c : ℝ) (hc : c < 1) :
    ∃ (n : ℕ) (hn : 2 ≤ n) (w : Fin n → ℝ) (hw : ∀ i, 0 < w i) (i j : Fin n),
      i ≠ j ∧ c * (1 / covarianceMatrix w 1 i i + 1 / covarianceMatrix w 1 j j) <
        quadraticForm (externalFieldPseudoinverse w hw 1 (by omega)
          (by simpa using (show 1 ≤ n - 1 by omega))) (pairDemand i j) := by
  obtain ⟨n, hn, i, j, hij, hlt⟩ := uniform_rankOne_resistance_constant_one_is_sharp c hc
  exact ⟨n, hn, uniformWeights n, uniformWeights_pos n, i, j, hij, hlt⟩

end
end CoefficientOne
