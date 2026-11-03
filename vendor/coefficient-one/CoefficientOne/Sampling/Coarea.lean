import CoefficientOne.CovarianceEnergy
import EffectiveResistance.EdgeVariation
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic

/-! # Layer cake for finite graph cuts and the elementary one-norm estimate -/

open scoped BigOperators
open Matrix EffectiveResistance MeasureTheory

namespace CoefficientOne.Sampling
noncomputable section

def levelIndicator (a s : ℝ) : ℝ := if s ≤ a then 1 else 0

def cutVector {ι : Type*} (a : ι → ℝ) (s : ℝ) : ι → ℝ :=
  fun i => levelIndicator (a i) s

theorem levelIndicator_sq_difference (a b s : ℝ) :
    (levelIndicator a s - levelIndicator b s) ^ 2 =
      (Set.Ioc (min a b) (max a b)).indicator (fun _ => (1 : ℝ)) s := by
  rcases le_total a b with hab | hba
  · by_cases hsa : s ≤ a <;> by_cases hsb : s ≤ b
    · simp [levelIndicator, hsa, hsb, min_eq_left hab, max_eq_right hab,
        Set.indicator, Set.mem_Ioc, not_lt.mpr hsa]
    · exact False.elim (hsb (hsa.trans hab))
    · simp [levelIndicator, hsa, hsb, min_eq_left hab, max_eq_right hab,
        Set.indicator, Set.mem_Ioc, lt_of_not_ge hsa]
    · simp [levelIndicator, hsa, hsb, min_eq_left hab, max_eq_right hab,
        Set.indicator, Set.mem_Ioc]
  · by_cases hsa : s ≤ a <;> by_cases hsb : s ≤ b
    · simp [levelIndicator, hsa, hsb, min_eq_right hba, max_eq_left hba,
        Set.indicator, Set.mem_Ioc, not_lt.mpr hsb]
    · simp [levelIndicator, hsa, hsb, min_eq_right hba, max_eq_left hba,
        Set.indicator, Set.mem_Ioc, lt_of_not_ge hsb]
    · exact False.elim (hsa (hsb.trans hba))
    · simp [levelIndicator, hsa, hsb, min_eq_right hba, max_eq_left hba,
        Set.indicator, Set.mem_Ioc]

theorem integrable_levelIndicator_difference (a b : ℝ) :
    Integrable (fun s => (levelIndicator a s - levelIndicator b s) ^ 2) := by
  simp_rw [levelIndicator_sq_difference]
  apply (integrable_indicator_iff measurableSet_Ioc).mpr
  exact (intervalIntegrable_const : IntervalIntegrable (fun _ : ℝ => (1 : ℝ))
    volume (min a b) (max a b)).1

theorem integral_levelIndicator_difference (a b : ℝ) :
    (∫ s : ℝ, (levelIndicator a s - levelIndicator b s) ^ 2) = |a - b| := by
  simp_rw [levelIndicator_sq_difference]
  rw [integral_indicator_const _ measurableSet_Ioc]
  simp only [Measure.real, Real.volume_Ioc, smul_eq_mul, mul_one]
  rw [ENNReal.toReal_ofReal (sub_nonneg.mpr (min_le_max : min a b ≤ max a b))]
  simpa only [abs_sub_comm b a] using max_sub_min_eq_abs a b

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

theorem cut_energy_eq_ordered_sum (N : ConductanceNetwork ι) (a : ι → ℝ) (s : ℝ) :
    quadraticForm N.laplacian (cutVector a s) =
      (2 : ℝ)⁻¹ * ∑ i, ∑ j, N.conductance i j *
        (levelIndicator (a i) s - levelIndicator (a j) s) ^ 2 := by
  rw [← N.energy_eq_quadraticForm, N.energy_eq_half_edgePairingSum]
  simp [ConductanceNetwork.edgePairingSum, Fintype.sum_prod_type, cutVector,
    pow_two, mul_assoc]

theorem integrable_cut_energy (N : ConductanceNetwork ι) (a : ι → ℝ) :
    Integrable (fun s : ℝ => quadraticForm N.laplacian (cutVector a s)) := by
  simp_rw [cut_energy_eq_ordered_sum]
  apply Integrable.const_mul
  apply integrable_finsetSum
  intro i _
  apply integrable_finsetSum
  intro j _
  exact (integrable_levelIndicator_difference (a i) (a j)).const_mul _

/-- The full real-line layer-cake identity; every integral is a genuine
Lebesgue integral and integrability of the cut energies is proved separately. -/
theorem edgeVariation_eq_integral_cut_energy (N : ConductanceNetwork ι) (a : ι → ℝ) :
    N.edgeVariation a = ∫ s : ℝ, quadraticForm N.laplacian (cutVector a s) := by
  simp_rw [cut_energy_eq_ordered_sum]
  rw [integral_const_mul]
  erw [integral_finsetSum _ (fun i _ => integrable_finsetSum _ (fun j _ =>
    (integrable_levelIndicator_difference (a i) (a j)).const_mul _))]
  simp_rw [integral_finsetSum _ (fun j _ =>
    (integrable_levelIndicator_difference _ (a j)).const_mul _)]
  simp_rw [integral_const_mul, integral_levelIndicator_difference]
  rfl

/-- The triangle inequality for graph currents, independent of any spectral gap. -/
theorem l1_laplacian_le_two_edgeVariation (N : ConductanceNetwork ι) (a : ι → ℝ) :
    l1Norm (N.laplacian *ᵥ a) ≤ 2 * N.edgeVariation a := by
  unfold l1Norm
  calc
    _ ≤ ∑ i, ∑ j, N.conductance i j * |a i - a j| := by
      apply Finset.sum_le_sum
      intro i _
      rw [N.laplacian_mulVec]
      have h := Finset.abs_sum_le_sum_abs (fun j => N.conductance i j * (a i - a j))
        Finset.univ
      simpa only [abs_mul, abs_of_nonneg (N.nonnegative i _)] using h
    _ = 2 * N.edgeVariation a := by unfold ConductanceNetwork.edgeVariation; ring

end
end CoefficientOne.Sampling
