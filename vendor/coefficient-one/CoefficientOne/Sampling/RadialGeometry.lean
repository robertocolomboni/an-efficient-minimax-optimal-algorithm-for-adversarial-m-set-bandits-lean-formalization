import CoefficientOne.Sampling.RadialContinuity
import CoefficientOne.Sampling.DummyLift

/-! # The explicit dyadic radial approximations used at the boundary -/

open scoped BigOperators Topology
open Filter

namespace CoefficientOne.Sampling
noncomputable section

def dyadicTime (j : ℕ) : unitInterval :=
  ⟨(1 / 2 : ℝ) ^ (j + 1), pow_nonneg (by norm_num) _,
    pow_le_one₀ (by norm_num) (by norm_num)⟩

theorem dyadicTime_pos (j : ℕ) : 0 < (dyadicTime j : ℝ) :=
  pow_pos (by norm_num) _

theorem dyadicTime_succ (j : ℕ) :
    (dyadicTime (j + 1) : ℝ) = (1 / 2) * (dyadicTime j : ℝ) := by
  change (1 / 2 : ℝ) ^ (j + 1 + 1) = (1 / 2) * (1 / 2) ^ (j + 1)
  rw [pow_succ, mul_comm]

theorem dyadicTime_sub_succ (j : ℕ) :
    (dyadicTime j : ℝ) - (dyadicTime (j + 1) : ℝ) = (dyadicTime (j + 1) : ℝ) := by
  rw [dyadicTime_succ]
  ring

theorem dyadicTime_tendsto : Tendsto dyadicTime atTop (𝓝 0) := by
  apply tendsto_subtype_rng.mpr
  have h := (tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num : (0 : ℝ) ≤ 1 / 2)
    (by norm_num : (1 / 2 : ℝ) < 1)).mul_const (1 / 2)
  simpa [dyadicTime, pow_succ] using h

theorem summable_dyadicTime : Summable (fun j => (dyadicTime j : ℝ)) := by
  have h := (summable_geometric_of_lt_one (by norm_num : (0 : ℝ) ≤ 1 / 2)
    (by norm_num : (1 / 2 : ℝ) < 1)).mul_right (1 / 2)
  simpa only [dyadicTime, pow_succ] using h

theorem summable_dyadicTime_succ : Summable (fun j => (dyadicTime (j + 1) : ℝ)) := by
  simpa only [dyadicTime_succ] using summable_dyadicTime.mul_left (1 / 2 : ℝ)

variable {ι : Type*} [Fintype ι] [DecidableEq ι] {k : ℕ}

theorem radialMarginal_apply (x : hypersimplex ι k) (t : unitInterval) (i : ι) :
    (radialMarginal x t).val i =
      (1 - (t : ℝ)) * x.val i + (t : ℝ) * ((k : ℝ) / Fintype.card ι) := rfl

theorem continuous_radialMarginal (t : unitInterval) :
    Continuous (fun x : hypersimplex ι k => radialMarginal x t) := by
  apply Continuous.subtype_mk
  apply continuous_pi
  intro i
  change Continuous (fun x : hypersimplex ι k =>
    (1 - (t : ℝ)) * x.val i + (t : ℝ) * ((k : ℝ) / Fintype.card ι))
  have hxi : Continuous (fun x : hypersimplex ι k => x.val i) :=
    (continuous_apply i).comp continuous_subtype_val
  exact (hxi.const_mul (1 - (t : ℝ))).add continuous_const

theorem vectorL1_const_mul (c : ℝ) (v : ι → ℝ) :
    vectorL1 (fun i => c * v i) = |c| * vectorL1 v := by
  simp only [vectorL1, EffectiveResistance.l1Norm, abs_mul, Finset.mul_sum]

theorem radialMarginal_pair_l1 (x y : hypersimplex ι k) (t : unitInterval) :
    vectorL1 (fun i => (radialMarginal x t).val i - (radialMarginal y t).val i) =
      (1 - (t : ℝ)) * vectorL1 (fun i => x.val i - y.val i) := by
  have he : (fun i => (radialMarginal x t).val i - (radialMarginal y t).val i) =
      fun i => (1 - (t : ℝ)) * (x.val i - y.val i) := by
    funext i
    simp only [radialMarginal_apply]
    ring
  rw [he, vectorL1_const_mul, abs_of_nonneg (sub_nonneg.mpr t.property.2)]

theorem radialMarginal_adjacent_l1 (x : hypersimplex ι k) (j : ℕ) :
    vectorL1 (fun i => (radialMarginal x (dyadicTime (j + 1))).val i -
      (radialMarginal x (dyadicTime j)).val i) =
      (dyadicTime (j + 1) : ℝ) *
        vectorL1 (fun i => x.val i - (k : ℝ) / Fintype.card ι) := by
  have he : (fun i => (radialMarginal x (dyadicTime (j + 1))).val i -
      (radialMarginal x (dyadicTime j)).val i) =
      fun i => (dyadicTime (j + 1) : ℝ) * (x.val i - (k : ℝ) / Fintype.card ι) := by
    funext i
    simp only [radialMarginal_apply, dyadicTime_succ]
    ring
  rw [he, vectorL1_const_mul, abs_of_nonneg (dyadicTime_pos _).le]

theorem radialMarginal_self_l1 (x : hypersimplex ι k) (t : unitInterval) :
    vectorL1 (fun i => (radialMarginal x t).val i - x.val i) =
      (t : ℝ) * vectorL1 (fun i => (k : ℝ) / Fintype.card ι - x.val i) := by
  have he : (fun i => (radialMarginal x t).val i - x.val i) =
      fun i => (t : ℝ) * ((k : ℝ) / Fintype.card ι - x.val i) := by
    funext i
    simp only [radialMarginal_apply]
    ring
  rw [he, vectorL1_const_mul, abs_of_nonneg t.property.1]

theorem radialMarginal_pair_l1_tendsto (x y : hypersimplex ι k) :
    Tendsto (fun j => vectorL1 (fun i => (radialMarginal x (dyadicTime j)).val i -
      (radialMarginal y (dyadicTime j)).val i)) atTop
      (𝓝 (vectorL1 (fun i => x.val i - y.val i))) := by
  simp only [radialMarginal_pair_l1]
  have ht := continuous_subtype_val.continuousAt.tendsto.comp dyadicTime_tendsto
  simpa using ((tendsto_const_nhds (x := (1 : ℝ))).sub ht).mul_const
    (vectorL1 (fun i => x.val i - y.val i))

theorem maximumEntropyMass_dyadic_tendsto (x : hypersimplex ι k) :
    Tendsto (fun j => maximumEntropyMass (radialMarginal x (dyadicTime j))) atTop
      (𝓝 (maximumEntropyMass x)) :=
  (maximumEntropyMass_radial_tendsto_zero x).comp dyadicTime_tendsto

end
end CoefficientOne.Sampling
