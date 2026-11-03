import MsetsPaper.Upper.WeightedLaw
import Mathlib.Topology.Algebra.Order.Field
import Mathlib.Tactic

/-! A genuine positive weighted-family witness for the blow-up of the
majorant when an inclusion marginal approaches the boundary. -/

noncomputable section
open MsetsLower MsetsLower.History MsetsPaper.Upper Filter
open scoped BigOperators Topology

namespace MsetsPaper.Alignment.UpperAuditBoundary

def a0 : Action 2 1 := ⟨{0}, by decide⟩
def a1 : Action 2 1 := ⟨{1}, by decide⟩

theorem action_univ : (Finset.univ : Finset (Action 2 1)) = {a0, a1} := by decide

def parameter (t : ℝ) : Fin 2 → ℝ := ![Real.log t, Real.log (1 - t)]

theorem marginal_parameter {t : ℝ} (ht : 0 < t) (ht1 : t < 1) :
    weightedMarginal (m := 1) (parameter t) = ![t, 1 - t] := by
  ext i
  fin_cases i <;>
    simp [weightedMarginal, marginal, weightedLaw, partition, action_univ, a0, a1,
      parameter, actionLoss_eq_finset_sum, selectedIndicator, Real.exp_log ht,
      Real.exp_log (sub_pos.mpr ht1)]

theorem majorant_parameter {t : ℝ} (ht : 0 < t) (ht1 : t < 1) :
    phi (weightedMarginal (m := 1) (parameter t)) (fun i ↦ selectedIndicator i a0) =
      2 / t - 1 := by
  rw [marginal_parameter ht ht1]
  norm_num [phi, Fin.sum_univ_succ, a0, selectedIndicator]
  field_simp [ht.ne', (sub_pos.mpr ht1).ne']
  ring

theorem inverse_ratio_diverges :
    Tendsto (fun t : ℝ ↦ (1 - t) / t) (𝓝[>] 0) atTop := by
  have h := tendsto_atTop_add_const_right (𝓝[>] (0 : ℝ)) (-1)
    (tendsto_inv_nhdsGT_zero : Tendsto (fun t : ℝ ↦ t⁻¹) (𝓝[>] 0) atTop)
  apply h.congr'
  filter_upwards [self_mem_nhdsWithin] with t ht
  have ht0 : t ≠ 0 := ne_of_gt ht
  field_simp
  ring

theorem weighted_majorant_diverges :
    Tendsto (fun t : ℝ ↦
      phi (weightedMarginal (m := 1) (parameter t)) (fun i ↦ selectedIndicator i a0))
      (𝓝[>] 0) atTop := by
  have h := tendsto_atTop_add_const_right (𝓝[>] (0 : ℝ)) (-1)
    ((tendsto_inv_nhdsGT_zero : Tendsto (fun t : ℝ ↦ t⁻¹) (𝓝[>] 0) atTop).const_mul_atTop
      (by norm_num : (0 : ℝ) < 2))
  apply h.congr'
  filter_upwards [self_mem_nhdsWithin,
    mem_nhdsWithin_of_mem_nhds (Iio_mem_nhds (show (0 : ℝ) < 1 by norm_num))] with t ht ht1
  rw [majorant_parameter ht ht1]
  simp [div_eq_mul_inv, sub_eq_add_neg]

/-- The same strictly positive weighted family simultaneously has one
marginal tending to0, the other to1, and an unbounded majorant. -/
theorem weighted_boundary_witness :
    Tendsto (fun t : ℝ ↦ weightedMarginal (m := 1) (parameter t) 0) (𝓝[>] 0) (𝓝 0) ∧
    Tendsto (fun t : ℝ ↦ weightedMarginal (m := 1) (parameter t) 1) (𝓝[>] 0) (𝓝 1) ∧
    Tendsto (fun t : ℝ ↦
      phi (weightedMarginal (m := 1) (parameter t)) (fun i ↦ selectedIndicator i a0))
      (𝓝[>] 0) atTop := by
  have ht : Tendsto (fun t : ℝ ↦ t) (𝓝[>] 0) (𝓝 0) :=
    (tendsto_id : Tendsto (fun t : ℝ ↦ t) (𝓝 0) (𝓝 0)).mono_left inf_le_left
  have h1 : Tendsto (fun t : ℝ ↦ 1 - t) (𝓝[>] 0) (𝓝 1) := by
    simpa using tendsto_const_nhds.sub ht
  refine ⟨?_, ?_, weighted_majorant_diverges⟩
  · apply ht.congr'
    filter_upwards [self_mem_nhdsWithin,
      mem_nhdsWithin_of_mem_nhds (Iio_mem_nhds (show (0 : ℝ) < 1 by norm_num))] with t ht ht1
    rw [marginal_parameter ht ht1]
    rfl
  · apply h1.congr'
    filter_upwards [self_mem_nhdsWithin,
      mem_nhdsWithin_of_mem_nhds (Iio_mem_nhds (show (0 : ℝ) < 1 by norm_num))] with t ht ht1
    rw [marginal_parameter ht ht1]
    rfl

end MsetsPaper.Alignment.UpperAuditBoundary
