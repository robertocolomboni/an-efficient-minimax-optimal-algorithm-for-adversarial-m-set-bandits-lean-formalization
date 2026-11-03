import MsetsPaper.Upper.ProjectionSearchProgram
import MsetsPaper.Upper.ProjectionEllipsoidMeasurable

/-! End-to-end ESP/ellipsoid program, output correctness and operation count.
The loop budget is an input computed from the displayed real parameters; the
counter covers the search, initialization and final parameter addition.
List accesses, allocations and the fixed-size parameter-setup calculation are
not included in this counter. No bit-complexity claim is made for exact reals. -/

noncomputable section
open scoped BigOperators
open MeasureTheory

namespace MsetsPaper.Upper

variable {d m : ℕ}

def countedVectorAdd (x y : Fin d → ℝ) : List ℝ × ℕ :=
  countedMap (fun i => (x i + y i, 1)) (List.finRange d)

theorem countedVectorAdd_values (x y : Fin d → ℝ) :
    (countedVectorAdd x y).1 = List.ofFn (x + y) := by
  simp only [countedVectorAdd, countedMap_values, List.ofFn_eq_map, Pi.add_apply]
  rfl

theorem countedVectorAdd_length (x y : Fin d → ℝ) : (countedVectorAdd x y).1.length = d := by
  rw [countedVectorAdd_values, List.length_ofFn]

theorem countedVectorAdd_cached (x y : Fin d → ℝ) :
    cachedRealVector (countedVectorAdd x y).1 (countedVectorAdd_length x y) = x + y := by
  ext i
  simp [cachedRealVector, countedVectorAdd_values]

theorem countedVectorAdd_cost (x y : Fin d → ℝ) : (countedVectorAdd x y).2 = d := by
  simp [countedVectorAdd, countedMap_cost, List.map_const']

def projectionProgram (theta : Fin d → ℝ) (eta T : ℝ) (hm : 1 ≤ m) : (Fin d → ℝ) × ℕ :=
  let search := projectionSearchProgram theta (projectionLower d m (128 * eta * d))
    (projectionUpper d m (128 * eta * d)) (projectionRadius d T) hm (projectionOracleBudget d eta T)
  let updated := countedVectorAdd theta search.1.best
  (cachedRealVector updated.1 (countedVectorAdd_length theta search.1.best), search.2 + updated.2)

theorem projectionProgram_values (theta : Fin d → ℝ) (eta T : ℝ) (hm : 1 ≤ m) :
    (projectionProgram theta eta T hm).1 = ellipsoidProjection (m := m) theta eta T := by
  simp only [projectionProgram, countedVectorAdd_cached, projectionSearchProgram_values,
    ellipsoidProjection, ellipsoidProjectionShift]

theorem projectionProgram_cost (theta : Fin d → ℝ) (eta T : ℝ) (hm : 1 ≤ m) :
    (projectionProgram theta eta T hm).2 ≤
      1 + projectionOracleBudget d eta T * projectionStepCost d m + d := by
  dsimp only [projectionProgram]
  rw [countedVectorAdd_cost]
  exact Nat.add_le_add_right (projectionSearchProgram_cost theta _ _ _ hm _) d

theorem projection_log_radius_ratio (d : ℕ) (hd : 1 ≤ d) (R tau : ℝ)
    (hR : 0 < R) (htau : 0 < tau) :
    Real.log (R / (tau / (2 * Real.sqrt (d : ℝ)))) =
      Real.log R - Real.log tau + Real.log 2 + Real.log (d : ℝ) / 2 := by
  have hd0 : (0 : ℝ) < d := by exact_mod_cast (show 0 < d by omega)
  have hsqrt : 0 < Real.sqrt (d : ℝ) := Real.sqrt_pos.mpr hd0
  rw [Real.log_div hR.ne' (div_pos htau (by positivity)).ne',
    Real.log_div htau.ne' (mul_pos (by norm_num : (0 : ℝ) < 2) hsqrt).ne',
    Real.log_mul (by norm_num : (2 : ℝ) ≠ 0) hsqrt.ne', Real.log_sqrt hd0.le]
  ring

/-- Explicit polynomial real-operation bound, with logarithmic accuracy
dependence. It is derived from the counted inner loops and their refinement,
not merely declared as a function called a complexity bound. -/
theorem projectionProgram_polynomial_real_cost (theta : Fin d → ℝ)
    (hm : 1 ≤ m) (hmtop : m ≤ d - 1) (eta T : ℝ)
    (heta : 0 < eta) (hetaMax : eta ≤ 1 / (256 * (d : ℝ))) (hT : 1 ≤ T) :
    ((projectionProgram theta eta T hm).2 : ℝ) ≤
      1 + (8 * (d : ℝ) ^ 2 *
        (Real.log (projectionRadius d T) - Real.log (projectionTolerance d eta T) +
          Real.log 2 + Real.log (d : ℝ) / 2) + 2) * (projectionStepCost d m : ℝ) + d := by
  have hd : 1 ≤ d := by omega
  have hc : ((projectionProgram theta eta T hm).2 : ℝ) ≤
      1 + (projectionOracleBudget d eta T : ℝ) * (projectionStepCost d m : ℝ) + d := by
    exact_mod_cast projectionProgram_cost theta eta T hm
  have hb := projectionOracleBudget_bound d hd eta T heta hetaMax hT
  have htau := (projectionTolerance_pos_le_radius d hd eta T heta hetaMax hT).1
  have hR : 0 < projectionRadius d T := by
    have := (projection_parameter_bounds d hd eta T heta hetaMax hT).2.2.2.2.1
    linarith
  rw [projection_log_radius_ratio d hd _ _ hR htau] at hb
  have hmul := mul_le_mul_of_nonneg_right hb (Nat.cast_nonneg (projectionStepCost d m) : (0 : ℝ) ≤ _)
  linarith

theorem measurable_projectionProgram (eta T : ℝ) (hm : 1 ≤ m) :
    Measurable (fun theta : Fin d → ℝ => (projectionProgram theta eta T hm).1) := by
  simp only [projectionProgram_values]
  exact measurable_ellipsoidProjection eta T

/-- Actual non-enumerative output theorem: no successful optimizer, oracle
correctness, projection guarantee or marginal feasibility is a premise. -/
theorem projectionProgram_correct (theta : Fin d → ℝ)
    (hm : 1 ≤ m) (hmtop : m ≤ d - 1) (eta T : ℝ)
    (heta : 0 < eta) (hetaMax : eta ≤ 1 / (256 * (d : ℝ))) (hT : 1 ≤ T)
    (hKL : finiteKL (weightedLaw (m := m) (0 : Fin d → ℝ)) (weightedLaw theta) ≤ T) :
    (∀ i, projectionLower d m ((128 * eta * d) / 2) i ≤
        weightedMarginal (m := m) (projectionProgram theta eta T hm).1 i ∧
      weightedMarginal (m := m) (projectionProgram theta eta T hm).1 i ≤
        projectionUpper d m ((128 * eta * d) / 2) i) ∧
    (∀ q : Action d m → ℝ, (∀ x, 0 ≤ q x) → (∑ x, q x) = 1 →
      (∀ i, projectionLower d m (128 * eta * d) i ≤ marginal q i ∧
        marginal q i ≤ projectionUpper d m (128 * eta * d) i) →
      finiteKL q (weightedLaw (m := m) (projectionProgram theta eta T hm).1) +
        finiteKL (weightedLaw (m := m) (projectionProgram theta eta T hm).1) (weightedLaw theta) ≤
      finiteKL q (weightedLaw theta) + eta / T) := by
  rw [projectionProgram_values]
  exact ellipsoid_projection_correct theta hm hmtop eta T heta hetaMax hT hKL

end MsetsPaper.Upper
