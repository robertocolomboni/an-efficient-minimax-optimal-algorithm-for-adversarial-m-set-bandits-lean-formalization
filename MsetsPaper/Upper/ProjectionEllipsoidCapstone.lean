import MsetsPaper.Upper.ProjectionSearch
import MsetsPaper.Upper.ProjectionJensen

/-! Actual approximate projection: the accurate point is computed by a fixed
number of central-cut updates, not supplied as an assumption. -/

noncomputable section
open scoped BigOperators

namespace MsetsPaper.Upper

variable {d m : ℕ}

def projectionOracleBudget (d : ℕ) (eta T : ℝ) : ℕ :=
  ellipsoidIterationBudget d (projectionRadius d T)
    (projectionTolerance d eta T / (2 * Real.sqrt (d : ℝ)))

def ellipsoidProjectionShift (theta : Fin d → ℝ) (eta T : ℝ) : Fin d → ℝ :=
  (projectionSearchRun (m := m) theta (projectionLower d m (128 * eta * d))
    (projectionUpper d m (128 * eta * d)) (projectionRadius d T)
    (projectionOracleBudget d eta T)).best

def ellipsoidProjection (theta : Fin d → ℝ) (eta T : ℝ) : Fin d → ℝ :=
  theta + ellipsoidProjectionShift (m := m) theta eta T

theorem projectionTolerance_pos_le_radius (d : ℕ) (hd : 1 ≤ d) (eta T : ℝ)
    (heta : 0 < eta) (hetaMax : eta ≤ 1 / (256 * (d : ℝ))) (hT : 1 ≤ T) :
    0 < projectionTolerance d eta T ∧ projectionTolerance d eta T ≤ projectionRadius d T := by
  have hpar := projection_parameter_bounds d hd eta T heta hetaMax hT
  have hR : 1 ≤ projectionRadius d T := hpar.2.2.2.2.1
  have heps : 0 < eta / T := div_pos heta (by linarith)
  have heps1 : eta / T ≤ 1 := hpar.2.2.2.1
  refine ⟨by unfold projectionTolerance; positivity, ?_⟩
  have hsmall : projectionTolerance d eta T ≤ 1 := by
    unfold projectionTolerance
    apply (div_le_one (by positivity : 0 < 2 * projectionRadius d T ^ 2)).mpr
    nlinarith
  exact hsmall.trans hR

/-- This is the accuracy conclusion of the actual fixed-budget search,
with the manuscript's R and tau. No approximate optimizer is assumed. -/
theorem ellipsoidProjectionShift_accuracy (theta : Fin d → ℝ)
    (hmpos : 1 ≤ m) (hmtop : m ≤ d - 1) (eta T : ℝ)
    (heta : 0 < eta) (hetaMax : eta ≤ 1 / (256 * (d : ℝ))) (hT : 1 ≤ T)
    (hKL : finiteKL (weightedLaw (m := m) (0 : Fin d → ℝ)) (weightedLaw theta) ≤ T) :
    coordinateL1 (ellipsoidProjectionShift (m := m) theta eta T) ≤ projectionRadius d T ∧
    ∀ u, projectionDual (m := m) theta (projectionLower d m (128 * eta * d))
        (projectionUpper d m (128 * eta * d)) (ellipsoidProjectionShift (m := m) theta eta T) ≤
      projectionDual (m := m) theta (projectionLower d m (128 * eta * d))
        (projectionUpper d m (128 * eta * d)) u + projectionTolerance d eta T := by
  have hd : 1 ≤ d := by omega
  have hpar := projection_parameter_bounds d hd eta T heta hetaMax hT
  have hlam := hpar.1
  have hlamhalf := hpar.2.1
  obtain ⟨ha, hb, hab⟩ := projection_box_bounds hmpos hmtop (128 * eta * d) hlam hlamhalf
  obtain ⟨vstar, hmin⟩ := projectionDual_exists theta hmpos hmtop
    (128 * eta * d) hlam hlamhalf
  have hstar0 := projectionDual_minimum_radius_via_Jensen theta vstar hmpos hmtop
    (128 * eta * d) T hlamhalf hKL hmin
  have hstar : coordinateL1 vstar ≤ projectionRadius d T / 2 := by
    unfold projectionRadius
    linarith
  have htol := projectionTolerance_pos_le_radius d hd eta T heta hetaMax hT
  obtain ⟨hfeas, hacc, _⟩ := projectionSearchRun_accuracy theta _ _ vstar
    hmpos hmtop ha hb hab (projectionRadius d T) (projectionTolerance d eta T)
    hstar htol.1 htol.2
  refine ⟨hfeas, ?_⟩
  intro u
  have hminu := hmin u
  exact hacc.trans (by linarith)

/-- Complete mathematical L8 output guarantee for the concrete ellipsoid
program. The only input premise beyond the paper parameters is the stated
uniform-law KL budget. Arithmetic/access-space refinements are separate. -/
theorem ellipsoid_projection_correct (theta : Fin d → ℝ)
    (hmpos : 1 ≤ m) (hmtop : m ≤ d - 1) (eta T : ℝ)
    (heta : 0 < eta) (hetaMax : eta ≤ 1 / (256 * (d : ℝ))) (hT : 1 ≤ T)
    (hKL : finiteKL (weightedLaw (m := m) (0 : Fin d → ℝ)) (weightedLaw theta) ≤ T) :
    (∀ i, projectionLower d m ((128 * eta * d) / 2) i ≤
        weightedMarginal (m := m) (ellipsoidProjection (m := m) theta eta T) i ∧
      weightedMarginal (m := m) (ellipsoidProjection (m := m) theta eta T) i ≤
        projectionUpper d m ((128 * eta * d) / 2) i) ∧
    (∀ q : Action d m → ℝ, (∀ x, 0 ≤ q x) → (∑ x, q x) = 1 →
      (∀ i, projectionLower d m (128 * eta * d) i ≤ marginal q i ∧
        marginal q i ≤ projectionUpper d m (128 * eta * d) i) →
      finiteKL q (weightedLaw (m := m) (ellipsoidProjection (m := m) theta eta T)) +
        finiteKL (weightedLaw (m := m) (ellipsoidProjection (m := m) theta eta T)) (weightedLaw theta) ≤
      finiteKL q (weightedLaw theta) + eta / T) := by
  obtain ⟨hfeas, haccuracy⟩ := ellipsoidProjectionShift_accuracy theta hmpos hmtop
    eta T heta hetaMax hT hKL
  exact approximate_projection_of_dual_accuracy theta
    (ellipsoidProjectionShift (m := m) theta eta T) hmpos hmtop eta T heta hetaMax hT hKL
    hfeas (fun u _ => haccuracy u)

theorem projectionOracleBudget_bound (d : ℕ) (hd : 1 ≤ d) (eta T : ℝ)
    (heta : 0 < eta) (hetaMax : eta ≤ 1 / (256 * (d : ℝ))) (hT : 1 ≤ T) :
    (projectionOracleBudget d eta T : ℝ) ≤
      8 * (d : ℝ) ^ 2 * Real.log
        (projectionRadius d T / (projectionTolerance d eta T / (2 * Real.sqrt (d : ℝ)))) + 2 := by
  have hpar := projection_parameter_bounds d hd eta T heta hetaMax hT
  have htol := projectionTolerance_pos_le_radius d hd eta T heta hetaMax hT
  have hdR : (1 : ℝ) ≤ d := by exact_mod_cast hd
  have hsqrt : 1 ≤ Real.sqrt (d : ℝ) := (Real.one_le_sqrt).mpr hdR
  have hden : 0 < 2 * Real.sqrt (d : ℝ) := by positivity
  have htolpos := htol.1
  apply ellipsoidIterationBudget_bound hd _ _ (div_pos htolpos hden)
  apply (div_le_iff₀ hden).mpr
  have hR : 0 ≤ projectionRadius d T := by linarith [hpar.2.2.2.2.1]
  nlinarith [mul_nonneg hR (sub_nonneg.mpr hsqrt)]

end MsetsPaper.Upper
