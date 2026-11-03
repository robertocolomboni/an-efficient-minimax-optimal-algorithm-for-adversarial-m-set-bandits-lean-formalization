import MsetsPaper.Upper.ProjectionStoredSearch
import MsetsPaper.Upper.ProjectionSetupExpLogArena

/-! Complete stored-input projection with explicit arena reset. Read-only
input/box vectors and final output construction are included in the peak.
The search peak and fixed-word setup peak do not depend on the iteration count.
-/

noncomputable section
-- The stored program is a nested composition of certified scalar/list loops.
set_option maxRecDepth 4096
open scoped BigOperators

namespace MsetsPaper.Upper.ResourcePrograms

open SchurSolver (StoredVector storedVector resourceVectorRead resourceVectorRead_values
  resourceVectorRead_bounds)

variable {d m : ℕ}

def boxResource (d m : ℕ) (lambda : ℝ) : ResourceRun (StoredVector d × StoredVector d) :=
  let ratio := (m : ℝ) / d
  let low := lambda * ratio
  let high := 1 - lambda * (1 - ratio)
  let a := vectorProgram (fun _ : Fin d => (⟨low, 1, 1⟩ : ResourceRun ℝ))
  let b := vectorProgram (fun _ : Fin d => (⟨high, 1, 1⟩ : ResourceRun ℝ))
  ⟨(a.value, b.value), a.work + b.work + 9, a.allocated + b.allocated + 13⟩

theorem boxResource_values (d m : ℕ) (lambda : ℝ) :
    storedVector (boxResource d m lambda).value.1 = projectionLower d m lambda ∧
      storedVector (boxResource d m lambda).value.2 = projectionUpper d m lambda := by
  simp only [boxResource, vectorProgram_values, projectionLower, projectionUpper]
  exact ⟨rfl, rfl⟩

theorem boxResource_bounds (d m : ℕ) (lambda : ℝ) :
    (boxResource d m lambda).work ≤ 20 * (d + 1) ∧
      (boxResource d m lambda).allocated ≤ 20 * (d + 1) := by
  have ha := vectorProgram_bounds (fun _ : Fin d =>
    (⟨lambda * ((m : ℝ) / d), 1, 1⟩ : ResourceRun ℝ)) 1 1 (fun _ => ⟨le_rfl, le_rfl⟩)
  have hb := vectorProgram_bounds (fun _ : Fin d =>
    (⟨1 - lambda * (1 - (m : ℝ) / d), 1, 1⟩ : ResourceRun ℝ))
    1 1 (fun _ => ⟨le_rfl, le_rfl⟩)
  dsimp only [boxResource]
  constructor <;> omega

def addCellResource (x y : StoredVector d) (i : Fin d) : ResourceRun ℝ :=
  let a := resourceVectorRead x i
  let b := resourceVectorRead y i
  ⟨a.value + b.value, a.work + b.work + 1, a.allocated + b.allocated + 1⟩

def addVectorResource (x y : StoredVector d) : ResourceRun (StoredVector d) :=
  vectorProgram (addCellResource x y)

theorem addVectorResource_values (x y : StoredVector d) :
    storedVector (addVectorResource x y).value = storedVector x + storedVector y := by
  simp only [addVectorResource, vectorProgram_values, addCellResource, resourceVectorRead_values]
  rfl

theorem addVectorResource_bounds (x y : StoredVector d) :
    (addVectorResource x y).work ≤ 100 * (d + 1) ^ 2 ∧
      (addVectorResource x y).allocated ≤ 100 * (d + 1) ^ 2 := by
  have hc (i : Fin d) : (addCellResource x y i).work ≤ 2 * d + 5 ∧
      (addCellResource x y i).allocated ≤ 4 * d + 7 := by
    have hx := resourceVectorRead_bounds x i
    have hy := resourceVectorRead_bounds y i
    dsimp only [addCellResource]
    constructor <;> omega
  have h := vectorProgram_bounds (addCellResource x y) (2 * d + 5) (4 * d + 7) hc
  dsimp only [addVectorResource]
  constructor <;> nlinarith [h.1, h.2]

def projectionArena (theta : StoredVector d) (m : ℕ) (eta T : ℝ) :
    ResourceRun (StoredVector d) × ℕ :=
  let setup := projectionSetupExpLogArena d eta T
  let box := boxResource d m setup.1.value.lambda
  let search := searchArena theta box.value.1 box.value.2 m
    setup.1.value.radius setup.1.value.budget
  let updated := addVectorResource theta search.1.value.best
  let readOnly := 6 * d + 50
  (⟨updated.value, setup.1.work + box.work + search.1.work + updated.work + 5,
      setup.1.allocated + box.allocated + search.1.allocated + updated.allocated + 8⟩,
    max setup.2 (max (readOnly + box.allocated)
      (max (readOnly + search.2) (readOnly + search.1.value.footprint + updated.allocated))))

theorem projectionArena_values (theta : StoredVector d) (hm : 1 ≤ m) (eta T : ℝ) :
    storedVector (projectionArena theta m eta T).1.value =
      ellipsoidProjection (m := m) (storedVector theta) eta T := by
  dsimp only [projectionArena]
  rw [addVectorResource_values, projectionSetupExpLogArena_values]
  have hs := congrArg ProjectionSearchState.best
    (searchArena_values theta (boxResource d m (128 * eta * d)).value.1
      (boxResource d m (128 * eta * d)).value.2 hm
      (projectionRadius d T) (projectionOracleBudget d eta T))
  simp only [StoredSearch.decode, (boxResource_values d m (128 * eta * d)).1,
    (boxResource_values d m (128 * eta * d)).2] at hs
  exact congrArg (fun x => storedVector theta + x) hs

theorem projectionArena_work (theta : StoredVector d) (m : ℕ) (eta T : ℝ) :
    (projectionArena theta m eta T).1.work ≤
      150 * (d + 1) ^ 2 + projectionOracleBudget d eta T * (searchStepBudget d m + 6) + 50 := by
  let setup := (projectionSetupExpLogArena d eta T).1.value
  let box := (boxResource d m setup.lambda).value
  let search := searchArena theta box.1 box.2 m setup.radius setup.budget
  have hsetup := projectionSetupExpLogArena_work d eta T
  have hbudget : setup.budget = projectionOracleBudget d eta T := by
    simp only [setup, projectionSetupExpLogArena_values]
  have hb := boxResource_bounds d m setup.lambda
  have hs := searchArena_work theta box.1 box.2 m setup.radius setup.budget
  have hu := addVectorResource_bounds theta search.1.value.best
  rw [hbudget] at hs
  dsimp only [projectionArena]
  dsimp only [setup, box, search] at hb hs hu
  dsimp only [setup] at hbudget
  rw [hbudget] at hu ⊢
  nlinarith [hb.1, hs, hu.1]

def projectionArenaSpace (d m : ℕ) : ℕ := searchArenaSpace d m + 200 * (d + 1) ^ 2 + 100

/-- The bound contains neither T, eta, the iteration count, nor the number
of rounds. It includes all retained state copies and the read-only inputs. -/
theorem projectionArena_peak (theta : StoredVector d) (m : ℕ) (eta T : ℝ) :
    (projectionArena theta m eta T).2 ≤ projectionArenaSpace d m := by
  let setup := (projectionSetupExpLogArena d eta T).1.value
  let box := (boxResource d m setup.lambda).value
  let search := searchArena theta box.1 box.2 m setup.radius setup.budget
  have hsetup := projectionSetupExpLogArena_peak d eta T
  have hb := (boxResource_bounds d m setup.lambda).2
  have hs := searchArena_peak theta box.1 box.2 m setup.radius setup.budget
  have hu := (addVectorResource_bounds theta search.1.value.best).2
  have hf := StoredSearch.footprint_eq search.1.value
  dsimp only [projectionArena]
  dsimp only [setup, box, search] at hb hs hu hf
  unfold projectionArenaSpace
  apply max_le
  · rw [hsetup]
    omega
  apply max_le
  · nlinarith
  apply max_le
  · nlinarith
  · unfold searchArenaSpace
    nlinarith [Nat.zero_le (searchStepBudget d m)]

theorem projectionArena_correct (theta : StoredVector d)
    (hm : 1 ≤ m) (hmtop : m ≤ d - 1) (eta T : ℝ)
    (heta : 0 < eta) (hetaMax : eta ≤ 1 / (256 * (d : ℝ))) (hT : 1 ≤ T)
    (hKL : finiteKL (weightedLaw (m := m) (0 : Fin d → ℝ)) (weightedLaw (storedVector theta)) ≤ T) :
    (∀ i, projectionLower d m ((128 * eta * d) / 2) i ≤
        weightedMarginal (m := m) (storedVector (projectionArena theta m eta T).1.value) i ∧
      weightedMarginal (m := m) (storedVector (projectionArena theta m eta T).1.value) i ≤
        projectionUpper d m ((128 * eta * d) / 2) i) ∧
    (∀ q : Action d m → ℝ, (∀ x, 0 ≤ q x) → (∑ x, q x) = 1 →
      (∀ i, projectionLower d m (128 * eta * d) i ≤ marginal q i ∧
        marginal q i ≤ projectionUpper d m (128 * eta * d) i) →
      finiteKL q (weightedLaw (m := m) (storedVector (projectionArena theta m eta T).1.value)) +
        finiteKL (weightedLaw (m := m) (storedVector (projectionArena theta m eta T).1.value))
          (weightedLaw (storedVector theta)) ≤ finiteKL q (weightedLaw (storedVector theta)) + eta / T) := by
  rw [projectionArena_values theta hm]
  exact ellipsoid_projection_correct (storedVector theta) hm hmtop eta T heta hetaMax hT hKL

theorem projectionArena_polynomial_work (theta : StoredVector d)
    (hd : 1 ≤ d) (m : ℕ) (eta T : ℝ)
    (heta : 0 < eta) (hetaMax : eta ≤ 1 / (256 * (d : ℝ))) (hT : 1 ≤ T) :
    ((projectionArena theta m eta T).1.work : ℝ) ≤
      150 * ((d : ℝ) + 1) ^ 2 +
        (8 * (d : ℝ) ^ 2 * (Real.log (projectionRadius d T) -
          Real.log (projectionTolerance d eta T) + Real.log 2 + Real.log (d : ℝ) / 2) + 2) *
          ((searchStepBudget d m : ℝ) + 6) + 50 := by
  have hw : ((projectionArena theta m eta T).1.work : ℝ) ≤
      150 * ((d : ℝ) + 1) ^ 2 +
        (projectionOracleBudget d eta T : ℝ) * ((searchStepBudget d m : ℝ) + 6) + 50 := by
    exact_mod_cast projectionArena_work theta m eta T
  have hb := projectionOracleBudget_bound d hd eta T heta hetaMax hT
  have htau := (projectionTolerance_pos_le_radius d hd eta T heta hetaMax hT).1
  have hR : 0 < projectionRadius d T := by
    have hp := (projection_parameter_bounds d hd eta T heta hetaMax hT).2.2.2.2.1
    linarith
  rw [projection_log_radius_ratio d hd _ _ hR htau] at hb
  have hm := mul_le_mul_of_nonneg_right hb
    (by positivity : (0 : ℝ) ≤ (searchStepBudget d m : ℝ) + 6)
  linarith

end MsetsPaper.Upper.ResourcePrograms
