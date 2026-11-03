import MsetsPaper.Upper.RoundPreparation
import MsetsPaper.Upper.RoundRAMSampling

/-! # A concrete feedback-only round through the unprojected update

Sampling precedes the observation Y. The post-observation phase receives
only the sampled coordinates and Y, not the unobserved item-loss vector.
The projection phase is intentionally separate: its materialized program,
correctness, and horizon-independent peak memory must be supplied by the
projection implementation before claiming the complete P1 bound.
-/

namespace MsetsPaper.Upper.RoundProgram

open SchurSolver ResourcePrograms ESPSampling VectorProgram
open MsetsLower MsetsLower.History Matrix MeasureTheory
open scoped unitInterval

noncomputable section

variable {d m : ℕ}

structure SampledAction (d m : ℕ) where
  coordinates : List (Fin d)
  nodup : coordinates.Nodup
  length_eq : coordinates.length = m

def SampledAction.action (a : SampledAction d m) : Action d m :=
  ⟨⟨a.coordinates, a.nodup⟩, by
    change a.coordinates.length = m
    exact a.length_eq⟩

theorem SampledAction.toFinset_eq (a : SampledAction d m) :
    a.coordinates.toFinset = a.action.1 := by
  ext i
  change i ∈ a.coordinates.toFinset ↔ i ∈ a.coordinates
  exact List.mem_toFinset

def sampleResource (theta : StoredVector d) (hmd : m ≤ d) (u : Fin d → unitInterval) :
    ResourceRun (SampledAction d m) :=
  let sampled := sampleStoredRAM theta m u
  ⟨⟨sampled.value,
      (sampleStoredRAM_card_nodup theta hmd u).2,
      (sampleStoredRAM_card_nodup theta hmd u).1⟩,
    sampled.work + 1, sampled.allocated + 1⟩

theorem sampleResource_probability (theta : StoredVector d) (hmd : m ≤ d)
    (a : Action d m) :
    uniformCube (Fin d) {u | (sampleResource theta hmd u).value.action = a} =
      ENNReal.ofReal (weightedLaw (storedVector theta) a) := by
  have heq : {u | (sampleResource theta hmd u).value.action = a} =
      {u | (sampleStoredRAM theta m u).value.toFinset = a.1} := by
    ext u
    simp only [Set.mem_setOf_eq]
    rw [← Subtype.val_inj]
    rw [← SampledAction.toFinset_eq]
    rfl
  rw [heq]
  exact sampleStoredRAM_probability theta hmd a

theorem sampleResource_bounds (theta : StoredVector d) (hmd : m ≤ d)
    (u : Fin d → unitInterval) :
    (sampleResource theta hmd u).work ≤ 158 * d * m + 7 * d + 8 ∧
    (sampleResource theta hmd u).allocated ≤ 158 * d * m + 5 * d + 8 := by
  have h := sampleStoredRAM_bounds theta hmd u
  dsimp only [sampleResource]
  constructor <;> omega

/-- Linear-dm cost of the very sampler executed by the full round. -/
theorem sampleResource_linear (theta : StoredVector d) (hmd : m ≤ d)
    (hd : 1 ≤ d) (hm : 1 ≤ m) (u : Fin d → unitInterval) :
    (sampleResource theta hmd u).work ≤ 230 * d * m ∧
    (sampleResource theta hmd u).allocated ≤ 230 * d * m := by
  have hb := sampleResource_bounds theta hmd u
  have hdm : d ≤ d * m := by nlinarith
  have hone : 1 ≤ d * m := by nlinarith
  constructor <;> nlinarith [hb.1, hb.2]

structure PreparedRound (d m : ℕ) where
  moments : StoredMatrix d
  marginals : StoredVector d
  sampled : SampledAction d m

def startRoundResource (theta : StoredVector d) (hmd : m ≤ d) (u : Fin d → unitInterval) :
    ResourceRun (PreparedRound d m) :=
  let moments := prepareMomentsResource theta m
  let sampled := sampleResource theta hmd u
  ⟨⟨moments.value.1, moments.value.2, sampled.value⟩,
    moments.work + sampled.work + 1, moments.allocated + sampled.allocated + 3⟩

def finishRoundResource (theta : StoredVector d) (eta Y : ℝ) (prepared : PreparedRound d m) :
    ResourceRun (StoredVector d) :=
  let rhs := feedbackResource prepared.sampled.coordinates Y
  let estimate := profiledSolve d prepared.moments rhs.value
  let updated := resourceUnprojected m eta theta estimate.1.value prepared.marginals
  ⟨updated.value.2, rhs.work + estimate.1.work + updated.work + 1,
    rhs.allocated + estimate.1.allocated + updated.allocated + 1⟩

theorem finishRoundResource_exact (theta : StoredVector d) (eta Y : ℝ)
    (prepared : PreparedRound d m) (hm : 1 ≤ m) (hmtop : m ≤ d - 1)
    (hM : storedMatrix prepared.moments =
      secondMoment (weightedLaw (m := m) (storedVector theta)))
    (hmu : storedVector prepared.marginals =
      weightedMarginal (m := m) (storedVector theta)) :
    storedVector (finishRoundResource theta eta Y prepared).value =
      unprojectedFromFeedback (storedVector theta) eta prepared.sampled.action Y := by
  have hA : (storedMatrix prepared.moments).PosDef := by
    rw [hM]
    exact secondMoment_posDef _ (weightedLaw_pos _ (by omega : m ≤ d)) hm hmtop
  have he := (profiledSolve_correct_and_bounded d prepared.moments
    (feedbackResource prepared.sampled.coordinates Y).value hA).1
  rw [hM, feedbackResource_action _ prepared.sampled.action Y
    prepared.sampled.toFinset_eq, Matrix.mulVec_smul] at he
  change storedVector (resourceUnprojected _ _ _ _ _).value.2 = _
  exact resourceUnprojected_feedback eta theta _ prepared.marginals
    prepared.sampled.action Y he hmu

def unprojectedRoundResource (theta : StoredVector d) (eta : ℝ) (hmd : m ≤ d)
    (u : Fin d → unitInterval) (Y : ℝ) : ResourceRun (StoredVector d) :=
  let prepared := startRoundResource theta hmd u
  let updated := finishRoundResource theta eta Y prepared.value
  ⟨updated.value, prepared.work + updated.work + 1,
    prepared.allocated + updated.allocated + 1⟩

theorem unprojectedRoundResource_exact (theta : StoredVector d) (eta Y : ℝ)
    (hm : 1 ≤ m) (hmtop : m ≤ d - 1) (u : Fin d → unitInterval) :
    storedVector (unprojectedRoundResource theta eta (by omega : m ≤ d) u Y).value =
      unprojectedFromFeedback (storedVector theta) eta
        (sampleResource theta (by omega : m ≤ d) u).value.action Y := by
  apply finishRoundResource_exact theta eta Y _ hm hmtop
  · exact prepareMomentsResource_matrix theta hm
  · exact prepareMomentsResource_marginal theta hm

theorem finishRoundResource_bounds (theta : StoredVector d) (eta Y : ℝ)
    (prepared : PreparedRound d m) :
    (finishRoundResource theta eta Y prepared).work ≤
      (2 * m + 4) * d + 2 + 200 * (d + 1)^4 + (25 * d + 12) + 1 ∧
    (finishRoundResource theta eta Y prepared).allocated ≤
      (2 * m + 6) * d + 2 + 200 * (d + 1)^4 + (31 * d + 10) + 1 := by
  have hb := feedbackResource_bounds prepared.sampled.coordinates Y
  rw [prepared.sampled.length_eq] at hb
  have hs := resourceSolve_bounds d prepared.moments
    (feedbackResource prepared.sampled.coordinates Y).value
  rw [← profiledSolve_resource] at hs
  have hu := resourceUnprojected_bounds (m : ℝ) eta theta
    (profiledSolve d prepared.moments (feedbackResource prepared.sampled.coordinates Y).value).1.value
    prepared.marginals
  dsimp only [finishRoundResource]
  constructor <;> omega

/-- All pre-projection work and temporary allocation is polynomial in d,m
alone. The projection's own lifetime discipline is not hidden in this bound. -/
theorem unprojectedRoundResource_bounds (theta : StoredVector d) (eta Y : ℝ)
    (hmd : m ≤ d) (u : Fin d → unitInterval) :
    (unprojectedRoundResource theta eta hmd u Y).work ≤ 1000 * (d + m + 1)^4 ∧
    (unprojectedRoundResource theta eta hmd u Y).allocated ≤ 1000 * (d + m + 1)^4 := by
  have hM := prepareMomentsResource_bounds theta m
  have hS := sampleResource_bounds theta hmd u
  have hF := finishRoundResource_bounds theta eta Y (startRoundResource theta hmd u).value
  have hp : 200 * (d + m + 1)^4 + (158 * d * m + 7 * d + 8) + 3 +
      ((2 * m + 6) * d + 2 + 200 * (d + 1)^4 + (31 * d + 10) + 1) + 1 ≤
      1000 * (d + m + 1)^4 := by
    ring_nf
    omega
  dsimp only [startRoundResource] at hF
  dsimp only [unprojectedRoundResource, startRoundResource]
  constructor <;> nlinarith [hM.1, hM.2, hS.1, hS.2, hF.1, hF.2]

end

end MsetsPaper.Upper.RoundProgram
