import MsetsPaper.Upper.SamplerResources
import MsetsPaper.Upper.SPDSchurResources

noncomputable section
open scoped BigOperators unitInterval ENNReal
open MeasureTheory ProbabilityTheory

namespace MsetsPaper.Upper.ESPSampling

open SchurSolver (StoredVector storedVector resourceVectorRead resourceVectorRead_values
  resourceVectorRead_bounds resourceTabulate resourceTabulate_values resourceTabulate_bounds)

variable {d m : ℕ}

def samplerOrderResource (d : ℕ) : ResourceRun (List (Fin d)) :=
  resourceTabulate d (fun i => ⟨i, 1, 1⟩)

theorem samplerOrderResource_values (d : ℕ) :
    (samplerOrderResource d).value = List.finRange d := by
  simp only [samplerOrderResource, resourceTabulate_values]
  exact List.ofFn_id d

theorem samplerOrderResource_bounds (d : ℕ) :
    (samplerOrderResource d).work ≤ 3 * d + 1 ∧
      (samplerOrderResource d).allocated ≤ 5 * d + 1 := by
  exact resourceTabulate_bounds d (fun i => ⟨i, 1, 1⟩) 1 1 (fun _ => ⟨le_rfl, le_rfl⟩)

def samplerWeightsResource (theta : StoredVector d) : ResourceRun (StoredVector d) :=
  let run := resourceMap (fun t => (⟨Real.exp t, 1, 1⟩ : ResourceRun ℝ)) theta.val
  ⟨⟨run.value, by simp [run, resourceMap_values, theta.property]⟩,
    run.work + 1, run.allocated + 1⟩

theorem samplerWeightsResource_values (theta : StoredVector d) :
    storedVector (samplerWeightsResource theta).value = fun i => Real.exp (storedVector theta i) := by
  ext i
  simp [storedVector, samplerWeightsResource, resourceMap_values, cachedRealVector]

theorem samplerWeightsResource_bounds (theta : StoredVector d) :
    (samplerWeightsResource theta).work ≤ 3 * d + 2 ∧
      (samplerWeightsResource theta).allocated ≤ 4 * d + 2 := by
  have h := resourceMap_bounds (fun t => (⟨Real.exp t, 1, 1⟩ : ResourceRun ℝ))
    theta.val 1 1 (fun _ _ => ⟨le_rfl, le_rfl⟩)
  simp only [theta.property] at h
  dsimp only [samplerWeightsResource]
  constructor <;> omega

/-- Suffix preprocessing and actual sampling over stored data. `uniforms` is
the finite input random tape; its accesses are charged just like weight reads. -/
def sampleStoredResource (theta uniforms : StoredVector d) (m : ℕ) :
    ResourceRun (List (Fin d)) :=
  let weights := samplerWeightsResource theta
  let order := samplerOrderResource d
  let cache := espSuffixResource (resourceVectorRead weights.value) m order.value
  let run := samplerListResource (resourceVectorRead weights.value)
    (resourceVectorRead uniforms) order.value m cache.value.rows
  ⟨run.value, weights.work + order.work + cache.work + run.work + 4,
    weights.allocated + order.allocated + cache.allocated + run.allocated + 8⟩

theorem sampleStoredResource_values (theta uniforms : StoredVector d) (m : ℕ) :
    (sampleStoredResource theta uniforms m).value.toFinset =
      sequentialList (fun i => Real.exp (storedVector theta i))
        (storedVector uniforms) (List.finRange d) m := by
  simp only [sampleStoredResource, samplerListResource_values,
    samplerOrderResource_values, espSuffixResource_values, resourceVectorRead_values,
    samplerWeightsResource_values]
  exact tableSampler_correct _ _ m _ (List.nodup_finRange d) m le_rfl

theorem sampleStoredResource_nodup (theta uniforms : StoredVector d) (m : ℕ) :
    (sampleStoredResource theta uniforms m).value.Nodup := by
  apply samplerListResource_nodup
  rw [samplerOrderResource_values]
  exact List.nodup_finRange d

theorem sampleStoredResource_card (theta uniforms : StoredVector d) (hmd : m ≤ d) :
    (sampleStoredResource theta uniforms m).value.length = m := by
  have h := sequentialList_card (fun i => Real.exp (storedVector theta i))
    (storedVector uniforms) (List.finRange d) (List.nodup_finRange d) m (by simpa using hmd)
  rw [← sampleStoredResource_values] at h
  simpa only [List.toFinset_card_of_nodup (sampleStoredResource_nodup theta uniforms m)] using h

set_option maxHeartbeats 1000000 in
theorem sampleStoredResource_bounds (theta uniforms : StoredVector d) (m : ℕ) :
    (sampleStoredResource theta uniforms m).work ≤ 2 * m + 12 + d * (5 * d + 7 * m + 51) ∧
    (sampleStoredResource theta uniforms m).allocated ≤ 2 * m + 18 + d * (8 * d + 11 * m + 73) := by
  let weights := (samplerWeightsResource theta).value
  have hw := samplerWeightsResource_bounds theta
  have ho := samplerOrderResource_bounds d
  have hc := espSuffixResource_bounds (resourceVectorRead weights) m (samplerOrderResource d).value
    (d + 2) (2 * d + 3) (fun i _ => resourceVectorRead_bounds weights i)
  have hr := samplerListResource_bounds (resourceVectorRead weights) (resourceVectorRead uniforms)
    (samplerOrderResource d).value m
    (espSuffixResource (resourceVectorRead weights) m (samplerOrderResource d).value).value.rows
    d m (d + 2) (2 * d + 3) (d + 2) (2 * d + 3)
    (by simp [samplerOrderResource_values]) le_rfl
    (fun i _ => resourceVectorRead_bounds weights i)
    (fun i _ => resourceVectorRead_bounds uniforms i)
  simp only [samplerOrderResource_values, List.length_finRange] at hc hr
  dsimp only [sampleStoredResource]
  change _ ≤ _ ∧ _ ≤ _
  dsimp only [weights] at hc hr
  simp only [samplerOrderResource_values] at *
  constructor <;> nlinarith [hw.1, hw.2, ho.1, ho.2, hc.1, hc.2, hr.1, hr.2]

/-- A nodup list is reinterpreted as a finite set, not deduplicated. The
Nodup proof is erased; no search or equality algorithm is invoked here. -/
def sampleStoredSet (theta uniforms : StoredVector d) (m : ℕ) : Finset (Fin d) :=
  ⟨(sampleStoredResource theta uniforms m).value,
    sampleStoredResource_nodup theta uniforms m⟩

theorem sampleStoredSet_eq (theta uniforms : StoredVector d) (m : ℕ) :
    sampleStoredSet theta uniforms m = (sampleStoredResource theta uniforms m).value.toFinset := by
  ext i
  change i ∈ (sampleStoredResource theta uniforms m).value ↔
    i ∈ (sampleStoredResource theta uniforms m).value.toFinset
  exact List.mem_toFinset.symm

def storedUniformTape (u : Fin d → unitInterval) : StoredVector d :=
  ⟨List.ofFn (fun i => (u i : ℝ)), List.length_ofFn⟩

theorem storedUniformTape_values (u : Fin d → unitInterval) :
    storedVector (storedUniformTape u) = fun i => (u i : ℝ) := by
  simp [storedUniformTape, storedVector, cachedRealVector_ofFn]

theorem sampleStoredResource_probability (theta : StoredVector d) (hmd : m ≤ d)
    (a : Action d m) :
    uniformCube (Fin d) {u | sampleStoredSet theta (storedUniformTape u) m = a.val} =
      ENNReal.ofReal (weightedLaw (storedVector theta) a) := by
  have heq (u : Fin d → unitInterval) :
      sampleStoredSet theta (storedUniformTape u) m =
        (sampleMSet (storedVector theta) m u).output := by
    rw [sampleStoredSet_eq, sampleStoredResource_values, storedUniformTape_values]
    exact (tableSampler_correct _ _ m _ (List.nodup_finRange d) m le_rfl).symm
  simp only [heq]
  exact sampleMSet_probability (storedVector theta) hmd a

/-- One independent uniform draw per coordinate is the probabilistic input
primitive. Its returned scalar, list cell and traversal are charged; subsequent
accesses to this materialized tape are ordinary counted list reads. -/
def uniformTapeResource (u : Fin d → unitInterval) : ResourceRun (StoredVector d) :=
  let run := resourceTabulate d (fun i => (⟨(u i : ℝ), 1, 1⟩ : ResourceRun ℝ))
  ⟨⟨run.value, by simp [run, resourceTabulate_values]⟩,
    run.work + 1, run.allocated + 1⟩

theorem uniformTapeResource_values (u : Fin d → unitInterval) :
    (uniformTapeResource u).value = storedUniformTape u := by
  apply Subtype.ext
  exact resourceTabulate_values d _

theorem uniformTapeResource_bounds (u : Fin d → unitInterval) :
    (uniformTapeResource u).work ≤ 3 * d + 2 ∧
      (uniformTapeResource u).allocated ≤ 5 * d + 2 := by
  have h := resourceTabulate_bounds d (fun i => (⟨(u i : ℝ), 1, 1⟩ : ResourceRun ℝ))
    1 1 (fun _ => ⟨le_rfl, le_rfl⟩)
  dsimp only [uniformTapeResource]
  constructor <;> omega

def fullSamplerResource (theta : StoredVector d) (m : ℕ) (u : Fin d → unitInterval) :
    ResourceRun (List (Fin d)) :=
  let tape := uniformTapeResource u
  let run := sampleStoredResource theta tape.value m
  ⟨run.value, tape.work + run.work + 1, tape.allocated + run.allocated + 2⟩

theorem fullSamplerResource_values (theta : StoredVector d) (m : ℕ)
    (u : Fin d → unitInterval) :
    (fullSamplerResource theta m u).value =
      (sampleStoredResource theta (storedUniformTape u) m).value := by
  simp only [fullSamplerResource, uniformTapeResource_values]

theorem fullSamplerResource_bounds (theta : StoredVector d) (m : ℕ)
    (u : Fin d → unitInterval) :
    (fullSamplerResource theta m u).work ≤ 2 * m + 15 + d * (5 * d + 7 * m + 54) ∧
    (fullSamplerResource theta m u).allocated ≤ 2 * m + 22 + d * (8 * d + 11 * m + 78) := by
  have ht := uniformTapeResource_bounds u
  have hs := sampleStoredResource_bounds theta (uniformTapeResource u).value m
  dsimp only [fullSamplerResource]
  constructor <;> nlinarith [ht.1, ht.2, hs.1, hs.2]

theorem fullSamplerResource_probability (theta : StoredVector d) (hmd : m ≤ d)
    (a : Action d m) :
    uniformCube (Fin d) {u | (fullSamplerResource theta m u).value.toFinset = a.val} =
      ENNReal.ofReal (weightedLaw (storedVector theta) a) := by
  simp only [fullSamplerResource_values, ← sampleStoredSet_eq]
  exact sampleStoredResource_probability theta hmd a

end MsetsPaper.Upper.ESPSampling
