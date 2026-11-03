import MsetsPaper.Upper.RoundProgram

/-! # The operational sampler implements the observable weighted kernel

Joint measurability is inherited from the verified finite threshold recursion,
not inferred solely from the probabilities of its atoms. Equality of the
pushforward measure then identifies the actual algorithmic random draw with
the kernel used by the adaptive regret theorem.
-/

namespace MsetsPaper.Upper.RoundProgram

open SchurSolver ESPSampling MsetsLower MsetsLower.History
open MeasureTheory MsetsPaper.Probability
open scoped unitInterval

noncomputable section

variable {d m : ℕ}

theorem sampleResource_set (theta : StoredVector d) (hmd : m ≤ d)
    (u : Fin d → unitInterval) :
    (sampleResource theta hmd u).value.action.1 =
      sequentialList (fun i => Real.exp (storedVector theta i))
        (fun i => (u i : ℝ)) (List.finRange d) m := by
  rw [← SampledAction.toFinset_eq]
  change (sampleStoredRAM theta m u).value.toFinset = _
  rw [sampleStoredRAM_output]
  exact tableSampler_correct _ _ m _ (List.nodup_finRange d) m le_rfl

theorem measurable_sampleResource_action {Ω : Type*} [MeasurableSpace Ω]
    (theta : Ω → StoredVector d) (u : Ω → Fin d → unitInterval) (hmd : m ≤ d)
    (htheta : Measurable (fun w => storedVector (theta w))) (hu : Measurable u) :
    Measurable (fun w => (sampleResource (theta w) hmd (u w)).value.action) := by
  have hw : Measurable (fun w i => Real.exp (storedVector (theta w) i)) :=
    measurable_pi_iff.mpr fun i => ((measurable_pi_apply i).comp htheta).exp
  have huR : Measurable (fun w i => (u w i : ℝ)) :=
    measurable_pi_iff.mpr fun i =>
      measurable_subtype_coe.comp ((measurable_pi_apply i).comp hu)
  have hseq := (measurable_sequentialList (List.finRange d) m).comp (hw.prodMk huR)
  have hval : Measurable (fun w => (sampleResource (theta w) hmd (u w)).value.action.1) := by
    simpa only [sampleResource_set, Function.comp_def] using hseq
  apply measurable_to_countable'
  intro a
  convert hval (measurableSet_singleton a.1) using 1
  ext w
  simp only [Set.mem_preimage, Set.mem_singleton_iff, Subtype.val_inj]

theorem sampleResource_map (theta : StoredVector d) (hmd : m ≤ d) :
    (uniformCube (Fin d)).map (fun u => (sampleResource theta hmd u).value.action) =
      finiteAtomicMeasure (weightedLaw (storedVector theta)) id := by
  classical
  have hmeas := measurable_sampleResource_action (fun _ : Fin d → unitInterval => theta)
    id hmd measurable_const measurable_id
  simp only [id_eq] at hmeas
  apply Measure.ext_of_singleton
  intro a
  rw [Measure.map_apply hmeas (measurableSet_singleton a)]
  change uniformCube (Fin d) {u | (sampleResource theta hmd u).value.action = a} = _
  rw [sampleResource_probability]
  simp [finiteAtomicMeasure_apply, Set.mem_singleton_iff]

/-- Actual history-dependent sampling implements precisely the kernel used
in observableWeightedPolicy; there is no premise asserting law equivalence. -/
theorem sampleResource_map_weightedActionKernel {Ω : Type*} [MeasurableSpace Ω]
    (theta : Ω → StoredVector d) (htheta : Measurable (fun w => storedVector (theta w)))
    (hmd : m ≤ d) (w : Ω) :
    (uniformCube (Fin d)).map (fun u => (sampleResource (theta w) hmd u).value.action) =
      weightedActionKernel (m := m) (fun w => storedVector (theta w)) htheta w := by
  exact sampleResource_map (theta w) hmd

end

end MsetsPaper.Upper.RoundProgram
