import CoefficientOne.Sampling.RadialSampler

/-!
# Agreement with the interior sampler by the manuscript's distance argument

This proves the statement before and independently of the later direct-law
boundary agreement. The second sampler is held fixed in bounded convergence.
-/

open scoped Topology
open MeasureTheory Filter

namespace CoefficientOne.Sampling
noncomputable section

variable {n k : ℕ} [NeZero n]

theorem boundarySampler_ae_eq_interiorSampler_by_distance
    (hkpos : 1 ≤ k) (hktop : k < n) (hstretch : InteriorStretchSix n k)
    (x : interiorHypersimplex (Fin n) k) :
    boundarySampler hkpos hktop (interiorInputToClosed x) =ᵐ[seedMeasure n] interiorSampler k x := by
  let xc := interiorInputToClosed x
  let C := vectorL1 (fun i : Fin n => (k : ℝ) / Fintype.card (Fin n) - x.val i)
  have hm : Measurable (interiorSampler k x) := by
    have hp : Measurable (fun ω : Seed n => (x, ω)) := measurable_const.prodMk measurable_id
    exact fun s hs => hp (measurable_interiorSampler hkpos hktop hs)
  have hs : ∀ᵐ ω ∂seedMeasure n, ∃ S, StableValue (fun _ : ℕ => interiorSampler k x ω) S :=
    Eventually.of_forall fun ω => ⟨interiorSampler k x ω, 0, fun _ _ => rfl⟩
  have ht : Tendsto (fun j => 6 * ((dyadicTime j : ℝ) * C)) atTop (𝓝 0) := by
    have hd := continuous_subtype_val.continuousAt.tendsto.comp dyadicTime_tendsto
    simpa using (hd.mul_const C).const_mul 6
  have hb := expectedOutputDistance_completion_le (seedMeasure n) (initialSegment n k)
    (fun j => radialSampler hkpos hktop j xc) (fun _ => interiorSampler k x)
    (fun j => measurable_radialSampler_fixed hkpos hktop j xc) (fun _ => hm)
    (radialSampler_ae_stable_of_interior_stretch hkpos hktop hstretch xc) hs ht
    (fun j => by
      have h := hstretch (radialInteriorInput hkpos hktop xc j) x
      change expectedOutputDistance (seedMeasure n) (radialSampler hkpos hktop j xc) (interiorSampler k x) ≤
        6 * vectorL1 (fun i => (radialMarginal xc (dyadicTime j)).val i - xc.val i) at h
      rw [radialMarginal_self_l1] at h
      exact h)
  have he : (fun ω : Seed n => finiteCompletion (initialSegment n k)
      (fun _ : ℕ => interiorSampler k x ω)) = interiorSampler k x := by
    funext ω
    exact finiteCompletion_of_stable _ ⟨0, fun _ _ => rfl⟩
  rw [he] at hb
  apply (expectedOutputDistance_eq_zero_iff (seedMeasure n)
    (measurable_boundarySampler_fixed hkpos hktop xc) hm).mp
  exact le_antisymm hb (expectedOutputDistance_nonneg _ _ _)

end
end CoefficientOne.Sampling
