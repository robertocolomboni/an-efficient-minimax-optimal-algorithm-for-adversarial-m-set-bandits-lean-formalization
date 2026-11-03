import CoefficientOne.Sampling.InteriorStretch
import CoefficientOne.Sampling.TypedSamplers
import CoefficientOne.Sampling.BoundaryVersion
import CoefficientOne.Sampling.BoundaryInteriorAgreement

/-! # Appendix E.2: the unconditional correlated-sampling corollary

The local estimate is proved for the actual shared permutation and uniforms.
The interior theorem supplies every premise of the radial completion and dummy
coordinate transfers. The statements here have no local-coupling or stretch
assumption. Exact-cardinality laws follow the Borel--Cantelli and bounded
convergence route in the manuscript; direct boundary sampling is also identified.
-/

open MeasureTheory EffectiveResistance

namespace CoefficientOne.Sampling
noncomputable section

variable {n k : ℕ} [NeZero n]

theorem exactSampler_stretch_six (hk : k ≤ n) (x y : hypersimplex (Fin n) k) :
    expectedOutputDistance (seedMeasure n) (exactSampler n k x) (exactSampler n k y) ≤
      6 * vectorL1 (fun i => x.val i - y.val i) :=
  exactSampler_stretch_of_interior_stretch hk (fun h₁ h₂ => interiorStretchSix h₁ h₂) x y

theorem exactSampler_marginal (hk : k ≤ n) (x : hypersimplex (Fin n) k) (i : Fin n) :
    (∫ ω, indicator i (exactSampler n k x ω) ∂seedMeasure n) = x.val i :=
  exactSampler_marginal_of_interior_stretch hk (fun h₁ h₂ => interiorStretchSix h₁ h₂) x i

theorem exactSampler_probability (hk : k ≤ n) (x : hypersimplex (Fin n) k) (i : Fin n) :
    (seedMeasure n) {ω | i ∈ exactSampler n k x ω} = ENNReal.ofReal (x.val i) :=
  probability_member_eq_of_integral (seedMeasure n) (measurable_exactSampler_fixed hk x) i
    (exactSampler_marginal hk x i)

theorem exactRankSampler_measurePreserving (hk : k ≤ n) (x : hypersimplex (Fin n) k) :
    MeasurePreserving (exactRankSampler hk x) (seedMeasure n) (lawMeasure (maximumEntropyLaw x)) :=
  exactRankSampler_measurePreserving_of_interior_stretch hk (fun h₁ h₂ => interiorStretchSix h₁ h₂) x

theorem exactRankSampler_stretch_six (hk : k ≤ n) (x y : hypersimplex (Fin n) k) :
    (∫ ω, outputDistance (exactRankSampler hk x ω).val (exactRankSampler hk y ω).val ∂seedMeasure n) ≤
      6 * vectorL1 (fun i => x.val i - y.val i) := exactSampler_stretch_six hk x y

theorem exactSampler_ae_eq_interior_by_distance (hkpos : 1 ≤ k) (hktop : k < n)
    (x : interiorHypersimplex (Fin n) k) :
    exactSampler n k (interiorInputToClosed x) =ᵐ[seedMeasure n] interiorSampler k x := by
  filter_upwards [boundarySampler_ae_eq_interiorSampler_by_distance hkpos hktop
    (interiorStretchSix hkpos hktop) x] with ω hω
  rw [exactSampler_nondegenerate hkpos hktop]
  exact hω

/-- All guarantees for the concrete exact-cardinality sampler, including its
full maximum-entropy law and its version relation to direct boundary sampling. -/
theorem exact_correlated_sampling (hk : k ≤ n) :
    Measurable (fun z : hypersimplex (Fin n) k × Seed n => exactRankSampler hk z.1 z.2) ∧
    (∀ x, MeasurePreserving (exactRankSampler hk x) (seedMeasure n) (lawMeasure (maximumEntropyLaw x))) ∧
    (∀ x i, (seedMeasure n) {ω | i ∈ (exactRankSampler hk x ω).val} = ENNReal.ofReal (x.val i)) ∧
    (∀ x y, (∫ ω, outputDistance (exactRankSampler hk x ω).val (exactRankSampler hk y ω).val ∂seedMeasure n) ≤
      6 * vectorL1 (fun i => x.val i - y.val i)) ∧
    (∀ x, (fun ω => (exactRankSampler hk x ω).val) =ᵐ[seedMeasure n] directSampler x) :=
  ⟨measurable_exactRankSampler hk, exactRankSampler_measurePreserving hk,
    exactSampler_probability hk, exactRankSampler_stretch_six hk, exactSampler_ae_eq_directSampler hk⟩

local instance : NeZero (n + k) := ⟨by have h := NeZero.ne n; omega⟩

theorem atMostSampler_marginal (x : atMostHypersimplex (Fin n) k) (i : Fin n) :
    (∫ ω, indicator i (atMostSampler n k x ω) ∂seedMeasure (n + k)) = x.val i :=
  atMostSampler_marginal_of_interior_stretch (fun h₁ h₂ => interiorStretchSix h₁ h₂) x i

theorem atMostSampler_probability (x : atMostHypersimplex (Fin n) k) (i : Fin n) :
    (seedMeasure (n + k)) {ω | i ∈ atMostSampler n k x ω} = ENNReal.ofReal (x.val i) :=
  atMostSampler_probability_of_interior_stretch (fun h₁ h₂ => interiorStretchSix h₁ h₂) x i

theorem atMostSampler_stretch_twelve (x y : atMostHypersimplex (Fin n) k) :
    expectedOutputDistance (seedMeasure (n + k)) (atMostSampler n k x) (atMostSampler n k y) ≤
      12 * vectorL1 (fun i => x.val i - y.val i) :=
  atMostSampler_stretch_of_interior_stretch (fun h₁ h₂ => interiorStretchSix h₁ h₂) x y

/-- All guarantees for the concrete at-most-cardinality sampler. Its codomain
imposes cardinality at most `k` at every seed, and the stronger floor/ceiling
property below also holds everywhere, including when `k = 0`. -/
theorem atMost_correlated_sampling :
    Measurable (fun z : atMostHypersimplex (Fin n) k × Seed (n + k) => atMostRankSampler n k z.1 z.2) ∧
    (∀ x ω, (atMostRankSampler n k x ω).val.card = ⌊coordinateSum x.val⌋₊ ∨
      (atMostRankSampler n k x ω).val.card = ⌈coordinateSum x.val⌉₊) ∧
    (∀ x i, (seedMeasure (n + k)) {ω | i ∈ (atMostRankSampler n k x ω).val} = ENNReal.ofReal (x.val i)) ∧
    (∀ x y, (∫ ω, outputDistance (atMostRankSampler n k x ω).val
      (atMostRankSampler n k y ω).val ∂seedMeasure (n + k)) ≤
        12 * vectorL1 (fun i => x.val i - y.val i)) :=
  ⟨measurable_atMostRankSampler, atMostRankSampler_card,
    atMostSampler_probability, atMostSampler_stretch_twelve⟩

end
end CoefficientOne.Sampling
