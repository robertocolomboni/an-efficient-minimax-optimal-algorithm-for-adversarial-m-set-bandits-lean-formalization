import CoefficientOne.Sampling.AtMostSampler

/-! # The exact codomains stated in the correlated-sampling corollary -/

open MeasureTheory EffectiveResistance

namespace CoefficientOne.Sampling
noncomputable section

variable {n k : ℕ} [NeZero n]

def exactRankSampler (hk : k ≤ n) (x : hypersimplex (Fin n) k) (ω : Seed n) : RankSubset (Fin n) k :=
  ⟨exactSampler n k x ω, exactSampler_card hk x ω⟩

theorem measurable_exactRankSampler (hk : k ≤ n) :
    Measurable (fun z : hypersimplex (Fin n) k × Seed n => exactRankSampler hk z.1 z.2) :=
  (measurable_exactSampler hk).subtype_mk

theorem measurable_exactRankSampler_fixed (hk : k ≤ n) (x : hypersimplex (Fin n) k) :
    Measurable (exactRankSampler hk x) := (measurable_exactSampler_fixed hk x).subtype_mk

theorem exactRankSampler_measurePreserving_of_interior_stretch (hk : k ≤ n)
    (hinterior : 1 ≤ k → k < n → InteriorStretchSix n k) (x : hypersimplex (Fin n) k) :
    MeasurePreserving (exactRankSampler hk x) (seedMeasure n) (lawMeasure (maximumEntropyLaw x)) := by
  have hm := measurable_exactRankSampler_fixed hk x
  refine ⟨hm, ?_⟩
  have hv : MeasurableEmbedding (Subtype.val : RankSubset (Fin n) k → Finset (Fin n)) :=
    MeasurableEmbedding.subtype_coe (Set.toFinite {S : Finset (Fin n) | S.card = k}).measurableSet
  apply hv.map_injective
  rw [Measure.map_map hv.measurable hm]
  exact exactSampler_map_maximumEntropyLaw_of_interior_stretch hk hinterior x

theorem exactRankSampler_stretch_of_interior_stretch (hk : k ≤ n)
    (hinterior : 1 ≤ k → k < n → InteriorStretchSix n k) (x y : hypersimplex (Fin n) k) :
    (∫ ω, outputDistance (exactRankSampler hk x ω).val (exactRankSampler hk y ω).val ∂seedMeasure n) ≤
      6 * vectorL1 (fun i => x.val i - y.val i) :=
  exactSampler_stretch_of_interior_stretch hk hinterior x y

abbrev AtMostSubset (n k : ℕ) := {S : Finset (Fin n) // S.card ≤ k}

def atMostRankSampler (n k : ℕ) [NeZero n] (x : atMostHypersimplex (Fin n) k)
    (ω : Seed (n + k)) : AtMostSubset n k :=
  ⟨atMostSampler n k x ω, atMostSampler_card_le x ω⟩

theorem measurable_atMostRankSampler :
    Measurable (fun z : atMostHypersimplex (Fin n) k × Seed (n + k) => atMostRankSampler n k z.1 z.2) :=
  measurable_atMostSampler.subtype_mk

theorem atMostRankSampler_card (x : atMostHypersimplex (Fin n) k) (ω : Seed (n + k)) :
    (atMostRankSampler n k x ω).val.card = ⌊coordinateSum x.val⌋₊ ∨
      (atMostRankSampler n k x ω).val.card = ⌈coordinateSum x.val⌉₊ := atMostSampler_card x ω

end
end CoefficientOne.Sampling
