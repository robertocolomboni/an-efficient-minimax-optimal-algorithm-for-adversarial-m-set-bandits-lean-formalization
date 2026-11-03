import CoefficientOne.Sampling.InteriorSampler
import CoefficientOne.Sampling.RadialGeometry
import CoefficientOne.Sampling.BoundaryCompletion
import CoefficientOne.Sampling.DummyCardinality
import CoefficientOne.Sampling.SamplerLaw

/-!
# The concrete radial completion

The transfer lemmas in this module take the interior stretch statement as an
explicit input. The final corollary supplies its proof from the local coupling
and Dini argument; these transfer lemmas do not assert that result on their own.
-/

open scoped BigOperators Topology
open MeasureTheory Filter EffectiveResistance

namespace CoefficientOne.Sampling
noncomputable section

variable {n k : ℕ} [NeZero n]

def InteriorStretchSix (n k : ℕ) [NeZero n] : Prop :=
  ∀ x y : interiorHypersimplex (Fin n) k,
    expectedOutputDistance (seedMeasure n) (interiorSampler k x) (interiorSampler k y) ≤
      6 * vectorL1 (fun i => x.val i - y.val i)

def radialInteriorInput (hkpos : 1 ≤ k) (hktop : k < n)
    (x : hypersimplex (Fin n) k) (j : ℕ) : interiorHypersimplex (Fin n) k :=
  ⟨(radialMarginal x (dyadicTime j)).val,
    radialMarginal_mem_interior hkpos (by simpa using hktop) x _ (dyadicTime_pos j)⟩

theorem continuous_radialInteriorInput (hkpos : 1 ≤ k) (hktop : k < n) (j : ℕ) :
    Continuous (fun x : hypersimplex (Fin n) k => radialInteriorInput hkpos hktop x j) := by
  exact ((continuous_radialMarginal (dyadicTime j)).subtype_val).subtype_mk _

def radialSampler (hkpos : 1 ≤ k) (hktop : k < n) (j : ℕ)
    (x : hypersimplex (Fin n) k) (ω : Seed n) : Finset (Fin n) :=
  interiorSampler k (radialInteriorInput hkpos hktop x j) ω

theorem measurable_radialSampler (hkpos : 1 ≤ k) (hktop : k < n) (j : ℕ) :
    Measurable (fun z : hypersimplex (Fin n) k × Seed n => radialSampler hkpos hktop j z.1 z.2) := by
  have hx : Measurable (fun z : hypersimplex (Fin n) k × Seed n =>
      radialInteriorInput hkpos hktop z.1 j) := fun s hs =>
    measurable_fst ((continuous_radialInteriorInput hkpos hktop j).measurable hs)
  have hp : Measurable (fun z : hypersimplex (Fin n) k × Seed n =>
      (radialInteriorInput hkpos hktop z.1 j, z.2)) := hx.prodMk measurable_snd
  exact fun s hs => hp (measurable_interiorSampler hkpos hktop hs)

theorem measurable_radialSampler_fixed (hkpos : 1 ≤ k) (hktop : k < n) (j : ℕ)
    (x : hypersimplex (Fin n) k) : Measurable (radialSampler hkpos hktop j x) := by
  have hp : Measurable (fun ω : Seed n => (x, ω)) := measurable_const.prodMk measurable_id
  exact fun s hs => hp (measurable_radialSampler hkpos hktop j hs)

theorem radialSampler_card (hkpos : 1 ≤ k) (hktop : k < n) (j : ℕ)
    (x : hypersimplex (Fin n) k) (ω : Seed n) : (radialSampler hkpos hktop j x ω).card = k :=
  interiorSampler_card hktop.le _ ω

def boundarySampler (hkpos : 1 ≤ k) (hktop : k < n)
    (x : hypersimplex (Fin n) k) (ω : Seed n) : Finset (Fin n) :=
  finiteCompletion (initialSegment n k) (fun j => radialSampler hkpos hktop j x ω)

theorem measurable_boundarySampler (hkpos : 1 ≤ k) (hktop : k < n) :
    Measurable (fun z : hypersimplex (Fin n) k × Seed n => boundarySampler hkpos hktop z.1 z.2) :=
  measurable_finiteCompletion _ _ (measurable_radialSampler hkpos hktop)

theorem measurable_boundarySampler_fixed (hkpos : 1 ≤ k) (hktop : k < n)
    (x : hypersimplex (Fin n) k) : Measurable (boundarySampler hkpos hktop x) := by
  have hp : Measurable (fun ω : Seed n => (x, ω)) := measurable_const.prodMk measurable_id
  exact fun s hs => hp (measurable_boundarySampler hkpos hktop hs)

theorem boundarySampler_card (hkpos : 1 ≤ k) (hktop : k < n)
    (x : hypersimplex (Fin n) k) (ω : Seed n) : (boundarySampler hkpos hktop x ω).card = k :=
  finiteCompletion_property (fun S : Finset (Fin n) => S.card = k) _ (initialSegment_card hktop.le) _
    (fun j => radialSampler_card hkpos hktop j x ω)

theorem summable_radialSampler_expected_of_interior_stretch (hkpos : 1 ≤ k) (hktop : k < n)
    (hstretch : InteriorStretchSix n k) (x : hypersimplex (Fin n) k) :
    Summable (fun j => expectedOutputDistance (seedMeasure n)
      (radialSampler hkpos hktop (j + 1) x) (radialSampler hkpos hktop j x)) := by
  let C := vectorL1 (fun i => x.val i - (k : ℝ) / Fintype.card (Fin n))
  apply Summable.of_nonneg_of_le (fun _ => expectedOutputDistance_nonneg _ _ _)
    (f := fun j => 6 * ((dyadicTime (j + 1) : ℝ) * C))
  · intro j
    have h := hstretch (radialInteriorInput hkpos hktop x (j + 1)) (radialInteriorInput hkpos hktop x j)
    change expectedOutputDistance (seedMeasure n) (radialSampler hkpos hktop (j + 1) x)
      (radialSampler hkpos hktop j x) ≤
      6 * vectorL1 (fun i => (radialMarginal x (dyadicTime (j + 1))).val i -
        (radialMarginal x (dyadicTime j)).val i) at h
    rw [radialMarginal_adjacent_l1] at h
    exact h
  · exact (summable_dyadicTime_succ.mul_right C).mul_left 6

theorem radialSampler_ae_stable_of_interior_stretch (hkpos : 1 ≤ k) (hktop : k < n)
    (hstretch : InteriorStretchSix n k) (x : hypersimplex (Fin n) k) :
    ∀ᵐ ω ∂seedMeasure n, ∃ S, StableValue (fun j => radialSampler hkpos hktop j x ω) S := by
  apply ae_stableValue_of_summable_expected
  · intro j
    exact measurable_radialSampler_fixed hkpos hktop j x
  · intro j ω
    rw [radialSampler_card, radialSampler_card]
  · exact summable_radialSampler_expected_of_interior_stretch hkpos hktop hstretch x

theorem boundarySampler_integral_of_interior_stretch (hkpos : 1 ≤ k) (hktop : k < n)
    (hstretch : InteriorStretchSix n k) (x : hypersimplex (Fin n) k) (φ : Finset (Fin n) → ℝ) :
    (∫ ω, φ (boundarySampler hkpos hktop x ω) ∂seedMeasure n) =
      lawExpectation (maximumEntropyLaw x) (fun S => φ S.val) := by
  have hlim := integral_finiteCompletion_tendsto (seedMeasure n) (initialSegment n k)
    (fun j => radialSampler hkpos hktop j x)
    (fun j => measurable_radialSampler_fixed hkpos hktop j x)
    (radialSampler_ae_stable_of_interior_stretch hkpos hktop hstretch x) φ
  have hφ : Continuous (fun p : RankSubset (Fin n) k → ℝ => ∑ S, p S * φ S.val) := by fun_prop
  have hmass := hφ.continuousAt.tendsto.comp (maximumEntropyMass_dyadic_tendsto x)
  have he (j : ℕ) : (∫ ω, φ (radialSampler hkpos hktop j x ω) ∂seedMeasure n) =
      ∑ S : RankSubset (Fin n) k, maximumEntropyMass (radialMarginal x (dyadicTime j)) S * φ S.val := by
    exact interiorSampler_integral hkpos hktop (radialInteriorInput hkpos hktop x j) φ
  simp only [he] at hlim
  exact tendsto_nhds_unique hlim hmass

theorem boundarySampler_map_maximumEntropyLaw_of_interior_stretch
    (hkpos : 1 ≤ k) (hktop : k < n) (hstretch : InteriorStretchSix n k)
    (x : hypersimplex (Fin n) k) :
    (seedMeasure n).map (boundarySampler hkpos hktop x) =
      (lawMeasure (maximumEntropyLaw x)).map (Subtype.val : RankSubset (Fin n) k → Finset (Fin n)) :=
  sampler_map_law_of_integral (seedMeasure n) _ (measurable_boundarySampler_fixed hkpos hktop x)
    (maximumEntropyLaw x) Subtype.val (boundarySampler_integral_of_interior_stretch hkpos hktop hstretch x)

theorem boundarySampler_marginal_of_interior_stretch
    (hkpos : 1 ≤ k) (hktop : k < n) (hstretch : InteriorStretchSix n k)
    (x : hypersimplex (Fin n) k) (i : Fin n) :
    (∫ ω, indicator i (boundarySampler hkpos hktop x ω) ∂seedMeasure n) = x.val i := by
  rw [boundarySampler_integral_of_interior_stretch hkpos hktop hstretch]
  exact congrFun (maximumEntropyLaw_mean x) i

theorem boundarySampler_stretch_of_interior_stretch (hkpos : 1 ≤ k) (hktop : k < n)
    (hstretch : InteriorStretchSix n k) (x y : hypersimplex (Fin n) k) :
    expectedOutputDistance (seedMeasure n) (boundarySampler hkpos hktop x) (boundarySampler hkpos hktop y) ≤
      6 * vectorL1 (fun i => x.val i - y.val i) := by
  apply expectedOutputDistance_completion_le (seedMeasure n) (initialSegment n k)
    (fun j => radialSampler hkpos hktop j x) (fun j => radialSampler hkpos hktop j y)
    (fun j => measurable_radialSampler_fixed hkpos hktop j x)
    (fun j => measurable_radialSampler_fixed hkpos hktop j y)
    (radialSampler_ae_stable_of_interior_stretch hkpos hktop hstretch x)
    (radialSampler_ae_stable_of_interior_stretch hkpos hktop hstretch y)
    ((radialMarginal_pair_l1_tendsto x y).const_mul 6)
  intro j
  exact hstretch _ _

end
end CoefficientOne.Sampling
