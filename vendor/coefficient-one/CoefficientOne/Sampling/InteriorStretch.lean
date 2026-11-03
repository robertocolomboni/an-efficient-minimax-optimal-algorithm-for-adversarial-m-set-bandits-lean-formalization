import CoefficientOne.Sampling.InteriorSegment
import CoefficientOne.Sampling.CommonSeedDini
import CoefficientOne.Sampling.VariationTheorem
import CoefficientOne.Sampling.RadialSampler
import CoefficientOne.Sampling.LocalCoupling

/-! # Assembling the interior stretch estimate

The transfer lemma keeps the local input explicit. The final theorem supplies
the proved local coupling statement and yields the unconditional stretch-six
bound for the actual interior sampler.
-/

open scoped BigOperators Topology
open EffectiveResistance Matrix MeasureTheory Set Filter
namespace CoefficientOne.Sampling
noncomputable section

def ParameterLocalCoupling (n k : ℕ) : Prop :=
  ∀ (θ : ℝ → Fin n → ℝ) (a : Fin n → ℝ), HasDerivAt θ a 0 →
    ∀ ε > 0, ∀ᶠ t in 𝓝[≠] (0 : ℝ),
      expectedOutputDistance (seedMeasure n)
        (sequentialSampler (fun i => Real.exp (θ 0 i)) k)
        (sequentialSampler (fun i => Real.exp (θ t i)) k) / |t| ≤
        2 * samplerVariation (fun i => Real.exp (θ 0 i)) k a + ε

variable {n k : ℕ} [NeZero n]

def interiorSegmentSampler (x y : interiorHypersimplex (Fin n) k)
    (s : ℝ) : Seed n → Finset (Fin n) :=
  sequentialSampler (marginalWeights k (interiorSegmentVector x y s)) k

theorem measurable_interiorSegmentSampler (x y : interiorHypersimplex (Fin n) k) (s : ℝ) :
    Measurable (interiorSegmentSampler x y s) :=
  (measurable_sequentialSampler k).comp (measurable_const.prodMk measurable_id)

theorem interiorSegment_localSlope_of_localCoupling
    (hkpos : 1 ≤ k) (hktop : k < n) (hlocal : ParameterLocalCoupling n k)
    (x y : interiorHypersimplex (Fin n) k) (s : ℝ) (hs : s ∈ Icc (0 : ℝ) 1) :
    LocalSeedSlope (seedMeasure n) (interiorSegmentSampler x y)
      (6 * vectorL1 (y.val - x.val)) s := by
  intro ε hε
  let θ := interiorSegmentParameter x y s
  let a := deriv θ 0
  have hθ : HasDerivAt θ a 0 := interiorSegmentParameter_hasDerivAt hkpos hktop x y s hs
  have hloc := hlocal θ a hθ ε hε
  have hV := samplerVariation_le_three_l1
    (marginalWeights k (interiorSegmentVector x y s))
    (marginalWeights_pos k (interiorSegmentVector x y s)) k hkpos (by omega) a
  have hv : covarianceMatrix (marginalWeights k (interiorSegmentVector x y s)) k *ᵥ a =
      y.val - x.val := interiorSegment_covariance_velocity hkpos hktop x y s hs
  rw [hv] at hV
  have hw0 : (fun i => Real.exp (θ 0 i)) = marginalWeights k (interiorSegmentVector x y s) := by
    ext i
    simp only [θ, interiorSegmentParameter, add_zero, marginalWeights]
  have hwt (t : ℝ) : (fun i => Real.exp (θ t i)) = marginalWeights k (interiorSegmentVector x y (s + t)) := rfl
  rw [hw0] at hloc
  filter_upwards [hloc] with t ht
  rw [hwt t] at ht
  change expectedOutputDistance (seedMeasure n)
    (sequentialSampler (marginalWeights k (interiorSegmentVector x y s)) k)
    (sequentialSampler (marginalWeights k (interiorSegmentVector x y (s + t))) k) / |t| ≤ _
  exact ht.trans (by change _ ≤ 6 * l1Norm (y.val - x.val) + ε; linarith)

theorem interiorStretchSix_of_localCoupling (hkpos : 1 ≤ k) (hktop : k < n)
    (hlocal : ParameterLocalCoupling n k) : InteriorStretchSix n k := by
  intro x y
  have hL : 0 ≤ 6 * vectorL1 (y.val - x.val) := by
    apply mul_nonneg (by norm_num)
    exact Finset.sum_nonneg (fun _ _ => abs_nonneg _)
  have h := commonSeed_dini_stretch (seedMeasure n) (interiorSegmentSampler x y)
    (measurable_interiorSegmentSampler x y) (6 * vectorL1 (y.val - x.val)) hL
    (interiorSegment_localSlope_of_localCoupling hkpos hktop hlocal x y)
  have hzero : interiorSegmentSampler x y 0 = interiorSampler k x := by
    unfold interiorSegmentSampler
    rw [interiorSegmentVector_zero]
    rfl
  have hone : interiorSegmentSampler x y 1 = interiorSampler k y := by
    unfold interiorSegmentSampler
    rw [interiorSegmentVector_one]
    rfl
  have hnorm : vectorL1 (y.val - x.val) = vectorL1 (fun i => x.val i - y.val i) := by
    apply Finset.sum_congr rfl
    intro i _
    exact abs_sub_comm _ _
  rwa [hzero, hone, hnorm] at h

/-- The actual interior sampler has stretch six on its common product seed. -/
theorem interiorStretchSix (hkpos : 1 ≤ k) (hktop : k < n) : InteriorStretchSix n k :=
  interiorStretchSix_of_localCoupling hkpos hktop
    (fun θ a hθ => parameter_local_coupling k hktop.le θ a hθ)

end
end CoefficientOne.Sampling
