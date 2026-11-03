import CoefficientOne.Sampling.ParametrizationTheorem
import CoefficientOne.Sampling.RankSubsetLaw

/-! # The actual jointly Borel interior sampler -/

open scoped BigOperators Topology
open EffectiveResistance MeasureTheory

namespace CoefficientOne.Sampling

noncomputable section

variable {ι : Type*} [Fintype ι] [DecidableEq ι] [Nonempty ι]

def marginalWeights (k : ℕ) (x : ι → ℝ) (i : ι) : ℝ :=
  Real.exp ((parameterOfMarginal k x).val i)

theorem marginalWeights_pos (k : ℕ) (x : ι → ℝ) (i : ι) :
    0 < marginalWeights k x i := Real.exp_pos _

theorem continuous_interior_marginalWeights {k : ℕ} (hkpos : 1 ≤ k)
    (hktop : k < Fintype.card ι) :
    Continuous (fun x : interiorHypersimplex ι k => marginalWeights k x.val) := by
  apply continuous_iff_continuousAt.mpr
  intro x
  have hp := (parameterOfMarginal_contDiffAt hkpos hktop x.val x.property).continuousAt.comp
    continuous_subtype_val.continuousAt
  apply continuousAt_pi.mpr
  intro i
  exact Real.continuous_exp.continuousAt.comp
    ((continuous_apply i).continuousAt.comp (continuous_subtype_val.continuousAt.comp hp))

def interiorInputToClosed {k : ℕ} (x : interiorHypersimplex ι k) : hypersimplex ι k :=
  ⟨x.val, interiorHypersimplex_subset x.property⟩

theorem maximumEntropyLaw_eq_marginalWeights {k : ℕ} (hkpos : 1 ≤ k)
    (hktop : k < Fintype.card ι) (x : interiorHypersimplex ι k) :
    maximumEntropyLaw (interiorInputToClosed x) =
      externalFieldLaw (marginalWeights k x.val) (marginalWeights_pos k x.val) hktop.le := by
  exact maximumEntropyLaw_eq_parameterOfMarginal hkpos hktop (interiorInputToClosed x) x.property.1

variable {n : ℕ} [NeZero n]

def interiorSampler (k : ℕ) (x : interiorHypersimplex (Fin n) k) (ω : Seed n) : Finset (Fin n) :=
  sequentialSampler (marginalWeights k x.val) k ω

theorem interiorSampler_card {k : ℕ} (hk : k ≤ n)
    (x : interiorHypersimplex (Fin n) k) (ω : Seed n) : (interiorSampler k x ω).card = k :=
  sequentialSampler_card _ k hk ω

theorem measurable_interiorSampler {k : ℕ} (hkpos : 1 ≤ k) (hktop : k < n) :
    Measurable (fun z : interiorHypersimplex (Fin n) k × Seed n => interiorSampler k z.1 z.2) := by
  have hw := (continuous_interior_marginalWeights (ι := Fin n) hkpos
    (by simpa using hktop)).measurable
  have hp : Measurable (fun z : interiorHypersimplex (Fin n) k × Seed n =>
      (marginalWeights k z.1.val, z.2)) := (hw.comp measurable_fst).prodMk measurable_snd
  exact (measurable_sequentialSampler k).comp hp

theorem interiorSampler_productLaw {k : ℕ} (hk : k ≤ n)
    (x : interiorHypersimplex (Fin n) k) :
    MeasurePreserving (interiorSampler k x) (seedMeasure n)
      (lawMeasure (restrictedLaw (marginalWeights k x.val) (marginalWeights_pos k x.val)
        Finset.univ k (by simpa using hk))) :=
  sequentialSampler_measurePreserving _ (marginalWeights_pos k x.val) k hk

theorem interiorSampler_map_maximumEntropyLaw {k : ℕ} (hkpos : 1 ≤ k) (hktop : k < n)
    (x : interiorHypersimplex (Fin n) k) :
    (seedMeasure n).map (interiorSampler k x) =
      (lawMeasure (maximumEntropyLaw (interiorInputToClosed x))).map
        (Subtype.val : RankSubset (Fin n) k → Finset (Fin n)) := by
  rw [maximumEntropyLaw_eq_marginalWeights hkpos (by simpa using hktop)]
  exact sequentialSampler_map_externalFieldLaw _ (marginalWeights_pos k x.val) k hktop.le

theorem interiorSampler_integral {k : ℕ} (hkpos : 1 ≤ k) (hktop : k < n)
    (x : interiorHypersimplex (Fin n) k) (φ : Finset (Fin n) → ℝ) :
    (∫ ω, φ (interiorSampler k x ω) ∂seedMeasure n) =
      lawExpectation (maximumEntropyLaw (interiorInputToClosed x)) (fun S => φ S.val) := by
  have hp := interiorSampler_productLaw hktop.le x
  rw [← integral_map hp.measurable.aemeasurable (measurable_of_finite φ).aestronglyMeasurable,
    hp.map_eq, integral_restrictedLaw_univ _ _ k (by simpa using hktop.le)]
  rw [maximumEntropyLaw_eq_marginalWeights hkpos (by simpa using hktop), integral_lawMeasure]

theorem interiorSampler_marginal {k : ℕ} (hkpos : 1 ≤ k) (hktop : k < n)
    (x : interiorHypersimplex (Fin n) k) (i : Fin n) :
    (∫ ω, indicator i (interiorSampler k x ω) ∂seedMeasure n) = x.val i := by
  rw [interiorSampler_integral hkpos hktop]
  exact congrFun (maximumEntropyLaw_mean (interiorInputToClosed x)) i

end
end CoefficientOne.Sampling
