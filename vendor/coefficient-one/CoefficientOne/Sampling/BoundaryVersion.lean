import CoefficientOne.Sampling.ExactSampler
import CoefficientOne.Sampling.AmbientRankLaw
import CoefficientOne.Sampling.FiniteLawStability
import CoefficientOne.Sampling.FiniteLawProductAgreement

/-!
# The direct-sampling version at each boundary input

For each fixed input, convergence of the finite masses gives eventual agreement
with the direct sequential algorithm. The exceptional set may depend on the
input. No finite limit of the external-field parameters is asserted or used.
-/

open MeasureTheory Filter EffectiveResistance
open scoped Topology

namespace CoefficientOne.Sampling
noncomputable section

variable {n k : ℕ} [NeZero n]

def directSampler (x : hypersimplex (Fin n) k) : Seed n → Finset (Fin n) :=
  finiteLawSampler (ambientRankLaw (maximumEntropyLaw x))

theorem directSampler_card (x : hypersimplex (Fin n) k) (ω : Seed n) :
    (directSampler x ω).card = k :=
  finiteLawSampler_card _ (ambientRankLaw_support (maximumEntropyLaw x)) ω

theorem measurable_directSampler (x : hypersimplex (Fin n) k) : Measurable (directSampler x) :=
  measurable_finiteLawSampler _

theorem directSampler_map_maximumEntropyLaw (x : hypersimplex (Fin n) k) :
    (seedMeasure n).map (directSampler x) =
      (lawMeasure (maximumEntropyLaw x)).map
        (Subtype.val : RankSubset (Fin n) k → Finset (Fin n)) := by
  rw [(ambientRankLaw_val_measurePreserving (maximumEntropyLaw x)).map_eq]
  exact (finiteLawSampler_measurePreserving _).map_eq

/-- In the interior the two sequential algorithms agree on every seed. -/
theorem directSampler_eq_interiorSampler (hkpos : 1 ≤ k) (hktop : k < n)
    (x : interiorHypersimplex (Fin n) k) (ω : Seed n) :
    directSampler (interiorInputToClosed x) ω = interiorSampler k x ω := by
  unfold directSampler
  rw [maximumEntropyLaw_eq_marginalWeights hkpos (by simpa using hktop), ambientRankLaw_externalField]
  exact finiteLawSampler_restrictedLaw_eq_sequentialSampler _ _ k hktop.le ω

theorem radialSampler_eq_directSampler (hkpos : 1 ≤ k) (hktop : k < n)
    (x : hypersimplex (Fin n) k) (j : ℕ) (ω : Seed n) :
    radialSampler hkpos hktop j x ω = directSampler (radialMarginal x (dyadicTime j)) ω := by
  exact (directSampler_eq_interiorSampler hkpos hktop (radialInteriorInput hkpos hktop x j) ω).symm

/-- Almost-sure eventual agreement for each fixed input, including boundary inputs. -/
theorem radialSampler_ae_eventually_eq_directSampler (hkpos : 1 ≤ k) (hktop : k < n)
    (x : hypersimplex (Fin n) k) :
    ∀ᵐ ω ∂seedMeasure n, ∀ᶠ j in atTop, radialSampler hkpos hktop j x ω = directSampler x ω := by
  have hmass (S : RankSubset (Fin n) k) :
      Tendsto (fun j => (maximumEntropyLaw (radialMarginal x (dyadicTime j))).val S)
        atTop (𝓝 ((maximumEntropyLaw x).val S)) :=
    (continuous_apply S).tendsto _ |>.comp (maximumEntropyMass_dyadic_tendsto x)
  have h := finiteLawSampler_ae_eventually_eq (ambientRankLaw (maximumEntropyLaw x))
    (fun j => ambientRankLaw (maximumEntropyLaw (radialMarginal x (dyadicTime j))))
    (ambientRankMass_tendsto _ _ hmass)
  filter_upwards [h] with ω hω
  simpa only [radialSampler_eq_directSampler, directSampler] using hω

/-- The Borel completion is a version of direct sampling at each fixed input. -/
theorem boundarySampler_ae_eq_directSampler (hkpos : 1 ≤ k) (hktop : k < n)
    (x : hypersimplex (Fin n) k) :
    boundarySampler hkpos hktop x =ᵐ[seedMeasure n] directSampler x := by
  filter_upwards [radialSampler_ae_eventually_eq_directSampler hkpos hktop x] with ω hω
  exact finiteCompletion_of_stable (initialSegment n k) (eventually_atTop.mp hω)

theorem boundarySampler_ae_eq_interiorSampler (hkpos : 1 ≤ k) (hktop : k < n)
    (x : interiorHypersimplex (Fin n) k) :
    boundarySampler hkpos hktop (interiorInputToClosed x) =ᵐ[seedMeasure n] interiorSampler k x := by
  filter_upwards [boundarySampler_ae_eq_directSampler hkpos hktop (interiorInputToClosed x)] with ω hω
  exact hω.trans (directSampler_eq_interiorSampler hkpos hktop x ω)

theorem boundarySampler_map_maximumEntropyLaw (hkpos : 1 ≤ k) (hktop : k < n)
    (x : hypersimplex (Fin n) k) :
    (seedMeasure n).map (boundarySampler hkpos hktop x) =
      (lawMeasure (maximumEntropyLaw x)).map
        (Subtype.val : RankSubset (Fin n) k → Finset (Fin n)) :=
  (Measure.map_congr (boundarySampler_ae_eq_directSampler hkpos hktop x)).trans
    (directSampler_map_maximumEntropyLaw x)

/-- Both deterministic ranks are included in the direct-sampling version statement. -/
theorem exactSampler_ae_eq_directSampler (hk : k ≤ n) (x : hypersimplex (Fin n) k) :
    exactSampler n k x =ᵐ[seedMeasure n] directSampler x := by
  by_cases hk0 : k = 0
  · subst k
    apply Filter.Eventually.of_forall
    intro ω
    rw [exactSampler_zero]
    exact (Finset.card_eq_zero.mp (directSampler_card x ω)).symm
  by_cases hkn : k = n
  · subst k
    apply Filter.Eventually.of_forall
    intro ω
    rw [exactSampler_full]
    exact (Finset.eq_univ_of_card _ (by simpa using directSampler_card x ω)).symm
  have hkpos : 1 ≤ k := by omega
  have hktop : k < n := by omega
  filter_upwards [boundarySampler_ae_eq_directSampler hkpos hktop x] with ω hω
  rw [exactSampler_nondegenerate hkpos hktop]
  exact hω

theorem exactSampler_ae_eq_interiorSampler (hkpos : 1 ≤ k) (hktop : k < n)
    (x : interiorHypersimplex (Fin n) k) :
    exactSampler n k (interiorInputToClosed x) =ᵐ[seedMeasure n] interiorSampler k x := by
  filter_upwards [exactSampler_ae_eq_directSampler hktop.le (interiorInputToClosed x)] with ω hω
  exact hω.trans (directSampler_eq_interiorSampler hkpos hktop x ω)

end
end CoefficientOne.Sampling
