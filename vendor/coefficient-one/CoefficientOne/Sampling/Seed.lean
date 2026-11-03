import Mathlib

/-!
# The common random seed

The permutation and all uniforms are sampled once, independently of the input.
Uniforms are indexed by the original coordinates, rather than reveal times.
-/

noncomputable section

open MeasureTheory Set
open scoped ENNReal unitInterval

namespace CoefficientOne.Sampling

abbrev Seed (n : ℕ) := Equiv.Perm (Fin n) × (Fin n → unitInterval)

instance seedOrder_measurableSpace (n : ℕ) : MeasurableSpace (Equiv.Perm (Fin n)) := ⊤

instance seedOrder_discreteMeasurableSpace (n : ℕ) :
    DiscreteMeasurableSpace (Equiv.Perm (Fin n)) := ⟨fun _ => trivial⟩

def uniformMeasure (α : Type*) [Fintype α] [Nonempty α] [MeasurableSpace α] :
    Measure α := Measure.uniformOfFinset (Finset.univ : Finset α)

instance uniformMeasure_isProbabilityMeasure (α : Type*) [Fintype α] [Nonempty α]
    [MeasurableSpace α] : IsProbabilityMeasure (uniformMeasure α) := by
  classical
  constructor
  simp [uniformMeasure, Measure.uniformOfFinset]
  exact ENNReal.mul_inv_cancel (by simp) (by simp)

def uniformCube (ι : Type*) [Fintype ι] : Measure (ι → unitInterval) :=
  Measure.pi (fun _ => volume)

instance uniformCube_isProbabilityMeasure (ι : Type*) [Fintype ι] :
    IsProbabilityMeasure (uniformCube ι) := by
  unfold uniformCube
  infer_instance

def seedMeasure (n : ℕ) : Measure (Seed n) :=
  (uniformMeasure (Equiv.Perm (Fin n))).prod (uniformCube (Fin n))

instance seedMeasure_isProbabilityMeasure (n : ℕ) :
    IsProbabilityMeasure (seedMeasure n) := by
  unfold seedMeasure
  infer_instance

@[fun_prop]
theorem measurable_seedOrder (n : ℕ) :
    Measurable (fun ω : Seed n => ω.1) := measurable_fst

@[fun_prop]
theorem measurable_seedUniform (n : ℕ) (i : Fin n) :
    Measurable (fun ω : Seed n => ω.2 i) :=
  (measurable_pi_apply i).comp measurable_snd

@[fun_prop]
theorem measurable_revealIndex (n : ℕ) (j : Fin n) :
    Measurable (fun ω : Seed n => ω.1 j) := by
  exact (measurable_of_finite (fun π : Equiv.Perm (Fin n) => π j)).comp measurable_fst

@[fun_prop]
theorem measurable_revealUniform (n : ℕ) (j : Fin n) :
    Measurable (fun ω : Seed n => ω.2 (ω.1 j)) := by
  exact measurable_from_prod_countable_right (fun π => measurable_pi_apply (π j))

theorem measurePreserving_seedUniform (n : ℕ) (i : Fin n) :
    MeasurePreserving (fun ω : Seed n => ω.2 i) (seedMeasure n) volume := by
  exact (measurePreserving_eval (fun _ : Fin n => (volume : Measure unitInterval)) i).comp
    measurePreserving_snd

theorem seedMeasure_uniform_eq_zero (n : ℕ) (i : Fin n) (a : unitInterval) :
    seedMeasure n {ω | ω.2 i = a} = 0 := by
  have h := (measurePreserving_seedUniform n i).measure_preimage
    (measurableSet_singleton a).nullMeasurableSet
  simpa only [Set.preimage, Set.mem_singleton_iff, measure_singleton] using h

theorem seedUniform_ne_ae (n : ℕ) (i : Fin n) (a : unitInterval) :
    ∀ᵐ ω ∂seedMeasure n, ω.2 i ≠ a := by
  rw [ae_iff]
  simpa only [not_not] using seedMeasure_uniform_eq_zero n i a

theorem seedUniform_real_ne_ae (n : ℕ) (i : Fin n) (a : ℝ) :
    ∀ᵐ ω ∂seedMeasure n, (ω.2 i : ℝ) ≠ a := by
  by_cases ha : a ∈ Set.Icc (0 : ℝ) 1
  · filter_upwards [seedUniform_ne_ae n i ⟨a, ha⟩] with ω hω
    exact fun h => hω (Subtype.ext h)
  · exact Filter.Eventually.of_forall fun ω h => ha (h ▸ (ω.2 i).property)

theorem seedUniform_finite_thresholds_ne_ae (n : ℕ) {κ : Type*} [Fintype κ]
    (threshold : κ → Fin n → ℝ) :
    ∀ᵐ ω ∂seedMeasure n, ∀ a i, (ω.2 i : ℝ) ≠ threshold a i := by
  simp only [ae_all_iff]
  intro a i
  exact seedUniform_real_ne_ae n i (threshold a i)

end CoefficientOne.Sampling
