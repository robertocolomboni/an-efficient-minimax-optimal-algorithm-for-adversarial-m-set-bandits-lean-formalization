import MsetsPaper.Upper.ESPBernoulli
import Mathlib.Probability.Distributions.Bernoulli
import Mathlib.Probability.Independence.Basic
import Mathlib.Probability.ConditionalProbability

/-! # Independent Bernoulli product and literal conditioning on cardinality

This supplements the finite-mass formulas with an actual product measure,
proved coordinate independence, a positive rank-event probability and the
actual conditional-measure atom probabilities. No Chen theorem is assumed. -/

namespace MsetsPaper.Upper

open MeasureTheory ProbabilityTheory Set
open scoped BigOperators ENNReal

noncomputable section
variable {d m : ℕ}

def oddsProbability (theta : Fin d → ℝ) (i : Fin d) : unitInterval :=
  ⟨Real.exp (theta i) / (1 + Real.exp (theta i)),
    by constructor
       · positivity
       · exact (div_le_one (by positivity)).mpr (by linarith)⟩

def oddsProductMeasure (theta : Fin d → ℝ) : Measure (Fin d → Bool) :=
  Measure.pi fun i => bernoulliMeasure true false (oddsProbability theta i)

instance oddsProductMeasure_isProbability (theta : Fin d → ℝ) :
    IsProbabilityMeasure (oddsProductMeasure theta) := by
  unfold oddsProductMeasure
  infer_instance

theorem oddsProductMeasure_independent (theta : Fin d → ℝ) :
    iIndepFun (fun i (b : Fin d → Bool) => b i) (oddsProductMeasure theta) :=
  iIndepFun_pi (X := fun _ => id) (fun _ => aemeasurable_id)

theorem oddsProductMeasure_coordinate (theta : Fin d → ℝ) (i : Fin d) :
    (oddsProductMeasure theta).map (fun b => b i) =
      bernoulliMeasure true false (oddsProbability theta i) :=
  (measurePreserving_eval (fun j => bernoulliMeasure true false (oddsProbability theta j)) i).map_eq

def selectedBits (S : Finset (Fin d)) : Fin d → Bool := fun i => decide (i ∈ S)
def bitsSubset (b : Fin d → Bool) : Finset (Fin d) := Finset.univ.filter fun i => b i = true

theorem bitsSubset_selectedBits (S : Finset (Fin d)) : bitsSubset (selectedBits S) = S := by
  ext i
  simp [bitsSubset, selectedBits]

theorem selectedBits_bitsSubset (b : Fin d → Bool) : selectedBits (bitsSubset b) = b := by
  funext i
  cases h : b i <;> simp [selectedBits, bitsSubset, h]

theorem selectedBits_injective : Function.Injective (selectedBits (d := d)) := by
  intro S T h
  simpa only [bitsSubset_selectedBits] using congrArg bitsSubset h

theorem oddsCoordinate_singleton (theta : Fin d → ℝ) (i : Fin d) (b : Bool) :
    (bernoulliMeasure true false (oddsProbability theta i)).real {b} =
      if b then Real.exp (theta i) / (1 + Real.exp (theta i))
      else 1 / (1 + Real.exp (theta i)) := by
  rw [bernoulliMeasure_real_apply _ (measurableSet_singleton b)]
  cases b <;> simp [oddsProbability]
  have h : (1 + Real.exp (theta i)) ≠ 0 := by positivity
  field_simp
  <;> ring

theorem oddsProductMeasure_subset_probability (theta : Fin d → ℝ) (S : Finset (Fin d)) :
    (oddsProductMeasure theta).real {selectedBits S} =
      bernoulliSubsetMass (fun i => Real.exp (theta i)) S := by
  rw [oddsProductMeasure, measureReal_def, Measure.pi_singleton, ENNReal.toReal_prod]
  change (∏ i, (bernoulliMeasure true false (oddsProbability theta i)).real {selectedBits S i}) = _
  simp [oddsCoordinate_singleton, selectedBits, bernoulliSubsetMass]

def rankEvent (d m : ℕ) : Set (Fin d → Bool) := {b | (bitsSubset b).card = m}

theorem rankEvent_eq_union (d m : ℕ) :
    rankEvent d m = ⋃ a : Action d m, {selectedBits a.val} := by
  ext b
  simp only [rankEvent, Set.mem_setOf_eq, Set.mem_iUnion, Set.mem_singleton_iff]
  constructor
  · intro hb
    exact ⟨⟨bitsSubset b, hb⟩, (selectedBits_bitsSubset b).symm⟩
  · rintro ⟨a, rfl⟩
    rw [bitsSubset_selectedBits]
    exact a.property

theorem oddsProductMeasure_rank_probability (theta : Fin d → ℝ) (m : ℕ) :
    (oddsProductMeasure theta).real (rankEvent d m) =
      ∑ a : Action d m, bernoulliSubsetMass (fun i => Real.exp (theta i)) a.val := by
  rw [rankEvent_eq_union, measureReal_iUnion_fintype]
  · simp only [oddsProductMeasure_subset_probability]
  · intro a b hab
    exact Set.disjoint_singleton.mpr fun h => hab (Subtype.ext (selectedBits_injective h))
  · intro a
    exact measurableSet_singleton _

/-- The literal conditional atom probability of the independent Bernoulli
product, with the conditioning event expressed as exact selected cardinality. -/
theorem conditioned_oddsProduct_probability (theta : Fin d → ℝ) (a : Action d m) :
    (oddsProductMeasure theta).real {selectedBits a.val} /
        (oddsProductMeasure theta).real (rankEvent d m) = weightedLaw theta a := by
  rw [oddsProductMeasure_subset_probability, oddsProductMeasure_rank_probability]
  exact conditionalBernoulli_eq_weightedLaw theta a

theorem oddsProductMeasure_rank_pos (theta : Fin d → ℝ) (a : Action d m) :
    0 < (oddsProductMeasure theta).real (rankEvent d m) := by
  rw [oddsProductMeasure_rank_probability]
  have hp : 0 < bernoulliSubsetMass (fun i => Real.exp (theta i)) a.val := by
    rw [bernoulliSubsetMass_factor]
    positivity
  exact hp.trans_le (Finset.single_le_sum (fun b _ =>
    bernoulliSubsetMass_nonneg _ (fun i => Real.exp_pos (theta i)) b.val) (Finset.mem_univ a))

theorem conditioned_oddsProduct_isProbability (theta : Fin d → ℝ) (hmd : m ≤ d) :
    IsProbabilityMeasure (ProbabilityTheory.cond (oddsProductMeasure theta) (rankEvent d m)) := by
  obtain ⟨a⟩ := MsetsLower.nonempty_MSetAction hmd
  apply cond_isProbabilityMeasure
  intro hz
  have hp := oddsProductMeasure_rank_pos theta a
  simp [measureReal_def, hz] at hp

/-- Actual conditional-measure probability, not only normalized formal weights. -/
theorem conditioned_oddsProduct_atom (theta : Fin d → ℝ) (a : Action d m) :
    (ProbabilityTheory.cond (oddsProductMeasure theta) (rankEvent d m)).real
        {selectedBits a.val} = weightedLaw theta a := by
  have hmem : selectedBits a.val ∈ rankEvent d m := by
    simp [rankEvent, bitsSubset_selectedBits, a.property]
  rw [measureReal_def, cond_apply' (measurableSet_singleton _) (oddsProductMeasure theta),
    Set.inter_singleton_of_mem hmem, ENNReal.toReal_mul, ENNReal.toReal_inv]
  simpa [measureReal_def, div_eq_mul_inv, mul_comm] using conditioned_oddsProduct_probability theta a

end
end MsetsPaper.Upper
