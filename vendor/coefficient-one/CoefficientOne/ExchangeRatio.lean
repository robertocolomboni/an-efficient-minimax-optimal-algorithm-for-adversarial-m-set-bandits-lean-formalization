import EffectiveResistance.FiniteLaw
import Mathlib.Tactic

/-!
# The exact exchange ratio of the finite external-field law

The common background weight and the elementary normalizer cancel.  The
background may be empty, so the statement includes rank one.
-/

open scoped BigOperators
open EffectiveResistance

namespace CoefficientOne

noncomputable section

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- Adjoin a missing element, retaining the actual fixed-rank sample space. -/
def exchangeInsert (m : ℕ) (T : Finset ι) (hT : T.card + 1 = m)
    (i : ι) (hi : i ∉ T) : RankSubset ι m :=
  ⟨insert i T, by simpa only [Finset.card_insert_of_notMem hi] using hT⟩

theorem exchangeInsert_probability
    (w : ι → ℝ) (m : ℕ) (T : Finset ι) (hT : T.card + 1 = m)
    (i : ι) (hi : i ∉ T) :
    subsetProbability w m (exchangeInsert m T hT i hi) =
      w i * subsetWeight w T / elementarySum w m := by
  simp [subsetProbability, subsetWeight, exchangeInsert, Finset.prod_insert hi]

/-- Cancelling the two positive common factors gives the exchange ratio. -/
theorem exchange_probability_ratio
    (w : ι → ℝ) (hw : ∀ i, 0 < w i) (m : ℕ)
    (T : Finset ι) (hT : T.card + 1 = m)
    (i j : ι) (hi : i ∉ T) (hj : j ∉ T) :
    subsetProbability w m (exchangeInsert m T hT i hi) /
      subsetProbability w m (exchangeInsert m T hT j hj) = w i / w j := by
  have hm : m ≤ Fintype.card ι := by
    rw [← hT, ← Finset.card_insert_of_notMem hi]
    exact Finset.card_le_univ _
  have hZ := (elementarySum_pos w hw hm).ne'
  have hW : subsetWeight w T ≠ 0 := ne_of_gt (Finset.prod_pos (fun i _ => hw i))
  rw [exchangeInsert_probability, exchangeInsert_probability]
  field_simp [hZ, hW, (hw j).ne']

/-- Appendix E.3, with the paper's rank and background-cardinality convention.
No restriction m≥2 is imposed, and i=j is harmless as well. -/
theorem externalField_exchange_probability_ratio
    (w : ι → ℝ) (hw : ∀ i, 0 < w i) (m : ℕ) (hm : 1 ≤ m)
    (T : Finset ι) (hT : T.card = m - 1)
    (i j : ι) (hi : i ∉ T) (hj : j ∉ T) :
    subsetProbability w m (exchangeInsert m T (by omega) i hi) /
      subsetProbability w m (exchangeInsert m T (by omega) j hj) = w i / w j :=
  exchange_probability_ratio w hw m T (by omega) i j hi hj

/-- The empty-background boundary case is the ratio of singleton masses. -/
theorem externalField_singleton_probability_ratio
    (w : ι → ℝ) (hw : ∀ i, 0 < w i) (i j : ι) :
    subsetProbability w 1 ⟨{i}, by simp⟩ /
      subsetProbability w 1 ⟨{j}, by simp⟩ = w i / w j := by
  simpa [exchangeInsert] using
    exchange_probability_ratio w hw 1 ∅ (by simp) i j (by simp) (by simp)

end

end CoefficientOne
