import CoefficientOne.Sampling.Sequential
import CoefficientOne.Sampling.FiniteLawMeasure
import CoefficientOne.ElementaryDeletion

/-!
# Conditional product weights on a remaining coordinate set

The deletion identity splits the subsets according to whether the next
coordinate is selected, as in the exactness proof of Appendix E.2.
-/

open scoped BigOperators
open EffectiveResistance

namespace CoefficientOne.Sampling

noncomputable section

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

@[simp] theorem restrictedElementary_zero (w : ι → ℝ) (R : Finset ι) :
    restrictedElementary w R 0 = 1 := by
  simp [restrictedElementary, subsetWeight, Finset.powersetCard_zero]

theorem restrictedElementary_nonneg (w : ι → ℝ) (hw : ∀ i, 0 ≤ w i)
    (R : Finset ι) (r : ℕ) : 0 ≤ restrictedElementary w R r := by
  apply Finset.sum_nonneg
  intro S _
  exact Finset.prod_nonneg fun i _ => hw i

theorem restrictedElementary_pos (w : ι → ℝ) (hw : ∀ i, 0 < w i)
    (R : Finset ι) (r : ℕ) (hr : r ≤ R.card) :
    0 < restrictedElementary w R r := by
  exact Finset.sum_pos (fun S _ => Finset.prod_pos (fun i _ => hw i))
    (Finset.powersetCard_nonempty.mpr hr)

theorem restrictedElementary_eq_zero_of_card_lt (w : ι → ℝ) (R : Finset ι)
    (r : ℕ) (hr : R.card < r) : restrictedElementary w R r = 0 := by
  simp [restrictedElementary, Finset.powersetCard_eq_empty.mpr hr]

theorem restrictedElementary_eq_multiset (w : ι → ℝ) (R : Finset ι) (r : ℕ) :
    restrictedElementary w R r = (R.val.map w).esymm r :=
  (Finset.esymm_map_val w R r).symm

theorem restrictedElementary_insert_succ (w : ι → ℝ) (R : Finset ι)
    (i : ι) (hi : i ∉ R) (r : ℕ) :
    restrictedElementary w (insert i R) (r + 1) =
      restrictedElementary w R (r + 1) + w i * restrictedElementary w R r := by
  simp only [restrictedElementary_eq_multiset, Finset.insert_val_of_notMem hi,
    Multiset.map_cons, ElementaryDeletion.multiset_esymm_cons_succ]

theorem restrictedElementary_delete (w : ι → ℝ) (R : Finset ι)
    (i : ι) (hi : i ∈ R) (r : ℕ) (hr : 0 < r) :
    restrictedElementary w R r = restrictedElementary w (R.erase i) r +
      w i * restrictedElementary w (R.erase i) (r - 1) := by
  have h := restrictedElementary_insert_succ w (R.erase i) i (Finset.notMem_erase _ _) (r - 1)
  simpa only [Finset.insert_erase hi, Nat.sub_add_cancel hr] using h

theorem sequentialThreshold_pos (w : ι → ℝ) (hw : ∀ i, 0 < w i)
    (R : Finset ι) (r : ℕ) (hr : 0 < r) (hR : r ≤ R.card)
    (i : ι) (hi : i ∈ R) : 0 < sequentialThreshold w R r i := by
  apply div_pos
  · apply mul_pos (hw i)
    apply restrictedElementary_pos w hw
    rw [Finset.card_erase_of_mem hi]
    omega
  · exact restrictedElementary_pos w hw R r hR

theorem sequentialThreshold_lt_one (w : ι → ℝ) (hw : ∀ i, 0 < w i)
    (R : Finset ι) (r : ℕ) (hr : 0 < r) (hR : r < R.card)
    (i : ι) (hi : i ∈ R) : sequentialThreshold w R r i < 1 := by
  apply (div_lt_one (restrictedElementary_pos w hw R r hR.le)).mpr
  have hp := restrictedElementary_pos w hw (R.erase i) r (by
    rw [Finset.card_erase_of_mem hi]; omega)
  rw [restrictedElementary_delete w R i hi r hr]
  linarith

theorem one_sub_sequentialThreshold (w : ι → ℝ) (hw : ∀ i, 0 < w i)
    (R : Finset ι) (r : ℕ) (hr : 0 < r) (hR : r ≤ R.card)
    (i : ι) (hi : i ∈ R) :
    1 - sequentialThreshold w R r i =
      restrictedElementary w (R.erase i) r / restrictedElementary w R r := by
  unfold sequentialThreshold
  have hz := (restrictedElementary_pos w hw R r hR).ne'
  apply (eq_div_iff hz).mpr
  field_simp
  linarith [restrictedElementary_delete w R i hi r hr]

theorem restrictedElementary_eq_elementarySum_subtype (w : ι → ℝ)
    (R : Finset ι) (r : ℕ) :
    restrictedElementary w R r = elementarySum (fun i : R => w i.val) r := by
  have hR : (Finset.univ : Finset R).map (Function.Embedding.subtype (fun i => i ∈ R)) = R := by
    ext i
    simp
  have hm := congrArg (fun S : Finset ι => S.val.map w) hR
  simp only [Finset.map_val, Multiset.map_map, Function.comp_def, Function.Embedding.coe_subtype] at hm
  rw [restrictedElementary_eq_multiset, ElementaryDeletion.elementarySum_eq_multiset, hm]

/-- The mass of an output subset in a residual state, zero off its support. -/
def restrictedMass (w : ι → ℝ) (R : Finset ι) (r : ℕ) (S : Finset ι) : ℝ :=
  if S ∈ R.powersetCard r then subsetWeight w S / restrictedElementary w R r else 0

theorem restrictedMass_nonneg (w : ι → ℝ) (hw : ∀ i, 0 < w i)
    (R : Finset ι) (r : ℕ) (hr : r ≤ R.card) (S : Finset ι) :
    0 ≤ restrictedMass w R r S := by
  unfold restrictedMass
  split_ifs
  · exact div_nonneg (Finset.prod_nonneg (fun i _ => (hw i).le))
      (restrictedElementary_pos w hw R r hr).le
  · exact le_rfl

theorem sum_restrictedMass (w : ι → ℝ) (hw : ∀ i, 0 < w i)
    (R : Finset ι) (r : ℕ) (hr : r ≤ R.card) :
    ∑ S : Finset ι, restrictedMass w R r S = 1 := by
  classical
  simp only [restrictedMass, Finset.sum_ite_mem, Finset.univ_inter]
  rw [← Finset.sum_div]
  exact div_self (restrictedElementary_pos w hw R r hr).ne'

/-- The actual normalized residual law, with no assumed sampling properties. -/
def restrictedLaw (w : ι → ℝ) (hw : ∀ i, 0 < w i)
    (R : Finset ι) (r : ℕ) (hr : r ≤ R.card) : FiniteLaw (Finset ι) :=
  ⟨restrictedMass w R r, ⟨restrictedMass_nonneg w hw R r hr,
    sum_restrictedMass w hw R r hr⟩⟩

end
end CoefficientOne.Sampling
