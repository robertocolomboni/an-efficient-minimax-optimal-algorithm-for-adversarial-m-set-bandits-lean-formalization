import MsetsPaper.Upper.ESPAlgorithms
import Mathlib.Probability.Independence.Basic
import Mathlib.MeasureTheory.Constructions.UnitInterval

/-!
# Exact sequential conditional-weight sampler: algebra and support

The finite residual-law arguments are ported from the local spectral companion,
then checked afresh by Lean 4.32.2. No binary artifacts or imports cross toolchains.
The efficient table-backed implementation is treated separately.
-/

noncomputable section
open scoped BigOperators unitInterval ENNReal
open MeasureTheory ProbabilityTheory Set
namespace MsetsPaper.Upper.ESPSampling
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- The product-weight conditional threshold in a nonterminal state. -/
def sequentialThreshold (w : ι → ℝ) (R : Finset ι) (r : ℕ) (i : ι) : ℝ :=
  w i * esp w (R.erase i) (r - 1) / esp w R r

/-- The deterministic recursion underlying the common-seed sampler. -/
def sequentialList (w u : ι → ℝ) : List ι → ℕ → Finset ι
  | [], _ => ∅
  | i :: tail, r =>
    if r = 0 then ∅
    else if r = (i :: tail).length then (i :: tail).toFinset
    else if u i ≤ sequentialThreshold w (i :: tail).toFinset r i then
      insert i (sequentialList w u tail (r - 1))
    else sequentialList w u tail r

@[simp] theorem sequentialList_nil (w u : ι → ℝ) (r : ℕ) :
    sequentialList w u [] r = ∅ := rfl

@[simp] theorem sequentialList_zero (w u : ι → ℝ) (order : List ι) :
    sequentialList w u order 0 = ∅ := by
  cases order <;> simp [sequentialList]

theorem sequentialList_full (w u : ι → ℝ) (order : List ι) :
    sequentialList w u order order.length = order.toFinset := by
  cases order <;> simp [sequentialList]

theorem sequentialList_subset (w u : ι → ℝ) (order : List ι) (r : ℕ) :
    sequentialList w u order r ⊆ order.toFinset := by
  induction order generalizing r with
  | nil => simp
  | cons i tail ih =>
    simp only [sequentialList]
    split_ifs with hzero hfull htake
    · exact Finset.empty_subset _
    · exact Finset.Subset.rfl
    · simpa only [List.toFinset_cons] using Finset.insert_subset_insert i (ih (r - 1))
    · exact (ih r).trans (by simp only [List.toFinset_cons]; exact Finset.subset_insert _ _)

/-- Exact cardinality is pointwise; it does not discard exceptional seeds. -/
theorem sequentialList_card (w u : ι → ℝ) (order : List ι)
    (hn : order.Nodup) (r : ℕ) (hr : r ≤ order.length) :
    (sequentialList w u order r).card = r := by
  induction order generalizing r with
  | nil =>
    have : r = 0 := by simpa using hr
    subst r
    simp
  | cons i tail ih =>
    obtain ⟨hi, ht⟩ := List.nodup_cons.mp hn
    simp only [sequentialList]
    split_ifs with hzero hfull htake
    · subst r; simp
    · simpa only [List.toFinset_card_of_nodup hn] using hfull.symm
    · have hnot : i ∉ sequentialList w u tail (r - 1) := by
        intro h
        exact hi (List.mem_toFinset.mp (sequentialList_subset w u tail (r - 1) h))
      rw [Finset.card_insert_of_notMem hnot, ih ht (r - 1) (by simp only [List.length_cons] at hr; omega)]
      omega
    · exact ih ht r (by simp only [List.length_cons] at hr hfull; omega)

@[fun_prop] theorem measurable_esp (R : Finset ι) (r : ℕ) :
    Measurable (fun w : ι → ℝ => esp w R r) := by
  unfold esp
  fun_prop

@[fun_prop] theorem measurable_sequentialThreshold (R : Finset ι) (r : ℕ) (i : ι) :
    Measurable (fun w : ι → ℝ => sequentialThreshold w R r i) := by
  unfold sequentialThreshold
  fun_prop

/-- Joint measurability in the weights and all uniform coordinates. -/
theorem measurable_sequentialList (order : List ι) (r : ℕ) :
    Measurable (fun wu : (ι → ℝ) × (ι → ℝ) => sequentialList wu.1 wu.2 order r) := by
  induction order generalizing r with
  | nil => exact measurable_const
  | cons i tail ih =>
    simp only [sequentialList]
    by_cases hzero : r = 0
    · simp only [hzero, ↓reduceIte]; exact measurable_const
    · simp only [hzero, ↓reduceIte]
      by_cases hfull : r = (i :: tail).length
      · simp only [hfull, ↓reduceIte]; exact measurable_const
      · simp only [hfull, ↓reduceIte]
        apply Measurable.ite
        · exact measurableSet_le ((measurable_pi_apply i).comp measurable_snd)
            ((measurable_sequentialThreshold _ _ _).comp measurable_fst)
        · exact (measurable_of_finite (fun S : Finset ι => insert i S)).comp (ih (r - 1))
        · exact ih r

theorem sequentialThreshold_pos (w : ι → ℝ) (hw : ∀ i, 0 < w i)
    (R : Finset ι) (r : ℕ) (hr : 0 < r) (hR : r ≤ R.card)
    (i : ι) (hi : i ∈ R) : 0 < sequentialThreshold w R r i := by
  apply div_pos
  · apply mul_pos (hw i)
    apply esp_pos w hw
    rw [Finset.card_erase_of_mem hi]
    omega
  · exact esp_pos w hw R r hR

theorem sequentialThreshold_lt_one (w : ι → ℝ) (hw : ∀ i, 0 < w i)
    (R : Finset ι) (r : ℕ) (hr : 0 < r) (hR : r < R.card)
    (i : ι) (hi : i ∈ R) : sequentialThreshold w R r i < 1 := by
  apply (div_lt_one (esp_pos w hw R r hR.le)).mpr
  have hp := esp_pos w hw (R.erase i) r (by
    rw [Finset.card_erase_of_mem hi]; omega)
  rw [esp_delete w R i hi r hr]
  linarith

theorem one_sub_sequentialThreshold (w : ι → ℝ) (hw : ∀ i, 0 < w i)
    (R : Finset ι) (r : ℕ) (hr : 0 < r) (hR : r ≤ R.card)
    (i : ι) (hi : i ∈ R) :
    1 - sequentialThreshold w R r i =
      esp w (R.erase i) r / esp w R r := by
  unfold sequentialThreshold
  have hz := (esp_pos w hw R r hR).ne'
  apply (eq_div_iff hz).mpr
  field_simp
  linarith [esp_delete w R i hi r hr]

/-- Residual product-weight mass, zero outside the cardinality support. -/
def restrictedMass (w : ι → ℝ) (R : Finset ι) (r : ℕ) (S : Finset ι) : ℝ :=
  if S ∈ R.powersetCard r then (∏ i ∈ S, w i) / esp w R r else 0

@[simp] theorem restrictedMass_zero (w : ι → ℝ) (R S : Finset ι) :
    restrictedMass w R 0 S = if S = ∅ then 1 else 0 := by
  by_cases h : S = ∅
  · subst S; simp [restrictedMass, Finset.powersetCard_zero]
  · simp [restrictedMass, Finset.powersetCard_zero, h]

theorem restrictedMass_full (w : ι → ℝ) (hw : ∀ i, 0 < w i) (R S : Finset ι) :
    restrictedMass w R R.card S = if S = R then 1 else 0 := by
  have hpos : 0 < (∏ i ∈ R, w i) := Finset.prod_pos fun i _ => hw i
  simp only [restrictedMass, Finset.powersetCard_self, Finset.mem_singleton]
  split_ifs with h
  · subst S
    simp [esp, Finset.powersetCard_self, ne_of_gt hpos]
  · rfl

theorem residual_selected_support (R S : Finset ι) (i : ι) (hi : i ∉ R)
    (r : ℕ) (hS : S ∈ (insert i R).powersetCard r) (hiS : i ∈ S) :
    S.erase i ∈ R.powersetCard (r - 1) := by
  obtain ⟨hsub, hcard⟩ := Finset.mem_powersetCard.mp hS
  apply Finset.mem_powersetCard.mpr
  refine ⟨?_, by rw [Finset.card_erase_of_mem hiS, hcard]⟩
  intro j hj
  exact (Finset.mem_insert.mp (hsub (Finset.mem_of_mem_erase hj))).resolve_left
    (Finset.ne_of_mem_erase hj)

theorem residual_rejected_support (R S : Finset ι) (i : ι) (r : ℕ)
    (hS : S ∈ (insert i R).powersetCard r) (hiS : i ∉ S) :
    S ∈ R.powersetCard r := by
  obtain ⟨hsub, hcard⟩ := Finset.mem_powersetCard.mp hS
  apply Finset.mem_powersetCard.mpr
  refine ⟨?_, hcard⟩
  intro j hj
  exact (Finset.mem_insert.mp (hsub hj)).resolve_left (fun h => hiS (h ▸ hj))

theorem restrictedMass_selected (w : ι → ℝ) (hw : ∀ i, 0 < w i)
    (R S : Finset ι) (i : ι) (hi : i ∉ R) (r : ℕ)
    (hr : 0 < r) (hrR : r ≤ R.card)
    (hS : S ∈ (insert i R).powersetCard r) (hiS : i ∈ S) :
    restrictedMass w (insert i R) r S =
      sequentialThreshold w (insert i R) r i * restrictedMass w R (r - 1) (S.erase i) := by
  have htail := residual_selected_support R S i hi r hS hiS
  rw [restrictedMass, if_pos hS, restrictedMass, if_pos htail,
    sequentialThreshold, Finset.erase_insert hi]
  have hweight : (∏ i ∈ S, w i) = w i * (∏ j ∈ S.erase i, w j) := by
    simpa only [Finset.insert_erase hiS] using
      (Finset.prod_insert (f := w) (Finset.notMem_erase i S))
  rw [hweight]
  have hp := (esp_pos w hw R (r - 1) (by omega)).ne'
  have hq := (esp_pos w hw (insert i R) r (by
    rw [Finset.card_insert_of_notMem hi]; omega)).ne'
  field_simp

theorem restrictedMass_rejected (w : ι → ℝ) (hw : ∀ i, 0 < w i)
    (R S : Finset ι) (i : ι) (hi : i ∉ R) (r : ℕ)
    (hr : 0 < r) (hrR : r ≤ R.card)
    (hS : S ∈ (insert i R).powersetCard r) (hiS : i ∉ S) :
    restrictedMass w (insert i R) r S =
      (1 - sequentialThreshold w (insert i R) r i) * restrictedMass w R r S := by
  have htail := residual_rejected_support R S i r hS hiS
  rw [one_sub_sequentialThreshold w hw (insert i R) r hr (by
      rw [Finset.card_insert_of_notMem hi]; omega) i (Finset.mem_insert_self _ _),
    Finset.erase_insert hi, restrictedMass, if_pos hS, restrictedMass, if_pos htail]
  have hp := (esp_pos w hw R r hrR).ne'
  have hq := (esp_pos w hw (insert i R) r (by
    rw [Finset.card_insert_of_notMem hi]; omega)).ne'
  field_simp


end MsetsPaper.Upper.ESPSampling

