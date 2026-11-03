import CoefficientOne.Sampling.RestrictedElementary

noncomputable section

open EffectiveResistance

namespace CoefficientOne.Sampling

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

@[simp] theorem restrictedMass_zero (w : ι → ℝ) (R S : Finset ι) :
    restrictedMass w R 0 S = if S = ∅ then 1 else 0 := by
  by_cases h : S = ∅
  · subst S; simp [restrictedMass, Finset.powersetCard_zero, subsetWeight]
  · simp [restrictedMass, Finset.powersetCard_zero, h]

theorem restrictedMass_full (w : ι → ℝ) (hw : ∀ i, 0 < w i) (R S : Finset ι) :
    restrictedMass w R R.card S = if S = R then 1 else 0 := by
  have hpos : 0 < subsetWeight w R := Finset.prod_pos fun i _ => hw i
  simp only [restrictedMass, Finset.powersetCard_self, Finset.mem_singleton]
  split_ifs with h
  · subst S
    simp [restrictedElementary, Finset.powersetCard_self, ne_of_gt hpos]
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
  have hweight : subsetWeight w S = w i * subsetWeight w (S.erase i) := by
    simpa only [subsetWeight, Finset.insert_erase hiS] using
      (Finset.prod_insert (f := w) (Finset.notMem_erase i S))
  rw [hweight]
  have hp := (restrictedElementary_pos w hw R (r - 1) (by omega)).ne'
  have hq := (restrictedElementary_pos w hw (insert i R) r (by
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
  have hp := (restrictedElementary_pos w hw R r hrR).ne'
  have hq := (restrictedElementary_pos w hw (insert i R) r (by
    rw [Finset.card_insert_of_notMem hi]; omega)).ne'
  field_simp

end CoefficientOne.Sampling
