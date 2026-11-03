import CoefficientOne.Sampling.QuotaMonotonicity

/-!
# Adjacent-quota coupling on the actual sequential recursion

Equal decisions preserve the quota difference. If the decisions differ, only
the larger-quota run selects, so both future recursions have the same quota and
coincide. The proof is pointwise for the shared seed, including forced branches.
-/

open scoped BigOperators
open EffectiveResistance

namespace CoefficientOne.Sampling
noncomputable section

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- The smaller adjacent quota produces a subset of the larger one's output,
under the same weights, order, and uniforms. This includes arbitrary real
uniform-coordinate arguments; the sampling seed is a specialization. -/
theorem sequentialList_adjacent_subset (w : ι → ℝ) (hw : ∀ i, 0 < w i)
    (u : ι → ℝ) (order : List ι) (hn : order.Nodup) (r : ℕ)
    (hr : r + 1 ≤ order.length) :
    sequentialList w u order r ⊆ sequentialList w u order (r + 1) := by
  induction order generalizing r with
  | nil => simp at hr
  | cons i tail ih =>
    have ht := (List.nodup_cons.mp hn).2
    by_cases hz : r = 0
    · subst r
      simp
    by_cases hf : r + 1 = (i :: tail).length
    · rw [hf, sequentialList_full]
      exact sequentialList_subset w u (i :: tail) r
    have hsmall : r ≠ (i :: tail).length := by omega
    have hbig : r + 1 ≠ 0 := by omega
    have hlen : (i :: tail).toFinset.card = (i :: tail).length := List.toFinset_card_of_nodup hn
    have hi : i ∈ (i :: tail).toFinset := by simp
    have hmono : sequentialThreshold w (i :: tail).toFinset r i ≤
        sequentialThreshold w (i :: tail).toFinset (r + 1) i := by
      have hm := quotaThreshold_le_succ w hw (i :: tail).toFinset r (by omega) i hi
      rw [quotaThreshold_eq_sequentialThreshold w hw _ r (by omega) (by omega) i hi,
        quotaThreshold_eq_sequentialThreshold w hw _ (r + 1) (by omega) (by omega) i hi] at hm
      exact hm
    simp only [sequentialList, hz, hf, hsmall, hbig, ↓reduceIte]
    by_cases hs : u i ≤ sequentialThreshold w (i :: tail).toFinset r i
    · have hb := hs.trans hmono
      simp only [hs, hb, ↓reduceIte]
      have hsub := ih ht (r - 1) (by simp only [List.length_cons] at hr; omega)
      have heq : r - 1 + 1 = r := by omega
      simpa only [heq, Nat.add_sub_cancel] using Finset.insert_subset_insert i hsub
    · simp only [hs, ↓reduceIte]
      by_cases hb : u i ≤ sequentialThreshold w (i :: tail).toFinset (r + 1) i
      · simp only [hb, ↓reduceIte, Nat.add_sub_cancel]
        exact Finset.subset_insert _ _
      · simp only [hb, ↓reduceIte]
        exact ih ht r (by simp only [List.length_cons] at hr hf; omega)

/-- Monotonicity for any pair of legal quotas, obtained by adjacent steps. -/
theorem sequentialList_quota_subset (w : ι → ℝ) (hw : ∀ i, 0 < w i)
    (u : ι → ℝ) (order : List ι) (hn : order.Nodup) (r s : ℕ)
    (hrs : r ≤ s) (hs : s ≤ order.length) :
    sequentialList w u order r ⊆ sequentialList w u order s := by
  induction s generalizing r with
  | zero =>
    have hr : r = 0 := by omega
    subst r
    exact Finset.Subset.rfl
  | succ s ih =>
    by_cases heq : r = s + 1
    · subst r
      exact Finset.Subset.rfl
    · exact (ih r (by omega) (by omega)).trans
        (sequentialList_adjacent_subset w hw u order hn s hs)

theorem sequentialList_adjacent_sdiff_card (w : ι → ℝ) (hw : ∀ i, 0 < w i)
    (u : ι → ℝ) (order : List ι) (hn : order.Nodup) (r : ℕ)
    (hr : r + 1 ≤ order.length) :
    (sequentialList w u order (r + 1) \ sequentialList w u order r).card = 1 := by
  rw [Finset.card_sdiff_of_subset (sequentialList_adjacent_subset w hw u order hn r hr),
    sequentialList_card w u order hn (r + 1) hr,
    sequentialList_card w u order hn r (by omega)]
  omega

/-- Exactly one future coordinate is selected only by the larger-quota run. -/
theorem sequentialList_adjacent_unique_extra (w : ι → ℝ) (hw : ∀ i, 0 < w i)
    (u : ι → ℝ) (order : List ι) (hn : order.Nodup) (r : ℕ)
    (hr : r + 1 ≤ order.length) :
    ∃! i, i ∈ sequentialList w u order (r + 1) ∧ i ∉ sequentialList w u order r := by
  obtain ⟨i, hi⟩ := Finset.card_eq_one.mp (sequentialList_adjacent_sdiff_card w hw u order hn r hr)
  have hmem : ∀ j, (j ∈ sequentialList w u order (r + 1) ∧
      j ∉ sequentialList w u order r) ↔ j = i := by
    intro j
    rw [← Finset.mem_sdiff, hi, Finset.mem_singleton]
  exact ⟨i, (hmem i).mpr rfl, fun j hj => (hmem j).mp hj⟩

theorem insert_symmDiff_eq_of_subset {A B : Finset ι} (hAB : A ⊆ B)
    (i : ι) (hi : i ∉ B) : symmDiff (insert i A) B = insert i (B \ A) := by
  ext j
  by_cases hji : j = i
  · subst j
    simp [Finset.mem_symmDiff, hi]
  · by_cases hjA : j ∈ A
    · have hjB := hAB hjA
      simp [Finset.mem_symmDiff, hji, hjA, hjB]
    · simp [Finset.mem_symmDiff, hji, hjA]

/-- After opposite decisions at i, the selecting run has quota r and the other
has quota r+1 on the same remaining order. Their completed outputs differ in
exactly two coordinates, for every common seed. -/
theorem opposite_decision_distance_two (w : ι → ℝ) (hw : ∀ i, 0 < w i)
    (u : ι → ℝ) (order : List ι) (hn : order.Nodup) (r : ℕ)
    (hr : r + 1 ≤ order.length) (i : ι) (hi : i ∉ order) :
    outputDistance (insert i (sequentialList w u order r))
      (sequentialList w u order (r + 1)) = 2 := by
  have hin : i ∉ sequentialList w u order (r + 1) := by
    intro hm
    exact hi (List.mem_toFinset.mp (sequentialList_subset w u order (r + 1) hm))
  unfold outputDistance
  rw [insert_symmDiff_eq_of_subset (sequentialList_adjacent_subset w hw u order hn r hr) i hin,
    Finset.card_insert_of_notMem (by simp [hin]),
    sequentialList_adjacent_sdiff_card w hw u order hn r hr]
  norm_num

theorem symmDiff_union_common_of_disjoint (P A B : Finset ι)
    (hPA : Disjoint P A) (hPB : Disjoint P B) :
    symmDiff (P ∪ A) (P ∪ B) = symmDiff A B := by
  ext i
  by_cases hi : i ∈ P
  · have hA : i ∉ A := fun ha => Finset.disjoint_left.mp hPA hi ha
    have hB : i ∉ B := fun hb => Finset.disjoint_left.mp hPB hi hb
    simp [Finset.mem_symmDiff, hi, hA, hB]
  · simp [Finset.mem_symmDiff, hi]

/-- The same statement with the common earlier selections restored. -/
theorem opposite_decision_distance_two_with_prefix (w : ι → ℝ) (hw : ∀ i, 0 < w i)
    (u : ι → ℝ) (order : List ι) (hn : order.Nodup) (r : ℕ)
    (hr : r + 1 ≤ order.length) (i : ι) (hi : i ∉ order) (P : Finset ι)
    (hP : Disjoint P (insert i order.toFinset)) :
    outputDistance (P ∪ insert i (sequentialList w u order r))
      (P ∪ sequentialList w u order (r + 1)) = 2 := by
  have hA : Disjoint P (insert i (sequentialList w u order r)) :=
    hP.mono_right (Finset.insert_subset_insert i (sequentialList_subset w u order r))
  have hB : Disjoint P (sequentialList w u order (r + 1)) :=
    hP.mono_right ((sequentialList_subset w u order (r + 1)).trans (Finset.subset_insert _ _))
  change ((symmDiff (P ∪ insert i (sequentialList w u order r))
    (P ∪ sequentialList w u order (r + 1))).card : ℝ) = 2
  rw [symmDiff_union_common_of_disjoint P _ _ hA hB]
  exact opposite_decision_distance_two w hw u order hn r hr i hi

end
end CoefficientOne.Sampling
