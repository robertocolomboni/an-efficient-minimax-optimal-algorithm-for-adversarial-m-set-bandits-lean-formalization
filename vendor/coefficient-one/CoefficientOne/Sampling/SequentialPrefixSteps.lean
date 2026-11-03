import CoefficientOne.Sampling.FirstDisagreement

/-! # Resuming a revealed prefix for a prescribed number of further steps -/

namespace CoefficientOne.Sampling
noncomputable section

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

theorem prefixSelected_add (w u : ι → ℝ) (order : List ι) (hn : order.Nodup)
    (r ℓ s : ℕ) :
    prefixSelected w u order r (ℓ + s) = prefixSelected w u order r ℓ ∪
      prefixSelected w u (order.drop ℓ) (prefixQuota w u order r ℓ) s := by
  induction order generalizing r ℓ with
  | nil => simp [prefixSelected]
  | cons i tail ih =>
    obtain ⟨hi, ht⟩ := List.nodup_cons.mp hn
    cases ℓ with
    | zero => simp [prefixQuota]
    | succ ℓ =>
      by_cases htake : SelectsHead w u i tail r
      · rw [prefixQuota_step_selected w u i tail hi r ℓ htake]
        simp only [Nat.succ_add, prefixSelected, if_pos htake, List.drop_succ_cons]
        rw [ih ht (r - 1) ℓ]
        ext j
        simp only [Finset.mem_insert, Finset.mem_union]
        tauto
      · rw [prefixQuota_step_rejected w u i tail r ℓ htake]
        simp only [Nat.succ_add, prefixSelected, if_neg htake, List.drop_succ_cons]
        exact ih ht r ℓ

theorem prefixSelected_disjoint_drop (w u : ι → ℝ) (order : List ι) (hn : order.Nodup)
    (r ℓ : ℕ) : Disjoint (prefixSelected w u order r ℓ) (order.drop ℓ).toFinset := by
  rw [prefixSelected_eq_output_inter w u order hn r ℓ]
  exact (List.disjoint_toFinset_iff_disjoint.mpr (List.disjoint_take_drop hn le_rfl)).mono_left
    (Finset.inter_subset_right)

theorem prefixSelected_card_le_quota (w u : ι → ℝ) (order : List ι) (hn : order.Nodup)
    (r ℓ : ℕ) (hr : r ≤ order.length) : (prefixSelected w u order r ℓ).card ≤ r := by
  have hs : prefixSelected w u order r ℓ ⊆ sequentialList w u order r := by
    rw [prefixSelected_eq_output_inter w u order hn r ℓ]
    exact Finset.inter_subset_left
  calc
    _ ≤ (sequentialList w u order r).card := Finset.card_le_card hs
    _ = r := sequentialList_card w u order hn r hr

theorem prefixSelected_succ_of_drop (w u : ι → ℝ) (order : List ι) (hn : order.Nodup)
    (r ℓ : ℕ) (i : ι) (tail : List ι) (hd : order.drop ℓ = i :: tail) :
    prefixSelected w u order r (ℓ + 1) =
      if SelectsHead w u i tail (prefixQuota w u order r ℓ)
      then insert i (prefixSelected w u order r ℓ) else prefixSelected w u order r ℓ := by
  rw [prefixSelected_add w u order hn r ℓ 1, hd]
  simp only [prefixSelected, prefixSelected_zero]
  split_ifs
  · simp
  · simp

theorem prefixQuota_succ_of_drop (w u : ι → ℝ) (order : List ι) (hn : order.Nodup)
    (r ℓ : ℕ) (i : ι) (tail : List ι) (hd : order.drop ℓ = i :: tail) :
    prefixQuota w u order r (ℓ + 1) =
      if SelectsHead w u i tail (prefixQuota w u order r ℓ)
      then prefixQuota w u order r ℓ - 1 else prefixQuota w u order r ℓ := by
  have hnot : i ∉ prefixSelected w u order r ℓ := by
    intro hmem
    have hdis := prefixSelected_disjoint_drop w u order hn r ℓ
    exact Finset.disjoint_left.mp hdis hmem (by simp [hd])
  rw [prefixQuota, prefixSelected_succ_of_drop w u order hn r ℓ i tail hd]
  split_ifs
  · rw [Finset.card_insert_of_notMem hnot]
    simp only [prefixQuota]
    omega
  · rfl

end
end CoefficientOne.Sampling
