import CoefficientOne.Sampling.SequentialLaw
import CoefficientOne.Sampling.StoppedSeed

/-!
# Revealed histories of the concrete recursion

The selected prefix is computed by the revealed decisions. It is then proved
equal to the intersection of the final output with the revealed coordinates.
Thus both the procedural and the order/output descriptions denote the same
history, including after a quota becomes forced.
-/

noncomputable section

open EffectiveResistance MeasureTheory Set
open scoped unitInterval

namespace CoefficientOne.Sampling

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

def SelectsHead (w u : ι → ℝ) (i : ι) (tail : List ι) (r : ℕ) : Prop :=
  r ≠ 0 ∧ (r = (i :: tail).length ∨ u i ≤ sequentialThreshold w (i :: tail).toFinset r i)

instance selectsHead_decidable (w u : ι → ℝ) (i : ι) (tail : List ι) (r : ℕ) :
    Decidable (SelectsHead w u i tail r) := Classical.propDecidable _

theorem sequentialList_step (w u : ι → ℝ) (i : ι) (tail : List ι) (r : ℕ) :
    sequentialList w u (i :: tail) r =
      if SelectsHead w u i tail r then insert i (sequentialList w u tail (r - 1))
      else sequentialList w u tail r := by
  by_cases hr : r = 0
  · subst r; simp [SelectsHead]
  by_cases hf : r = (i :: tail).length
  · subst r
    simp [SelectsHead, sequentialList, sequentialList_full]
  · simp only [List.length_cons] at hf
    simp [SelectsHead, sequentialList, hr, hf]

def prefixSelected (w u : ι → ℝ) : List ι → ℕ → ℕ → Finset ι
  | [], _, _ => ∅
  | _ :: _, _, 0 => ∅
  | i :: tail, r, ℓ + 1 =>
    if SelectsHead w u i tail r then insert i (prefixSelected w u tail (r - 1) ℓ)
    else prefixSelected w u tail r ℓ

@[simp] theorem prefixSelected_zero (w u : ι → ℝ) (order : List ι) (r : ℕ) :
    prefixSelected w u order r 0 = ∅ := by cases order <;> rfl

theorem prefixSelected_subset (w u : ι → ℝ) (order : List ι) (r ℓ : ℕ) :
    prefixSelected w u order r ℓ ⊆ order.toFinset := by
  induction order generalizing r ℓ with
  | nil => simp [prefixSelected]
  | cons i tail ih =>
    cases ℓ with
    | zero => simp
    | succ ℓ =>
      simp only [prefixSelected, List.toFinset_cons]
      split_ifs
      · exact Finset.insert_subset_insert i (ih (r - 1) ℓ)
      · exact (ih r ℓ).trans (Finset.subset_insert _ _)

/-- Every revealed decision agrees with membership in the eventual output. -/
theorem prefixSelected_eq_output_inter (w u : ι → ℝ) (order : List ι)
    (hn : order.Nodup) (r ℓ : ℕ) :
    prefixSelected w u order r ℓ = sequentialList w u order r ∩ (order.take ℓ).toFinset := by
  induction order generalizing r ℓ with
  | nil => simp [prefixSelected]
  | cons i tail ih =>
    obtain ⟨hi, ht⟩ := List.nodup_cons.mp hn
    cases ℓ with
    | zero => simp
    | succ ℓ =>
      rw [prefixSelected, sequentialList_step]
      split_ifs with htake
      · rw [ih ht (r - 1) ℓ]
        ext j
        simp only [List.take_succ_cons, List.toFinset_cons, Finset.mem_insert, Finset.mem_inter]
        tauto
      · rw [ih ht r ℓ]
        have hnot : i ∉ sequentialList w u tail r := by
          intro h
          exact hi (List.mem_toFinset.mp (sequentialList_subset w u tail r h))
        simp only [List.take_succ_cons, List.toFinset_cons, Finset.inter_insert_of_notMem hnot]

def prefixQuota (w u : ι → ℝ) (order : List ι) (r ℓ : ℕ) : ℕ :=
  r - (prefixSelected w u order r ℓ).card

theorem prefixQuota_step_selected (w u : ι → ℝ) (i : ι) (tail : List ι)
    (hi : i ∉ tail) (r ℓ : ℕ) (htake : SelectsHead w u i tail r) :
    prefixQuota w u (i :: tail) r (ℓ + 1) = prefixQuota w u tail (r - 1) ℓ := by
  have hnot : i ∉ prefixSelected w u tail (r - 1) ℓ := by
    intro h
    exact hi (List.mem_toFinset.mp (prefixSelected_subset w u tail (r - 1) ℓ h))
  simp only [prefixQuota, prefixSelected, if_pos htake, Finset.card_insert_of_notMem hnot]
  omega

theorem prefixQuota_step_rejected (w u : ι → ℝ) (i : ι) (tail : List ι)
    (r ℓ : ℕ) (htake : ¬SelectsHead w u i tail r) :
    prefixQuota w u (i :: tail) r (ℓ + 1) = prefixQuota w u tail r ℓ := by
  simp only [prefixQuota, prefixSelected, if_neg htake]

/-- Continuing from the actual remaining quota reproduces the same final output. -/
theorem sequentialList_eq_prefix_union_continuation (w u : ι → ℝ) (order : List ι)
    (hn : order.Nodup) (r ℓ : ℕ) :
    sequentialList w u order r = prefixSelected w u order r ℓ ∪
      sequentialList w u (order.drop ℓ) (prefixQuota w u order r ℓ) := by
  induction order generalizing r ℓ with
  | nil => simp [prefixSelected, prefixQuota]
  | cons i tail ih =>
    obtain ⟨hi, ht⟩ := List.nodup_cons.mp hn
    cases ℓ with
    | zero => simp [prefixQuota]
    | succ ℓ =>
      rw [sequentialList_step]
      by_cases htake : SelectsHead w u i tail r
      · rw [if_pos htake, prefixQuota_step_selected w u i tail hi r ℓ htake]
        simp only [prefixSelected, if_pos htake, List.drop_succ_cons]
        rw [ih ht (r - 1) ℓ]
        ext j
        simp only [Finset.mem_insert, Finset.mem_union]
        tauto
      · rw [if_neg htake, prefixQuota_step_rejected w u i tail r ℓ htake]
        simp only [prefixSelected, if_neg htake, List.drop_succ_cons]
        exact ih ht r ℓ

theorem prefixSelected_uniforms_congr (w u v : ι → ℝ) (order : List ι) (r ℓ : ℕ)
    (hu : ∀ i ∈ order.take ℓ, u i = v i) :
    prefixSelected w u order r ℓ = prefixSelected w v order r ℓ := by
  induction order generalizing r ℓ with
  | nil => rfl
  | cons i tail ih =>
    cases ℓ with
    | zero => simp
    | succ ℓ =>
      have hi : u i = v i := hu i (by simp)
      have ht : ∀ j ∈ tail.take ℓ, u j = v j := fun j hj => hu j (by simp [hj])
      have hd : SelectsHead w u i tail r ↔ SelectsHead w v i tail r := by
        simp only [SelectsHead, hi]
      simp only [prefixSelected, hd]
      split_ifs
      · rw [ih (r - 1) ℓ ht]
      · exact ih r ℓ ht

theorem prefixQuota_le_drop_length (w u : ι → ℝ) (order : List ι)
    (hn : order.Nodup) (r ℓ : ℕ) (hr : r ≤ order.length) :
    prefixQuota w u order r ℓ ≤ (order.drop ℓ).length := by
  induction order generalizing r ℓ with
  | nil =>
    have hr0 : r = 0 := by simpa using hr
    simp [prefixQuota, prefixSelected, hr0]
  | cons i tail ih =>
    obtain ⟨hi, ht⟩ := List.nodup_cons.mp hn
    cases ℓ with
    | zero => simpa [prefixQuota] using hr
    | succ ℓ =>
      by_cases htake : SelectsHead w u i tail r
      · rw [prefixQuota_step_selected w u i tail hi r ℓ htake]
        simpa only [List.drop_succ_cons] using ih ht (r - 1) ℓ (by
          simp only [List.length_cons] at hr; omega)
      · rw [prefixQuota_step_rejected w u i tail r ℓ htake]
        have hrtail : r ≤ tail.length := by
          have hne : r ≠ tail.length + 1 := by
            intro he
            apply htake
            exact ⟨by omega, Or.inl (by simpa using he)⟩
          simp only [List.length_cons] at hr
          omega
        simpa only [List.drop_succ_cons] using ih ht r ℓ hrtail

theorem nodup_drop (order : List ι) (hn : order.Nodup) (ℓ : ℕ) :
    (order.drop ℓ).Nodup := by
  have h : (order.take ℓ ++ order.drop ℓ).Nodup := by rwa [List.take_append_drop]
  exact (List.nodup_append.mp h).2.1

/-- Reordering only unrevealed positions does not change any revealed decision. -/
theorem prefixSelected_order_congr (w u : ι → ℝ) (order order' : List ι)
    (hn : order.Nodup) (hn' : order'.Nodup) (r ℓ : ℕ)
    (hR : order.toFinset = order'.toFinset) (hp : order.take ℓ = order'.take ℓ) :
    prefixSelected w u order r ℓ = prefixSelected w u order' r ℓ := by
  induction ℓ generalizing order order' r with
  | zero => simp
  | succ ℓ ih =>
    cases order with
    | nil =>
      cases order' with
      | nil => rfl
      | cons j tail' => simp at hp
    | cons i tail =>
      cases order' with
      | nil => simp at hp
      | cons j tail' =>
        simp only [List.take_succ_cons] at hp
        obtain ⟨hij, hpt⟩ := List.cons.inj hp
        subst j
        obtain ⟨hi, ht⟩ := List.nodup_cons.mp hn
        obtain ⟨hi', ht'⟩ := List.nodup_cons.mp hn'
        have htail : tail.toFinset = tail'.toFinset := by
          have h := congrArg (fun R : Finset ι => R.erase i) hR
          simpa [hi, hi'] using h
        have hlen : tail.length = tail'.length := by
          rw [← List.toFinset_card_of_nodup ht, ← List.toFinset_card_of_nodup ht', htail]
        have hd : SelectsHead w u i tail r ↔ SelectsHead w u i tail' r := by
          simp only [SelectsHead, List.length_cons, hlen, hR]
        simp only [prefixSelected, hd]
        split_ifs
        · rw [ih tail tail' ht ht' (r - 1) htail hpt]
        · exact ih tail tail' ht ht' r htail hpt

theorem measurable_prefixSelected (w : ι → ℝ) (order : List ι)
    (hn : order.Nodup) (r ℓ : ℕ) :
    Measurable (fun u : ι → ℝ => prefixSelected w u order r ℓ) := by
  have hf : (fun u : ι → ℝ => prefixSelected w u order r ℓ) =
      fun u => sequentialList w u order r ∩ (order.take ℓ).toFinset :=
    funext fun u => prefixSelected_eq_output_inter w u order hn r ℓ
  rw [hf]
  exact (measurable_of_finite (fun S : Finset ι => S ∩ (order.take ℓ).toFinset)).comp
    ((measurable_sequentialList order r).comp (measurable_const.prodMk measurable_id))

theorem prefixMatches_take_eq {n ℓ : ℕ} {ρ π : Equiv.Perm (Fin n)}
    (h : PrefixMatches ℓ ρ π) : (List.ofFn π).take ℓ = (List.ofFn ρ).take ℓ := by
  apply List.ext_getElem (by simp)
  intro j hj hj'
  have hjℓ : j < ℓ := (lt_min_iff.mp (by simpa using hj)).1
  simp only [List.getElem_take, List.getElem_ofFn]
  exact h _ hjℓ

theorem mem_permutation_take_iff {n ℓ : ℕ} (ρ : Equiv.Perm (Fin n)) (i : Fin n) :
    i ∈ (List.ofFn ρ).take ℓ ↔ Revealed ℓ ρ i := by
  rw [List.mem_take_iff_getElem]
  constructor
  · rintro ⟨j, hj, he⟩
    have hjn : j < n := (lt_min_iff.mp (by simpa using hj)).2
    have hej : ρ ⟨j, hjn⟩ = i := by simpa using he
    have hback := congrArg ρ.symm hej
    simp only [ρ.symm_apply_apply] at hback
    unfold Revealed
    rw [← hback]
    exact (lt_min_iff.mp (by simpa using hj)).1
  · intro hi
    refine ⟨(ρ.symm i).val, ?_, ?_⟩
    · simpa only [List.length_ofFn] using lt_min hi (ρ.symm i).isLt
    · simp

theorem mem_permutation_drop_iff {n ℓ : ℕ} (ρ : Equiv.Perm (Fin n)) (i : Fin n) :
    i ∈ (List.ofFn ρ).drop ℓ ↔ ¬Revealed ℓ ρ i := by
  have hd : Disjoint (((List.ofFn ρ).take ℓ).toFinset) (((List.ofFn ρ).drop ℓ).toFinset) :=
    List.disjoint_toFinset_iff_disjoint.mpr
      (List.disjoint_take_drop (List.nodup_ofFn.mpr ρ.injective) le_rfl)
  have hm : i ∈ List.ofFn ρ := List.mem_ofFn.mpr ⟨ρ.symm i, ρ.apply_symm_apply i⟩
  have hor : i ∈ (List.ofFn ρ).take ℓ ∨ i ∈ (List.ofFn ρ).drop ℓ := by
    simpa only [← List.mem_append, List.take_append_drop] using hm
  rw [← mem_permutation_take_iff]
  constructor
  · intro hdrop htake
    exact Finset.disjoint_left.mp hd (List.mem_toFinset.mpr htake) (List.mem_toFinset.mpr hdrop)
  · intro hnot
    exact hor.resolve_left hnot

def remainingSet {n : ℕ} (ℓ : ℕ) (ρ : Equiv.Perm (Fin n)) : Finset (Fin n) :=
  Finset.univ.filter (fun i => ¬Revealed ℓ ρ i)

theorem permutation_drop_toFinset {n ℓ : ℕ} (ρ : Equiv.Perm (Fin n)) :
    ((List.ofFn ρ).drop ℓ).toFinset = remainingSet ℓ ρ := by
  ext i
  simp [remainingSet, mem_permutation_drop_iff]

theorem prefixMatches_remainingSet {n ℓ : ℕ} {ρ π : Equiv.Perm (Fin n)}
    (hπ : PrefixMatches ℓ ρ π) : remainingSet ℓ π = remainingSet ℓ ρ := by
  ext i
  have he : Revealed ℓ ρ i ↔ Revealed ℓ π i := by
    simpa only [π.apply_symm_apply, Revealed] using
      prefixMatches_revealed_iff hπ (π.symm i)
  simp only [remainingSet, Finset.mem_filter, Finset.mem_univ, true_and, he]

def extendPastUniforms {n : ℕ} (ℓ : ℕ) (ρ : Equiv.Perm (Fin n))
    (v : PastUniforms ℓ ρ) : Fin n → ℝ :=
  fun i => if hi : Revealed ℓ ρ i then (v ⟨i, hi⟩ : ℝ) else 0

theorem measurable_extendPastUniforms {n : ℕ} (ℓ : ℕ) (ρ : Equiv.Perm (Fin n)) :
    Measurable (extendPastUniforms ℓ ρ) := by
  apply measurable_pi_iff.mpr
  intro i
  by_cases hi : Revealed ℓ ρ i
  · simp only [extendPastUniforms, dif_pos hi]
    exact measurable_subtype_coe.comp (measurable_pi_apply (⟨i, hi⟩ : {i // Revealed ℓ ρ i}))
  · simp only [extendPastUniforms, dif_neg hi]
    exact measurable_const

def historySelected {n : ℕ} (w : Fin n → ℝ) (k ℓ : ℕ) (ω : Seed n) : Finset (Fin n) :=
  prefixSelected w (fun i => (ω.2 i : ℝ)) (List.ofFn ω.1) k ℓ

def historyRemaining {n : ℕ} (ℓ : ℕ) (ω : Seed n) : Finset (Fin n) :=
  ((List.ofFn ω.1).drop ℓ).toFinset

def historyQuota {n : ℕ} (w : Fin n → ℝ) (k ℓ : ℕ) (ω : Seed n) : ℕ :=
  k - (historySelected w k ℓ ω).card

theorem historySelected_eq_output_inter {n : ℕ} (w : Fin n → ℝ) (k ℓ : ℕ) (ω : Seed n) :
    historySelected w k ℓ ω = sequentialSampler w k ω ∩ ((List.ofFn ω.1).take ℓ).toFinset :=
  prefixSelected_eq_output_inter w _ _ (List.nodup_ofFn.mpr ω.1.injective) k ℓ

theorem historyQuota_le_remaining_card {n : ℕ} (w : Fin n → ℝ) (k ℓ : ℕ)
    (hk : k ≤ n) (ω : Seed n) : historyQuota w k ℓ ω ≤ (historyRemaining ℓ ω).card := by
  have hn := List.nodup_ofFn.mpr ω.1.injective
  have h := prefixQuota_le_drop_length w (fun i => (ω.2 i : ℝ)) (List.ofFn ω.1) hn k ℓ
    (by simpa using hk)
  simpa only [historyRemaining, historyQuota, historySelected, prefixQuota,
    List.toFinset_card_of_nodup (nodup_drop _ hn ℓ)] using h

theorem sequentialSampler_eq_history_union_continuation {n : ℕ} (w : Fin n → ℝ)
    (k ℓ : ℕ) (ω : Seed n) :
    sequentialSampler w k ω = historySelected w k ℓ ω ∪
      sequentialList w (fun i => (ω.2 i : ℝ)) ((List.ofFn ω.1).drop ℓ) (historyQuota w k ℓ ω) :=
  sequentialList_eq_prefix_union_continuation w _ _ (List.nodup_ofFn.mpr ω.1.injective) k ℓ

theorem historySelected_prefixObservable {n : ℕ} (w : Fin n → ℝ) (k ℓ : ℕ)
    (S : Finset (Fin n)) : PrefixObservableEvent ℓ {ω | historySelected w k ℓ ω = S} := by
  intro ρ
  refine ⟨{v | prefixSelected w (extendPastUniforms ℓ ρ v) (List.ofFn ρ) k ℓ = S}, ?_, ?_⟩
  · exact (measurableSet_singleton S).preimage
      ((measurable_prefixSelected w _ (List.nodup_ofFn.mpr ρ.injective) k ℓ).comp
        (measurable_extendPastUniforms ℓ ρ))
  · intro ω hπ
    have ho := prefixSelected_order_congr w (fun i => (ω.2 i : ℝ))
      (List.ofFn ω.1) (List.ofFn ρ) (List.nodup_ofFn.mpr ω.1.injective)
      (List.nodup_ofFn.mpr ρ.injective) k ℓ
      (by rw [permutation_order_toFinset, permutation_order_toFinset]) (prefixMatches_take_eq hπ)
    have hu : ∀ i ∈ (List.ofFn ρ).take ℓ, (ω.2 i : ℝ) =
        extendPastUniforms ℓ ρ (splitUniforms ℓ ρ ω.2).1 i := by
      intro i hi
      simp only [extendPastUniforms, dif_pos ((mem_permutation_take_iff ρ i).mp hi)]
      rfl
    have he := ho.trans (prefixSelected_uniforms_congr w _ _ (List.ofFn ρ) k ℓ hu)
    exact congrArg (· = S) he |>.to_iff

end CoefficientOne.Sampling
