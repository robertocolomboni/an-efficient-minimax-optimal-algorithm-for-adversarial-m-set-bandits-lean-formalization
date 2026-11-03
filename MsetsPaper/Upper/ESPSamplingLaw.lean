import MsetsPaper.Upper.ESPSequential

/-!
# Exact law under independent uniform draws

Only the fixed-order conditional Bernoulli sampler is used. The independence
and branch probabilities are proved for the product of uniform measures.
-/

noncomputable section
open scoped BigOperators unitInterval ENNReal
open MeasureTheory ProbabilityTheory Set
namespace MsetsPaper.Upper.ESPSampling
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

def uniformCube (ι : Type*) [Fintype ι] : Measure (ι → unitInterval) :=
  Measure.pi (fun _ => volume)

instance uniformCube_isProbabilityMeasure (ι : Type*) [Fintype ι] :
    IsProbabilityMeasure (uniformCube ι) := by
  unfold uniformCube
  infer_instance

def cubeSampler (w : ι → ℝ) (order : List ι) (r : ℕ)
    (u : ι → unitInterval) : Finset ι := sequentialList w (fun i => (u i : ℝ)) order r

@[fun_prop] theorem measurable_cubeSampler (w : ι → ℝ) (order : List ι) (r : ℕ) :
    Measurable (cubeSampler w order r) := by
  exact (measurable_sequentialList order r).comp
    (measurable_const.prodMk (measurable_pi_iff.mpr fun i =>
      measurable_subtype_coe.comp (measurable_pi_apply i)))

theorem sequentialList_uniforms_congr (w u v : ι → ℝ) (order : List ι) (r : ℕ)
    (h : ∀ i ∈ order, u i = v i) :
    sequentialList w u order r = sequentialList w v order r := by
  induction order generalizing r with
  | nil => rfl
  | cons i tail ih =>
    have hi := h i (by simp)
    have ht : ∀ j ∈ tail, u j = v j := fun j hj => h j (by simp [hj])
    simp only [sequentialList, hi]
    split_ifs <;> try rfl
    · rw [ih (r - 1) ht]
    · exact ih r ht

def fillUniforms (R : Finset ι) (u : R → unitInterval) : ι → ℝ :=
  fun i => if hi : i ∈ R then (u ⟨i, hi⟩ : ℝ) else 0

@[fun_prop] theorem measurable_fillUniforms (R : Finset ι) : Measurable (fillUniforms R) := by
  apply measurable_pi_iff.mpr
  intro i
  by_cases hi : i ∈ R
  · simp only [fillUniforms, dif_pos hi]
    exact measurable_subtype_coe.comp (measurable_pi_apply (⟨i, hi⟩ : R))
  · simp only [fillUniforms, dif_neg hi]
    exact measurable_const

theorem cubeSampler_fill (w : ι → ℝ) (order : List ι) (r : ℕ) (u : ι → unitInterval) :
    sequentialList w (fillUniforms order.toFinset (fun i => u i.val)) order r =
      cubeSampler w order r u := by
  apply sequentialList_uniforms_congr
  intro i hi
  simp [fillUniforms, List.mem_toFinset.mpr hi]

theorem cubeSampler_indep_uniform (w : ι → ℝ) (order : List ι) (r : ℕ)
    (i : ι) (hi : i ∉ order) :
    IndepFun (fun u : ι → unitInterval => u i) (cubeSampler w order r) (uniformCube ι) := by
  have hind : iIndepFun (fun j (u : ι → unitInterval) => u j) (uniformCube ι) :=
    iIndepFun_pi (fun _ => measurable_id.aemeasurable)
  have hdis : Disjoint ({i} : Finset ι) order.toFinset := by simp [hi]
  have ht := hind.indepFun_finset {i} order.toFinset hdis (fun j => measurable_pi_apply j)
  have hmap : Measurable (fun u : order.toFinset → unitInterval =>
      sequentialList w (fillUniforms order.toFinset u) order r) :=
    (measurable_sequentialList order r).comp
      (measurable_const.prodMk (measurable_fillUniforms order.toFinset))
  have hc := ht.comp (measurable_pi_apply (⟨i, by simp⟩ : ({i} : Finset ι))) hmap
  simpa only [Function.comp_def, cubeSampler_fill] using hc

theorem uniformCube_le_threshold (i : ι) (p : ℝ) (hp0 : 0 ≤ p) (hp1 : p ≤ 1) :
    uniformCube ι {u | (u i : ℝ) ≤ p} = ENNReal.ofReal p := by
  let a : unitInterval := ⟨p, hp0, hp1⟩
  have h := (measurePreserving_eval (fun _ : ι => (volume : Measure unitInterval)) i).measure_preimage
    (measurableSet_Iic (a := a)).nullMeasurableSet
  have hs : {u : ι → unitInterval | (u i : ℝ) ≤ p} = Function.eval i ⁻¹' Iic a := by
    ext u
    rfl
  rw [hs]
  exact h.trans (unitInterval.volume_Iic a)

theorem uniformCube_gt_threshold (i : ι) (p : ℝ) (hp0 : 0 ≤ p) (hp1 : p ≤ 1) :
    uniformCube ι {u | p < (u i : ℝ)} = ENNReal.ofReal (1 - p) := by
  let a : unitInterval := ⟨p, hp0, hp1⟩
  have h := (measurePreserving_eval (fun _ : ι => (volume : Measure unitInterval)) i).measure_preimage
    (measurableSet_Ioi (a := a)).nullMeasurableSet
  have hs : {u : ι → unitInterval | p < (u i : ℝ)} = Function.eval i ⁻¹' Ioi a := by
    ext u
    rfl
  rw [hs]
  exact h.trans (unitInterval.volume_Ioi a)

theorem cubeSampler_threshold_inter (w : ι → ℝ) (order : List ι) (r : ℕ)
    (i : ι) (hi : i ∉ order) (S : Finset ι) (T : Set unitInterval) (hT : MeasurableSet T) :
    uniformCube ι {u | u i ∈ T ∧ cubeSampler w order r u = S} =
      uniformCube ι {u | u i ∈ T} * uniformCube ι {u | cubeSampler w order r u = S} := by
  exact (cubeSampler_indep_uniform w order r i hi).measure_inter_preimage_eq_mul
    T {S} hT (measurableSet_singleton S)

theorem cubeSampler_notMem (w : ι → ℝ) (order : List ι) (r : ℕ)
    (i : ι) (hi : i ∉ order) (u : ι → unitInterval) : i ∉ cubeSampler w order r u := by
  intro hm
  exact hi (List.mem_toFinset.mp (sequentialList_subset w _ order r hm))

theorem cubeSampler_selected_event (w : ι → ℝ) (tail : List ι) (r : ℕ)
    (i : ι) (hi : i ∉ tail) (hr : r ≠ 0) (hfull : r ≠ (i :: tail).length)
    (S : Finset ι) (hiS : i ∈ S) :
    {u | cubeSampler w (i :: tail) r u = S} =
      {u | (u i : ℝ) ≤ sequentialThreshold w (i :: tail).toFinset r i ∧
        cubeSampler w tail (r - 1) u = S.erase i} := by
  ext u
  simp only [mem_setOf_eq]
  simp only [cubeSampler, sequentialList, hr, hfull, ↓reduceIte]
  split_ifs with htake
  · simp only [htake, true_and]
    constructor
    · intro h
      have hn : i ∉ sequentialList w (fun j => (u j : ℝ)) tail (r - 1) :=
        cubeSampler_notMem w tail (r - 1) i hi u
      rw [← h, Finset.erase_insert hn]
    · intro h
      rw [h, Finset.insert_erase hiS]
  · simp only [htake, false_and, iff_false]
    intro h
    apply cubeSampler_notMem w tail r i hi u
    change i ∈ sequentialList w (fun j => (u j : ℝ)) tail r
    rwa [h]

theorem cubeSampler_rejected_event (w : ι → ℝ) (tail : List ι) (r : ℕ)
    (i : ι) (hi : i ∉ tail) (hr : r ≠ 0) (hfull : r ≠ (i :: tail).length)
    (S : Finset ι) (hiS : i ∉ S) :
    {u | cubeSampler w (i :: tail) r u = S} =
      {u | sequentialThreshold w (i :: tail).toFinset r i < (u i : ℝ) ∧
        cubeSampler w tail r u = S} := by
  ext u
  simp only [mem_setOf_eq]
  simp only [cubeSampler, sequentialList, hr, hfull, ↓reduceIte]
  split_ifs with htake
  · simp only [not_lt.mpr htake, false_and, iff_false]
    intro h
    exact hiS (h ▸ Finset.mem_insert_self i _)
  · simp only [lt_of_not_ge htake, true_and]

theorem cubeSampler_selected_probability (w : ι → ℝ) (tail : List ι) (r : ℕ)
    (i : ι) (hi : i ∉ tail) (hr : r ≠ 0) (hfull : r ≠ (i :: tail).length)
    (S : Finset ι) (hiS : i ∈ S)
    (hp0 : 0 ≤ sequentialThreshold w (i :: tail).toFinset r i)
    (hp1 : sequentialThreshold w (i :: tail).toFinset r i ≤ 1) :
    uniformCube ι {u | cubeSampler w (i :: tail) r u = S} =
      ENNReal.ofReal (sequentialThreshold w (i :: tail).toFinset r i) *
        uniformCube ι {u | cubeSampler w tail (r - 1) u = S.erase i} := by
  rw [cubeSampler_selected_event w tail r i hi hr hfull S hiS]
  have h := cubeSampler_threshold_inter w tail (r - 1) i hi (S.erase i)
    {v : unitInterval | (v : ℝ) ≤ sequentialThreshold w (i :: tail).toFinset r i}
    (measurableSet_le measurable_subtype_coe measurable_const)
  simp only [Set.mem_setOf_eq] at h
  rw [h, uniformCube_le_threshold i _ hp0 hp1]

theorem cubeSampler_rejected_probability (w : ι → ℝ) (tail : List ι) (r : ℕ)
    (i : ι) (hi : i ∉ tail) (hr : r ≠ 0) (hfull : r ≠ (i :: tail).length)
    (S : Finset ι) (hiS : i ∉ S)
    (hp0 : 0 ≤ sequentialThreshold w (i :: tail).toFinset r i)
    (hp1 : sequentialThreshold w (i :: tail).toFinset r i ≤ 1) :
    uniformCube ι {u | cubeSampler w (i :: tail) r u = S} =
      ENNReal.ofReal (1 - sequentialThreshold w (i :: tail).toFinset r i) *
        uniformCube ι {u | cubeSampler w tail r u = S} := by
  rw [cubeSampler_rejected_event w tail r i hi hr hfull S hiS]
  have h := cubeSampler_threshold_inter w tail r i hi S
    {v : unitInterval | sequentialThreshold w (i :: tail).toFinset r i < (v : ℝ)}
    (measurableSet_lt measurable_const measurable_subtype_coe)
  simp only [Set.mem_setOf_eq] at h
  rw [h, uniformCube_gt_threshold i _ hp0 hp1]

theorem cubeSampler_probability_of_mem (w : ι → ℝ) (hw : ∀ i, 0 < w i)
    (order : List ι) (hn : order.Nodup) (r : ℕ) (hr : r ≤ order.length)
    (S : Finset ι) (hS : S ∈ order.toFinset.powersetCard r) :
    uniformCube ι {u | cubeSampler w order r u = S} =
      ENNReal.ofReal (restrictedMass w order.toFinset r S) := by
  induction order generalizing r S with
  | nil =>
    have hr0 : r = 0 := by simpa using hr
    subst r
    have hS0 : S = ∅ := by simpa using hS
    subst S
    simp [cubeSampler]
  | cons i tail ih =>
    obtain ⟨hi, ht⟩ := List.nodup_cons.mp hn
    by_cases hr0 : r = 0
    · subst r
      have hS0 : S = ∅ := by simpa using hS
      subst S
      simp [cubeSampler]
    by_cases hfull : r = (i :: tail).length
    · have hcard : (i :: tail).toFinset.card = (i :: tail).length :=
        List.toFinset_card_of_nodup (List.nodup_cons.mpr ⟨hi, ht⟩)
      have hSr : S = (i :: tail).toFinset := by
        simpa only [hfull, ← hcard, Finset.powersetCard_self, Finset.mem_singleton] using hS
      subst S
      rw [hfull, ← hcard, restrictedMass_full w hw]
      simp only [↓reduceIte, ENNReal.ofReal_one]
      simp only [hcard, cubeSampler, sequentialList_full, Set.setOf_true, measure_univ]
    have hrpos : 0 < r := Nat.pos_of_ne_zero hr0
    have hrtail : r ≤ tail.length := by simp only [List.length_cons] at hr hfull; omega
    have hic : i ∉ tail.toFinset := by simpa using hi
    have htailcard : tail.toFinset.card = tail.length := List.toFinset_card_of_nodup ht
    have hR : r ≤ tail.toFinset.card := by rwa [htailcard]
    have hp0 := (sequentialThreshold_pos w hw (i :: tail).toFinset r hrpos
      (by rw [List.toFinset_card_of_nodup (List.nodup_cons.mpr ⟨hi, ht⟩)]; exact hr)
      i (by simp)).le
    have hp1 := (sequentialThreshold_lt_one w hw (i :: tail).toFinset r hrpos
      (by rw [List.toFinset_card_of_nodup (List.nodup_cons.mpr ⟨hi, ht⟩)];
          simp only [List.length_cons]; omega) i (by simp)).le
    by_cases hiS : i ∈ S
    · rw [cubeSampler_selected_probability w tail r i hi hr0 hfull S hiS hp0 hp1,
        ih ht (r - 1) (by omega) (S.erase i)
          (residual_selected_support tail.toFinset S i hic r (by simpa using hS) hiS)]
      rw [List.toFinset_cons, restrictedMass_selected w hw tail.toFinset S i hic r
        hrpos hR (by simpa using hS) hiS, ENNReal.ofReal_mul (by simpa using hp0)]
    · rw [cubeSampler_rejected_probability w tail r i hi hr0 hfull S hiS hp0 hp1,
        ih ht r hrtail S
          (residual_rejected_support tail.toFinset S i r (by simpa using hS) hiS)]
      rw [List.toFinset_cons, restrictedMass_rejected w hw tail.toFinset S i hic r
        hrpos hR (by simpa using hS) hiS, ENNReal.ofReal_mul (by simpa using sub_nonneg.mpr hp1)]

/-- The exact atom probabilities of the actual fixed-order sampler. -/
theorem cubeSampler_probability (w : ι → ℝ) (hw : ∀ i, 0 < w i)
    (order : List ι) (hn : order.Nodup) (r : ℕ) (hr : r ≤ order.length) (S : Finset ι) :
    uniformCube ι {u | cubeSampler w order r u = S} =
      ENNReal.ofReal (restrictedMass w order.toFinset r S) := by
  by_cases hS : S ∈ order.toFinset.powersetCard r
  · exact cubeSampler_probability_of_mem w hw order hn r hr S hS
  · have he : {u | cubeSampler w order r u = S} = (∅ : Set (ι → unitInterval)) := by
      apply Set.eq_empty_iff_forall_notMem.mpr
      intro u hu
      have hm : cubeSampler w order r u ∈ order.toFinset.powersetCard r :=
        Finset.mem_powersetCard.mpr ⟨sequentialList_subset w _ order r,
          sequentialList_card w _ order hn r hr⟩
      exact hS (hu ▸ hm)
    rw [he, measure_empty, restrictedMass, if_neg hS, ENNReal.ofReal_zero]


end MsetsPaper.Upper.ESPSampling

