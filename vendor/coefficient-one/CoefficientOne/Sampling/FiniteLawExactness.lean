import CoefficientOne.Sampling.FiniteLawSequential

/-! # Chain-rule exactness of direct finite-law sampling -/

open scoped BigOperators unitInterval ENNReal
open EffectiveResistance MeasureTheory ProbabilityTheory Set

namespace CoefficientOne.Sampling
noncomputable section

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

def finiteCubeSampler (p : Finset ι → ℝ) (H : Finset (Finset ι)) (order : List ι)
    (u : ι → unitInterval) : Finset ι :=
  finiteSamplerList p H (fun i => (u i : ℝ)) order

theorem measurable_finiteCubeSampler (p : Finset ι → ℝ) (H : Finset (Finset ι))
    (order : List ι) : Measurable (finiteCubeSampler p H order) :=
  (measurable_finiteSamplerList H order).comp (measurable_const.prodMk
    (measurable_pi_iff.mpr fun i => measurable_subtype_coe.comp (measurable_pi_apply i)))

theorem finiteCubeSampler_fill (p : Finset ι → ℝ) (H : Finset (Finset ι))
    (order : List ι) (u : ι → unitInterval) :
    finiteSamplerList p H (fillUniforms order.toFinset (fun i => u i.val)) order =
      finiteCubeSampler p H order u := by
  apply finiteSamplerList_uniforms_congr
  intro i hi
  simp [fillUniforms, List.mem_toFinset.mpr hi]

theorem finiteCubeSampler_indep_uniform (p : Finset ι → ℝ) (H : Finset (Finset ι))
    (order : List ι) (i : ι) (hi : i ∉ order) :
    IndepFun (fun u : ι → unitInterval => u i) (finiteCubeSampler p H order) (uniformCube ι) := by
  have hind : iIndepFun (fun j (u : ι → unitInterval) => u j) (uniformCube ι) :=
    iIndepFun_pi (fun _ => measurable_id.aemeasurable)
  have hdis : Disjoint ({i} : Finset ι) order.toFinset := by simp [hi]
  have ht := hind.indepFun_finset {i} order.toFinset hdis (fun j => measurable_pi_apply j)
  have hmap : Measurable (fun u : order.toFinset → unitInterval =>
      finiteSamplerList p H (fillUniforms order.toFinset u) order) :=
    (measurable_finiteSamplerList H order).comp
      (measurable_const.prodMk (measurable_fillUniforms order.toFinset))
  have hc := ht.comp (measurable_pi_apply (⟨i, by simp⟩ : ({i} : Finset ι))) hmap
  simpa only [Function.comp_def, finiteCubeSampler_fill] using hc

theorem uniformCube_finiteDecision (i : ι) (t : ℝ) (ht : t ∈ Icc (0 : ℝ) 1) (b : Bool) :
    uniformCube ι {u | finiteDecision t (u i : ℝ) = b} =
      ENNReal.ofReal (if b then t else 1 - t) := by
  by_cases ht0 : t = 0
  · subst t
    cases b <;> simp [finiteDecision]
  by_cases ht1 : t = 1
  · subst t
    cases b <;> norm_num [finiteDecision]
  have h0 : ¬t ≤ 0 := not_le.mpr (lt_of_le_of_ne ht.1 (Ne.symm ht0))
  have h1 : ¬1 ≤ t := not_le.mpr (lt_of_le_of_ne ht.2 ht1)
  cases b
  · have he : {u : ι → unitInterval | finiteDecision t (u i : ℝ) = false} =
        {u | t < (u i : ℝ)} := by
      ext u
      simp [finiteDecision, h0, h1]
    rw [he]
    exact uniformCube_gt_threshold i t ht.1 ht.2
  · have he : {u : ι → unitInterval | finiteDecision t (u i : ℝ) = true} =
        {u | (u i : ℝ) ≤ t} := by
      ext u
      simp [finiteDecision, h0, h1]
    rw [he]
    exact uniformCube_le_threshold i t ht.1 ht.2

theorem finiteCubeSampler_decision_inter (p : Finset ι → ℝ) (H : Finset (Finset ι))
    (order : List ι) (i : ι) (hi : i ∉ order) (S : Finset ι)
    (t : ℝ) (ht : t ∈ Icc (0 : ℝ) 1) (b : Bool) :
    uniformCube ι {u | finiteDecision t (u i : ℝ) = b ∧ finiteCubeSampler p H order u = S} =
      ENNReal.ofReal (if b then t else 1 - t) *
        uniformCube ι {u | finiteCubeSampler p H order u = S} := by
  have hm : Measurable (fun v : unitInterval => finiteDecision t v) :=
    measurable_finiteDecision.comp (measurable_const.prodMk measurable_subtype_coe)
  have he := (finiteCubeSampler_indep_uniform p H order i hi).measure_inter_preimage_eq_mul
    {v : unitInterval | finiteDecision t v = b} {S}
    (measurableSet_eq_fun hm measurable_const) (measurableSet_singleton S)
  change uniformCube ι {u | finiteDecision t (u i : ℝ) = b ∧ finiteCubeSampler p H order u = S} =
    uniformCube ι {u | finiteDecision t (u i : ℝ) = b} *
      uniformCube ι {u | finiteCubeSampler p H order u = S} at he
  rw [he, uniformCube_finiteDecision i t ht b]

theorem finiteCubeSampler_notMem (p : Finset ι → ℝ) (H : Finset (Finset ι))
    (order : List ι) (i : ι) (hi : i ∉ order) (u : ι → unitInterval) :
    i ∉ finiteCubeSampler p H order u := by
  intro h
  exact hi (List.mem_toFinset.mp (finiteSamplerList_subset p H _ order h))

theorem finiteCubeSampler_selected_event (p : Finset ι → ℝ) (H : Finset (Finset ι))
    (tail : List ι) (i : ι) (hi : i ∉ tail) (S : Finset ι) (hiS : i ∈ S) :
    {u | finiteCubeSampler p H (i :: tail) u = S} =
      {u | finiteDecision (candidateThreshold p H i) (u i : ℝ) = true ∧
        finiteCubeSampler p (selectedCandidates H i) tail u = S.erase i} := by
  ext u
  simp only [Set.mem_setOf_eq, finiteCubeSampler, finiteSamplerList]
  cases hd : finiteDecision (candidateThreshold p H i) (u i : ℝ)
  · simp only [Bool.false_eq_true, ↓reduceIte, false_and, iff_false]
    intro he
    apply finiteCubeSampler_notMem p (rejectedCandidates H i) tail i hi u
    change i ∈ finiteSamplerList p (rejectedCandidates H i) (fun j => (u j : ℝ)) tail
    rwa [he]
  · simp only [↓reduceIte, true_and]
    constructor
    · intro he
      have hnot : i ∉ finiteSamplerList p (selectedCandidates H i) (fun j => (u j : ℝ)) tail :=
        finiteCubeSampler_notMem p (selectedCandidates H i) tail i hi u
      rw [← he, Finset.erase_insert hnot]
    · intro he
      rw [he, Finset.insert_erase hiS]

theorem finiteCubeSampler_rejected_event (p : Finset ι → ℝ) (H : Finset (Finset ι))
    (tail : List ι) (i : ι) (S : Finset ι) (hiS : i ∉ S) :
    {u | finiteCubeSampler p H (i :: tail) u = S} =
      {u | finiteDecision (candidateThreshold p H i) (u i : ℝ) = false ∧
        finiteCubeSampler p (rejectedCandidates H i) tail u = S} := by
  ext u
  simp only [Set.mem_setOf_eq, finiteCubeSampler, finiteSamplerList]
  cases hd : finiteDecision (candidateThreshold p H i) (u i : ℝ)
  · simp
  · simp only [↓reduceIte, Bool.true_eq_false, false_and, iff_false]
    intro he
    exact hiS (he ▸ Finset.mem_insert_self i _)

def projectedCandidates (H : Finset (Finset ι)) (R S : Finset ι) : Finset (Finset ι) :=
  H.filter (fun T => T ∩ R = S)

theorem projectedCandidates_selected (H : Finset (Finset ι)) (R S : Finset ι)
    (i : ι) (hi : i ∉ R) (hiS : i ∈ S) :
    projectedCandidates H (insert i R) S =
      projectedCandidates (selectedCandidates H i) R (S.erase i) := by
  ext T
  simp only [projectedCandidates, selectedCandidates, Finset.mem_filter]
  constructor
  · rintro ⟨hH, he⟩
    have hiT : i ∈ T := (Finset.mem_inter.mp (he ▸ hiS)).1
    refine ⟨⟨hH, hiT⟩, ?_⟩
    rw [← he]
    ext j
    simp only [Finset.mem_inter, Finset.mem_erase, Finset.mem_insert]
    constructor
    · rintro ⟨hT, hR⟩
      exact ⟨fun h => hi (h ▸ hR), hT, Or.inr hR⟩
    · rintro ⟨hne, hT, heq | hR⟩
      · exact False.elim (hne heq)
      · exact ⟨hT, hR⟩
  · rintro ⟨⟨hH, hiT⟩, he⟩
    refine ⟨hH, ?_⟩
    ext j
    by_cases hj : j = i
    · subst j; simp [hiT, hiS]
    · have hj' := Finset.ext_iff.mp he j
      simpa [hj] using hj'

theorem projectedCandidates_rejected (H : Finset (Finset ι)) (R S : Finset ι)
    (i : ι) (hiS : i ∉ S) :
    projectedCandidates H (insert i R) S = projectedCandidates (rejectedCandidates H i) R S := by
  ext T
  simp only [projectedCandidates, rejectedCandidates, Finset.mem_filter]
  constructor
  · rintro ⟨hH, he⟩
    have hiT : i ∉ T := by
      intro h
      apply hiS
      rw [← he]
      simp [h]
    refine ⟨⟨hH, hiT⟩, ?_⟩
    rw [← he]
    ext j
    by_cases hj : j = i <;> simp [hj, hiT]
  · rintro ⟨⟨hH, hiT⟩, he⟩
    refine ⟨hH, ?_⟩
    rw [← he]
    ext j
    by_cases hj : j = i <;> simp [hj, hiT]

theorem candidateMass_mono (p : Finset ι → ℝ) (hp : ∀ S, 0 ≤ p S)
    {H K : Finset (Finset ι)} (hHK : H ⊆ K) : candidateMass p H ≤ candidateMass p K :=
  Finset.sum_le_sum_of_subset_of_nonneg hHK (fun S _ _ => hp S)

theorem projectedCandidates_mass_zero (p : Finset ι → ℝ) (hp : ∀ S, 0 ≤ p S)
    (H : Finset (Finset ι)) (hH : candidateMass p H = 0) (R S : Finset ι) :
    candidateMass p (projectedCandidates H R S) = 0 := by
  apply le_antisymm
  · calc
      _ ≤ candidateMass p H := candidateMass_mono p hp (Finset.filter_subset _ _)
      _ = 0 := hH
  · exact candidateMass_nonneg p hp _

theorem one_sub_candidateThreshold (p : Finset ι → ℝ) (H : Finset (Finset ι))
    (hH : candidateMass p H ≠ 0) (i : ι) :
    1 - candidateThreshold p H i = candidateMass p (rejectedCandidates H i) / candidateMass p H := by
  unfold candidateThreshold
  apply (eq_div_iff hH).mpr
  field_simp
  linarith [candidateMass_split p H i]

/-- Chain-rule atom probabilities, including zero-mass branches. -/
theorem finiteCubeSampler_probability (p : Finset ι → ℝ) (hp : ∀ S, 0 ≤ p S)
    (H : Finset (Finset ι)) (hH : 0 < candidateMass p H)
    (order : List ι) (hn : order.Nodup) (S : Finset ι) :
    uniformCube ι {u | finiteCubeSampler p H order u = S} =
      ENNReal.ofReal (candidateMass p (projectedCandidates H order.toFinset S) / candidateMass p H) := by
  induction order generalizing H S with
  | nil =>
    by_cases hS : S = ∅
    · subst S
      simp [finiteCubeSampler, finiteSamplerList, projectedCandidates, hH.ne']
    · have he : projectedCandidates H ([] : List ι).toFinset S = ∅ := by
        simp [projectedCandidates, Ne.symm hS]
      rw [he]
      simp [finiteCubeSampler, finiteSamplerList, Ne.symm hS, candidateMass]
  | cons i tail ih =>
    obtain ⟨hi, hn⟩ := List.nodup_cons.mp hn
    have ht := candidateThreshold_mem_Icc p hp H hH i
    have hiR : i ∉ tail.toFinset := by simpa using hi
    by_cases hiS : i ∈ S
    · rw [finiteCubeSampler_selected_event p H tail i hi S hiS,
        finiteCubeSampler_decision_inter p (selectedCandidates H i) tail i hi (S.erase i)
          (candidateThreshold p H i) ht true]
      simp only [↓reduceIte, List.toFinset_cons]
      rw [projectedCandidates_selected H tail.toFinset S i hiR hiS]
      by_cases hs0 : candidateMass p (selectedCandidates H i) = 0
      · rw [candidateThreshold, hs0, zero_div, ENNReal.ofReal_zero, zero_mul,
          projectedCandidates_mass_zero p hp _ hs0, zero_div, ENNReal.ofReal_zero]
      · have hspos : 0 < candidateMass p (selectedCandidates H i) :=
          lt_of_le_of_ne (candidateMass_nonneg p hp _) (Ne.symm hs0)
        rw [ih _ hspos hn (S.erase i), ← ENNReal.ofReal_mul ht.1]
        congr 1
        unfold candidateThreshold
        field_simp [hH.ne', hs0]
    · rw [finiteCubeSampler_rejected_event p H tail i S hiS,
        finiteCubeSampler_decision_inter p (rejectedCandidates H i) tail i hi S
          (candidateThreshold p H i) ht false]
      simp only [Bool.false_eq_true, ↓reduceIte, List.toFinset_cons]
      rw [projectedCandidates_rejected H tail.toFinset S i hiS,
        one_sub_candidateThreshold p H hH.ne' i]
      by_cases hs0 : candidateMass p (rejectedCandidates H i) = 0
      · rw [hs0, zero_div, ENNReal.ofReal_zero, zero_mul,
          projectedCandidates_mass_zero p hp _ hs0, zero_div, ENNReal.ofReal_zero]
      · have hspos : 0 < candidateMass p (rejectedCandidates H i) :=
          lt_of_le_of_ne (candidateMass_nonneg p hp _) (Ne.symm hs0)
        rw [ih _ hspos hn S, ← ENNReal.ofReal_mul (div_nonneg hspos.le hH.le)]
        congr 1
        field_simp [hH.ne', hs0]

theorem projectedCandidates_univ (S : Finset ι) :
    projectedCandidates Finset.univ Finset.univ S = {S} := by
  ext T
  simp [projectedCandidates]

theorem finiteLawSampler_fixedOrder {n : ℕ} (p : FiniteLaw (Finset (Fin n)))
    (π : Equiv.Perm (Fin n)) :
    MeasurePreserving (fun u : Fin n → unitInterval => finiteLawSampler p (π, u))
      (uniformCube (Fin n)) (lawMeasure p) := by
  have hm : Measurable (fun u : Fin n → unitInterval => finiteLawSampler p (π, u)) :=
    (measurable_finiteLawSampler p).comp measurable_prodMk_left
  refine ⟨hm, Measure.ext_of_singleton fun S => ?_⟩
  rw [Measure.map_apply hm (measurableSet_singleton S), lawMeasure_singleton]
  have he := finiteCubeSampler_probability p.val (law_nonneg p) Finset.univ
    (by simp [candidateMass, law_sum]) (List.ofFn π) (List.nodup_ofFn.mpr π.injective) S
  change uniformCube (Fin n) {u | finiteLawSampler p (π, u) = S} = _
  simpa [finiteCubeSampler, finiteLawSampler, permutation_order_toFinset,
    projectedCandidates_univ, candidateMass, law_sum] using he

/-- The actual permutation/output pair has the product of uniform order and
the prescribed finite law. -/
theorem finiteLawSampler_joint_measurePreserving {n : ℕ} (p : FiniteLaw (Finset (Fin n))) :
    MeasurePreserving (fun ω : Seed n => (ω.1, finiteLawSampler p ω)) (seedMeasure n)
      ((uniformMeasure (Equiv.Perm (Fin n))).prod (lawMeasure p)) := by
  exact (MeasurePreserving.id (uniformMeasure (Equiv.Perm (Fin n)))).skew_product
    (g := fun π u => finiteLawSampler p (π, u))
    (measurable_finiteLawSampler p)
    (Filter.Eventually.of_forall fun π => (finiteLawSampler_fixedOrder p π).map_eq)

theorem finiteLawSampler_measurePreserving {n : ℕ} (p : FiniteLaw (Finset (Fin n))) :
    MeasurePreserving (finiteLawSampler p) (seedMeasure n) (lawMeasure p) :=
  measurePreserving_snd.comp (finiteLawSampler_joint_measurePreserving p)

end
end CoefficientOne.Sampling
