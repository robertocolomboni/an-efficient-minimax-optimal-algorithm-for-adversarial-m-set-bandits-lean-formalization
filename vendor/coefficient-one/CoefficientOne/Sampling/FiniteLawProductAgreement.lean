import CoefficientOne.Sampling.FiniteLawExactness
import CoefficientOne.Sampling.NextReveal

/-! # Agreement of direct and product-field sampling

The argument identifies the conditional thresholds from the actual output law,
then applies the same argument in each positive branch. Forced branches are
handled pointwise, including seeds equal to zero or one.
-/

open MeasureTheory Set EffectiveResistance
open scoped unitInterval ENNReal

namespace CoefficientOne.Sampling
noncomputable section

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

theorem finiteCubeSampler_output_probability_pos (p : Finset ι → ℝ) (hp : ∀ S, 0 ≤ p S)
    (H : Finset (Finset ι)) (hH : 0 < candidateMass p H) (order : List ι)
    (hn : order.Nodup) (u : ι → unitInterval) :
    0 < uniformCube ι {v | finiteCubeSampler p H order v = finiteCubeSampler p H order u} := by
  obtain ⟨S, hSH, hSpos, he⟩ := finiteSamplerList_positive_atom p hp H hH
    (fun i => (u i : ℝ)) order hn
  have hmem : S ∈ projectedCandidates H order.toFinset (finiteCubeSampler p H order u) := by
    exact Finset.mem_filter.mpr ⟨hSH, he.symm⟩
  have hm : 0 < candidateMass p
      (projectedCandidates H order.toFinset (finiteCubeSampler p H order u)) :=
    lt_of_lt_of_le hSpos (Finset.single_le_sum (fun T _ => hp T) hmem)
  rw [finiteCubeSampler_probability p hp H hH order hn]
  exact ENNReal.ofReal_pos.mpr (div_pos hm hH)

theorem finiteCubeSampler_head_mem_iff (p : Finset ι → ℝ) (H : Finset (Finset ι))
    (i : ι) (tail : List ι) (hi : i ∉ tail) (u : ι → unitInterval) :
    i ∈ finiteCubeSampler p H (i :: tail) u ↔
      finiteDecision (candidateThreshold p H i) (u i : ℝ) = true := by
  change i ∈ (if finiteDecision (candidateThreshold p H i) (u i : ℝ) then
    insert i (finiteCubeSampler p (selectedCandidates H i) tail u)
    else finiteCubeSampler p (rejectedCandidates H i) tail u) ↔ _
  cases hd : finiteDecision (candidateThreshold p H i) (u i : ℝ)
  · simp only [Bool.false_eq_true, ↓reduceIte, iff_false]
    exact finiteCubeSampler_notMem p _ tail i hi u
  · simp

/-- The first conditional threshold is determined by the output law. -/
theorem candidateThreshold_eq_of_output_law (p : Finset ι → ℝ) (hp : ∀ S, 0 ≤ p S)
    (H : Finset (Finset ι)) (hH : 0 < candidateMass p H)
    (w : ι → ℝ) (hw : ∀ i, 0 < w i) (i : ι) (tail : List ι)
    (hn : (i :: tail).Nodup) (r : ℕ) (hr0 : 0 < r) (hrtop : r < (i :: tail).length)
    (hprob : ∀ S, uniformCube ι {u | finiteCubeSampler p H (i :: tail) u = S} =
      uniformCube ι {u | cubeSampler w (i :: tail) r u = S}) :
    candidateThreshold p H i = sequentialThreshold w (i :: tail).toFinset r i := by
  have hi := (List.nodup_cons.mp hn).1
  have hmap : (uniformCube ι).map (finiteCubeSampler p H (i :: tail)) =
      (uniformCube ι).map (cubeSampler w (i :: tail) r) := by
    apply Measure.ext_of_singleton
    intro S
    rw [Measure.map_apply (measurable_finiteCubeSampler p H _) (measurableSet_singleton S),
      Measure.map_apply (measurable_cubeSampler w _ r) (measurableSet_singleton S)]
    exact hprob S
  have he := congrArg (fun μ : Measure (Finset ι) => μ {S | i ∈ S}) hmap
  rw [Measure.map_apply (measurable_finiteCubeSampler p H _)
      (Set.toFinite _).measurableSet,
    Measure.map_apply (measurable_cubeSampler w _ r) (Set.toFinite _).measurableSet] at he
  have hleft : (finiteCubeSampler p H (i :: tail)) ⁻¹' {S | i ∈ S} =
      {u | finiteDecision (candidateThreshold p H i) (u i : ℝ) = true} := by
    ext u
    exact finiteCubeSampler_head_mem_iff p H i tail hi u
  have hright : (cubeSampler w (i :: tail) r) ⁻¹' {S | i ∈ S} =
      {u | (u i : ℝ) ≤ sequentialThreshold w (i :: tail).toFinset r i} := by
    ext u
    exact sequentialList_head_mem_iff_threshold w (fun i => (u i : ℝ)) i tail hi r hr0 hrtop
  have hc := List.toFinset_card_of_nodup hn
  have hp0 := (sequentialThreshold_pos w hw (i :: tail).toFinset r hr0
    (by rw [hc]; exact hrtop.le) i (by simp)).le
  have hp1 := (sequentialThreshold_lt_one w hw (i :: tail).toFinset r hr0
    (by rwa [hc]) i (by simp)).le
  have hct := candidateThreshold_mem_Icc p hp H hH i
  rw [hleft, hright, uniformCube_finiteDecision i _ hct true,
    uniformCube_le_threshold i _ hp0 hp1] at he
  have hh := congrArg ENNReal.toReal he
  simpa only [↓reduceIte, ENNReal.toReal_ofReal hct.1, ENNReal.toReal_ofReal hp0] using hh

theorem finiteCubeSampler_eq_const_of_law (p : Finset ι → ℝ) (hp : ∀ S, 0 ≤ p S)
    (H : Finset (Finset ι)) (hH : 0 < candidateMass p H) (order : List ι)
    (hn : order.Nodup) (g : (ι → unitInterval) → Finset ι) (K : Finset ι)
    (hg : ∀ u, g u = K)
    (hprob : ∀ S, uniformCube ι {u | finiteCubeSampler p H order u = S} =
      uniformCube ι {u | g u = S}) (u : ι → unitInterval) :
    finiteCubeSampler p H order u = K := by
  by_contra hne
  have hpos := finiteCubeSampler_output_probability_pos p hp H hH order hn u
  rw [hprob] at hpos
  have he : {v | g v = finiteCubeSampler p H order u} = ∅ := by
    ext v
    simp [hg v, Ne.symm hne]
  rw [he, measure_empty] at hpos
  exact lt_irrefl _ hpos

/-- Equal output laws identify these two canonical sequential threshold
recursions on every seed. Equality is propagated through positive branches. -/
theorem finiteCubeSampler_eq_cubeSampler_of_law (p : Finset ι → ℝ) (hp : ∀ S, 0 ≤ p S)
    (H : Finset (Finset ι)) (hH : 0 < candidateMass p H)
    (w : ι → ℝ) (hw : ∀ i, 0 < w i) (order : List ι) (hn : order.Nodup)
    (r : ℕ) (hr : r ≤ order.length)
    (hprob : ∀ S, uniformCube ι {u | finiteCubeSampler p H order u = S} =
      uniformCube ι {u | cubeSampler w order r u = S}) (u : ι → unitInterval) :
    finiteCubeSampler p H order u = cubeSampler w order r u := by
  induction order generalizing H r with
  | nil => simp [finiteCubeSampler, cubeSampler, finiteSamplerList]
  | cons i tail ih =>
    by_cases hr0 : r = 0
    · subst r
      have hg (v : ι → unitInterval) : cubeSampler w (i :: tail) 0 v = ∅ := by
        simp [cubeSampler]
      rw [hg u]
      exact finiteCubeSampler_eq_const_of_law p hp H hH (i :: tail) hn _ ∅ hg hprob u
    by_cases hrfull : r = (i :: tail).length
    · have hg (v : ι → unitInterval) : cubeSampler w (i :: tail) r v = (i :: tail).toFinset := by
        simp only [cubeSampler, hrfull, sequentialList_full]
      rw [hg u]
      exact finiteCubeSampler_eq_const_of_law p hp H hH (i :: tail) hn _ _ hg hprob u
    have hrpos : 0 < r := Nat.pos_of_ne_zero hr0
    have hrtop : r < (i :: tail).length := lt_of_le_of_ne hr hrfull
    obtain ⟨hi, hntail⟩ := List.nodup_cons.mp hn
    have hrtail : r ≤ tail.length := by simp only [List.length_cons] at hrtop; omega
    have hc := List.toFinset_card_of_nodup hn
    have ht0 := sequentialThreshold_pos w hw (i :: tail).toFinset r hrpos
      (by rw [hc]; exact hr) i (by simp)
    have ht1 := sequentialThreshold_lt_one w hw (i :: tail).toFinset r hrpos
      (by rwa [hc]) i (by simp)
    have ht := candidateThreshold_eq_of_output_law p hp H hH w hw i tail hn r hrpos hrtop hprob
    have htI : candidateThreshold p H i ∈ Icc (0 : ℝ) 1 := candidateThreshold_mem_Icc p hp H hH i
    have hspos : 0 < candidateMass p (selectedCandidates H i) := by
      have hct0 : 0 < candidateThreshold p H i := by rw [ht]; exact ht0
      exact (div_pos_iff_of_pos_right hH).mp hct0
    have hrjpos : 0 < candidateMass p (rejectedCandidates H i) := by
      have hh : 0 < 1 - candidateThreshold p H i := by rw [ht]; linarith
      rw [one_sub_candidateThreshold p H hH.ne' i] at hh
      exact (div_pos_iff_of_pos_right hH).mp hh
    have hsLaw (S : Finset ι) :
        uniformCube ι {v | finiteCubeSampler p (selectedCandidates H i) tail v = S} =
        uniformCube ι {v | cubeSampler w tail (r - 1) v = S} := by
      by_cases hiS : i ∈ S
      · have hleft : {v | finiteCubeSampler p (selectedCandidates H i) tail v = S} = ∅ := by
          ext v
          simp only [Set.mem_setOf_eq, Set.mem_empty_iff_false, iff_false]
          intro he
          exact finiteCubeSampler_notMem p _ tail i hi v (he ▸ hiS)
        have hright : {v | cubeSampler w tail (r - 1) v = S} = ∅ := by
          ext v
          simp only [Set.mem_setOf_eq, Set.mem_empty_iff_false, iff_false]
          intro he
          exact cubeSampler_notMem w tail (r - 1) i hi v (he ▸ hiS)
        rw [hleft, hright]
      · have he := hprob (insert i S)
        rw [finiteCubeSampler_selected_event p H tail i hi _ (Finset.mem_insert_self _ _),
          finiteCubeSampler_decision_inter p (selectedCandidates H i) tail i hi _
            (candidateThreshold p H i) htI true,
          cubeSampler_selected_probability w tail r i hi hr0 hrfull _
            (Finset.mem_insert_self _ _) ht0.le ht1.le,
          Finset.erase_insert hiS, ht] at he
        exact (ENNReal.mul_right_inj (ne_of_gt (ENNReal.ofReal_pos.mpr ht0))
          ENNReal.ofReal_ne_top).mp he
    have hrLaw (S : Finset ι) :
        uniformCube ι {v | finiteCubeSampler p (rejectedCandidates H i) tail v = S} =
        uniformCube ι {v | cubeSampler w tail r v = S} := by
      by_cases hiS : i ∈ S
      · have hleft : {v | finiteCubeSampler p (rejectedCandidates H i) tail v = S} = ∅ := by
          ext v
          simp only [Set.mem_setOf_eq, Set.mem_empty_iff_false, iff_false]
          intro he
          exact finiteCubeSampler_notMem p _ tail i hi v (he ▸ hiS)
        have hright : {v | cubeSampler w tail r v = S} = ∅ := by
          ext v
          simp only [Set.mem_setOf_eq, Set.mem_empty_iff_false, iff_false]
          intro he
          exact cubeSampler_notMem w tail r i hi v (he ▸ hiS)
        rw [hleft, hright]
      · have he := hprob S
        rw [finiteCubeSampler_rejected_event p H tail i S hiS,
          finiteCubeSampler_decision_inter p (rejectedCandidates H i) tail i hi S
            (candidateThreshold p H i) htI false,
          cubeSampler_rejected_probability w tail r i hi hr0 hrfull S hiS ht0.le ht1.le,
          ht] at he
        exact (ENNReal.mul_right_inj (ne_of_gt (ENNReal.ofReal_pos.mpr (sub_pos.mpr ht1)))
          ENNReal.ofReal_ne_top).mp he
    have hsEq := ih (selectedCandidates H i) hspos hntail (r - 1) (by omega) hsLaw
    have hrEq := ih (rejectedCandidates H i) hrjpos hntail r hrtail hrLaw
    have hdecision : finiteDecision (candidateThreshold p H i) (u i : ℝ) =
        decide ((u i : ℝ) ≤ sequentialThreshold w (i :: tail).toFinset r i) := by
      rw [ht]
      unfold finiteDecision
      rw [if_neg (not_le.mpr ht0), if_neg (not_le.mpr ht1)]
    change (if finiteDecision (candidateThreshold p H i) (u i : ℝ) then
      insert i (finiteCubeSampler p (selectedCandidates H i) tail u)
      else finiteCubeSampler p (rejectedCandidates H i) tail u) = _
    rw [hdecision, hsEq, hrEq]
    simp only [cubeSampler, sequentialList, hr0, hrfull, ↓reduceIte, decide_eq_true_eq]

/-- The boundary-compatible direct algorithm agrees with the positive-field
algorithm, including all endpoint seeds. -/
theorem finiteLawSampler_restrictedLaw_eq_sequentialSampler {n : ℕ}
    (w : Fin n → ℝ) (hw : ∀ i, 0 < w i) (k : ℕ) (hk : k ≤ n) (ω : Seed n) :
    finiteLawSampler (restrictedLaw w hw Finset.univ k (by simpa using hk)) ω =
      sequentialSampler w k ω := by
  let p := restrictedLaw w hw Finset.univ k (by simpa using hk)
  apply finiteCubeSampler_eq_cubeSampler_of_law p.val (law_nonneg p) Finset.univ
    (by simp [candidateMass, law_sum]) w hw (List.ofFn ω.1)
    (List.nodup_ofFn.mpr ω.1.injective) k (by simpa using hk) _ ω.2
  intro S
  have hleft := (finiteLawSampler_fixedOrder p ω.1).measure_preimage
    (measurableSet_singleton S).nullMeasurableSet
  have hright := (sequentialSampler_fixedOrder w hw k hk ω.1).measure_preimage
    (measurableSet_singleton S).nullMeasurableSet
  exact hleft.trans hright.symm

end
end CoefficientOne.Sampling
