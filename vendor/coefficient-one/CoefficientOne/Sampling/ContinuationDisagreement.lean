import CoefficientOne.Sampling.ConditionalLaw
import CoefficientOne.Sampling.QuotaMonotonicity

/-!
# Disagreement bound for continuations with a common residual seed

At each step the first threshold mismatch costs at most the threshold
difference. The two common-decision branches are weighted by complementary
probabilities, so the finite induction costs one copy per remaining vertex.
-/

open MeasureTheory ProbabilityTheory Set
open scoped unitInterval ENNReal

namespace CoefficientOne.Sampling
noncomputable section

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

theorem cubeSampler_pair_indep_uniform (w v : ι → ℝ) (order : List ι) (r : ℕ)
    (i : ι) (hi : i ∉ order) :
    IndepFun (fun u : ι → unitInterval => u i)
      (fun u => (cubeSampler w order r u, cubeSampler v order r u)) (uniformCube ι) := by
  have hind : iIndepFun (fun j (u : ι → unitInterval) => u j) (uniformCube ι) :=
    iIndepFun_pi (fun _ => measurable_id.aemeasurable)
  have hdis : Disjoint ({i} : Finset ι) order.toFinset := by simp [hi]
  have ht := hind.indepFun_finset {i} order.toFinset hdis (fun j => measurable_pi_apply j)
  have hm (a : ι → ℝ) : Measurable (fun u : order.toFinset → unitInterval =>
      sequentialList a (fillUniforms order.toFinset u) order r) :=
    (measurable_sequentialList order r).comp
      (measurable_const.prodMk (measurable_fillUniforms order.toFinset))
  have hc := ht.comp (measurable_pi_apply (⟨i, by simp⟩ : ({i} : Finset ι))) ((hm w).prodMk (hm v))
  simpa only [Function.comp_def, cubeSampler_fill] using hc

theorem cubeSampler_disagreement_inter (w v : ι → ℝ) (order : List ι) (r : ℕ)
    (i : ι) (hi : i ∉ order) (T : Set unitInterval) (hT : MeasurableSet T) :
    uniformCube ι {u | u i ∈ T ∧ cubeSampler w order r u ≠ cubeSampler v order r u} =
      uniformCube ι {u | u i ∈ T} *
        uniformCube ι {u | cubeSampler w order r u ≠ cubeSampler v order r u} := by
  have h := (cubeSampler_pair_indep_uniform w v order r i hi).measure_inter_preimage_eq_mul
    T {z : Finset ι × Finset ι | z.1 ≠ z.2} hT (Set.toFinite _).measurableSet
  exact h

theorem uniformCube_threshold_disagreement (i : ι) (p q : ℝ)
    (hp : p ∈ Icc (0 : ℝ) 1) (hq : q ∈ Icc (0 : ℝ) 1) :
    uniformCube ι {u | ¬ ((u i : ℝ) ≤ p ↔ (u i : ℝ) ≤ q)} = ENNReal.ofReal |p - q| := by
  let a : unitInterval := ⟨p, hp⟩
  let b : unitInterval := ⟨q, hq⟩
  by_cases hpq : p ≤ q
  · have he : {u : ι → unitInterval | ¬ ((u i : ℝ) ≤ p ↔ (u i : ℝ) ≤ q)} =
        Function.eval i ⁻¹' Ioc a b := by
      ext u
      change ¬ ((u i : ℝ) ≤ p ↔ (u i : ℝ) ≤ q) ↔ p < (u i : ℝ) ∧ (u i : ℝ) ≤ q
      by_cases hu : (u i : ℝ) ≤ p
      · have hv := hu.trans hpq
        simp [hu, hv, not_lt.mpr hu]
      · simp [hu, lt_of_not_ge hu]
    have hm := (measurePreserving_eval (fun _ : ι => (volume : Measure unitInterval)) i).measure_preimage
      (measurableSet_Ioc (a := a) (b := b)).nullMeasurableSet
    change uniformCube ι (Function.eval i ⁻¹' Ioc a b) = volume (Ioc a b) at hm
    rw [he, hm, unitInterval.volume_Ioc]
    congr 1
    dsimp [a, b]
    rw [abs_of_nonpos (sub_nonpos.mpr hpq)]
    ring
  · have hqp : q ≤ p := (lt_of_not_ge hpq).le
    have he : {u : ι → unitInterval | ¬ ((u i : ℝ) ≤ p ↔ (u i : ℝ) ≤ q)} =
        Function.eval i ⁻¹' Ioc b a := by
      ext u
      change ¬ ((u i : ℝ) ≤ p ↔ (u i : ℝ) ≤ q) ↔ q < (u i : ℝ) ∧ (u i : ℝ) ≤ p
      by_cases hu : (u i : ℝ) ≤ q
      · have hv := hu.trans hqp
        simp [hu, hv, not_lt.mpr hu]
      · simp [hu, lt_of_not_ge hu]
    have hm := (measurePreserving_eval (fun _ : ι => (volume : Measure unitInterval)) i).measure_preimage
      (measurableSet_Ioc (a := b) (b := a)).nullMeasurableSet
    change uniformCube ι (Function.eval i ⁻¹' Ioc b a) = volume (Ioc b a) at hm
    rw [he, hm, unitInterval.volume_Ioc]
    congr 1
    dsimp [a, b]
    rw [abs_of_nonneg (sub_nonneg.mpr hqp)]

theorem cubeSampler_disagreement_subset (w v : ι → ℝ) (tail : List ι) (r : ℕ)
    (i : ι) (hr0 : r ≠ 0) (hrfull : r ≠ (i :: tail).length) :
    {u | cubeSampler w (i :: tail) r u ≠ cubeSampler v (i :: tail) r u} ⊆
      {u | ¬ ((u i : ℝ) ≤ sequentialThreshold w (i :: tail).toFinset r i ↔
        (u i : ℝ) ≤ sequentialThreshold v (i :: tail).toFinset r i)} ∪
      ({u | (u i : ℝ) ≤ sequentialThreshold w (i :: tail).toFinset r i ∧
        cubeSampler w tail (r - 1) u ≠ cubeSampler v tail (r - 1) u} ∪
       {u | sequentialThreshold w (i :: tail).toFinset r i < (u i : ℝ) ∧
        cubeSampler w tail r u ≠ cubeSampler v tail r u}) := by
  intro u hu
  by_cases hw : (u i : ℝ) ≤ sequentialThreshold w (i :: tail).toFinset r i
  · by_cases hv : (u i : ℝ) ≤ sequentialThreshold v (i :: tail).toFinset r i
    · apply Or.inr ∘ Or.inl
      refine ⟨hw, ?_⟩
      intro he
      apply hu
      change (if r = 0 then ∅ else if r = (i :: tail).length then _ else
        if (u i : ℝ) ≤ sequentialThreshold w (i :: tail).toFinset r i then _ else _) = _
      simp only [cubeSampler, sequentialList, hr0, hrfull, hw, hv, ↓reduceIte]
      exact congrArg (fun S : Finset ι => insert i S) he
    · exact Or.inl (fun h => hv (h.mp hw))
  · by_cases hv : (u i : ℝ) ≤ sequentialThreshold v (i :: tail).toFinset r i
    · exact Or.inl (fun h => hw (h.mpr hv))
    · apply Or.inr ∘ Or.inr
      refine ⟨lt_of_not_ge hw, ?_⟩
      intro he
      apply hu
      simpa only [cubeSampler, sequentialList, hr0, hrfull, hw, hv, ↓reduceIte] using he

/-- One copy of the uniform threshold error per remaining coordinate. -/
theorem cubeSampler_disagreement_le (w v : ι → ℝ) (hw : ∀ i, 0 < w i)
    (hv : ∀ i, 0 < v i) (order : List ι) (hn : order.Nodup) (r : ℕ) (hr : r ≤ order.length)
    (δ : ℝ) (hδ : 0 ≤ δ)
    (hbound : ∀ (R : Finset ι) (q : ℕ), q ≤ R.card → ∀ i ∈ R,
      |quotaThreshold w R q i - quotaThreshold v R q i| ≤ δ) :
    uniformCube ι {u | cubeSampler w order r u ≠ cubeSampler v order r u} ≤
      ENNReal.ofReal ((order.length : ℝ) * δ) := by
  induction order generalizing r with
  | nil => simp [cubeSampler]
  | cons i tail ih =>
    by_cases hr0 : r = 0
    · subst r
      simp [cubeSampler]
    by_cases hrfull : r = (i :: tail).length
    · simp only [cubeSampler, hrfull, sequentialList_full, ne_eq, not_true_eq_false,
        Set.setOf_false, measure_empty]
      exact zero_le
    obtain ⟨hi, hntail⟩ := List.nodup_cons.mp hn
    have hrpos : 0 < r := Nat.pos_of_ne_zero hr0
    have hrtop : r < (i :: tail).length := lt_of_le_of_ne hr hrfull
    have hrtail : r ≤ tail.length := by simp only [List.length_cons] at hrtop; omega
    have hc := List.toFinset_card_of_nodup hn
    have hp0 := sequentialThreshold_pos w hw (i :: tail).toFinset r hrpos
      (by rw [hc]; exact hr) i (by simp)
    have hp1 := sequentialThreshold_lt_one w hw (i :: tail).toFinset r hrpos
      (by rwa [hc]) i (by simp)
    have hq0 := sequentialThreshold_pos v hv (i :: tail).toFinset r hrpos
      (by rw [hc]; exact hr) i (by simp)
    have hq1 := sequentialThreshold_lt_one v hv (i :: tail).toFinset r hrpos
      (by rwa [hc]) i (by simp)
    let p := sequentialThreshold w (i :: tail).toFinset r i
    let q := sequentialThreshold v (i :: tail).toFinset r i
    have hp : p ∈ Icc (0 : ℝ) 1 := ⟨hp0.le, hp1.le⟩
    have hq : q ∈ Icc (0 : ℝ) 1 := ⟨hq0.le, hq1.le⟩
    have herr : |p - q| ≤ δ := by
      have he := hbound (i :: tail).toFinset r (by rw [hc]; exact hr) i (by simp)
      rwa [quotaThreshold_eq_sequentialThreshold w hw _ r hrpos (by rw [hc]; exact hr) i (by simp),
        quotaThreshold_eq_sequentialThreshold v hv _ r hrpos (by rw [hc]; exact hr) i (by simp)] at he
    let A : Set (ι → unitInterval) := {u | ¬ ((u i : ℝ) ≤ p ↔ (u i : ℝ) ≤ q)}
    let B : Set (ι → unitInterval) := {u | (u i : ℝ) ≤ p ∧
      cubeSampler w tail (r - 1) u ≠ cubeSampler v tail (r - 1) u}
    let C : Set (ι → unitInterval) := {u | p < (u i : ℝ) ∧
      cubeSampler w tail r u ≠ cubeSampler v tail r u}
    have hA : uniformCube ι A = ENNReal.ofReal |p - q| :=
      uniformCube_threshold_disagreement i p q hp hq
    have hB : uniformCube ι B = ENNReal.ofReal p *
        uniformCube ι {u | cubeSampler w tail (r - 1) u ≠ cubeSampler v tail (r - 1) u} := by
      have he := cubeSampler_disagreement_inter w v tail (r - 1) i hi
        {z : unitInterval | (z : ℝ) ≤ p}
        (measurableSet_le measurable_subtype_coe measurable_const)
      change uniformCube ι B = uniformCube ι {u | (u i : ℝ) ≤ p} * _ at he
      rw [he, uniformCube_le_threshold i p hp.1 hp.2]
    have hC : uniformCube ι C = ENNReal.ofReal (1 - p) *
        uniformCube ι {u | cubeSampler w tail r u ≠ cubeSampler v tail r u} := by
      have he := cubeSampler_disagreement_inter w v tail r i hi
        {z : unitInterval | p < (z : ℝ)}
        (measurableSet_lt measurable_const measurable_subtype_coe)
      change uniformCube ι C = uniformCube ι {u | p < (u i : ℝ)} * _ at he
      rw [he, uniformCube_gt_threshold i p hp.1 hp.2]
    have hsel := ih hntail (r - 1) (by omega)
    have hrej := ih hntail r hrtail
    have htailnonneg : 0 ≤ (tail.length : ℝ) * δ := mul_nonneg (Nat.cast_nonneg _) hδ
    have hsum : ENNReal.ofReal p + ENNReal.ofReal (1 - p) = 1 := by
      rw [← ENNReal.ofReal_add hp.1 (sub_nonneg.mpr hp.2)]
      norm_num
    calc
      _ ≤ uniformCube ι (A ∪ (B ∪ C)) :=
        measure_mono (cubeSampler_disagreement_subset w v tail r i hr0 hrfull)
      _ ≤ uniformCube ι A + (uniformCube ι B + uniformCube ι C) :=
        (measure_union_le A (B ∪ C)).trans (add_le_add le_rfl (measure_union_le B C))
      _ ≤ ENNReal.ofReal δ +
          (ENNReal.ofReal p * ENNReal.ofReal ((tail.length : ℝ) * δ) +
           ENNReal.ofReal (1 - p) * ENNReal.ofReal ((tail.length : ℝ) * δ)) := by
        rw [hA, hB, hC]
        exact add_le_add (ENNReal.ofReal_le_ofReal herr)
          (add_le_add (mul_le_mul_of_nonneg_left hsel zero_le)
            (mul_le_mul_of_nonneg_left hrej zero_le))
      _ = ENNReal.ofReal (((i :: tail).length : ℝ) * δ) := by
        rw [← add_mul, hsum, one_mul, ← ENNReal.ofReal_add hδ htailnonneg]
        congr 1
        simp only [List.length_cons, Nat.cast_add, Nat.cast_one]
        ring

theorem futureContinuation_fixedOrder_disagreement_le {n : ℕ}
    (w v : Fin n → ℝ) (hw : ∀ i, 0 < w i) (hv : ∀ i, 0 < v i)
    (ℓ : ℕ) (ρ : Equiv.Perm (Fin n)) (r : ℕ) (hr : r ≤ (remainingSet ℓ ρ).card)
    (δ : ℝ) (hδ : 0 ≤ δ)
    (hbound : ∀ (R : Finset (Fin n)) (q : ℕ), q ≤ R.card → ∀ i ∈ R,
      |quotaThreshold w R q i - quotaThreshold v R q i| ≤ δ)
    (π : PrefixOrders ℓ ρ) :
    uniformCube {i // ¬Revealed ℓ ρ i}
      {u | futureContinuation w ℓ ρ r (π, u) ≠ futureContinuation v ℓ ρ r (π, u)} ≤
      ENNReal.ofReal (((remainingSet ℓ ρ).card : ℝ) * δ) := by
  have hres : MeasurePreserving (fun u : Fin n → unitInterval => (splitUniforms ℓ ρ u).2)
      (uniformCube (Fin n)) (uniformCube {i // ¬Revealed ℓ ρ i}) :=
    measurePreserving_snd.comp (splitUniforms_measurePreserving ℓ ρ)
  have hwmeas : Measurable (fun u => futureContinuation w ℓ ρ r (π, u)) :=
    (measurable_futureContinuation w ℓ ρ r).comp measurable_prodMk_left
  have hvmeas : Measurable (fun u => futureContinuation v ℓ ρ r (π, u)) :=
    (measurable_futureContinuation v ℓ ρ r).comp measurable_prodMk_left
  have hset := (measurableSet_eq_fun hwmeas hvmeas).compl
  have he := hres.measure_preimage hset.nullMeasurableSet
  change uniformCube (Fin n)
      {u | futureContinuation w ℓ ρ r (π, (splitUniforms ℓ ρ u).2) ≠
        futureContinuation v ℓ ρ r (π, (splitUniforms ℓ ρ u).2)} =
    uniformCube {i // ¬Revealed ℓ ρ i}
      {u | futureContinuation w ℓ ρ r (π, u) ≠ futureContinuation v ℓ ρ r (π, u)} at he
  simp_rw [futureContinuation_restrict] at he
  rw [← he]
  have hn := nodup_drop (List.ofFn π.val) (List.nodup_ofFn.mpr π.val.injective) ℓ
  have hlen : ((List.ofFn π.val).drop ℓ).length = (remainingSet ℓ ρ).card := by
    rw [← prefixOrder_drop_toFinset ℓ ρ π, List.toFinset_card_of_nodup hn]
  simpa only [hlen] using cubeSampler_disagreement_le w v hw hv
    ((List.ofFn π.val).drop ℓ) hn r (by rwa [hlen]) δ hδ hbound

/-- The bound under the actual joint law of the unrevealed order and uniforms. -/
theorem futureContinuation_disagreement_le_card {n : ℕ}
    (w v : Fin n → ℝ) (hw : ∀ i, 0 < w i) (hv : ∀ i, 0 < v i)
    (ℓ : ℕ) (ρ : Equiv.Perm (Fin n)) (r : ℕ) (hr : r ≤ (remainingSet ℓ ρ).card)
    (δ : ℝ) (hδ : 0 ≤ δ)
    (hbound : ∀ (R : Finset (Fin n)) (q : ℕ), q ≤ R.card → ∀ i ∈ R,
      |quotaThreshold w R q i - quotaThreshold v R q i| ≤ δ) :
    prefixFutureMeasure ℓ ρ
      {z | futureContinuation w ℓ ρ r z ≠ futureContinuation v ℓ ρ r z} ≤
      ENNReal.ofReal (((remainingSet ℓ ρ).card : ℝ) * δ) := by
  have hset : MeasurableSet {z | futureContinuation w ℓ ρ r z ≠ futureContinuation v ℓ ρ r z} :=
    (measurableSet_eq_fun (measurable_futureContinuation w ℓ ρ r)
      (measurable_futureContinuation v ℓ ρ r)).compl
  change ((uniformMeasure (PrefixOrders ℓ ρ)).prod (uniformCube {i // ¬Revealed ℓ ρ i})) _ ≤ _
  rw [Measure.prod_apply hset]
  calc
    _ ≤ ∫⁻ _π : PrefixOrders ℓ ρ, ENNReal.ofReal (((remainingSet ℓ ρ).card : ℝ) * δ)
        ∂uniformMeasure (PrefixOrders ℓ ρ) := by
      apply lintegral_mono
      intro π
      exact futureContinuation_fixedOrder_disagreement_le w v hw hv ℓ ρ r hr δ hδ hbound π
    _ = _ := by simp

theorem futureContinuation_disagreement_le {n : ℕ}
    (w v : Fin n → ℝ) (hw : ∀ i, 0 < w i) (hv : ∀ i, 0 < v i)
    (ℓ : ℕ) (ρ : Equiv.Perm (Fin n)) (r : ℕ) (hr : r ≤ (remainingSet ℓ ρ).card)
    (δ : ℝ) (hδ : 0 ≤ δ)
    (hbound : ∀ (R : Finset (Fin n)) (q : ℕ), q ≤ R.card → ∀ i ∈ R,
      |quotaThreshold w R q i - quotaThreshold v R q i| ≤ δ) :
    prefixFutureMeasure ℓ ρ
      {z | futureContinuation w ℓ ρ r z ≠ futureContinuation v ℓ ρ r z} ≤
      ENNReal.ofReal ((n : ℝ) * δ) := by
  apply (futureContinuation_disagreement_le_card w v hw hv ℓ ρ r hr δ hδ hbound).trans
  apply ENNReal.ofReal_le_ofReal
  apply mul_le_mul_of_nonneg_right _ hδ
  exact_mod_cast (show (remainingSet ℓ ρ).card ≤ n by
    simpa using Finset.card_le_univ (remainingSet ℓ ρ))

end
end CoefficientOne.Sampling
