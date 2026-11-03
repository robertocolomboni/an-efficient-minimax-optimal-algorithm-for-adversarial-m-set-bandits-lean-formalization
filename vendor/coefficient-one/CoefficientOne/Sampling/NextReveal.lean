import CoefficientOne.Sampling.ConditionalLaw

/-! # The finite transition kernel of the next reveal -/

noncomputable section

open MeasureTheory Set
open scoped ENNReal unitInterval

namespace CoefficientOne.Sampling

section FiniteThreshold

variable {α : Type*} [Fintype α] [Nonempty α]
  [MeasurableSpace α] [MeasurableSingletonClass α]

def thresholdDecision (p : α → unitInterval) (z : α × unitInterval) : α × Bool :=
  (z.1, decide (z.2 ≤ p z.1))

theorem measurable_thresholdDecision (p : α → unitInterval) : Measurable (thresholdDecision p) := by
  have hf : thresholdDecision p = fun z : α × unitInterval =>
      if z.2 ≤ p z.1 then (z.1, true) else (z.1, false) := by
    funext z
    by_cases h : z.2 ≤ p z.1 <;> simp [thresholdDecision, h]
  rw [hf]
  exact Measurable.ite
    (measurableSet_le measurable_snd ((measurable_of_finite p).comp measurable_fst))
    (measurable_fst.prodMk measurable_const) (measurable_fst.prodMk measurable_const)

theorem thresholdDecision_probability (p : α → unitInterval) (i : α) (b : Bool) :
    ((uniformMeasure α).prod (volume : Measure unitInterval))
        (thresholdDecision p ⁻¹' {(i, b)}) =
      (Fintype.card α : ℝ≥0∞)⁻¹ * ENNReal.ofReal
        (if b then (p i : ℝ) else 1 - (p i : ℝ)) := by
  classical
  cases b
  · have hs : thresholdDecision p ⁻¹' {(i, false)} = {i} ×ˢ Ioi (p i) := by
      ext ⟨j, u⟩
      by_cases hj : j = i
      · subst j; simp [thresholdDecision]
      · simp [thresholdDecision, hj]
    rw [hs, Measure.prod_prod, uniformMeasure_singleton, unitInterval.volume_Ioi]
    rfl
  · have hs : thresholdDecision p ⁻¹' {(i, true)} = {i} ×ˢ Iic (p i) := by
      ext ⟨j, u⟩
      by_cases hj : j = i
      · subst j; simp [thresholdDecision]
      · simp [thresholdDecision, hj]
    rw [hs, Measure.prod_prod, uniformMeasure_singleton, unitInterval.volume_Iic]
    rfl

theorem thresholdDecision_integral (p : α → unitInterval) (F : α × Bool → ℝ) :
    (∫ z, F (thresholdDecision p z)
      ∂((uniformMeasure α).prod (volume : Measure unitInterval))) =
      (Fintype.card α : ℝ)⁻¹ *
        ∑ i : α, ((p i : ℝ) * F (i, true) + (1 - (p i : ℝ)) * F (i, false)) := by
  classical
  let μ := (uniformMeasure α).prod (volume : Measure unitInterval)
  have hm := measurable_thresholdDecision p
  have hmass (a : α × Bool) : (μ.map (thresholdDecision p)).real {a} =
      (Fintype.card α : ℝ)⁻¹ * (if a.2 then (p a.1 : ℝ) else 1 - (p a.1 : ℝ)) := by
    rw [measureReal_def, Measure.map_apply hm (measurableSet_singleton a)]
    change (μ (thresholdDecision p ⁻¹' {(a.1, a.2)})).toReal = _
    rw [thresholdDecision_probability, ENNReal.toReal_mul, ENNReal.toReal_inv,
      ENNReal.toReal_natCast, ENNReal.toReal_ofReal]
    cases a.2 <;> simp only [Bool.false_eq_true, ↓reduceIte]
    · exact sub_nonneg.mpr (p a.1).property.2
    · exact (p a.1).property.1
  calc
    _ = ∫ a, F a ∂μ.map (thresholdDecision p) :=
      (integral_map hm.aemeasurable (measurable_of_finite F).aestronglyMeasurable).symm
    _ = ∑ a : α × Bool, (μ.map (thresholdDecision p)).real {a} * F a := by
      rw [integral_fintype Integrable.of_finite]
      rfl
    _ = _ := by
      simp_rw [hmass]
      rw [Fintype.sum_prod_type, Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro i _
      simp only [Fintype.sum_bool, Bool.false_eq_true, ↓reduceIte]
      ring

end FiniteThreshold

def nextRevealBit {n : ℕ} (ℓ : ℕ) (ρ : Equiv.Perm (Fin n))
    (j : {j : Fin n // ¬j.val < ℓ}) (p : {i // ¬Revealed ℓ ρ i} → unitInterval)
    (z : PrefixOrders ℓ ρ × FutureUniforms ℓ ρ) : {i // ¬Revealed ℓ ρ i} × Bool :=
  thresholdDecision p (remainingOrder ℓ ρ z.1 j, z.2 (remainingOrder ℓ ρ z.1 j))

/-- The next reveal has the explicit uniform-index/Bernoulli transition kernel. -/
theorem nextRevealBit_integral {n : ℕ} (ℓ : ℕ) (ρ : Equiv.Perm (Fin n))
    [Nonempty {i // ¬Revealed ℓ ρ i}]
    (j : {j : Fin n // ¬j.val < ℓ}) (p : {i // ¬Revealed ℓ ρ i} → unitInterval)
    (F : ({i // ¬Revealed ℓ ρ i} × Bool) → ℝ) :
    (∫ z, F (nextRevealBit ℓ ρ j p z) ∂prefixFutureMeasure ℓ ρ) =
      (Fintype.card {i // ¬Revealed ℓ ρ i} : ℝ)⁻¹ *
        ∑ i : {i // ¬Revealed ℓ ρ i},
          ((p i : ℝ) * F (i, true) + (1 - (p i : ℝ)) * F (i, false)) := by
  have h := nextReveal_measurePreserving ℓ ρ j
  have hm : Measurable (fun z => F (thresholdDecision p z)) :=
    (measurable_of_finite F).comp (measurable_thresholdDecision p)
  have he := integral_map (μ := prefixFutureMeasure ℓ ρ)
    h.measurable.aemeasurable hm.aestronglyMeasurable
  rw [h.map_eq] at he
  exact he.symm.trans (thresholdDecision_integral p F)

def residualThreshold {n : ℕ} (w : Fin n → ℝ) (hw : ∀ i, 0 < w i)
    (ℓ : ℕ) (ρ : Equiv.Perm (Fin n)) (r : ℕ) (hr0 : 0 < r)
    (hrtop : r < (remainingSet ℓ ρ).card) : {i // ¬Revealed ℓ ρ i} → unitInterval :=
  fun i => ⟨sequentialThreshold w (remainingSet ℓ ρ) r i.val,
    (sequentialThreshold_pos w hw _ r hr0 hrtop.le i.val
      (by simp [remainingSet, i.property])).le,
    (sequentialThreshold_lt_one w hw _ r hr0 hrtop i.val
      (by simp [remainingSet, i.property])).le⟩

/-- Specialization to the actual product-weight conditional thresholds. -/
theorem residualNextReveal_integral {n : ℕ} (w : Fin n → ℝ) (hw : ∀ i, 0 < w i)
    (ℓ : ℕ) (ρ : Equiv.Perm (Fin n)) [Nonempty {i // ¬Revealed ℓ ρ i}]
    (j : {j : Fin n // ¬j.val < ℓ}) (r : ℕ) (hr0 : 0 < r)
    (hrtop : r < (remainingSet ℓ ρ).card)
    (F : ({i // ¬Revealed ℓ ρ i} × Bool) → ℝ) :
    (∫ z, F (nextRevealBit ℓ ρ j (residualThreshold w hw ℓ ρ r hr0 hrtop) z)
      ∂prefixFutureMeasure ℓ ρ) =
      ((remainingSet ℓ ρ).card : ℝ)⁻¹ *
        ∑ i : {i // ¬Revealed ℓ ρ i},
          (sequentialThreshold w (remainingSet ℓ ρ) r i.val * F (i, true) +
            (1 - sequentialThreshold w (remainingSet ℓ ρ) r i.val) * F (i, false)) := by
  have hc : Fintype.card {i // ¬Revealed ℓ ρ i} = (remainingSet ℓ ρ).card := by
    rw [Fintype.card_subtype]
    rfl
  simpa only [hc, residualThreshold] using
    nextRevealBit_integral ℓ ρ j (residualThreshold w hw ℓ ρ r hr0 hrtop) F

theorem sequentialList_head_mem_iff_threshold {ι : Type*} [Fintype ι] [DecidableEq ι]
    (w u : ι → ℝ) (i : ι) (tail : List ι) (hi : i ∉ tail)
    (r : ℕ) (hr0 : 0 < r) (hrtop : r < (i :: tail).length) :
    i ∈ sequentialList w u (i :: tail) r ↔
      u i ≤ sequentialThreshold w (i :: tail).toFinset r i := by
  have hnot : i ∉ sequentialList w u tail r := by
    intro h
    exact hi (List.mem_toFinset.mp (sequentialList_subset w u tail r h))
  simp only [sequentialList, if_neg hr0.ne', if_neg (ne_of_lt hrtop)]
  split_ifs with htake
  · simp only [Finset.mem_insert_self, true_iff]
    exact htake
  · simp only [hnot, false_iff]
    exact htake

/-- At the first unrevealed position, the kernel bit is the sampler's actual next decision. -/
theorem nextRevealBit_selects_iff {n : ℕ} (w : Fin n → ℝ) (hw : ∀ i, 0 < w i)
    (ℓ : ℕ) (hℓ : ℓ < n) (ρ : Equiv.Perm (Fin n)) (r : ℕ) (hr0 : 0 < r)
    (hrtop : r < (remainingSet ℓ ρ).card) (z : PrefixOrders ℓ ρ × FutureUniforms ℓ ρ) :
    (nextRevealBit ℓ ρ ⟨⟨ℓ, hℓ⟩, Nat.lt_irrefl ℓ⟩
        (residualThreshold w hw ℓ ρ r hr0 hrtop) z).2 = true ↔
      z.1.val ⟨ℓ, hℓ⟩ ∈ futureContinuation w ℓ ρ r z := by
  let i : Fin n := z.1.val ⟨ℓ, hℓ⟩
  let tail := (List.ofFn z.1.val).drop (ℓ + 1)
  have ho : (List.ofFn z.1.val).drop ℓ = i :: tail := by
    dsimp [i, tail]
    rw [List.drop_eq_getElem_cons (l := List.ofFn z.1.val)
      (i := ℓ) (by simpa using hℓ), List.getElem_ofFn]
  have hn : (i :: tail).Nodup := ho ▸ nodup_drop (List.ofFn z.1.val)
    (List.nodup_ofFn.mpr z.1.val.injective) ℓ
  have hR : (i :: tail).toFinset = remainingSet ℓ ρ := by
    rw [← ho, prefixOrder_drop_toFinset]
  have hi : ¬Revealed ℓ ρ i := by
    exact (remainingOrder ℓ ρ z.1 ⟨⟨ℓ, hℓ⟩, Nat.lt_irrefl ℓ⟩).property
  have hlen : r < (i :: tail).length := by
    rwa [← List.toFinset_card_of_nodup hn, hR]
  have hactual := sequentialList_head_mem_iff_threshold w (extendFutureUniforms ℓ ρ z.2)
    i tail (List.nodup_cons.mp hn).1 r hr0 hlen
  rw [hR] at hactual
  change decide (z.2 (remainingOrder ℓ ρ z.1 ⟨⟨ℓ, hℓ⟩, Nat.lt_irrefl ℓ⟩) ≤
    residualThreshold w hw ℓ ρ r hr0 hrtop
      (remainingOrder ℓ ρ z.1 ⟨⟨ℓ, hℓ⟩, Nat.lt_irrefl ℓ⟩)) = true ↔ _
  rw [decide_eq_true_eq]
  change (z.2 ⟨i, hi⟩ : ℝ) ≤ sequentialThreshold w (remainingSet ℓ ρ) r i ↔ _
  change _ ↔ i ∈ sequentialList w (extendFutureUniforms ℓ ρ z.2)
    ((List.ofFn z.1.val).drop ℓ) r
  rw [ho, hactual]
  simp only [extendFutureUniforms, dif_pos hi]

end CoefficientOne.Sampling
