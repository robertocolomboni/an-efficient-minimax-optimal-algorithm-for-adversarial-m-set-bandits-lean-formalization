import CoefficientOne.Sampling.FrozenCoupling
import CoefficientOne.Sampling.TwoThresholds
import CoefficientOne.Sampling.VariationHistory

/-! # The first different decision is covered by the hazards along the base history -/

open MeasureTheory Set

namespace CoefficientOne.Sampling
noncomputable section
set_option maxHeartbeats 1000000

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

theorem selectsHead_disagreement_iff (w v u : ι → ℝ) (i : ι) (tail : List ι)
    (hn : (i :: tail).Nodup) (r : ℕ) :
    (SelectsHead w u i tail r ≠ SelectsHead v u i tail r) ↔
      ((u i ≤ quotaThreshold w (i :: tail).toFinset r i) ≠
        (u i ≤ quotaThreshold v (i :: tail).toFinset r i)) := by
  unfold SelectsHead quotaThreshold
  rw [List.toFinset_card_of_nodup hn]
  by_cases h0 : r = 0
  · simp [h0]
  by_cases hf : r = (i :: tail).length
  · simp only [List.length_cons] at hf
    simp [h0, hf]
  · simp only [List.length_cons] at hf
    simp [h0, hf]

def nextHistoryThreshold {n : ℕ} (w v : Fin n → ℝ) (k : ℕ) (ℓ : Fin n) (ω : Seed n) : ℝ :=
  quotaThreshold v (historyRemaining ℓ.val ω) (historyQuota w k ℓ.val ω) (ω.1 ℓ)

def thresholdHazard {n : ℕ} (w v : Fin n → ℝ) (k : ℕ) (ℓ : Fin n) : Set (Seed n) :=
  {ω | ((ω.2 (ω.1 ℓ) : ℝ) ≤ nextHistoryThreshold w w k ℓ ω) ≠
    ((ω.2 (ω.1 ℓ) : ℝ) ≤ nextHistoryThreshold w v k ℓ ω)}

theorem measurable_nextHistoryThreshold {n : ℕ} (w v : Fin n → ℝ) (k : ℕ) (ℓ : Fin n) :
    Measurable (nextHistoryThreshold w v k ℓ) := by
  have hf := measurable_of_finite (fun z : Equiv.Perm (Fin n) × Finset (Fin n) =>
    quotaThreshold v (((List.ofFn z.1).drop ℓ.val).toFinset)
      (k - (z.2 ∩ ((List.ofFn z.1).take ℓ.val).toFinset).card) (z.1 ℓ))
  have he : nextHistoryThreshold w v k ℓ = fun ω : Seed n =>
      quotaThreshold v (((List.ofFn ω.1).drop ℓ.val).toFinset)
        (k - (sequentialSampler w k ω ∩ ((List.ofFn ω.1).take ℓ.val).toFinset).card) (ω.1 ℓ) := by
    funext ω
    simp only [nextHistoryThreshold, historyQuota, historyRemaining, historySelected_eq_output_inter]
  rw [he]
  exact fun s hs => measurable_samplerOrderOutput w k (hf hs)

theorem measurable_nextUniform {n : ℕ} (ℓ : Fin n) :
    Measurable (fun ω : Seed n => (ω.2 (ω.1 ℓ) : ℝ)) := by
  apply measurable_from_prod_countable_right
  intro π
  exact measurable_subtype_coe.comp (measurable_pi_apply (π ℓ))

theorem measurableSet_thresholdHazard {n : ℕ} (w v : Fin n → ℝ) (k : ℕ) (ℓ : Fin n) :
    MeasurableSet (thresholdHazard w v k ℓ) := by
  have hp := measurableSet_le (measurable_nextUniform ℓ) (measurable_nextHistoryThreshold w w k ℓ)
  have hq := measurableSet_le (measurable_nextUniform ℓ) (measurable_nextHistoryThreshold w v k ℓ)
  have he : thresholdHazard w v k ℓ =
      ({ω | (ω.2 (ω.1 ℓ) : ℝ) ≤ nextHistoryThreshold w w k ℓ ω} \
        {ω | (ω.2 (ω.1 ℓ) : ℝ) ≤ nextHistoryThreshold w v k ℓ ω}) ∪
      ({ω | (ω.2 (ω.1 ℓ) : ℝ) ≤ nextHistoryThreshold w v k ℓ ω} \
        {ω | (ω.2 (ω.1 ℓ) : ℝ) ≤ nextHistoryThreshold w w k ℓ ω}) := by
    ext ω
    simp only [thresholdHazard, mem_setOf_eq, mem_union, mem_diff]
    tauto
  rw [he]
  exact (hp.diff hq).union (hq.diff hp)

theorem firstDisagreement_mem_hazard {n : ℕ} (w v : Fin n → ℝ) (k : ℕ)
    (ℓ : Fin n) (ω : Seed n) (hstop : firstDisagreement w v k ω = ((ℓ.val + 1 : ℕ) : WithTop ℕ)) :
    ω ∈ thresholdHazard w v k ℓ := by
  have hs := (firstDisagreement_eq_coe_iff w v k (ℓ.val + 1) ω).mp hstop
  have hprev := hs.2.2 ℓ.val (by omega)
  have hq : prefixQuota v (fun i => (ω.2 i : ℝ)) (List.ofFn ω.1) k ℓ.val =
      prefixQuota w (fun i => (ω.2 i : ℝ)) (List.ofFn ω.1) k ℓ.val := by
    change k - (historySelected v k ℓ.val ω).card = k - (historySelected w k ℓ.val ω).card
    rw [hprev]
  let i := ω.1 ℓ
  let tail := (List.ofFn ω.1).drop (ℓ.val + 1)
  have hd : (List.ofFn ω.1).drop ℓ.val = i :: tail := by
    dsimp [i, tail]
    rw [List.drop_eq_getElem_cons (l := List.ofFn ω.1) (i := ℓ.val) (by simpa using ℓ.isLt),
      List.getElem_ofFn]
  have hn : (List.ofFn ω.1).Nodup := List.nodup_ofFn.mpr ω.1.injective
  have hnt : (i :: tail).Nodup := hd ▸ nodup_drop _ hn ℓ.val
  have hwstep := prefixSelected_succ_of_drop w (fun j => (ω.2 j : ℝ)) _ hn k ℓ.val i tail hd
  have hvstep := prefixSelected_succ_of_drop v (fun j => (ω.2 j : ℝ)) _ hn k ℓ.val i tail hd
  have hbase : prefixSelected w (fun j => (ω.2 j : ℝ)) (List.ofFn ω.1) k ℓ.val =
      prefixSelected v (fun j => (ω.2 j : ℝ)) (List.ofFn ω.1) k ℓ.val := hprev
  rw [hq, ← hbase] at hvstep
  have hdec : SelectsHead w (fun j => (ω.2 j : ℝ)) i tail (historyQuota w k ℓ.val ω) ≠
      SelectsHead v (fun j => (ω.2 j : ℝ)) i tail (historyQuota w k ℓ.val ω) := by
    intro he
    apply hs.2.1
    change prefixSelected w _ _ k _ = prefixSelected v _ _ k _
    rw [hwstep, hvstep]
    change (if SelectsHead w _ i tail (historyQuota w k ℓ.val ω) then _ else _) =
      (if SelectsHead v _ i tail (historyQuota w k ℓ.val ω) then _ else _)
    simp only [he]
  have hth := (selectsHead_disagreement_iff w v (fun j => (ω.2 j : ℝ)) i tail hnt _).mp hdec
  change ((ω.2 i : ℝ) ≤ quotaThreshold w (historyRemaining ℓ.val ω) _ i) ≠
    ((ω.2 i : ℝ) ≤ quotaThreshold v (historyRemaining ℓ.val ω) _ i)
  simpa only [historyRemaining, hd] using hth

theorem firstDisagreementEvent_subset_hazards {n : ℕ} (w v : Fin n → ℝ) (k : ℕ) :
    firstDisagreementEvent w v k ⊆ ⋃ ℓ : Fin n, thresholdHazard w v k ℓ := by
  intro ω hω
  obtain ⟨s, hs⟩ := WithTop.ne_top_iff_exists.mp hω
  have hsz : s ≠ 0 := by
    intro hz
    exact firstDisagreement_ne_zero w v k ω (by simpa [hz] using hs.symm)
  obtain ⟨ℓ, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hsz
  have hsn := (firstDisagreement_eq_coe_iff w v k (ℓ + 1) ω).mp hs.symm
  exact mem_iUnion.mpr ⟨⟨ℓ, by omega⟩, firstDisagreement_mem_hazard w v k ⟨ℓ, by omega⟩ ω hs.symm⟩

end
end CoefficientOne.Sampling
