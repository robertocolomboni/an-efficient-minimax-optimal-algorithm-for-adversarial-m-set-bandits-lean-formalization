import CoefficientOne.Sampling.SequentialPrefixSteps
import CoefficientOne.Sampling.AdjacentQuotas

/-! # Freezing the weights immediately after the first different decision -/

namespace CoefficientOne.Sampling
noncomputable section

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

def frozenContinuationAt (w v u : ι → ℝ) (order : List ι) (r ℓ : ℕ) : Finset ι :=
  prefixSelected v u order r ℓ ∪
    sequentialList w u (order.drop ℓ) (prefixQuota v u order r ℓ)

theorem frozenContinuationAt_distance_two (w v u : ι → ℝ) (hw : ∀ i, 0 < w i)
    (order : List ι) (hn : order.Nodup) (r ℓ : ℕ) (hr : r ≤ order.length)
    (hℓ : ℓ < order.length)
    (hprev : prefixSelected w u order r ℓ = prefixSelected v u order r ℓ)
    (hnext : prefixSelected w u order r (ℓ + 1) ≠ prefixSelected v u order r (ℓ + 1)) :
    outputDistance (sequentialList w u order r) (frozenContinuationAt w v u order r (ℓ + 1)) = 2 := by
  have hq : prefixQuota v u order r ℓ = prefixQuota w u order r ℓ := by
    simp only [prefixQuota, hprev]
  have hlen : 0 < (order.drop ℓ).length := by simp only [List.length_drop]; omega
  cases hd : order.drop ℓ with
  | nil => simp [hd] at hlen
  | cons i tail =>
    have hnt : (i :: tail).Nodup := hd ▸ nodup_drop order hn ℓ
    obtain ⟨hi, ht⟩ := List.nodup_cons.mp hnt
    have hd' : order.drop (ℓ + 1) = tail := by
      have he : (order.drop ℓ).drop 1 = order.drop (ℓ + 1) := by
        simp only [List.drop_drop, Nat.add_comm]
      rw [hd] at he
      simpa using he.symm
    have hpreW := prefixSelected_succ_of_drop w u order hn r ℓ i tail hd
    have hpreV := prefixSelected_succ_of_drop v u order hn r ℓ i tail hd
    rw [hq, ← hprev] at hpreV
    have hquota := prefixQuota_succ_of_drop v u order hn r ℓ i tail hd
    rw [hq] at hquota
    have hqle : prefixQuota w u order r ℓ ≤ tail.length + 1 := by
      simpa only [hd, List.length_cons] using prefixQuota_le_drop_length w u order hn r ℓ hr
    have hdis : Disjoint (prefixSelected w u order r ℓ) (insert i tail.toFinset) := by
      simpa only [hd, List.toFinset_cons] using prefixSelected_disjoint_drop w u order hn r ℓ
    have hbase := sequentialList_eq_prefix_union_continuation w u order hn r ℓ
    rw [hd, sequentialList_step] at hbase
    by_cases hwsel : SelectsHead w u i tail (prefixQuota w u order r ℓ)
    · have hvnot : ¬SelectsHead v u i tail (prefixQuota w u order r ℓ) := by
        intro hvsel
        apply hnext
        rw [hpreW, hpreV, if_pos hwsel, if_pos hvsel]
      have hqpos : 0 < prefixQuota w u order r ℓ := Nat.pos_of_ne_zero hwsel.1
      have hqtail : prefixQuota w u order r ℓ ≤ tail.length := by
        have hne : prefixQuota w u order r ℓ ≠ tail.length + 1 := by
          intro he
          exact hvnot ⟨by omega, Or.inl (by simpa using he)⟩
        omega
      have hplus : prefixQuota w u order r ℓ - 1 + 1 = prefixQuota w u order r ℓ := by omega
      rw [hbase, if_pos hwsel, frozenContinuationAt, hpreV, if_neg hvnot, hd', hquota, if_neg hvnot]
      simpa only [hplus] using opposite_decision_distance_two_with_prefix w hw u tail ht
        (prefixQuota w u order r ℓ - 1) (by omega) i hi (prefixSelected w u order r ℓ) hdis
    · have hvsel : SelectsHead v u i tail (prefixQuota w u order r ℓ) := by
        by_contra hvnot
        apply hnext
        rw [hpreW, hpreV, if_neg hwsel, if_neg hvnot]
      have hqpos : 0 < prefixQuota w u order r ℓ := Nat.pos_of_ne_zero hvsel.1
      have hqtail : prefixQuota w u order r ℓ ≤ tail.length := by
        have hne : prefixQuota w u order r ℓ ≠ tail.length + 1 := by
          intro he
          exact hwsel ⟨by omega, Or.inl (by simpa using he)⟩
        omega
      have hplus : prefixQuota w u order r ℓ - 1 + 1 = prefixQuota w u order r ℓ := by omega
      rw [hbase, if_neg hwsel, frozenContinuationAt, hpreV, if_pos hvsel, hd', hquota, if_pos hvsel]
      have hunion : insert i (prefixSelected w u order r ℓ) ∪
          sequentialList w u tail (prefixQuota w u order r ℓ - 1) =
          prefixSelected w u order r ℓ ∪ insert i
            (sequentialList w u tail (prefixQuota w u order r ℓ - 1)) := by
        ext j
        simp only [Finset.mem_insert, Finset.mem_union]
        tauto
      rw [hunion]
      have hsymm (A B : Finset ι) : outputDistance A B = outputDistance B A := by
        unfold outputDistance
        rw [symmDiff_comm]
      rw [hsymm]
      simpa only [hplus] using opposite_decision_distance_two_with_prefix w hw u tail ht
        (prefixQuota w u order r ℓ - 1) (by omega) i hi (prefixSelected w u order r ℓ) hdis

def frozenSampler {n : ℕ} (w v : Fin n → ℝ) (k : ℕ) (ω : Seed n) : Finset (Fin n) :=
  if h : firstDisagreement w v k ω = ⊤ then sequentialSampler w k ω
  else frozenContinuationAt w v (fun i => (ω.2 i : ℝ)) (List.ofFn ω.1) k
    ((firstDisagreement w v k ω).untop h)

theorem frozenSampler_eq_at_stop {n : ℕ} (w v : Fin n → ℝ) (k ℓ : ℕ) (ω : Seed n)
    (h : firstDisagreement w v k ω = (ℓ : WithTop ℕ)) :
    frozenSampler w v k ω =
      frozenContinuationAt w v (fun i => (ω.2 i : ℝ)) (List.ofFn ω.1) k ℓ := by
  simp only [frozenSampler]
  split_ifs with htop
  · exact False.elim (WithTop.coe_ne_top (h.symm.trans htop))
  · congr 1
    simp only [h]
    rfl

theorem frozenSampler_distance_two {n : ℕ} (w v : Fin n → ℝ) (hw : ∀ i, 0 < w i)
    (k : ℕ) (hk : k ≤ n) (ω : Seed n) (hstop : firstDisagreement w v k ω ≠ ⊤) :
    outputDistance (sequentialSampler w k ω) (frozenSampler w v k ω) = 2 := by
  obtain ⟨s, hs⟩ := WithTop.ne_top_iff_exists.mp hstop
  have hsz : s ≠ 0 := by
    intro hz
    exact firstDisagreement_ne_zero w v k ω (by simpa [hz] using hs.symm)
  obtain ⟨ℓ, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hsz
  have hspec := (firstDisagreement_eq_coe_iff w v k (ℓ + 1) ω).mp hs.symm
  rw [frozenSampler_eq_at_stop w v k (ℓ + 1) ω hs.symm]
  exact frozenContinuationAt_distance_two w v _ hw _ (List.nodup_ofFn.mpr ω.1.injective)
    k ℓ (by simpa using hk) (by simpa using (show ℓ < n by omega))
    (hspec.2.2 ℓ (by omega)) hspec.2.1

end
end CoefficientOne.Sampling
