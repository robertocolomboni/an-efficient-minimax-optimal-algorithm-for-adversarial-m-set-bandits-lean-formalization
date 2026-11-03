import CoefficientOne.Sampling.RankSubsetLaw

/-!
# Direct sequential sampling from a finite law

The state records the atoms compatible with the revealed decisions. Conditional
probabilities are ratios of their actual masses. Branches of probability zero
or one are deterministic, including at the endpoints of the uniform seed.
-/

open scoped BigOperators unitInterval
open EffectiveResistance MeasureTheory

namespace CoefficientOne.Sampling
noncomputable section

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

def candidateMass (p : Finset ι → ℝ) (H : Finset (Finset ι)) : ℝ := ∑ S ∈ H, p S

def selectedCandidates (H : Finset (Finset ι)) (i : ι) : Finset (Finset ι) :=
  H.filter (fun S => i ∈ S)

def rejectedCandidates (H : Finset (Finset ι)) (i : ι) : Finset (Finset ι) :=
  H.filter (fun S => i ∉ S)

def candidateThreshold (p : Finset ι → ℝ) (H : Finset (Finset ι)) (i : ι) : ℝ :=
  candidateMass p (selectedCandidates H i) / candidateMass p H

def finiteDecision (t u : ℝ) : Bool :=
  if t ≤ 0 then false else if 1 ≤ t then true else decide (u ≤ t)

def finiteSamplerList (p : Finset ι → ℝ) (H : Finset (Finset ι)) (u : ι → ℝ) :
    List ι → Finset ι
  | [] => ∅
  | i :: tail =>
    if finiteDecision (candidateThreshold p H i) (u i) then
      insert i (finiteSamplerList p (selectedCandidates H i) u tail)
    else finiteSamplerList p (rejectedCandidates H i) u tail

theorem candidateMass_nonneg (p : Finset ι → ℝ) (hp : ∀ S, 0 ≤ p S)
    (H : Finset (Finset ι)) : 0 ≤ candidateMass p H :=
  Finset.sum_nonneg fun S _ => hp S

theorem candidateMass_split (p : Finset ι → ℝ) (H : Finset (Finset ι)) (i : ι) :
    candidateMass p (selectedCandidates H i) + candidateMass p (rejectedCandidates H i) =
      candidateMass p H := by
  exact Finset.sum_filter_add_sum_filter_not H (fun S => i ∈ S) p

theorem candidateThreshold_mem_Icc (p : Finset ι → ℝ) (hp : ∀ S, 0 ≤ p S)
    (H : Finset (Finset ι)) (hH : 0 < candidateMass p H) (i : ι) :
    candidateThreshold p H i ∈ Set.Icc (0 : ℝ) 1 := by
  have hsel := candidateMass_nonneg p hp (selectedCandidates H i)
  have hrej := candidateMass_nonneg p hp (rejectedCandidates H i)
  have hsum := candidateMass_split p H i
  exact ⟨div_nonneg hsel hH.le, (div_le_one hH).mpr (by linarith)⟩

theorem finiteDecision_true_pos (t u : ℝ) (h : finiteDecision t u = true) : 0 < t := by
  by_contra hn
  simp [finiteDecision, not_lt.mp hn] at h

theorem finiteDecision_false_lt_one (t u : ℝ) (h : finiteDecision t u = false) : t < 1 := by
  by_contra hn
  have ht := not_lt.mp hn
  simp [finiteDecision, ht, show ¬t ≤ 0 by linarith] at h

theorem selectedCandidates_mass_pos (p : Finset ι → ℝ) (hp : ∀ S, 0 ≤ p S)
    (H : Finset (Finset ι)) (hH : 0 < candidateMass p H) (i : ι) (u : ℝ)
    (h : finiteDecision (candidateThreshold p H i) u = true) :
    0 < candidateMass p (selectedCandidates H i) := by
  have ht := finiteDecision_true_pos _ _ h
  exact (div_pos_iff_of_pos_right hH).mp ht

theorem rejectedCandidates_mass_pos (p : Finset ι → ℝ) (hp : ∀ S, 0 ≤ p S)
    (H : Finset (Finset ι)) (hH : 0 < candidateMass p H) (i : ι) (u : ℝ)
    (h : finiteDecision (candidateThreshold p H i) u = false) :
    0 < candidateMass p (rejectedCandidates H i) := by
  have ht := finiteDecision_false_lt_one _ _ h
  have hlt : candidateMass p (selectedCandidates H i) < candidateMass p H :=
    (div_lt_one hH).mp ht
  have hsum := candidateMass_split p H i
  linarith

theorem finiteSamplerList_subset (p : Finset ι → ℝ) (H : Finset (Finset ι))
    (u : ι → ℝ) (order : List ι) : finiteSamplerList p H u order ⊆ order.toFinset := by
  induction order generalizing H with
  | nil => simp [finiteSamplerList]
  | cons i tail ih =>
    simp only [finiteSamplerList, List.toFinset_cons]
    split_ifs
    · exact Finset.insert_subset_insert i (ih _)
    · exact (ih _).trans (Finset.subset_insert _ _)

theorem finiteSamplerList_uniforms_congr (p : Finset ι → ℝ) (H : Finset (Finset ι))
    (u v : ι → ℝ) (order : List ι) (huv : ∀ i ∈ order, u i = v i) :
    finiteSamplerList p H u order = finiteSamplerList p H v order := by
  induction order generalizing H with
  | nil => rfl
  | cons i tail ih =>
    simp only [finiteSamplerList, huv i (List.mem_cons_self)]
    split_ifs
    · rw [ih _ (fun j hj => huv j (List.mem_cons_of_mem _ hj))]
    · exact ih _ (fun j hj => huv j (List.mem_cons_of_mem _ hj))

/-- The output always agrees with a positive-mass atom on the coordinates read.
Thus impossible histories are avoided for every seed, not only almost surely. -/
theorem finiteSamplerList_positive_atom (p : Finset ι → ℝ) (hp : ∀ S, 0 ≤ p S)
    (H : Finset (Finset ι)) (hH : 0 < candidateMass p H)
    (u : ι → ℝ) (order : List ι) (hn : order.Nodup) :
    ∃ S ∈ H, 0 < p S ∧ finiteSamplerList p H u order = S ∩ order.toFinset := by
  induction order generalizing H with
  | nil =>
    obtain ⟨S, hS, hpos⟩ : ∃ S ∈ H, 0 < p S := by
      by_contra! he
      have hn : candidateMass p H ≤ 0 := Finset.sum_nonpos he
      exact (not_lt_of_ge hn) hH
    exact ⟨S, hS, hpos, by simp [finiteSamplerList]⟩
  | cons i tail ih =>
    obtain ⟨hi, htail⟩ := List.nodup_cons.mp hn
    cases hd : finiteDecision (candidateThreshold p H i) (u i) with
    | false =>
      obtain ⟨S, hS, hpos, he⟩ := ih (rejectedCandidates H i)
        (rejectedCandidates_mass_pos p hp H hH i (u i) hd) htail
      obtain ⟨hSH, hiS⟩ := Finset.mem_filter.mp hS
      refine ⟨S, hSH, hpos, ?_⟩
      simp only [finiteSamplerList, hd, Bool.false_eq_true, ↓reduceIte, he,
        List.toFinset_cons]
      ext j
      simp only [Finset.mem_inter, Finset.mem_insert]
      constructor
      · rintro ⟨hj, ht⟩; exact ⟨hj, Or.inr ht⟩
      · rintro ⟨hj, rfl | ht⟩
        · exact False.elim (hiS hj)
        · exact ⟨hj, ht⟩
    | true =>
      obtain ⟨S, hS, hpos, he⟩ := ih (selectedCandidates H i)
        (selectedCandidates_mass_pos p hp H hH i (u i) hd) htail
      obtain ⟨hSH, hiS⟩ := Finset.mem_filter.mp hS
      refine ⟨S, hSH, hpos, ?_⟩
      simp only [finiteSamplerList, hd, ↓reduceIte, he, List.toFinset_cons]
      ext j
      simp only [Finset.mem_insert, Finset.mem_inter]
      constructor
      · rintro (rfl | ⟨hj, ht⟩)
        · exact ⟨hiS, Or.inl rfl⟩
        · exact ⟨hj, Or.inr ht⟩
      · rintro ⟨hj, rfl | ht⟩
        · exact Or.inl rfl
        · exact Or.inr ⟨hj, ht⟩

def finiteHistoryCandidates (p : Finset ι → ℝ) (H : Finset (Finset ι)) (u : ι → ℝ) :
    List ι → ℕ → Finset (Finset ι)
  | _, 0 => H
  | [], _ + 1 => H
  | i :: tail, ℓ + 1 =>
    finiteHistoryCandidates p
      (if finiteDecision (candidateThreshold p H i) (u i)
        then selectedCandidates H i else rejectedCandidates H i) u tail ℓ

theorem finiteHistoryCandidates_mass_pos (p : Finset ι → ℝ) (hp : ∀ S, 0 ≤ p S)
    (H : Finset (Finset ι)) (hH : 0 < candidateMass p H)
    (u : ι → ℝ) (order : List ι) (ℓ : ℕ) :
    0 < candidateMass p (finiteHistoryCandidates p H u order ℓ) := by
  induction ℓ generalizing H order with
  | zero => cases order <;> exact hH
  | succ ℓ ih =>
    cases order with
    | nil => exact hH
    | cons i tail =>
      simp only [finiteHistoryCandidates]
      cases hd : finiteDecision (candidateThreshold p H i) (u i)
      · simp only [Bool.false_eq_true, ↓reduceIte]
        exact ih _ (rejectedCandidates_mass_pos p hp H hH i (u i) hd) tail
      · simp only [↓reduceIte]
        exact ih _ (selectedCandidates_mass_pos p hp H hH i (u i) hd) tail

def finiteLawSampler {n : ℕ} (p : FiniteLaw (Finset (Fin n))) (ω : Seed n) :
    Finset (Fin n) :=
  finiteSamplerList p.val Finset.univ (fun i => (ω.2 i : ℝ)) (List.ofFn ω.1)

theorem finiteLawSampler_positive_atom {n : ℕ} (p : FiniteLaw (Finset (Fin n)))
    (ω : Seed n) : 0 < p.val (finiteLawSampler p ω) := by
  obtain ⟨S, _, hpS, he⟩ := finiteSamplerList_positive_atom p.val (law_nonneg p)
    Finset.univ (by simpa [candidateMass, law_sum] using (zero_lt_one : (0 : ℝ) < 1))
    (fun i => (ω.2 i : ℝ)) (List.ofFn ω.1) (List.nodup_ofFn.mpr ω.1.injective)
  have hs : finiteLawSampler p ω = S := by
    simpa [finiteLawSampler, permutation_order_toFinset] using he
  rwa [hs]

theorem finiteLawSampler_card {n k : ℕ} (p : FiniteLaw (Finset (Fin n)))
    (hp : ∀ S, 0 < p.val S → S.card = k) (ω : Seed n) :
    (finiteLawSampler p ω).card = k :=
  hp _ (finiteLawSampler_positive_atom p ω)

theorem continuous_candidateMass (H : Finset (Finset ι)) : Continuous (fun p => candidateMass p H) :=
  continuous_finset_sum H (fun S _ => continuous_apply S)

theorem measurable_candidateThreshold (H : Finset (Finset ι)) (i : ι) :
    Measurable (fun p => candidateThreshold p H i) :=
  (continuous_candidateMass (selectedCandidates H i)).measurable.div
    (continuous_candidateMass H).measurable

theorem measurable_finiteDecision : Measurable (fun z : ℝ × ℝ => finiteDecision z.1 z.2) := by
  have he : (fun z : ℝ × ℝ => finiteDecision z.1 z.2) =
      fun z => if z.1 ≤ 0 then false else if 1 ≤ z.1 then true else
        if z.2 ≤ z.1 then true else false := by
    funext z
    by_cases h0 : z.1 ≤ 0 <;> by_cases h1 : 1 ≤ z.1 <;>
      by_cases hu : z.2 ≤ z.1 <;> simp [finiteDecision, h0, h1, hu]
  rw [he]
  exact Measurable.ite (measurableSet_le measurable_fst measurable_const) measurable_const
    (Measurable.ite (measurableSet_le measurable_const measurable_fst) measurable_const
      (Measurable.ite (measurableSet_le measurable_snd measurable_fst)
        measurable_const measurable_const))

theorem measurable_finiteSamplerList (H : Finset (Finset ι)) (order : List ι) :
    Measurable (fun z : (Finset ι → ℝ) × (ι → ℝ) => finiteSamplerList z.1 H z.2 order) := by
  induction order generalizing H with
  | nil => exact measurable_const
  | cons i tail ih =>
    have hd : Measurable (fun z : (Finset ι → ℝ) × (ι → ℝ) =>
        finiteDecision (candidateThreshold z.1 H i) (z.2 i)) :=
      measurable_finiteDecision.comp
        (((measurable_candidateThreshold H i).comp measurable_fst).prodMk
          ((measurable_pi_apply i).comp measurable_snd))
    change Measurable (fun z : (Finset ι → ℝ) × (ι → ℝ) =>
      if finiteDecision (candidateThreshold z.1 H i) (z.2 i) then
      insert i (finiteSamplerList z.1 (selectedCandidates H i) z.2 tail)
      else finiteSamplerList z.1 (rejectedCandidates H i) z.2 tail)
    exact Measurable.ite (measurableSet_eq_fun hd measurable_const)
      ((measurable_of_finite (fun S : Finset ι => insert i S)).comp (ih _)) (ih _)

theorem measurable_finiteLawSampler {n : ℕ} (p : FiniteLaw (Finset (Fin n))) :
    Measurable (finiteLawSampler p) := by
  apply measurable_from_prod_countable_right
  intro π
  exact (measurable_finiteSamplerList Finset.univ (List.ofFn π)).comp
    (measurable_const.prodMk (measurable_pi_iff.mpr (fun i =>
      measurable_subtype_coe.comp (measurable_pi_apply i))))

end
end CoefficientOne.Sampling
