import CoefficientOne.Sampling.RankSubsetLaw

/-! # Fixed-rank laws as laws on all finite subsets -/

open scoped BigOperators Topology
open EffectiveResistance MeasureTheory Filter

namespace CoefficientOne.Sampling
noncomputable section

variable {ι : Type*} [Fintype ι] [DecidableEq ι] {k : ℕ}

def ambientRankMass (p : FiniteLaw (RankSubset ι k)) (S : Finset ι) : ℝ :=
  if h : S.card = k then p.val ⟨S, h⟩ else 0

theorem ambientRankMass_nonneg (p : FiniteLaw (RankSubset ι k)) (S : Finset ι) :
    0 ≤ ambientRankMass p S := by
  unfold ambientRankMass
  split_ifs
  · exact law_nonneg p _
  · exact le_rfl

theorem sum_ambientRankMass (p : FiniteLaw (RankSubset ι k)) : ∑ S, ambientRankMass p S = 1 := by
  classical
  have he := Fintype.sum_subtype_add_sum_subtype (fun S : Finset ι => S.card = k) (ambientRankMass p)
  have hyes : (∑ S : RankSubset ι k, ambientRankMass p S.val) = 1 := by
    calc
      _ = ∑ S : RankSubset ι k, p.val S := by
        apply Finset.sum_congr rfl
        intro S _
        simp only [ambientRankMass, dif_pos S.property]
      _ = 1 := law_sum p
  have hno : (∑ S : {S : Finset ι // ¬S.card = k}, ambientRankMass p S.val) = 0 := by
    apply Finset.sum_eq_zero
    intro S _
    simp only [ambientRankMass, dif_neg S.property]
  rw [hyes, hno, add_zero] at he
  exact he.symm

def ambientRankLaw (p : FiniteLaw (RankSubset ι k)) : FiniteLaw (Finset ι) :=
  ⟨ambientRankMass p, ⟨ambientRankMass_nonneg p, sum_ambientRankMass p⟩⟩

theorem ambientRankLaw_support (p : FiniteLaw (RankSubset ι k)) (S : Finset ι)
    (hS : 0 < (ambientRankLaw p).val S) : S.card = k := by
  by_contra h
  simpa [ambientRankLaw, ambientRankMass, h] using hS

theorem ambientRankLaw_val_measurePreserving (p : FiniteLaw (RankSubset ι k)) :
    MeasurePreserving (Subtype.val : RankSubset ι k → Finset ι)
      (lawMeasure p) (lawMeasure (ambientRankLaw p)) := by
  classical
  refine ⟨measurable_of_finite _, Measure.ext_of_singleton fun S => ?_⟩
  rw [Measure.map_apply (measurable_of_finite _) (measurableSet_singleton S)]
  by_cases hS : S.card = k
  · have he : (Subtype.val : RankSubset ι k → Finset ι) ⁻¹' {S} = {⟨S, hS⟩} := by
      ext T
      simp only [Set.mem_preimage, Set.mem_singleton_iff, Subtype.ext_iff]
    rw [he, lawMeasure_singleton, lawMeasure_singleton]
    simp [ambientRankLaw, ambientRankMass, hS]
  · have he : (Subtype.val : RankSubset ι k → Finset ι) ⁻¹' {S} = ∅ := by
      ext T
      simp only [Set.mem_preimage, Set.mem_singleton_iff, Set.mem_empty_iff_false, iff_false]
      intro h
      exact hS (h ▸ T.property)
    rw [he, measure_empty, lawMeasure_singleton]
    simp [ambientRankLaw, ambientRankMass, hS]

theorem ambientRankLaw_externalField (w : ι → ℝ) (hw : ∀ i, 0 < w i)
    (hk : k ≤ Fintype.card ι) :
    ambientRankLaw (externalFieldLaw w hw hk) =
      restrictedLaw w hw Finset.univ k (by simpa using hk) := by
  apply Subtype.ext
  funext S
  by_cases hS : S.card = k
  · have h := restrictedMass_univ_rankSubset w k ⟨S, hS⟩
    simpa only [ambientRankLaw, ambientRankMass, dif_pos hS, externalFieldLaw_apply,
      restrictedLaw] using h.symm
  · simp [ambientRankLaw, ambientRankMass, restrictedLaw, restrictedMass,
      Finset.mem_powersetCard, hS]

theorem ambientRankMass_tendsto (p : FiniteLaw (RankSubset ι k))
    (q : ℕ → FiniteLaw (RankSubset ι k))
    (hq : ∀ S, Tendsto (fun j => (q j).val S) atTop (𝓝 (p.val S))) (S : Finset ι) :
    Tendsto (fun j => (ambientRankLaw (q j)).val S) atTop (𝓝 ((ambientRankLaw p).val S)) := by
  by_cases hS : S.card = k
  · simpa only [ambientRankLaw, ambientRankMass, dif_pos hS] using hq ⟨S, hS⟩
  · simpa only [ambientRankLaw, ambientRankMass, dif_neg hS] using
      (tendsto_const_nhds : Tendsto (fun _ : ℕ => (0 : ℝ)) atTop (𝓝 0))

end
end CoefficientOne.Sampling
