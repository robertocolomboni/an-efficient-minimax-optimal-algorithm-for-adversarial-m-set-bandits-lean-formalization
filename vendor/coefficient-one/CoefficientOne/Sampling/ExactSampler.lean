import CoefficientOne.Sampling.RadialSampler

/-! # Exact-cardinality sampler, including both deterministic ranks -/

open MeasureTheory EffectiveResistance

namespace CoefficientOne.Sampling
noncomputable section

variable {n k : ℕ} [NeZero n]

def exactSampler (n k : ℕ) [NeZero n] (x : hypersimplex (Fin n) k) (ω : Seed n) : Finset (Fin n) :=
  if hkzero : k = 0 then ∅
  else if hktop : k = n then Finset.univ
  else boundarySampler (Nat.one_le_iff_ne_zero.mpr hkzero)
    (by have h := rank_le_card_of_mem_hypersimplex x; simp only [Fintype.card_fin] at h; omega) x ω

@[simp] theorem exactSampler_zero (x : hypersimplex (Fin n) 0) (ω : Seed n) :
    exactSampler n 0 x ω = ∅ := by simp [exactSampler]

@[simp] theorem exactSampler_full (x : hypersimplex (Fin n) n) (ω : Seed n) :
    exactSampler n n x ω = Finset.univ := by simp [exactSampler, NeZero.ne n]

theorem exactSampler_nondegenerate (hkpos : 1 ≤ k) (hktop : k < n)
    (x : hypersimplex (Fin n) k) (ω : Seed n) :
    exactSampler n k x ω = boundarySampler hkpos hktop x ω := by
  simp only [exactSampler, dif_neg (show k ≠ 0 by omega), dif_neg (Nat.ne_of_lt hktop)]

theorem exactSampler_card (hk : k ≤ n) (x : hypersimplex (Fin n) k) (ω : Seed n) :
    (exactSampler n k x ω).card = k := by
  by_cases hk0 : k = 0
  · subst k
    simp
  by_cases hkn : k = n
  · subst k
    simp
  have hkpos : 1 ≤ k := by omega
  have hktop : k < n := by omega
  rw [exactSampler_nondegenerate hkpos hktop]
  exact boundarySampler_card hkpos hktop x ω

theorem measurable_exactSampler (hk : k ≤ n) :
    Measurable (fun z : hypersimplex (Fin n) k × Seed n => exactSampler n k z.1 z.2) := by
  by_cases hk0 : k = 0
  · subst k
    simpa only [exactSampler_zero] using (measurable_const :
      Measurable (fun _ : hypersimplex (Fin n) 0 × Seed n => (∅ : Finset (Fin n))))
  by_cases hkn : k = n
  · subst k
    simpa only [exactSampler_full] using (measurable_const :
      Measurable (fun _ : hypersimplex (Fin n) n × Seed n => (Finset.univ : Finset (Fin n))))
  have hkpos : 1 ≤ k := by omega
  have hktop : k < n := by omega
  simpa only [exactSampler_nondegenerate hkpos hktop] using measurable_boundarySampler hkpos hktop

theorem measurable_exactSampler_fixed (hk : k ≤ n) (x : hypersimplex (Fin n) k) :
    Measurable (exactSampler n k x) := by
  have hp : Measurable (fun ω : Seed n => (x, ω)) := measurable_const.prodMk measurable_id
  exact fun s hs => hp (measurable_exactSampler hk hs)

theorem rankSubset_zero_val (S : RankSubset (Fin n) 0) : S.val = ∅ :=
  Finset.card_eq_zero.mp S.property

theorem rankSubset_full_val (S : RankSubset (Fin n) n) : S.val = Finset.univ := by
  apply Finset.eq_univ_of_card
  simpa using S.property

theorem exactSampler_integral_of_interior_stretch (hk : k ≤ n)
    (hinterior : 1 ≤ k → k < n → InteriorStretchSix n k)
    (x : hypersimplex (Fin n) k) (φ : Finset (Fin n) → ℝ) :
    (∫ ω, φ (exactSampler n k x ω) ∂seedMeasure n) =
      lawExpectation (maximumEntropyLaw x) (fun S => φ S.val) := by
  by_cases hk0 : k = 0
  · subst k
    simp only [exactSampler_zero, rankSubset_zero_val]
    rw [lawExpectation_const]
    simp
  by_cases hkn : k = n
  · subst k
    simp only [exactSampler_full, rankSubset_full_val]
    rw [lawExpectation_const]
    simp
  have hkpos : 1 ≤ k := by omega
  have hktop : k < n := by omega
  simp only [exactSampler_nondegenerate hkpos hktop]
  exact boundarySampler_integral_of_interior_stretch hkpos hktop (hinterior hkpos hktop) x φ

theorem exactSampler_map_maximumEntropyLaw_of_interior_stretch (hk : k ≤ n)
    (hinterior : 1 ≤ k → k < n → InteriorStretchSix n k) (x : hypersimplex (Fin n) k) :
    (seedMeasure n).map (exactSampler n k x) =
      (lawMeasure (maximumEntropyLaw x)).map (Subtype.val : RankSubset (Fin n) k → Finset (Fin n)) :=
  sampler_map_law_of_integral (seedMeasure n) _ (measurable_exactSampler_fixed hk x)
    (maximumEntropyLaw x) Subtype.val (exactSampler_integral_of_interior_stretch hk hinterior x)

theorem exactSampler_marginal_of_interior_stretch (hk : k ≤ n)
    (hinterior : 1 ≤ k → k < n → InteriorStretchSix n k)
    (x : hypersimplex (Fin n) k) (i : Fin n) :
    (∫ ω, indicator i (exactSampler n k x ω) ∂seedMeasure n) = x.val i := by
  rw [exactSampler_integral_of_interior_stretch hk hinterior]
  exact congrFun (maximumEntropyLaw_mean x) i

theorem vectorL1_nonneg {ι : Type*} [Fintype ι] (v : ι → ℝ) : 0 ≤ vectorL1 v :=
  Finset.sum_nonneg (fun i _ => abs_nonneg (v i))

theorem exactSampler_stretch_of_interior_stretch (hk : k ≤ n)
    (hinterior : 1 ≤ k → k < n → InteriorStretchSix n k) (x y : hypersimplex (Fin n) k) :
    expectedOutputDistance (seedMeasure n) (exactSampler n k x) (exactSampler n k y) ≤
      6 * vectorL1 (fun i => x.val i - y.val i) := by
  by_cases hk0 : k = 0
  · subst k
    simp only [expectedOutputDistance, exactSampler_zero, outputDistance_self, integral_zero]
    exact mul_nonneg (by norm_num) (vectorL1_nonneg _)
  by_cases hkn : k = n
  · subst k
    simp only [expectedOutputDistance, exactSampler_full, outputDistance_self, integral_zero]
    exact mul_nonneg (by norm_num) (vectorL1_nonneg _)
  have hkpos : 1 ≤ k := by omega
  have hktop : k < n := by omega
  have he (z : hypersimplex (Fin n) k) : exactSampler n k z = boundarySampler hkpos hktop z :=
    funext (exactSampler_nondegenerate hkpos hktop z)
  rw [he x, he y]
  exact boundarySampler_stretch_of_interior_stretch hkpos hktop (hinterior hkpos hktop) x y

end
end CoefficientOne.Sampling
