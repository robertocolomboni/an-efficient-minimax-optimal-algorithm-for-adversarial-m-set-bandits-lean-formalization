import CoefficientOne.Sampling.FiniteLawSequential

/-! # Stability of direct sampling under convergence of finite masses

Only ratios along positive histories are used. A finite family of excluded
threshold ties gives eventual agreement for each fixed limiting law.
-/

open MeasureTheory Filter
open scoped Topology unitInterval

namespace CoefficientOne.Sampling
noncomputable section

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

theorem candidateMass_tendsto (p : Finset ι → ℝ) (q : ℕ → Finset ι → ℝ)
    (hq : ∀ S, Tendsto (fun j => q j S) atTop (𝓝 (p S))) (H : Finset (Finset ι)) :
    Tendsto (fun j => candidateMass (q j) H) atTop (𝓝 (candidateMass p H)) :=
  (continuous_candidateMass H).tendsto p |>.comp (tendsto_pi_nhds.mpr hq)

theorem candidateThreshold_tendsto (p : Finset ι → ℝ) (q : ℕ → Finset ι → ℝ)
    (hq : ∀ S, Tendsto (fun j => q j S) atTop (𝓝 (p S)))
    (H : Finset (Finset ι)) (hH : candidateMass p H ≠ 0) (i : ι) :
    Tendsto (fun j => candidateThreshold (q j) H i) atTop (𝓝 (candidateThreshold p H i)) :=
  (candidateMass_tendsto p q hq (selectedCandidates H i)).div
    (candidateMass_tendsto p q hq H) hH

/-- For a seed that is not the limiting threshold, forced endpoint decisions
are stable as well as decisions with a threshold strictly between zero and one. -/
theorem finiteDecision_eventually_eq (t : ℝ) (s : ℕ → ℝ)
    (hs : Tendsto s atTop (𝓝 t)) (ht : t ∈ Set.Icc (0 : ℝ) 1)
    (u : unitInterval) (hu : (u : ℝ) ≠ t) :
    ∀ᶠ j in atTop, finiteDecision (s j) u = finiteDecision t u := by
  rcases lt_or_gt_of_ne hu with hlt | hgt
  · have ht0 : 0 < t := lt_of_le_of_lt u.property.1 hlt
    have he : finiteDecision t u = true := by
      by_cases h1 : 1 ≤ t <;> simp [finiteDecision, not_le.mpr ht0, h1, hlt.le]
    filter_upwards [hs.eventually_const_lt hlt, hs.eventually_const_lt ht0] with j hj hj0
    rw [he]
    by_cases hj1 : 1 ≤ s j <;> simp [finiteDecision, not_le.mpr hj0, hj1, hj.le]
  · have ht1 : t < 1 := lt_of_lt_of_le hgt u.property.2
    have he : finiteDecision t u = false := by
      by_cases h0 : t ≤ 0 <;> simp [finiteDecision, h0, not_le.mpr ht1, not_le.mpr hgt]
    filter_upwards [hs.eventually_lt_const hgt, hs.eventually_lt_const ht1] with j hj hj1
    rw [he]
    by_cases hj0 : s j ≤ 0 <;>
      simp [finiteDecision, hj0, not_le.mpr hj1, not_le.mpr hj]

/-- Finite induction along the limiting positive histories. -/
theorem finiteSamplerList_eventually_eq (p : Finset ι → ℝ) (hp : ∀ S, 0 ≤ p S)
    (q : ℕ → Finset ι → ℝ)
    (hq : ∀ S, Tendsto (fun j => q j S) atTop (𝓝 (p S)))
    (H : Finset (Finset ι)) (hH : 0 < candidateMass p H) (u : ι → unitInterval)
    (hu : ∀ K i, (u i : ℝ) ≠ candidateThreshold p K i) (order : List ι) :
    ∀ᶠ j in atTop,
      finiteSamplerList (q j) H (fun i => (u i : ℝ)) order =
        finiteSamplerList p H (fun i => (u i : ℝ)) order := by
  induction order generalizing H with
  | nil => exact Filter.Eventually.of_forall fun _ => rfl
  | cons i tail ih =>
    have hd := finiteDecision_eventually_eq (candidateThreshold p H i)
      (fun j => candidateThreshold (q j) H i)
      (candidateThreshold_tendsto p q hq H hH.ne' i)
      (candidateThreshold_mem_Icc p hp H hH i) (u i) (hu H i)
    cases hdec : finiteDecision (candidateThreshold p H i) (u i) with
    | false =>
      have htail := ih (rejectedCandidates H i)
        (rejectedCandidates_mass_pos p hp H hH i (u i) hdec)
      filter_upwards [hd, htail] with j hj he
      simp only [finiteSamplerList, hj, hdec, Bool.false_eq_true, ↓reduceIte, he]
    | true =>
      have htail := ih (selectedCandidates H i)
        (selectedCandidates_mass_pos p hp H hH i (u i) hdec)
      filter_upwards [hd, htail] with j hj he
      simp only [finiteSamplerList, hj, hdec, ↓reduceIte, he]

/-- For each fixed limiting law, the direct common-seed samplers eventually
agree almost surely. This does not assert one common null set for all laws. -/
theorem finiteLawSampler_ae_eventually_eq {n : ℕ}
    (p : FiniteLaw (Finset (Fin n))) (q : ℕ → FiniteLaw (Finset (Fin n)))
    (hq : ∀ S, Tendsto (fun j => (q j).val S) atTop (𝓝 (p.val S))) :
    ∀ᵐ ω ∂seedMeasure n, ∀ᶠ j in atTop, finiteLawSampler (q j) ω = finiteLawSampler p ω := by
  have ht := seedUniform_finite_thresholds_ne_ae n
    (fun H : Finset (Finset (Fin n)) => fun i => candidateThreshold p.val H i)
  filter_upwards [ht] with ω hω
  exact finiteSamplerList_eventually_eq p.val (law_nonneg p) (fun j => (q j).val) hq
    Finset.univ (by simp [candidateMass, law_sum]) ω.2 hω (List.ofFn ω.1)

end
end CoefficientOne.Sampling
