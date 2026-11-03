import CoefficientOne.Sampling.MaximumEntropy
import CoefficientOne.Sampling.FiniteLawMeasure

/-!
# Entropy stationarity and the finite exponential family

Full support permits two-sided perturbations in the kernel of the normalization
and marginal constraints. Stationarity then places the log masses in their row
span, as in Appendix E.2.
-/

open scoped BigOperators Topology
open EffectiveResistance Filter

namespace CoefficientOne.Sampling

noncomputable section

variable {ι : Type*} [Fintype ι] [DecidableEq ι] {k : ℕ}

theorem maximumEntropy_stationary (x : hypersimplex ι k)
    (hx : ∀ i, 0 < x.val i ∧ x.val i < 1)
    (z : RankSubset ι k → ℝ) (hzsum : ∑ S, z S = 0)
    (hzmean : massMeanLinear z = 0) :
    ∑ S, (-Real.log ((maximumEntropyLaw x).val S) - 1) * z S = 0 := by
  let p := (maximumEntropyLaw x).val
  have hp : p ∈ marginalFiber x.val := (maximumEntropyMass_spec x).1
  have hppos : ∀ S, 0 < p S := maximumEntropyLaw_fullSupport x hx
  have hevent : ∀ᶠ t : ℝ in 𝓝 0, ∀ S, 0 < p S + t * z S := by
    apply eventually_all.2
    intro S
    have hlim : Tendsto (fun t : ℝ => p S + t * z S) (𝓝 0) (𝓝 (p S)) := by
      have hc : Continuous (fun t : ℝ => p S + t * z S) :=
        continuous_const.add (continuous_id.mul continuous_const)
      simpa only [zero_mul, add_zero] using hc.tendsto 0
    exact hlim.eventually (Ioi_mem_nhds (hppos S))
  have hlocal : IsLocalMax (fun t : ℝ => finiteEntropy (p + t • z)) 0 := by
    filter_upwards [hevent] with t ht
    have hmem : p + t • z ∈ marginalFiber x.val := by
      refine ⟨⟨fun S => (ht S).le, ?_⟩, ?_⟩
      · simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, Finset.sum_add_distrib,
          ← Finset.mul_sum, hp.1.2, hzsum, mul_zero, add_zero]
      · simp only [map_add, map_smul, hp.2, hzmean, smul_zero, add_zero]
    change finiteEntropy (p + t • z) ≤ finiteEntropy (p + 0 • z)
    rw [zero_smul, add_zero]
    exact (maximumEntropyMass_spec x).2 hmem
  have hderiv : HasDerivAt (fun t : ℝ => finiteEntropy (p + t • z))
      (∑ S, (-Real.log (p S) - 1) * z S) 0 := by
    unfold finiteEntropy
    apply HasDerivAt.fun_sum
    intro S _
    have hd : HasDerivAt (fun t : ℝ => p S + t * z S) (z S) 0 := by
      convert (hasDerivAt_const (0 : ℝ) (p S)).add
        ((hasDerivAt_id 0).mul_const (z S)) using 1 <;> first | rfl | simp
    have hout := Real.hasDerivAt_negMulLog (hppos S).ne'
    have hout' : HasDerivAt Real.negMulLog (-Real.log (p S) - 1) (p S + 0 * z S) := by
      simpa only [zero_mul, add_zero] using hout
    convert hout'.comp 0 hd using 1 <;> rfl
  exact hlocal.hasDerivAt_eq_zero hderiv

/-- All affine constraints collected in one finite-dimensional linear map. -/
def marginalConstraints : (RankSubset ι k → ℝ) →ₗ[ℝ] (Option ι → ℝ) where
  toFun p a := match a with
    | none => ∑ S, p S
    | some i => massMeanLinear p i
  map_add' p q := by
    ext a; cases a <;> simp [Finset.sum_add_distrib, add_mul]
  map_smul' c p := by
    ext a; cases a <;> simp [Finset.mul_sum, mul_assoc]

/-- The derivative of entropy at the actual maximizing mass vector. -/
def entropyGradient (x : hypersimplex ι k) : (RankSubset ι k → ℝ) →ₗ[ℝ] ℝ where
  toFun z := ∑ S, (-Real.log ((maximumEntropyLaw x).val S) - 1) * z S
  map_add' z w := by simp [mul_add, Finset.sum_add_distrib]
  map_smul' c z := by simp [Finset.mul_sum, mul_left_comm]

theorem entropyGradient_in_constraint_rowSpan (x : hypersimplex ι k)
    (hx : ∀ i, 0 < x.val i ∧ x.val i < 1) :
    ∃ β : (Option ι → ℝ) →ₗ[ℝ] ℝ,
      β.comp marginalConstraints = entropyGradient x := by
  have hmem : entropyGradient x ∈
      (LinearMap.ker (marginalConstraints (ι := ι) (k := k))).dualAnnihilator := by
    rw [Submodule.mem_dualAnnihilator]
    intro z hz
    have hzero : marginalConstraints z = 0 := hz
    have hsum : ∑ S, z S = 0 := congrFun hzero none
    have hmean : massMeanLinear z = 0 := by
      ext i
      exact congrFun hzero (some i)
    exact maximumEntropy_stationary x hx z hsum hmean
  rw [← LinearMap.range_dualMap_eq_dualAnnihilator_ker] at hmem
  exact hmem

theorem linearFunctional_eq_coordinate_sum {α : Type*} [Fintype α] [DecidableEq α]
    (β : (α → ℝ) →ₗ[ℝ] ℝ) (v : α → ℝ) :
    β v = ∑ a, v a * β (Pi.single a 1) := by
  conv_lhs => rw [← Finset.univ_sum_single v]
  rw [map_sum]
  apply Finset.sum_congr rfl
  intro a _
  have h : Pi.single a (v a) = v a • Pi.single a (1 : ℝ) := by
    ext b
    by_cases hb : b = a
    · subst b; simp
    · simp [Pi.single_eq_of_ne hb]
  rw [h, map_smul, smul_eq_mul]

@[simp] theorem marginalConstraints_single_none (S : RankSubset ι k) :
    marginalConstraints (Pi.single S 1) none = 1 := by
  simp [marginalConstraints, Pi.single_apply]

@[simp] theorem marginalConstraints_single_some (S : RankSubset ι k) (i : ι) :
    marginalConstraints (Pi.single S 1) (some i) = indicator i S.val := by
  simp [marginalConstraints, Pi.single_apply]

theorem maximumEntropy_log_affine (x : hypersimplex ι k)
    (hx : ∀ i, 0 < x.val i ∧ x.val i < 1) :
    ∃ (c : ℝ) (θ : ι → ℝ), ∀ S : RankSubset ι k,
      Real.log ((maximumEntropyLaw x).val S) = c + ∑ i ∈ S.val, θ i := by
  obtain ⟨β, hβ⟩ := entropyGradient_in_constraint_rowSpan x hx
  refine ⟨-1 - β (Pi.single none 1), fun i => -β (Pi.single (some i) 1), ?_⟩
  intro S
  have hb := congrArg (fun f : (RankSubset ι k → ℝ) →ₗ[ℝ] ℝ => f (Pi.single S 1)) hβ
  simp only [LinearMap.comp_apply] at hb
  rw [linearFunctional_eq_coordinate_sum] at hb
  simp [entropyGradient, indicator, Fintype.sum_option, Pi.single_apply] at hb
  simp only [Finset.sum_neg_distrib]
  linarith

theorem maximumEntropy_log_affine_zeroSum (x : hypersimplex ι k)
    (hx : ∀ i, 0 < x.val i ∧ x.val i < 1) :
    ∃ (c : ℝ) (θ : ι → ℝ), (∑ i, θ i = 0) ∧ ∀ S : RankSubset ι k,
      Real.log ((maximumEntropyLaw x).val S) = c + ∑ i ∈ S.val, θ i := by
  obtain ⟨c, θ, hθ⟩ := maximumEntropy_log_affine x hx
  let b : ℝ := (∑ i, θ i) / Fintype.card ι
  refine ⟨c + k * b, fun i => θ i - b, ?_, ?_⟩
  · by_cases hn : Fintype.card ι = 0
    · haveI : IsEmpty ι := Fintype.card_eq_zero_iff.mp hn
      simp
    · have hn' : (Fintype.card ι : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr hn
      simp only [Finset.sum_sub_distrib, Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
      dsimp [b]
      field_simp
      ring
  · intro S
    rw [hθ S, Finset.sum_sub_distrib]
    simp only [Finset.sum_const, nsmul_eq_mul, S.property]
    ring

theorem subsetWeight_exp (θ : ι → ℝ) (S : Finset ι) :
    subsetWeight (fun i => Real.exp (θ i)) S = Real.exp (∑ i ∈ S, θ i) := by
  simp [subsetWeight, Real.exp_sum]

/-- The actual entropy maximizer is an external-field law, with the additive
gauge fixed by requiring the parameter sum to vanish. -/
theorem maximumEntropy_exponential (x : hypersimplex ι k)
    (hx : ∀ i, 0 < x.val i ∧ x.val i < 1) :
    ∃ θ : ι → ℝ, (∑ i, θ i = 0) ∧ ∀ S : RankSubset ι k,
      (maximumEntropyLaw x).val S = subsetProbability (fun i => Real.exp (θ i)) k S := by
  obtain ⟨c, θ, hsum, hlog⟩ := maximumEntropy_log_affine_zeroSum x hx
  refine ⟨θ, hsum, ?_⟩
  have hp (S : RankSubset ι k) : (maximumEntropyLaw x).val S =
      Real.exp c * subsetWeight (fun i => Real.exp (θ i)) S.val := by
    rw [subsetWeight_exp, ← Real.exp_add, ← hlog S,
      Real.exp_log (maximumEntropyLaw_fullSupport x hx S)]
  have hZ : Real.exp c * elementarySum (fun i => Real.exp (θ i)) k = 1 := by
    rw [elementarySum, Finset.mul_sum]
    simpa only [← hp] using law_sum (maximumEntropyLaw x)
  have hZne : elementarySum (fun i => Real.exp (θ i)) k ≠ 0 := by
    intro hzero
    rw [hzero, mul_zero] at hZ
    norm_num at hZ
  intro S
  rw [hp, subsetProbability, eq_div_iff hZne]
  nlinarith [congrArg (fun r : ℝ =>
    r * subsetWeight (fun i => Real.exp (θ i)) S.val) hZ]

theorem rank_le_card_of_mem_hypersimplex (x : hypersimplex ι k) :
    k ≤ Fintype.card ι := by
  have h : (k : ℝ) ≤ (Fintype.card ι : ℝ) := calc
    (k : ℝ) = ∑ i, x.val i := x.property.2.symm
    _ ≤ ∑ _ : ι, (1 : ℝ) := Finset.sum_le_sum fun i _ => (x.property.1 i).2
    _ = Fintype.card ι := by simp
  exact_mod_cast h

theorem maximumEntropyLaw_eq_externalFieldLaw (x : hypersimplex ι k)
    (hx : ∀ i, 0 < x.val i ∧ x.val i < 1) :
    ∃ θ : ι → ℝ, (∑ i, θ i = 0) ∧ maximumEntropyLaw x =
      externalFieldLaw (fun i => Real.exp (θ i)) (fun i => Real.exp_pos (θ i))
        (rank_le_card_of_mem_hypersimplex x) := by
  obtain ⟨θ, hsum, hp⟩ := maximumEntropy_exponential x hx
  refine ⟨θ, hsum, ?_⟩
  apply Subtype.ext
  funext S
  exact hp S

end
end CoefficientOne.Sampling
