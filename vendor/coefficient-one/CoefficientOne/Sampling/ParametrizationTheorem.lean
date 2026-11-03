import CoefficientOne.Sampling.RadialContinuity

/-!
# Complete maximum-entropy parametrization interface

The law is the actual entropy maximizer on the fixed-rank finite sample space.
The gauge, covariance kernel and path-velocity assertions are made explicit.
-/

open scoped BigOperators Topology
open EffectiveResistance Filter

namespace CoefficientOne.Sampling
noncomputable section

variable {ι : Type*} [Fintype ι] [DecidableEq ι] {k : ℕ}

theorem subsetProbability_exp_add_const (θ : ι → ℝ) (c : ℝ) (S : RankSubset ι k) :
    subsetProbability (fun i => Real.exp (θ i + c)) k S =
      subsetProbability (fun i => Real.exp (θ i)) k S := by
  have hw (T : RankSubset ι k) :
      subsetWeight (fun i => Real.exp (θ i + c)) T.val =
      Real.exp ((k : ℝ) * c) * subsetWeight (fun i => Real.exp (θ i)) T.val := by
    rw [subsetWeight_exp, subsetWeight_exp, Finset.sum_add_distrib]
    simp only [Finset.sum_const, nsmul_eq_mul, T.property, Real.exp_add]
    ring
  have hZ : elementarySum (fun i => Real.exp (θ i + c)) k =
      Real.exp ((k : ℝ) * c) * elementarySum (fun i => Real.exp (θ i)) k := by
    simp only [elementarySum, hw, Finset.mul_sum]
  rw [subsetProbability, subsetProbability, hw, hZ]
  exact mul_div_mul_left _ _ (Real.exp_ne_zero _)

theorem exponentialMean_add_const (θ : ι → ℝ) (c : ℝ) :
    exponentialMean k (fun i => θ i + c) = exponentialMean k θ := by
  funext i
  simp only [exponentialMean, inclusionMean, expectation, subsetProbability_exp_add_const]

variable [Nonempty ι]

theorem exponentialMean_parameterProjection (θ : ι → ℝ) :
    exponentialMean k (parameterProjection θ).val = exponentialMean k θ := by
  have heq : (parameterProjection θ).val = fun i => θ i + (-(∑ j, θ j) / Fintype.card ι) := by
    funext i
    simp [sub_eq_add_neg, neg_div]
  rw [heq, exponentialMean_add_const]

theorem exponentialMean_eq_iff_add_constant (hkpos : 1 ≤ k) (hktop : k < Fintype.card ι)
    (θ η : ι → ℝ) :
    exponentialMean k θ = exponentialMean k η ↔ ∃ c : ℝ, ∀ i, θ i = η i + c := by
  constructor
  · intro hm
    have heq := exponentialMean_injective_zeroSum hkpos hktop
      (parameterProjection θ).val (parameterProjection η).val
      (parameterSpace_sum _) (parameterSpace_sum _)
      (by simpa only [exponentialMean_parameterProjection] using hm)
    refine ⟨(∑ i, θ i) / Fintype.card ι - (∑ i, η i) / Fintype.card ι, ?_⟩
    intro i
    have hh := congrFun heq i
    simp only [parameterProjection_apply] at hh
    linarith
  · rintro ⟨c, hc⟩
    have heq : θ = fun i => η i + c := funext hc
    rw [heq, exponentialMean_add_const]

theorem covariance_kernel_eq_span_one (hkpos : 1 ≤ k) (hktop : k < Fintype.card ι)
    (θ u : ι → ℝ) :
    (covarianceMatrix (fun i => Real.exp (θ i)) k).mulVec u = 0 ↔
      u ∈ Submodule.span ℝ {fun _ : ι => (1 : ℝ)} := by
  rw [covariance_mulVec_eq_zero_iff_constant hkpos hktop]
  constructor
  · intro hc
    let i : ι := Classical.choice inferInstance
    apply Submodule.mem_span_singleton.mpr
    refine ⟨u i, ?_⟩
    funext j
    simpa using hc i j
  · intro hu
    obtain ⟨c, hc⟩ := Submodule.mem_span_singleton.mp hu
    rw [← hc]
    simp

theorem maximumEntropyLaw_covariance_kernel (hkpos : 1 ≤ k) (hktop : k < Fintype.card ι)
    (x : hypersimplex ι k) (hx : ∀ i, 0 < x.val i ∧ x.val i < 1) (u : ι → ℝ) :
    (lawCovariance (maximumEntropyLaw x)).mulVec u = 0 ↔
      u ∈ Submodule.span ℝ {fun _ : ι => (1 : ℝ)} := by
  rw [maximumEntropyLaw_eq_parameterOfMarginal hkpos hktop x hx, externalFieldLaw_covariance]
  exact covariance_kernel_eq_span_one hkpos hktop _ u

theorem maximumEntropyLaw_explicit (hkpos : 1 ≤ k) (hktop : k < Fintype.card ι)
    (x : hypersimplex ι k) (hx : ∀ i, 0 < x.val i ∧ x.val i < 1) (S : RankSubset ι k) :
    (maximumEntropyLaw x).val S =
      Real.exp (∑ i ∈ S.val, (parameterOfMarginal k x.val).val i) /
        (∑ T : RankSubset ι k, Real.exp (∑ i ∈ T.val, (parameterOfMarginal k x.val).val i)) := by
  rw [maximumEntropyLaw_eq_parameterOfMarginal hkpos hktop x hx]
  simp only [externalFieldLaw_apply, subsetProbability, elementarySum, subsetWeight_exp]

theorem exponentialMean_integral_identity (hk : k ≤ Fintype.card ι) (θ u : ι → ℝ) :
    coordinateDot u (exponentialMean k (θ + u) - exponentialMean k θ) =
      ∫ t : ℝ in (0 : ℝ)..1,
        quadraticForm (covarianceMatrix (fun i => Real.exp ((θ + t • u) i)) k) u := by
  let f : ℝ → ℝ := fun t => coordinateDot u (exponentialMean k (θ + t • u))
  have hf : ContDiff ℝ ⊤ f := by
    exact (coordinateDot u).contDiff.comp ((exponentialMean_contDiff hk).comp
      (contDiff_const.add (contDiff_id.smul contDiff_const)))
  have hder (t : ℝ) := exponentialMean_line_derivative hk θ u t
  have heq : deriv f = fun t =>
      quadraticForm (covarianceMatrix (fun i => Real.exp ((θ + t • u) i)) k) u := by
    funext t
    exact (hder t).deriv
  have hint : IntervalIntegrable (fun t : ℝ =>
      quadraticForm (covarianceMatrix (fun i => Real.exp ((θ + t • u) i)) k) u)
      MeasureTheory.volume 0 1 := by
    rw [← heq]
    exact (hf.continuous_deriv (by simp)).intervalIntegrable 0 1
  have hh := intervalIntegral.integral_eq_sub_of_hasDerivAt (fun t _ => hder t) hint
  simpa only [zero_smul, add_zero, one_smul, map_sub] using hh.symm

theorem parameterOfMarginal_path_velocity (hkpos : 1 ≤ k) (hktop : k < Fintype.card ι)
    (x : ℝ → ι → ℝ) (v : ι → ℝ) (hxd : HasDerivAt x v 0)
    (hx : ∀ᶠ t in 𝓝 (0 : ℝ), x t ∈ interiorHypersimplex ι k) :
    v = (covarianceMatrix (fun i => Real.exp ((parameterOfMarginal k (x 0)).val i)) k).mulVec
      (deriv (fun t : ℝ => (parameterOfMarginal k (x t)).val) 0) := by
  have hx0 : x 0 ∈ interiorHypersimplex ι k := hx.self_of_nhds
  have hp := (parameterOfMarginal_hasFDerivAt hkpos hktop (x 0) hx0).comp_hasDerivAt 0 hxd
  have hparam := (parameterSpace ι).subtypeL.hasFDerivAt.comp_hasDerivAt 0 hp
  have hm := (exponentialMean_hasFDerivAt hktop.le
    (parameterOfMarginal k (x 0)).val).comp_hasDerivAt 0 hparam
  have heq : (fun t : ℝ => exponentialMean k (parameterOfMarginal k (x t)).val) =ᶠ[𝓝 0] x := by
    filter_upwards [hx] with t ht
    exact parameterOfMarginal_mean hkpos hktop (x t) ht
  have hm' := hm.congr_of_eventuallyEq heq.symm
  have huniq := hxd.unique hm'
  have hparamDeriv := hparam.deriv
  change deriv (fun t : ℝ => (parameterOfMarginal k (x t)).val) 0 = _ at hparamDeriv
  rw [hparamDeriv]
  conv_lhs => rw [huniq]
  funext i
  exact meanDerivative_apply hktop.le _ _ i

end
end CoefficientOne.Sampling
