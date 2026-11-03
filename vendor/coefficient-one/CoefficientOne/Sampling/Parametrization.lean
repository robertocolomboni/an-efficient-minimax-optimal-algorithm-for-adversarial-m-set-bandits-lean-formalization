import CoefficientOne.Sampling.ParametrizationBijective

/-!
# Smooth normalized parametrization

The inverse function theorem is applied on the zero-sum parameter space. The
global inverse agrees locally with these smooth inverses by injectivity.
-/

open scoped BigOperators Topology
open EffectiveResistance Filter

namespace CoefficientOne.Sampling
noncomputable section

variable (ι : Type*) [Fintype ι] [DecidableEq ι]

def parameterSpace : Submodule ℝ (ι → ℝ) :=
  LinearMap.ker (coordinateDot (fun _ : ι => (1 : ℝ))).toLinearMap

variable {ι} {k : ℕ}

@[simp] theorem mem_parameterSpace (u : ι → ℝ) :
    u ∈ parameterSpace ι ↔ ∑ i, u i = 0 := by
  simp [parameterSpace, LinearMap.mem_ker, coordinateDot_apply]

theorem parameterSpace_sum (u : parameterSpace ι) : ∑ i, u.val i = 0 :=
  (mem_parameterSpace _).mp u.property

variable [Nonempty ι]

def parameterProjectionRaw : (ι → ℝ) →L[ℝ] (ι → ℝ) :=
  ContinuousLinearMap.id ℝ (ι → ℝ) -
    (1 / (Fintype.card ι : ℝ)) •
      (coordinateDot (fun _ : ι => (1 : ℝ))).smulRight (fun _ => (1 : ℝ))

@[simp] theorem parameterProjectionRaw_apply (x : ι → ℝ) (i : ι) :
    parameterProjectionRaw x i = x i - (∑ j, x j) / Fintype.card ι := by
  simp [parameterProjectionRaw, div_eq_mul_inv, mul_comm]

theorem parameterProjectionRaw_mem (x : ι → ℝ) : parameterProjectionRaw x ∈ parameterSpace ι := by
  rw [mem_parameterSpace]
  simp only [parameterProjectionRaw_apply, Finset.sum_sub_distrib, Finset.sum_const,
    Finset.card_univ, nsmul_eq_mul]
  have hn : (Fintype.card ι : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr Fintype.card_ne_zero
  field_simp
  ring

def parameterProjection : (ι → ℝ) →L[ℝ] parameterSpace ι :=
  parameterProjectionRaw.codRestrict (parameterSpace ι) parameterProjectionRaw_mem

@[simp] theorem parameterProjection_apply (x : ι → ℝ) (i : ι) :
    (parameterProjection x).val i = x i - (∑ j, x j) / Fintype.card ι :=
  parameterProjectionRaw_apply x i

@[simp] theorem parameterProjection_coe (u : parameterSpace ι) : parameterProjection u.val = u := by
  apply Subtype.ext
  funext i
  simp [parameterSpace_sum]

def normalizedMean (k : ℕ) (θ : parameterSpace ι) : parameterSpace ι :=
  parameterProjection (exponentialMean k θ.val)

def normalizedMeanDerivative (k : ℕ) (θ : parameterSpace ι) :
    parameterSpace ι →L[ℝ] parameterSpace ι :=
  parameterProjection.comp ((meanDerivative k θ.val).comp (parameterSpace ι).subtypeL)

theorem normalizedMean_contDiff (hk : k ≤ Fintype.card ι) :
    ContDiff ℝ ⊤ (normalizedMean (ι := ι) k) :=
  (parameterProjection (ι := ι)).contDiff.comp
    ((exponentialMean_contDiff hk).comp (parameterSpace ι).subtypeL.contDiff)

theorem normalizedMean_hasFDerivAt (hk : k ≤ Fintype.card ι) (θ : parameterSpace ι) :
    HasFDerivAt (normalizedMean k) (normalizedMeanDerivative k θ) θ :=
  parameterProjection.hasFDerivAt.comp θ
    ((exponentialMean_hasFDerivAt hk θ.val).comp θ (parameterSpace ι).subtypeL.hasFDerivAt)

theorem meanDerivative_sum_zero (hk : k ≤ Fintype.card ι) (θ u : ι → ℝ) :
    ∑ i, meanDerivative k θ u i = 0 := by
  have hcol (j : ι) : ∑ i, covarianceMatrix (fun l => Real.exp (θ l)) k i j = 0 := by
    simpa only [covariance_comm] using covariance_rowSum_zero
      (fun l => Real.exp (θ l)) (fun l => Real.exp_pos (θ l)) hk j
  simp only [meanDerivative_apply hk, Matrix.mulVec, dotProduct]
  rw [Finset.sum_comm]
  simp_rw [← Finset.sum_mul, hcol, zero_mul]
  simp

theorem normalizedMeanDerivative_apply (hk : k ≤ Fintype.card ι)
    (θ u : parameterSpace ι) (i : ι) :
    (normalizedMeanDerivative k θ u).val i = meanDerivative k θ.val u.val i := by
  change (parameterProjection (meanDerivative k θ.val u.val)).val i = _
  simp [meanDerivative_sum_zero hk]

theorem normalizedMeanDerivative_injective
    (hkpos : 1 ≤ k) (hktop : k < Fintype.card ι) (θ : parameterSpace ι) :
    Function.Injective (normalizedMeanDerivative k θ) := by
  intro a b hab
  have hzero : normalizedMeanDerivative k θ (a - b) = 0 := by rw [map_sub, hab, sub_self]
  have heq : a - b = 0 := by
    by_contra hne
    have huneq : (a - b).val ≠ 0 := by intro h; apply hne; exact Subtype.ext h
    have hq := covariance_quadratic_pos_zeroSum hkpos hktop θ.val (a - b).val
      (parameterSpace_sum (a - b)) huneq
    have hmul : (covarianceMatrix (fun i => Real.exp (θ.val i)) k).mulVec (a - b).val = 0 := by
      funext i
      have hh := congrArg (fun z : parameterSpace ι => z.val i) hzero
      rw [normalizedMeanDerivative_apply hktop.le, meanDerivative_apply hktop.le] at hh
      exact hh
    have hfalse : (0 : ℝ) < 0 := by simpa only [quadraticForm, hmul, dotProduct_zero] using hq
    exact lt_irrefl _ hfalse
  exact sub_eq_zero.mp heq

def normalizedMeanDerivativeEquiv
    (hkpos : 1 ≤ k) (hktop : k < Fintype.card ι) (θ : parameterSpace ι) :
    parameterSpace ι ≃L[ℝ] parameterSpace ι :=
  (LinearEquiv.ofBijective (normalizedMeanDerivative k θ).toLinearMap
    ⟨normalizedMeanDerivative_injective hkpos hktop θ,
      LinearMap.injective_iff_surjective.mp (normalizedMeanDerivative_injective hkpos hktop θ)⟩).toContinuousLinearEquiv

@[simp] theorem normalizedMeanDerivativeEquiv_coe
    (hkpos : 1 ≤ k) (hktop : k < Fintype.card ι) (θ : parameterSpace ι) :
    (normalizedMeanDerivativeEquiv hkpos hktop θ : parameterSpace ι →L[ℝ] parameterSpace ι) =
      normalizedMeanDerivative k θ := rfl

theorem normalizedMean_injective (hkpos : 1 ≤ k) (hktop : k < Fintype.card ι) :
    Function.Injective (normalizedMean (ι := ι) k) := by
  intro θ η h
  apply Subtype.ext
  apply exponentialMean_injective_zeroSum hkpos hktop θ.val η.val
    (parameterSpace_sum θ) (parameterSpace_sum η)
  funext i
  have hh := congrArg (fun z : parameterSpace ι => z.val i) h
  change (parameterProjection (exponentialMean k θ.val)).val i =
    (parameterProjection (exponentialMean k η.val)).val i at hh
  simp only [parameterProjection_apply, exponentialMean,
    sum_inclusionMean _ (fun l => Real.exp_pos _) hktop.le] at hh
  change inclusionMean _ k i = inclusionMean _ k i
  linarith

def normalizedParameter (k : ℕ) : parameterSpace ι → parameterSpace ι :=
  Function.invFun (normalizedMean k)

theorem normalizedParameter_mean (hkpos : 1 ≤ k) (hktop : k < Fintype.card ι)
    (θ : parameterSpace ι) : normalizedParameter k (normalizedMean k θ) = θ :=
  Function.leftInverse_invFun (normalizedMean_injective hkpos hktop) θ

theorem normalizedParameter_contDiffAt (hkpos : 1 ≤ k) (hktop : k < Fintype.card ι)
    (θ : parameterSpace ι) :
    ContDiffAt ℝ ⊤ (normalizedParameter k) (normalizedMean k θ) := by
  let e := normalizedMeanDerivativeEquiv hkpos hktop θ
  have hf := (normalizedMean_contDiff hktop.le).contDiffAt (x := θ)
  have hd : HasFDerivAt (normalizedMean k) (e : parameterSpace ι →L[ℝ] parameterSpace ι) θ := by
    simpa only [e, normalizedMeanDerivativeEquiv_coe] using normalizedMean_hasFDerivAt hktop.le θ
  have hlocal := hf.to_localInverse hd (by simp : (⊤ : WithTop ℕ∞) ≠ 0)
  apply hlocal.congr_of_eventuallyEq
  have hright := (hf.hasStrictFDerivAt' hd (by simp)).eventually_right_inverse
  filter_upwards [hright] with y hy
  change normalizedParameter k y = hf.localInverse hd (by simp) y
  calc
    normalizedParameter k y = normalizedParameter k
        (normalizedMean k (hf.localInverse hd (by simp) y)) := congrArg _ hy.symm
    _ = _ := normalizedParameter_mean hkpos hktop _

theorem normalizedMean_parameter_eventually (hkpos : 1 ≤ k) (hktop : k < Fintype.card ι)
    (θ : parameterSpace ι) :
    ∀ᶠ y in 𝓝 (normalizedMean k θ), normalizedMean k (normalizedParameter k y) = y := by
  let e := normalizedMeanDerivativeEquiv hkpos hktop θ
  have hf := (normalizedMean_contDiff hktop.le).contDiffAt (x := θ)
  have hd : HasFDerivAt (normalizedMean k) (e : parameterSpace ι →L[ℝ] parameterSpace ι) θ := by
    simpa only [e, normalizedMeanDerivativeEquiv_coe] using normalizedMean_hasFDerivAt hktop.le θ
  have hright := (hf.hasStrictFDerivAt' hd (by simp)).eventually_right_inverse
  filter_upwards [hright] with y hy
  have hleft : normalizedParameter k y = hf.localInverse hd (by simp) y := by
    calc
      normalizedParameter k y = normalizedParameter k
          (normalizedMean k (hf.localInverse hd (by simp) y)) := congrArg _ hy.symm
      _ = _ := normalizedParameter_mean hkpos hktop _
  rw [hleft]
  exact hy

theorem normalizedParameter_hasFDerivAt (hkpos : 1 ≤ k) (hktop : k < Fintype.card ι)
    (θ : parameterSpace ι) :
    HasFDerivAt (normalizedParameter k)
      ((normalizedMeanDerivativeEquiv hkpos hktop θ).symm :
        parameterSpace ι →L[ℝ] parameterSpace ι) (normalizedMean k θ) := by
  have hd : HasFDerivAt (normalizedMean k)
      (normalizedMeanDerivativeEquiv hkpos hktop θ : parameterSpace ι →L[ℝ] parameterSpace ι)
      (normalizedParameter k (normalizedMean k θ)) := by
    rw [normalizedParameter_mean hkpos hktop, normalizedMeanDerivativeEquiv_coe]
    exact normalizedMean_hasFDerivAt hktop.le θ
  exact hd.of_local_left_inverse (normalizedParameter_contDiffAt hkpos hktop θ).continuousAt
    (normalizedMean_parameter_eventually hkpos hktop θ)

/-- A smooth extension of the normalized parameter off the affine marginal
hyperplane, obtained by projecting onto that hyperplane's tangent space. -/
def parameterOfMarginal (k : ℕ) (x : ι → ℝ) : parameterSpace ι :=
  normalizedParameter k (parameterProjection x)

theorem parameterOfMarginal_mean (hkpos : 1 ≤ k) (hktop : k < Fintype.card ι)
    (x : ι → ℝ) (hx : x ∈ interiorHypersimplex ι k) :
    exponentialMean k (parameterOfMarginal k x).val = x := by
  obtain ⟨θ, hsum, hmean⟩ := exponentialMean_surjective_interior x hx
  let Θ : parameterSpace ι := ⟨θ, (mem_parameterSpace θ).mpr hsum⟩
  have hnorm : parameterProjection x = normalizedMean k Θ := by
    change parameterProjection x = parameterProjection (exponentialMean k θ)
    rw [hmean]
  rw [parameterOfMarginal, hnorm, normalizedParameter_mean hkpos hktop]
  exact hmean

theorem parameterOfMarginal_contDiffAt (hkpos : 1 ≤ k) (hktop : k < Fintype.card ι)
    (x : ι → ℝ) (hx : x ∈ interiorHypersimplex ι k) :
    ContDiffAt ℝ ⊤ (parameterOfMarginal (ι := ι) k) x := by
  have hnorm : normalizedMean k (parameterOfMarginal k x) = parameterProjection x := by
    unfold normalizedMean
    rw [parameterOfMarginal_mean hkpos hktop x hx]
  have hh := normalizedParameter_contDiffAt hkpos hktop (parameterOfMarginal k x)
  rw [hnorm] at hh
  exact hh.comp x (parameterProjection (ι := ι)).contDiff.contDiffAt

theorem parameterOfMarginal_hasFDerivAt (hkpos : 1 ≤ k) (hktop : k < Fintype.card ι)
    (x : ι → ℝ) (hx : x ∈ interiorHypersimplex ι k) :
    HasFDerivAt (parameterOfMarginal (ι := ι) k)
      (((normalizedMeanDerivativeEquiv hkpos hktop (parameterOfMarginal k x)).symm :
        parameterSpace ι →L[ℝ] parameterSpace ι).comp parameterProjection) x := by
  have hnorm : normalizedMean k (parameterOfMarginal k x) = parameterProjection x := by
    unfold normalizedMean
    rw [parameterOfMarginal_mean hkpos hktop x hx]
  have hh := normalizedParameter_hasFDerivAt hkpos hktop (parameterOfMarginal k x)
  rw [hnorm] at hh
  exact hh.comp x parameterProjection.hasFDerivAt

/-- The velocity equation `Σ θ̇ = h` on the tangent hyperplane. -/
theorem parameterOfMarginal_velocity (hkpos : 1 ≤ k) (hktop : k < Fintype.card ι)
    (x h : ι → ℝ) (hx : x ∈ interiorHypersimplex ι k) (hsum : ∑ i, h i = 0) :
    (covarianceMatrix (fun i => Real.exp ((parameterOfMarginal k x).val i)) k).mulVec
      ((fderiv ℝ (parameterOfMarginal k) x h).val) = h := by
  rw [(parameterOfMarginal_hasFDerivAt hkpos hktop x hx).fderiv]
  let e := normalizedMeanDerivativeEquiv hkpos hktop (parameterOfMarginal k x)
  have he := e.apply_symm_apply (parameterProjection h)
  funext i
  have hh := congrArg (fun z : parameterSpace ι => z.val i) he
  change (normalizedMeanDerivative k (parameterOfMarginal k x)
      (e.symm (parameterProjection h))).val i = (parameterProjection h).val i at hh
  rw [normalizedMeanDerivative_apply hktop.le, meanDerivative_apply hktop.le,
    parameterProjection_apply, hsum, zero_div, sub_zero] at hh
  exact hh

theorem maximumEntropyLaw_eq_parameterOfMarginal (hkpos : 1 ≤ k)
    (hktop : k < Fintype.card ι) (x : hypersimplex ι k)
    (hx : ∀ i, 0 < x.val i ∧ x.val i < 1) :
    maximumEntropyLaw x = externalFieldLaw
      (fun i => Real.exp ((parameterOfMarginal k x.val).val i))
      (fun i => Real.exp_pos _) hktop.le := by
  obtain ⟨θ, hsum, hlaw⟩ := maximumEntropyLaw_eq_externalFieldLaw x hx
  have hm : exponentialMean k θ = x.val := by
    have hh := maximumEntropyLaw_mean x
    rw [hlaw] at hh
    exact hh
  have heq := exponentialMean_injective_zeroSum hkpos hktop θ
    (parameterOfMarginal k x.val).val hsum (parameterSpace_sum _)
    (hm.trans (parameterOfMarginal_mean hkpos hktop x.val ⟨hx, x.property.2⟩).symm)
  rw [heq] at hlaw
  exact hlaw

end
end CoefficientOne.Sampling
