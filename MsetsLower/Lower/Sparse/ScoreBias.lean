import MsetsLower.Lower.Sparse.JointLikelihood
import MsetsLower.Lower.Dense.Assouad
import Mathlib.Probability.Kernel.Composition.IntegralCompProd

/-!
# Conditional sign comparison for the sparse learner-score bias

This file formalizes the information-theoretic core of
`eq:lower-score-bias`.  The policy remains arbitrary and adaptive.  We first
identify its exact one-round conditional KL as an integral of the scalar
feedback KL, telescope this identity, and then prove the conditional sign
estimate used for every block--coordinate pair in the manuscript.
-/

namespace MsetsLower.Lower.Sparse

open MsetsLower Feedback Set
open MeasureTheory ProbabilityTheory InformationTheory
open MsetsLower.Probability
open scoped BigOperators ENNReal ProbabilityTheory

noncomputable section

/-! ## A sharp bounded-observable form of the TV dual estimate -/

/-- For a `[0,M]`-valued observable the expectation gap is bounded by
`M * TV`.  This is obtained from the project's internally proved symmetric
TV dual estimate by centering at `M/2`; no external duality theorem is used. -/
theorem abs_integral_sub_integral_le_mul_totalVariationDistance_of_mem_Icc
    {Omega : Type*} [MeasurableSpace Omega]
    (mu nu : Measure Omega) [IsProbabilityMeasure mu] [IsProbabilityMeasure nu]
    {V : Omega -> Real} {M : Real}
    (_hM : 0 <= M) (hV : Measurable V)
    (hVM : forall omega, V omega ∈ Icc (0 : Real) M) :
    |(∫ omega, V omega ∂mu) - ∫ omega, V omega ∂nu| <=
      M * totalVariationDistance mu nu := by
  let centered : Omega -> Real := fun omega => V omega - M / 2
  have hcentered : Measurable centered := hV.sub measurable_const
  have hbound : forall omega, |centered omega| <= M / 2 := by
    intro omega
    dsimp [centered]
    rw [abs_le]
    constructor <;> linarith [(hVM omega).1, (hVM omega).2]
  have hdual :=
    abs_integral_sub_integral_le_two_mul_totalVariationDistance
      mu nu hcentered hbound
  have hVmu : Integrable V mu :=
    Integrable.of_bound hV.aestronglyMeasurable M
      (ae_of_all mu fun omega => by
        rw [Real.norm_eq_abs, abs_of_nonneg (hVM omega).1]
        exact (hVM omega).2)
  have hVnu : Integrable V nu :=
    Integrable.of_bound hV.aestronglyMeasurable M
      (ae_of_all nu fun omega => by
        rw [Real.norm_eq_abs, abs_of_nonneg (hVM omega).1]
        exact (hVM omega).2)
  have hcenterMu :
      (∫ omega, centered omega ∂mu) = (∫ omega, V omega ∂mu) - M / 2 := by
    rw [integral_sub hVmu (integrable_const _), integral_const, probReal_univ]
    simp [smul_eq_mul]
  have hcenterNu :
      (∫ omega, centered omega ∂nu) = (∫ omega, V omega ∂nu) - M / 2 := by
    rw [integral_sub hVnu (integrable_const _), integral_const, probReal_univ]
    simp [smul_eq_mul]
  rw [hcenterMu, hcenterNu] at hdual
  convert hdual using 1 <;> ring_nf

/-! ## Exact conditional KL for the adaptive scalar-feedback process -/

/-- The common history--action law followed by two parameterized feedback
kernels has KL equal to the average scalar-feedback KL. -/
theorem klDiv_sparseParamTwoStage_eq_lintegral
    {Omega : Type*} [MeasurableSpace Omega]
    (mu : Measure Omega) [IsProbabilityMeasure mu]
    (u v : Omega -> Real) (hu : Measurable u) (hv : Measurable v)
    (hub : forall omega, |u omega| <= (1 : Real) / 16)
    (hvb : forall omega, |v omega| <= (1 : Real) / 16) :
    klDiv (mu ⊗ₘ sparseParamFeedbackKernel u)
        (mu ⊗ₘ sparseParamFeedbackKernel v) =
      ∫⁻ omega, klDiv (feedbackDensityMeasure (u omega))
        (feedbackDensityMeasure (v omega)) ∂mu := by
  let Ku := sparseParamFeedbackKernel u
  let Kv := sparseParamFeedbackKernel v
  letI : IsMarkovKernel Ku := sparseParamFeedbackKernel_isMarkov u hu hub
  letI : IsMarkovKernel Kv := sparseParamFeedbackKernel_isMarkov v hv hvb
  let ratio : Omega × Real -> ENNReal := fun oy =>
    feedbackDensityRatio (u oy.1) (v oy.1) oy.2
  have hratio : Measurable ratio := measurable_feedbackDensityRatio_joint.comp <|
    ((hu.comp measurable_fst).prodMk (hv.comp measurable_fst)).prodMk
      measurable_snd
  have hwith : mu ⊗ₘ Ku = (mu ⊗ₘ Kv).withDensity ratio := by
    apply MsetsLower.Lower.Dense.compProd_eq_withDensity_of_apply mu Ku Kv
      (fun omega y => feedbackDensityRatio (u omega) (v omega) y) hratio
    intro omega
    rw [show Ku omega = feedbackDensityMeasure (u omega) by
        exact sparseParamFeedbackKernel_apply u hu omega (hub omega),
      show Kv omega = feedbackDensityMeasure (v omega) by
        exact sparseParamFeedbackKernel_apply v hv omega (hvb omega)]
    exact feedbackDensityMeasure_withDensity_ratio (hub omega) (hvb omega)
  letI : IsFiniteMeasure ((mu ⊗ₘ Kv).withDensity ratio) := by
    rw [<- hwith]
    infer_instance
  calc
    klDiv (mu ⊗ₘ Ku) (mu ⊗ₘ Kv) =
        klDiv ((mu ⊗ₘ Kv).withDensity ratio) (mu ⊗ₘ Kv) := by rw [hwith]
    _ = ∫⁻ oy, ENNReal.ofReal (klFun (ratio oy).toReal) ∂(mu ⊗ₘ Kv) :=
      MsetsLower.Lower.Dense.klDiv_withDensity_eq_lintegral_klFun
        (mu ⊗ₘ Kv) ratio hratio
    _ = ∫⁻ omega, ∫⁻ y,
        ENNReal.ofReal
          (klFun (feedbackDensityRatio (u omega) (v omega) y).toReal)
          ∂Kv omega ∂mu := by
      rw [Measure.lintegral_compProd (by fun_prop)]
    _ = ∫⁻ omega, klDiv (feedbackDensityMeasure (u omega))
          (feedbackDensityMeasure (v omega)) ∂mu := by
      apply lintegral_congr
      intro omega
      letI : IsProbabilityMeasure (feedbackDensityMeasure (u omega)) :=
        ⟨feedbackDensityMeasure_apply_univ (hub omega)⟩
      letI : IsProbabilityMeasure (feedbackDensityMeasure (v omega)) :=
        ⟨feedbackDensityMeasure_apply_univ (hvb omega)⟩
      rw [show Kv omega = feedbackDensityMeasure (v omega) by
        exact sparseParamFeedbackKernel_apply v hv omega (hvb omega)]
      have hfinite : IsFiniteMeasure
          ((feedbackDensityMeasure (v omega)).withDensity
            (feedbackDensityRatio (u omega) (v omega))) := by
        rw [<- feedbackDensityMeasure_withDensity_ratio
          (hub omega) (hvb omega)]
        infer_instance
      symm
      rw [feedbackDensityMeasure_withDensity_ratio
        (hub omega) (hvb omega)]
      exact MsetsLower.Lower.Dense.klDiv_withDensity_eq_lintegral_klFun
        (feedbackDensityMeasure (v omega))
        (feedbackDensityRatio (u omega) (v omega))
        (measurable_feedbackDensityRatio (u omega) (v omega))

/-- Exact one-round KL identity under the actual prefix law and the
arbitrary history-measurable policy. -/
theorem sparseAdaptive_roundKL_eq_lintegral
    {n k : Nat} (P : Policy n k)
    (V W : SparseAdaptiveParameters n k) (t : Nat) :
    (sparseAdaptiveProcess P V).roundKL (sparseAdaptiveProcess P W) t =
      ∫⁻ ha, klDiv
          (feedbackDensityMeasure (V.value t ha.1 ha.2))
          (feedbackDensityMeasure (W.value t ha.1 ha.2))
        ∂((sparseAdaptiveProcess P V).law t ⊗ₘ P.kernel t) := by
  letI : IsMarkovKernel (sparseAdaptiveRoundKernel P V t) :=
    sparseAdaptiveRoundKernel_isMarkov P V t
  letI : IsMarkovKernel (sparseAdaptiveRoundKernel P W t) :=
    sparseAdaptiveRoundKernel_isMarkov P W t
  letI : IsProbabilityMeasure
      ((sparseAdaptiveProcess P V).law t ⊗ₘ
        sparseAdaptiveRoundKernel P V t) := by infer_instance
  letI : IsProbabilityMeasure
      ((sparseAdaptiveProcess P V).law t ⊗ₘ
        sparseAdaptiveRoundKernel P W t) := by infer_instance
  unfold HistoryKernelProcess.roundKL
  change klDiv
      ((sparseAdaptiveProcess P V).law t ⊗ₘ
        sparseAdaptiveRoundKernel P V t)
      ((sparseAdaptiveProcess P V).law t ⊗ₘ
        sparseAdaptiveRoundKernel P W t) = _
  have hmap := MsetsLower.Lower.Dense.klDiv_map_measurableEmbedding
    MeasurableEquiv.prodAssoc.symm.measurableEmbedding
    ((sparseAdaptiveProcess P V).law t ⊗ₘ sparseAdaptiveRoundKernel P V t)
    ((sparseAdaptiveProcess P V).law t ⊗ₘ sparseAdaptiveRoundKernel P W t)
  rw [<- hmap]
  unfold sparseAdaptiveRoundKernel
  simp only [Measure.compProd_assoc]
  exact klDiv_sparseParamTwoStage_eq_lintegral
    ((sparseAdaptiveProcess P V).law t ⊗ₘ P.kernel t)
    (fun ha => V.value t ha.1 ha.2)
    (fun ha => W.value t ha.1 ha.2)
    (V.measurable_value t) (W.measurable_value t)
    (fun ha => V.abs_le t ha.1 ha.2)
    (fun ha => W.abs_le t ha.1 ha.2)

/-- Squared feedback-parameter displacement, as an ENNReal predictable
energy. -/
def sparseParameterEnergy {n k : Nat}
    (V W : SparseAdaptiveParameters n k) (t : Nat)
    (ha : History n k t × MSetAction n k) : ENNReal :=
  ENNReal.ofReal ((V.value t ha.1 ha.2 - W.value t ha.1 ha.2) ^ 2)

theorem measurable_sparseParameterEnergy
    {n k : Nat} (V W : SparseAdaptiveParameters n k) (t : Nat) :
    Measurable (sparseParameterEnergy V W t) := by
  exact Measurable.ennreal_ofReal
    ((V.measurable_value t).sub (W.measurable_value t) |>.pow_const 2)

/-- One adaptive round costs at most `128` times its actual predictable
parameter energy. -/
theorem sparseAdaptive_roundKL_le_parameterEnergy
    {n k : Nat} (P : Policy n k)
    (V W : SparseAdaptiveParameters n k) (t : Nat) :
    (sparseAdaptiveProcess P V).roundKL (sparseAdaptiveProcess P W) t <=
      ENNReal.ofReal 128 *
        ∫⁻ ha, sparseParameterEnergy V W t ha
          ∂((sparseAdaptiveProcess P V).law t ⊗ₘ P.kernel t) := by
  rw [sparseAdaptive_roundKL_eq_lintegral]
  calc
    (∫⁻ ha, klDiv
        (feedbackDensityMeasure (V.value t ha.1 ha.2))
        (feedbackDensityMeasure (W.value t ha.1 ha.2))
        ∂((sparseAdaptiveProcess P V).law t ⊗ₘ P.kernel t)) <=
      ∫⁻ ha, ENNReal.ofReal
        (128 * (V.value t ha.1 ha.2 - W.value t ha.1 ha.2) ^ 2)
        ∂((sparseAdaptiveProcess P V).law t ⊗ₘ P.kernel t) := by
          exact lintegral_mono fun ha =>
            klDiv_feedbackDensityMeasure_le
              (V.abs_le t ha.1 ha.2) (W.abs_le t ha.1 ha.2)
    _ = ENNReal.ofReal 128 *
        ∫⁻ ha, sparseParameterEnergy V W t ha
          ∂((sparseAdaptiveProcess P V).law t ⊗ₘ P.kernel t) := by
      have h128 : (0 : Real) <= 128 := by norm_num
      simp_rw [sparseParameterEnergy, ENNReal.ofReal_mul h128]
      exact lintegral_const_mul _ (measurable_sparseParameterEnergy V W t)

/-- Sequential chain rule plus the scalar feedback bound.  This is the
generic adaptive KL engine used by the conditional sign argument. -/
theorem sparseAdaptive_klDiv_le_sum_parameterEnergy
    {n k : Nat} (P : Policy n k)
    (V W : SparseAdaptiveParameters n k) (T : Nat) :
    klDiv ((sparseAdaptiveProcess P V).law T)
        ((sparseAdaptiveProcess P W).law T) <=
      ENNReal.ofReal 128 *
        ∑ t ∈ Finset.range T,
          ∫⁻ ha, sparseParameterEnergy V W t ha
            ∂((sparseAdaptiveProcess P V).law t ⊗ₘ P.kernel t) := by
  rw [(sparseAdaptiveProcess P V).klDiv_law_eq_sum_roundKL
    (sparseAdaptiveProcess P W)]
  calc
    (∑ t ∈ Finset.range T,
        (sparseAdaptiveProcess P V).roundKL
          (sparseAdaptiveProcess P W) t) <=
      ∑ t ∈ Finset.range T, ENNReal.ofReal 128 *
        ∫⁻ ha, sparseParameterEnergy V W t ha
          ∂((sparseAdaptiveProcess P V).law t ⊗ₘ P.kernel t) := by
            exact Finset.sum_le_sum fun t _ =>
              sparseAdaptive_roundKL_le_parameterEnergy P V W t
    _ = ENNReal.ofReal 128 *
        ∑ t ∈ Finset.range T,
          ∫⁻ ha, sparseParameterEnergy V W t ha
            ∂((sparseAdaptiveProcess P V).law t ⊗ₘ P.kernel t) := by
      rw [Finset.mul_sum]

/-! ## Pinsker and the manuscript's conditional sign estimate -/

/-- Pinsker turns the manuscript's conditional KL budget into the exact
`16 u sqrt rho` total-variation bound. -/
theorem sparse_sign_totalVariation_le
    {Omega : Type*} [MeasurableSpace Omega]
    (Pplus Pminus : Measure Omega)
    [IsProbabilityMeasure Pplus] [IsProbabilityMeasure Pminus]
    {rho u : Real} (hrho : 0 <= rho) (hu : u ∈ Icc (0 : Real) 1)
    (hKL : klDiv Pplus Pminus <= ENNReal.ofReal (512 * rho * u ^ 2)) :
    totalVariationDistance Pplus Pminus <= 16 * u * Real.sqrt rho := by
  have hbudget0 : 0 <= 512 * rho * u ^ 2 := by positivity
  have hfiniteBudget : ENNReal.ofReal (512 * rho * u ^ 2) ≠ ∞ :=
    ENNReal.ofReal_ne_top
  have hfinite : klDiv Pplus Pminus ≠ ∞ := by
    exact ne_top_of_le_ne_top hfiniteBudget hKL
  have hpinsker := MsetsLower.Lower.Dense.totalVariationDistance_pinsker_sq
    Pplus Pminus hfinite
  have htoReal : (klDiv Pplus Pminus).toReal <= 512 * rho * u ^ 2 := by
    calc
      (klDiv Pplus Pminus).toReal <=
          (ENNReal.ofReal (512 * rho * u ^ 2)).toReal :=
        ENNReal.toReal_mono hfiniteBudget (by exact hKL)
      _ = 512 * rho * u ^ 2 := ENNReal.toReal_ofReal hbudget0
  have htv0 := totalVariationDistance_nonneg Pplus Pminus
  have hsqrt0 := Real.sqrt_nonneg rho
  have hsqrtSq : (Real.sqrt rho) ^ 2 = rho := Real.sq_sqrt hrho
  have htarget0 : 0 <= 16 * u * Real.sqrt rho :=
    mul_nonneg (mul_nonneg (by norm_num) hu.1) hsqrt0
  have hsq : totalVariationDistance Pplus Pminus ^ 2 <=
      (16 * u * Real.sqrt rho) ^ 2 := by
    rw [show (16 * u * Real.sqrt rho) ^ 2 = 256 * rho * u ^ 2 by
      rw [mul_pow, mul_pow, hsqrtSq]
      ring]
    nlinarith
  nlinarith [sq_nonneg
    (totalVariationDistance Pplus Pminus - 16 * u * Real.sqrt rho)]

/-- Conditional comparison of the two hidden signs.  This is the exact
estimate displayed immediately before `eq:lower-score-bias`:
`|(u/2)(E_+V-E_-V)| <= 8 M u^2 sqrt rho`. -/
theorem lower_score_bias_conditional_sign
    {Omega : Type*} [MeasurableSpace Omega]
    (Pplus Pminus : Measure Omega)
    [IsProbabilityMeasure Pplus] [IsProbabilityMeasure Pminus]
    {rho u M : Real} (hrho : 0 <= rho) (hu : u ∈ Icc (0 : Real) 1)
    (hM : 0 <= M) (V : Omega -> Real) (hV : Measurable V)
    (hVM : forall omega, V omega ∈ Icc (0 : Real) M)
    (hKL : klDiv Pplus Pminus <= ENNReal.ofReal (512 * rho * u ^ 2)) :
    |u / 2 * ((∫ omega, V omega ∂Pplus) -
        ∫ omega, V omega ∂Pminus)| <=
      8 * M * u ^ 2 * Real.sqrt rho := by
  have hgap :=
    abs_integral_sub_integral_le_mul_totalVariationDistance_of_mem_Icc
      Pplus Pminus hM hV hVM
  have htv := sparse_sign_totalVariation_le
    Pplus Pminus hrho hu hKL
  have hu0 : 0 <= u := hu.1
  rw [abs_mul, abs_of_nonneg (div_nonneg hu0 (by norm_num))]
  calc
    u / 2 * |(∫ omega, V omega ∂Pplus) -
        ∫ omega, V omega ∂Pminus| <=
      u / 2 * (M * totalVariationDistance Pplus Pminus) :=
        mul_le_mul_of_nonneg_left hgap (div_nonneg hu0 (by norm_num))
    _ <= u / 2 * (M * (16 * u * Real.sqrt rho)) := by
      exact mul_le_mul_of_nonneg_left
        (mul_le_mul_of_nonneg_left htv hM)
        (div_nonneg hu0 (by norm_num))
    _ = 8 * M * u ^ 2 * Real.sqrt rho := by ring

/-- The bound after forgetting the harmless factor `u^2 <= 1`. -/
theorem lower_score_bias_conditional_sign_coarse
    {Omega : Type*} [MeasurableSpace Omega]
    (Pplus Pminus : Measure Omega)
    [IsProbabilityMeasure Pplus] [IsProbabilityMeasure Pminus]
    {rho u M : Real} (hrho : 0 <= rho) (hu : u ∈ Icc (0 : Real) 1)
    (hM : 0 <= M) (V : Omega -> Real) (hV : Measurable V)
    (hVM : forall omega, V omega ∈ Icc (0 : Real) M)
    (hKL : klDiv Pplus Pminus <= ENNReal.ofReal (512 * rho * u ^ 2)) :
    |u / 2 * ((∫ omega, V omega ∂Pplus) -
        ∫ omega, V omega ∂Pminus)| <=
      8 * M * Real.sqrt rho := by
  have hsharp := lower_score_bias_conditional_sign
    Pplus Pminus hrho hu hM V hV hVM hKL
  have huSq : u ^ 2 <= 1 := by
    nlinarith [mul_nonneg hu.1 (sub_nonneg.mpr hu.2)]
  have hsqrt0 := Real.sqrt_nonneg rho
  calc
    |u / 2 * ((∫ omega, V omega ∂Pplus) -
        ∫ omega, V omega ∂Pminus)| <=
      8 * M * u ^ 2 * Real.sqrt rho := hsharp
    _ <= 8 * M * 1 * Real.sqrt rho := by
      exact mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_left huSq (mul_nonneg (by norm_num) hM)) hsqrt0
    _ = 8 * M * Real.sqrt rho := by ring

/-- Fully sequential version of the conditional sign estimate.  Its sole
information hypothesis is a predictable squared-parameter energy budget;
the KL chain rule and Pinsker are both discharged internally. -/
theorem lower_score_bias_conditional_sign_of_parameterEnergy
    {n k T : Nat} (P : Policy n k)
    (Vplus Vminus : SparseAdaptiveParameters n k)
    {rho u M : Real} (hrho : 0 <= rho) (hu : u ∈ Icc (0 : Real) 1)
    (hM : 0 <= M) (V : History n k T -> Real) (hV : Measurable V)
    (hVM : forall h, V h ∈ Icc (0 : Real) M)
    (henergy : ENNReal.ofReal 128 *
        ∑ t ∈ Finset.range T,
          ∫⁻ ha, sparseParameterEnergy Vplus Vminus t ha
            ∂((sparseAdaptiveProcess P Vplus).law t ⊗ₘ P.kernel t) <=
      ENNReal.ofReal (512 * rho * u ^ 2)) :
    |u / 2 *
        ((∫ h, V h ∂(sparseAdaptiveProcess P Vplus).law T) -
          ∫ h, V h ∂(sparseAdaptiveProcess P Vminus).law T)| <=
      8 * M * u ^ 2 * Real.sqrt rho := by
  apply lower_score_bias_conditional_sign
    ((sparseAdaptiveProcess P Vplus).law T)
    ((sparseAdaptiveProcess P Vminus).law T)
    hrho hu hM V hV hVM
  exact (sparseAdaptive_klDiv_le_sum_parameterEnergy
    P Vplus Vminus T).trans henergy

/-! ## Exact finite aggregation used in `eq:lower-score-bias` -/

/-- Aggregating the two conditional sign estimates over `B n'` cells and
using the manuscript's three exact counting identities gives the displayed
constant `48`.  The hypotheses are the already-derived per-cell sign bounds,
not a renamed global conclusion. -/
theorem lower_score_bias_aggregate
    {B n' r k q c0 T0 : Nat} {rho coordinate learner : Real}
    (hr : 1 <= r)
    (hT0 : B * q = T0) (hnr : n' = k * r)
    (hc : B * n' * c0 = 8 * k * T0)
    (hcoordinate : -(16 / (3 : Real)) * B * n' * q * Real.sqrt rho / r <=
      coordinate)
    (hlearner : learner <=
      (16 / (3 : Real)) * B * n' * c0 * Real.sqrt rho) :
    -(48 * (k : Real) * (T0 : Real) * Real.sqrt rho) <=
      coordinate - learner := by
  have hr0 : (r : Real) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt hr)
  have hT0r : (B : Real) * (q : Real) = T0 := by exact_mod_cast hT0
  have hnrr : (n' : Real) = (k : Real) * (r : Real) := by exact_mod_cast hnr
  have hcr : (B : Real) * (n' : Real) * (c0 : Real) =
      8 * (k : Real) * (T0 : Real) := by exact_mod_cast hc
  have hfirst :
      (B : Real) * (n' : Real) * (q : Real) / (r : Real) =
        (k : Real) * (T0 : Real) := by
    rw [show (B : Real) * (n' : Real) * (q : Real) =
      ((B : Real) * (q : Real)) * (n' : Real) by ring, hT0r, hnrr]
    field_simp [hr0]
  calc
    -(48 * (k : Real) * (T0 : Real) * Real.sqrt rho) =
        (-(16 / (3 : Real)) * (B : Real) * (n' : Real) * (q : Real) *
            Real.sqrt rho / (r : Real)) -
          ((16 / (3 : Real)) * (B : Real) * (n' : Real) * (c0 : Real) *
            Real.sqrt rho) := by
      rw [show -(16 / (3 : Real)) * (B : Real) * (n' : Real) *
          (q : Real) * Real.sqrt rho / (r : Real) =
        (-(16 / (3 : Real))) *
          ((B : Real) * (n' : Real) * (q : Real) / (r : Real)) *
            Real.sqrt rho by ring,
        hfirst,
        show (16 / (3 : Real)) * (B : Real) * (n' : Real) *
            (c0 : Real) * Real.sqrt rho =
          (16 / (3 : Real)) *
            ((B : Real) * (n' : Real) * (c0 : Real)) * Real.sqrt rho by ring,
        hcr]
      ring
    _ <= coordinate - learner := sub_le_sub hcoordinate hlearner

#print axioms abs_integral_sub_integral_le_mul_totalVariationDistance_of_mem_Icc
#print axioms klDiv_sparseParamTwoStage_eq_lintegral
#print axioms sparseAdaptive_roundKL_eq_lintegral
#print axioms sparseAdaptive_klDiv_le_sum_parameterEnergy
#print axioms sparse_sign_totalVariation_le
#print axioms lower_score_bias_conditional_sign
#print axioms lower_score_bias_conditional_sign_of_parameterEnergy
#print axioms lower_score_bias_aggregate

end

end MsetsLower.Lower.Sparse
