import MsetsLower.Feedback.Hessian
import MsetsLower.Feedback.MeasureKL
import MsetsLower.Feedback.Moments
import MsetsLower.Lower.Dense.AdaptiveLaw
import MsetsLower.Lower.Sparse.GoodPartition
import Mathlib.MeasureTheory.Integral.Pi

/-!
# Likelihood products for the sparse lower-bound construction

This file formalizes the likelihood calculations labelled
`eq:lower-single-likelihood-product`, `eq:lower-likelihood-diagonal`, and
`eq:lower-likelihood-cross` in the manuscript.  We first isolate a generic
adaptive feedback experiment: the learner chooses an action from the common
observable past, and the scalar feedback has the exact density `p_u` from
`Feedback.Density`.  This makes the cancellation of the adaptive action
kernel explicit rather than assuming a product formula.
-/

namespace MsetsLower.Lower.Sparse

open MsetsLower Feedback Set
open MeasureTheory ProbabilityTheory
open scoped BigOperators ENNReal ProbabilityTheory

noncomputable section

/-! ## Feedback kernels with a history-dependent parameter -/

/-- Sample a fresh uniform `Z` and return `F_{u(a)}(Z)`.  Constructing the
kernel as a push-forward makes joint measurability in the state parameter
automatic. -/
def sparseParamFeedbackKernel {alpha : Type*} [MeasurableSpace alpha]
    (u : alpha -> Real) : Kernel alpha Real :=
  (Kernel.id ×ₖ Kernel.const alpha sourceUniformMeasure).map
    (fun az => feedbackMap (u az.1) az.2)

theorem sparseParamFeedbackKernel_apply
    {alpha : Type*} [MeasurableSpace alpha]
    (u : alpha -> Real) (hu : Measurable u) (a : alpha)
    (hua : |u a| <= (1 : Real) / 16) :
    sparseParamFeedbackKernel u a = feedbackDensityMeasure (u a) := by
  letI : IsProbabilityMeasure sourceUniformMeasure :=
    ⟨sourceUniformMeasure_apply_univ⟩
  have hmap : Measurable (fun az : alpha × Real =>
      feedbackMap (u az.1) az.2) := by
    unfold feedbackMap shape
    fun_prop
  rw [sparseParamFeedbackKernel, Kernel.map_apply _ hmap,
    Kernel.prod_apply, Kernel.id_apply, Kernel.const_apply,
    Measure.dirac_prod]
  rw [Measure.map_map]
  · exact feedbackPushforwardMeasure_eq_densityMeasure hua
  · exact hmap
  · exact measurable_prodMk_left

theorem sparseParamFeedbackKernel_isMarkov
    {alpha : Type*} [MeasurableSpace alpha]
    (u : alpha -> Real) (hu : Measurable u)
    (hubound : forall a, |u a| <= (1 : Real) / 16) :
    IsMarkovKernel (sparseParamFeedbackKernel u) := by
  letI : IsProbabilityMeasure sourceUniformMeasure :=
    ⟨sourceUniformMeasure_apply_univ⟩
  constructor
  intro a
  constructor
  rw [sparseParamFeedbackKernel_apply u hu a (hubound a),
    feedbackDensityMeasure_apply_univ (hubound a)]

/-! The explicit inverse formula makes the likelihood ratio jointly
measurable in both parameters and the observation. -/

theorem measurable_feedbackDensity_uncurry :
    Measurable (fun p : Real × Real => feedbackDensity p.1 p.2) := by
  unfold feedbackDensity feedbackDensityCore feedbackJacobian feedbackSlope
  apply Measurable.ite
  · exact measurable_snd measurableSet_Icc
  · have hinv : Measurable (fun p : Real × Real =>
        feedbackInverse p.1 p.2) := measurable_feedbackInverse_uncurry
    exact measurable_const.div
      (measurable_const.mul
        (measurable_const.sub
          ((measurable_fst.const_mul 2).mul hinv)))
  · exact measurable_const

theorem measurable_feedbackDensityRatio_joint :
    Measurable (fun p : (Real × Real) × Real =>
      feedbackDensityRatio p.1.1 p.1.2 p.2) := by
  unfold feedbackDensityRatio
  apply Measurable.ennreal_ofReal
  exact
    (measurable_feedbackDensity_uncurry.comp
      (measurable_fst.fst.prodMk measurable_snd)).div
    (measurable_feedbackDensity_uncurry.comp
      (measurable_fst.snd.prodMk measurable_snd))

/-! ## A genuine adaptive density process -/

/-- A history/action-dependent feedback parameter, including the joint
measurability and domain conditions needed by the density theorem. -/
structure SparseAdaptiveParameters (n k : Nat) where
  value : (t : Nat) -> History n k t -> MSetAction n k -> Real
  measurable_value : forall t,
    Measurable (fun ha : History n k t × MSetAction n k =>
      value t ha.1 ha.2)
  abs_le : forall t h A, |value t h A| <= (1 : Real) / 16

/-- First sample the learner's action, then exact scalar feedback with
density `p_{u_t}`.  Both compared experiments use the same policy kernel. -/
def sparseAdaptiveRoundKernel {n k : Nat} (P : Policy n k)
    (V : SparseAdaptiveParameters n k) (t : Nat) :
    Kernel (History n k t) (MSetAction n k × Real) :=
  P.kernel t ⊗ₖ sparseParamFeedbackKernel
    (fun ha : History n k t × MSetAction n k => V.value t ha.1 ha.2)

theorem sparseAdaptiveRoundKernel_isMarkov {n k : Nat} (P : Policy n k)
    (V : SparseAdaptiveParameters n k) (t : Nat) :
    IsMarkovKernel (sparseAdaptiveRoundKernel P V t) := by
  unfold sparseAdaptiveRoundKernel
  letI : IsMarkovKernel (sparseParamFeedbackKernel
      (fun ha : History n k t × MSetAction n k =>
        V.value t ha.1 ha.2)) :=
    sparseParamFeedbackKernel_isMarkov _ (V.measurable_value t)
      (fun ha => V.abs_le t ha.1 ha.2)
  infer_instance

/-- The adaptive law generated by a parameter field. -/
def sparseAdaptiveProcess {n k : Nat} (P : Policy n k)
    (V : SparseAdaptiveParameters n k) : HistoryKernelProcess n k where
  kernel t := sparseAdaptiveRoundKernel P V t
  isMarkov t := sparseAdaptiveRoundKernel_isMarkov P V t

/-- The one-round feedback likelihood ratio `p_u/p_v`. -/
def sparseRoundLikelihood {n k : Nat}
    (V W : SparseAdaptiveParameters n k) (t : Nat)
    (hAy : History n k t × (MSetAction n k × Real)) : ENNReal :=
  feedbackDensityRatio
    (V.value t hAy.1 hAy.2.1)
    (W.value t hAy.1 hAy.2.1) hAy.2.2

theorem measurable_sparseRoundLikelihood {n k : Nat}
    (V W : SparseAdaptiveParameters n k) (t : Nat) :
    Measurable (sparseRoundLikelihood V W t) := by
  exact measurable_feedbackDensityRatio_joint.comp <|
    ((V.measurable_value t).comp
        (measurable_fst.prodMk measurable_snd.fst)).prodMk
      ((W.measurable_value t).comp
        (measurable_fst.prodMk measurable_snd.fst)) |>.prodMk
      measurable_snd.snd

theorem sparseAdaptiveRoundKernel_apply_eq_withDensity
    {n k : Nat} (P : Policy n k)
    (V W : SparseAdaptiveParameters n k) (t : Nat) (h : History n k t) :
    sparseAdaptiveRoundKernel P V t h =
      (sparseAdaptiveRoundKernel P W t h).withDensity
        (fun Ay => sparseRoundLikelihood V W t (h, Ay)) := by
  letI : IsMarkovKernel (sparseParamFeedbackKernel
      (fun ha : History n k t × MSetAction n k =>
        V.value t ha.1 ha.2)) :=
    sparseParamFeedbackKernel_isMarkov _ (V.measurable_value t)
      (fun ha => V.abs_le t ha.1 ha.2)
  letI : IsMarkovKernel (sparseParamFeedbackKernel
      (fun ha : History n k t × MSetAction n k =>
        W.value t ha.1 ha.2)) :=
    sparseParamFeedbackKernel_isMarkov _ (W.measurable_value t)
      (fun ha => W.abs_le t ha.1 ha.2)
  let kV : Kernel (MSetAction n k) Real :=
    (sparseParamFeedbackKernel
      (fun ha : History n k t × MSetAction n k =>
        V.value t ha.1 ha.2)).comap (fun A => (h, A)) measurable_prodMk_left
  let kW : Kernel (MSetAction n k) Real :=
    (sparseParamFeedbackKernel
      (fun ha : History n k t × MSetAction n k =>
        W.value t ha.1 ha.2)).comap (fun A => (h, A)) measurable_prodMk_left
  letI : IsMarkovKernel kV := by
    dsimp [kV]
    infer_instance
  letI : IsMarkovKernel kW := by
    dsimp [kW]
    infer_instance
  have hV : sparseAdaptiveRoundKernel P V t h = P.kernel t h ⊗ₘ kV := by
    ext s hs
    rw [sparseAdaptiveRoundKernel, Kernel.compProd_apply hs,
      Measure.compProd_apply hs]
    rfl
  have hW : sparseAdaptiveRoundKernel P W t h = P.kernel t h ⊗ₘ kW := by
    ext s hs
    rw [sparseAdaptiveRoundKernel, Kernel.compProd_apply hs,
      Measure.compProd_apply hs]
    rfl
  rw [hV, hW]
  apply MsetsLower.Lower.Dense.compProd_eq_withDensity_of_apply
    (P.kernel t h) kV kW
      (fun A y => feedbackDensityRatio
        (V.value t h A) (W.value t h A) y)
  · exact measurable_feedbackDensityRatio_joint.comp <|
      ((measurable_of_finite (fun A : MSetAction n k => V.value t h A)).comp
          measurable_fst).prodMk
        ((measurable_of_finite (fun A : MSetAction n k => W.value t h A)).comp
          measurable_fst) |>.prodMk measurable_snd
  · intro A
    change sparseParamFeedbackKernel
        (fun ha : History n k t × MSetAction n k =>
          V.value t ha.1 ha.2) (h, A) =
      (sparseParamFeedbackKernel
        (fun ha : History n k t × MSetAction n k =>
          W.value t ha.1 ha.2) (h, A)).withDensity _
    rw [sparseParamFeedbackKernel_apply _ (V.measurable_value t) _
        (V.abs_le t h A),
      sparseParamFeedbackKernel_apply _ (W.measurable_value t) _
        (W.abs_le t h A)]
    exact feedbackDensityMeasure_withDensity_ratio
      (V.abs_le t h A) (W.abs_le t h A)

/-! ## Exact adaptive product formula -/

/-- Reweighting the incoming state law reweights a composition-product by
the same density pulled back through the first projection. -/
theorem compProd_withDensity_left
    {alpha beta : Type*} [MeasurableSpace alpha] [MeasurableSpace beta]
    (nu : Measure alpha) (kappa : Kernel alpha beta)
    [SFinite nu] [IsSFiniteKernel kappa]
    (f : alpha -> ENNReal) (hf : Measurable f) :
    nu.withDensity f ⊗ₘ kappa =
      (nu ⊗ₘ kappa).withDensity (fun p => f p.1) := by
  ext s hs
  rw [Measure.compProd_apply hs,
    lintegral_withDensity_eq_lintegral_mul nu hf
      (Kernel.measurable_kernel_prodMk_left hs),
    withDensity_apply _ hs, ← lintegral_indicator hs,
    Measure.lintegral_compProd]
  · apply lintegral_congr
    intro a
    change f a * kappa a (Prod.mk a ⁻¹' s) =
      ∫⁻ b, s.indicator (fun p => f p.1) (a, b) ∂kappa a
    rw [show (fun b => s.indicator (fun p => f p.1) (a, b)) =
        (Prod.mk a ⁻¹' s).indicator (fun _ => f a) by
      funext b
      by_cases hab : (a, b) ∈ s <;> simp [hab]]
    rw [lintegral_indicator_const (measurable_prodMk_left hs) (f a)]
  · exact (hf.comp measurable_fst).indicator hs

/-- Cumulative likelihood ratio along a recursive history. -/
def sparseLikelihoodProduct {n k : Nat}
    (V W : SparseAdaptiveParameters n k) :
    (T : Nat) -> History n k T -> ENNReal
  | 0, _ => 1
  | t + 1, h => sparseLikelihoodProduct V W t h.1 *
      sparseRoundLikelihood V W t h

@[simp] theorem sparseLikelihoodProduct_zero {n k : Nat}
    (V W : SparseAdaptiveParameters n k) (h : History n k 0) :
    sparseLikelihoodProduct V W 0 h = 1 := rfl

@[simp] theorem sparseLikelihoodProduct_succ {n k t : Nat}
    (V W : SparseAdaptiveParameters n k) (h : History n k (t + 1)) :
    sparseLikelihoodProduct V W (t + 1) h =
      sparseLikelihoodProduct V W t h.1 * sparseRoundLikelihood V W t h := rfl

theorem measurable_sparseLikelihoodProduct {n k : Nat}
    (V W : SparseAdaptiveParameters n k) : forall T,
    Measurable (sparseLikelihoodProduct V W T) := by
  intro T
  induction T with
  | zero => exact measurable_const
  | succ t ih =>
      exact (ih.comp measurable_fst).mul
        (measurable_sparseRoundLikelihood V W t)

set_option maxHeartbeats 2000000 in
-- Dependent-history kernel induction needs additional elaboration budget.
/-- The adaptive policy factors cancel at every round.  Thus the complete
base history law is exactly the changed history law reweighted by the
chronological product of scalar feedback-density ratios.  This is the
measure-theoretic content of `eq:lower-single-likelihood-product` for the
temporal part. -/
theorem lower_single_likelihood_product_adaptive {n k : Nat}
    (P : Policy n k) (V W : SparseAdaptiveParameters n k) : forall T,
    (sparseAdaptiveProcess P V).law T =
      ((sparseAdaptiveProcess P W).law T).withDensity
        (sparseLikelihoodProduct V W T) := by
  intro T
  induction T with
  | zero =>
      rw [show (sparseAdaptiveProcess P V).law 0 =
          (sparseAdaptiveProcess P W).law 0 by rfl]
      have hp : sparseLikelihoodProduct V W 0 =
          (1 : History n k 0 -> ENNReal) := by
        funext h
        exact sparseLikelihoodProduct_zero V W h
      rw [hp, withDensity_one]
  | succ t ih =>
      rw [HistoryKernelProcess.law_succ, HistoryKernelProcess.law_succ, ih]
      let kV := (sparseAdaptiveProcess P V).kernel t
      let kW := (sparseAdaptiveProcess P W).kernel t
      have hk : forall h, kV h = (kW h).withDensity
          (fun Ay => sparseRoundLikelihood V W t (h, Ay)) := by
        intro h
        exact sparseAdaptiveRoundKernel_apply_eq_withDensity P V W t h
      calc
        ((sparseAdaptiveProcess P W).law t).withDensity
              (sparseLikelihoodProduct V W t) ⊗ₘ kV =
            (((sparseAdaptiveProcess P W).law t).withDensity
                (sparseLikelihoodProduct V W t) ⊗ₘ kW).withDensity
              (fun hAy => sparseRoundLikelihood V W t (hAy.1, hAy.2)) := by
          convert
            MsetsLower.Lower.Dense.compProd_eq_withDensity_of_apply
              (((sparseAdaptiveProcess P W).law t).withDensity
                (sparseLikelihoodProduct V W t)) kV kW
              (fun h Ay => sparseRoundLikelihood V W t (h, Ay))
              (measurable_sparseRoundLikelihood V W t) hk using 1
          exact withDensity_congr_ae <| ae_of_all _ fun hAy => by
            rcases hAy with ⟨h, Ay⟩
            rfl
        _ = ((((sparseAdaptiveProcess P W).law t) ⊗ₘ kW).withDensity
              (fun hAy => sparseLikelihoodProduct V W t hAy.1)).withDensity
              (fun hAy => sparseRoundLikelihood V W t (hAy.1, hAy.2)) := by
          rw [compProd_withDensity_left]
          exact measurable_sparseLikelihoodProduct V W t
        _ = (((sparseAdaptiveProcess P W).law t) ⊗ₘ kW).withDensity
              (sparseLikelihoodProduct V W (t + 1)) := by
          have hf : Measurable (fun hAy : History n k t ×
              (MSetAction n k × Real) =>
              sparseLikelihoodProduct V W t hAy.1) :=
            (measurable_sparseLikelihoodProduct V W t).comp measurable_fst
          have hg : Measurable (fun hAy : History n k t ×
              (MSetAction n k × Real) =>
              sparseRoundLikelihood V W t (hAy.1, hAy.2)) :=
            measurable_sparseRoundLikelihood V W t
          have hp : sparseLikelihoodProduct V W (t + 1) =
              ((fun hAy : History n k t × (MSetAction n k × Real) =>
                  sparseLikelihoodProduct V W t hAy.1) *
                fun hAy => sparseRoundLikelihood V W t (hAy.1, hAy.2)) := by
            funext hAy
            rcases hAy with ⟨h, Ay⟩
            rfl
          rw [hp]
          exact (withDensity_mul
            (((sparseAdaptiveProcess P W).law t) ⊗ₘ kW) hf hg).symm

/-! ## The conditional second moment -/

/-- The second moment from `Feedback.Density` is literally the expectation
of the likelihood ratio `p_u/p_v` under the `p_u` feedback law. -/
theorem lintegral_feedbackDensityRatio_eq_secondMoment
    {u v : Real} (hu : |u| <= (1 : Real) / 16)
    (hv : |v| <= (1 : Real) / 16) :
    (∫⁻ y, feedbackDensityRatio u v y ∂feedbackDensityMeasure u) =
      ENNReal.ofReal (feedbackSecondMoment u v) := by
  let f : Real -> Real := fun y =>
    feedbackDensityCore u y ^ 2 / feedbackDensityCore v y
  have hfint : IntegrableOn f
      (Icc (-1 / 2 : Real) (1 / 2 : Real)) volume := by
    exact (intervalIntegrable_iff_integrableOn_Icc_of_le (by norm_num)).1
      (intervalIntegrable_feedbackSecondMomentIntegrand hu hv)
  have hfnn : (fun _ : Real => (0 : Real)) ≤ᵐ[volume.restrict
      (Icc (-1 / 2 : Real) (1 / 2 : Real))] f := by
    change ∀ᵐ y ∂volume.restrict
      (Icc (-1 / 2 : Real) (1 / 2 : Real)), 0 <= f y
    rw [ae_restrict_iff' measurableSet_Icc]
    filter_upwards with y
    intro hy
    exact div_nonneg (sq_nonneg _) <|
      le_trans (by norm_num)
        (feedbackDensityCore_mem_Icc hv hy).1
  have hset :
      (∫ y in Icc (-1 / 2 : Real) (1 / 2 : Real), f y) =
        feedbackSecondMoment u v := by
    rw [feedbackSecondMoment, intervalIntegral.integral_of_le (by norm_num),
      ← integral_Icc_eq_integral_Ioc]
  rw [feedbackDensityMeasure,
    lintegral_withDensity_eq_lintegral_mul volume
      (measurable_feedbackDensity u).ennreal_ofReal
      (measurable_feedbackDensityRatio u v)]
  have hpoint : (fun y =>
      ENNReal.ofReal (feedbackDensity u y) * feedbackDensityRatio u v y) =
      (Icc (-1 / 2 : Real) (1 / 2 : Real)).indicator
        (fun y => ENNReal.ofReal (f y)) := by
    funext y
    by_cases hy : y ∈ Icc (-1 / 2 : Real) (1 / 2 : Real)
    · rw [indicator_of_mem hy, feedbackDensity_eq_core hy,
        feedbackDensityRatio, feedbackDensity_eq_core hy,
        feedbackDensity_eq_core hy]
      have hpu : 0 <= feedbackDensityCore u y :=
        le_trans (by norm_num) (feedbackDensityCore_mem_Icc hu hy).1
      have hpv : 0 < feedbackDensityCore v y :=
        lt_of_lt_of_le (by norm_num) (feedbackDensityCore_mem_Icc hv hy).1
      rw [← ENNReal.ofReal_mul hpu]
      congr 1
      dsimp [f]
      field_simp [ne_of_gt hpv]
    · rw [indicator_of_notMem hy, feedbackDensity_eq_zero hy]
      simp
  change (∫⁻ y, ENNReal.ofReal (feedbackDensity u y) *
      feedbackDensityRatio u v y) = _
  rw [hpoint, lintegral_indicator measurableSet_Icc]
  rw [← ofReal_integral_eq_lintegral_ofReal hfint hfnn, hset]

theorem lintegral_feedbackDensityRatio_le_exp
    {u v : Real} (hu : |u| <= (1 : Real) / 16)
    (hv : |v| <= (1 : Real) / 16) :
    (∫⁻ y, feedbackDensityRatio u v y ∂feedbackDensityMeasure u) <=
      ENNReal.ofReal (Real.exp (128 * (u - v) ^ 2)) := by
  rw [lintegral_feedbackDensityRatio_eq_secondMoment hu hv]
  exact ENNReal.ofReal_le_ofReal (feedbackSecondMoment_le_exp hu hv)

/-! ## Chronological integration of the adaptive product -/

/-- Squared parameter displacement at one realized round. -/
def sparseRoundEnergy {n k : Nat}
    (V W : SparseAdaptiveParameters n k) (t : Nat)
    (hA : History n k t × MSetAction n k) : Real :=
  (V.value t hA.1 hA.2 - W.value t hA.1 hA.2) ^ 2

theorem measurable_sparseRoundEnergy {n k : Nat}
    (V W : SparseAdaptiveParameters n k) (t : Nat) :
    Measurable (sparseRoundEnergy V W t) := by
  exact ((V.measurable_value t).sub (W.measurable_value t)).pow_const 2

/-- The likelihood factor divided by its conditional second-moment budget.
Writing the division as `exp(-x)` avoids any convention at infinity. -/
def sparseCompensatedRoundLikelihood {n k : Nat}
    (V W : SparseAdaptiveParameters n k) (t : Nat)
    (hAy : History n k t × (MSetAction n k × Real)) : ENNReal :=
  ENNReal.ofReal (Real.exp (-128 * sparseRoundEnergy V W t
      (hAy.1, hAy.2.1))) * sparseRoundLikelihood V W t hAy

theorem measurable_sparseCompensatedRoundLikelihood {n k : Nat}
    (V W : SparseAdaptiveParameters n k) (t : Nat) :
    Measurable (sparseCompensatedRoundLikelihood V W t) := by
  unfold sparseCompensatedRoundLikelihood
  have hfirst : Measurable (fun hAy : History n k t ×
      (MSetAction n k × Real) =>
      ENNReal.ofReal (Real.exp (-128 * sparseRoundEnergy V W t
        (hAy.1, hAy.2.1)))) := by
    apply Measurable.ennreal_ofReal
    apply Measurable.exp
    exact measurable_const.mul <|
      (measurable_sparseRoundEnergy V W t).comp
        (measurable_fst.prodMk measurable_snd.fst)
  exact hfirst.mul (measurable_sparseRoundLikelihood V W t)

/-- One compensated likelihood increment has conditional expectation at
most one, even though the parameter and action are selected adaptively from
the preceding history. -/
theorem lintegral_sparseCompensatedRoundLikelihood_le_one
    {n k : Nat} (P : Policy n k)
    (V W : SparseAdaptiveParameters n k) (t : Nat)
    (h : History n k t) :
    (∫⁻ Ay, sparseCompensatedRoundLikelihood V W t (h, Ay)
        ∂sparseAdaptiveRoundKernel P V t h) <= 1 := by
  let feedbackK := sparseParamFeedbackKernel
    (fun hA : History n k t × MSetAction n k =>
      V.value t hA.1 hA.2)
  letI : IsMarkovKernel feedbackK := by
    dsimp [feedbackK]
    exact sparseParamFeedbackKernel_isMarkov _ (V.measurable_value t)
      (fun hA => V.abs_le t hA.1 hA.2)
  rw [sparseAdaptiveRoundKernel, Kernel.lintegral_compProd]
  · calc
      (∫⁻ A, ∫⁻ y, sparseCompensatedRoundLikelihood V W t
          (h, (A, y)) ∂feedbackK (h, A) ∂P.kernel t h) <=
          ∫⁻ _A, (1 : ENNReal) ∂P.kernel t h := by
        apply lintegral_mono
        intro A
        have happly : feedbackK (h, A) =
            feedbackDensityMeasure (V.value t h A) := by
          exact sparseParamFeedbackKernel_apply _ (V.measurable_value t) _
            (V.abs_le t h A)
        change (∫⁻ y, sparseCompensatedRoundLikelihood V W t
            (h, (A, y)) ∂feedbackK (h, A)) <= 1
        rw [happly]
        let d : Real := sparseRoundEnergy V W t (h, A)
        change (∫⁻ y, ENNReal.ofReal (Real.exp (-128 * d)) *
            feedbackDensityRatio (V.value t h A) (W.value t h A) y
              ∂feedbackDensityMeasure (V.value t h A)) <= 1
        rw [lintegral_const_mul _
          (measurable_feedbackDensityRatio (V.value t h A)
            (W.value t h A))]
        calc
          ENNReal.ofReal (Real.exp (-128 * d)) *
              (∫⁻ y, feedbackDensityRatio (V.value t h A)
                (W.value t h A) y
                ∂feedbackDensityMeasure (V.value t h A)) <=
            ENNReal.ofReal (Real.exp (-128 * d)) *
              ENNReal.ofReal (Real.exp (128 *
                (V.value t h A - W.value t h A) ^ 2)) :=
              mul_le_mul_right (lintegral_feedbackDensityRatio_le_exp
                (V.abs_le t h A) (W.abs_le t h A)) _
          _ = 1 := by
            change ENNReal.ofReal (Real.exp (-128 * d)) *
                ENNReal.ofReal (Real.exp (128 * d)) = 1
            rw [← ENNReal.ofReal_mul (Real.exp_nonneg _), ← Real.exp_add]
            norm_num
      _ = 1 := by simp
  · exact (measurable_sparseCompensatedRoundLikelihood V W t).comp
      (measurable_const.prodMk measurable_id)

/-- Product of the compensated increments. -/
def sparseCompensatedLikelihood {n k : Nat}
    (V W : SparseAdaptiveParameters n k) :
    (T : Nat) -> History n k T -> ENNReal
  | 0, _ => 1
  | t + 1, h => sparseCompensatedLikelihood V W t h.1 *
      sparseCompensatedRoundLikelihood V W t h

theorem measurable_sparseCompensatedLikelihood {n k : Nat}
    (V W : SparseAdaptiveParameters n k) : forall T,
    Measurable (sparseCompensatedLikelihood V W T) := by
  intro T
  induction T with
  | zero => exact measurable_const
  | succ t ih =>
      exact (ih.comp measurable_fst).mul
        (measurable_sparseCompensatedRoundLikelihood V W t)

/-- Iterated conditional integration: the compensated adaptive product is a
nonnegative supermartingale with initial expectation one. -/
theorem lintegral_sparseCompensatedLikelihood_le_one
    {n k : Nat} (P : Policy n k)
    (V W : SparseAdaptiveParameters n k) : forall T,
    (∫⁻ h, sparseCompensatedLikelihood V W T h
      ∂(sparseAdaptiveProcess P V).law T) <= 1 := by
  intro T
  induction T with
  | zero => simp [sparseCompensatedLikelihood]
  | succ t ih =>
      rw [HistoryKernelProcess.law_succ]
      change (∫⁻ hAy : History n k t × (MSetAction n k × Real),
          sparseCompensatedLikelihood V W (t + 1) hAy
          ∂(sparseAdaptiveProcess P V).law t ⊗ₘ
            (sparseAdaptiveProcess P V).kernel t) <= 1
      rw [Measure.lintegral_compProd]
      · calc
          (∫⁻ h, ∫⁻ Ay, sparseCompensatedLikelihood V W (t + 1) (h, Ay)
              ∂(sparseAdaptiveProcess P V).kernel t h
              ∂(sparseAdaptiveProcess P V).law t) <=
            ∫⁻ h, sparseCompensatedLikelihood V W t h
              ∂(sparseAdaptiveProcess P V).law t := by
              apply lintegral_mono
              intro h
              let g : MSetAction n k × Real -> ENNReal := fun Ay =>
                sparseCompensatedRoundLikelihood V W t (h, Ay)
              have hg : Measurable g :=
                (measurable_sparseCompensatedRoundLikelihood V W t).comp
                  (measurable_const.prodMk measurable_id)
              change (∫⁻ Ay, sparseCompensatedLikelihood V W t h *
                  g Ay
                    ∂sparseAdaptiveRoundKernel P V t h) <= _
              rw [lintegral_const_mul _ hg]
              exact (mul_le_mul_right (lintegral_sparseCompensatedRoundLikelihood_le_one
                P V W t h) _).trans_eq (mul_one _)
          _ <= 1 := ih
      · exact measurable_sparseCompensatedLikelihood V W (t + 1)

/-- Total squared parameter displacement along a realized history. -/
def sparseCumulativeEnergy {n k : Nat}
    (V W : SparseAdaptiveParameters n k) :
    (T : Nat) -> History n k T -> Real
  | 0, _ => 0
  | t + 1, h => sparseCumulativeEnergy V W t h.1 +
      sparseRoundEnergy V W t (h.1, h.2.1)

theorem sparseCumulativeEnergy_nonneg {n k : Nat}
    (V W : SparseAdaptiveParameters n k) : forall T (h : History n k T),
    0 <= sparseCumulativeEnergy V W T h := by
  intro T
  induction T with
  | zero => intro h; rfl
  | succ t ih =>
      intro h
      exact add_nonneg (ih h.1) (sq_nonneg _)

theorem sparseRoundLikelihood_eq_exp_mul_compensated {n k : Nat}
    (V W : SparseAdaptiveParameters n k) (t : Nat)
    (hAy : History n k t × (MSetAction n k × Real)) :
    sparseRoundLikelihood V W t hAy =
      ENNReal.ofReal (Real.exp (128 * sparseRoundEnergy V W t
        (hAy.1, hAy.2.1))) *
        sparseCompensatedRoundLikelihood V W t hAy := by
  let d := sparseRoundEnergy V W t (hAy.1, hAy.2.1)
  unfold sparseCompensatedRoundLikelihood
  change sparseRoundLikelihood V W t hAy =
    ENNReal.ofReal (Real.exp (128 * d)) *
      (ENNReal.ofReal (Real.exp (-128 * d)) *
        sparseRoundLikelihood V W t hAy)
  rw [← mul_assoc]
  have hcancel : ENNReal.ofReal (Real.exp (128 * d)) *
      ENNReal.ofReal (Real.exp (-128 * d)) = 1 := by
    rw [← ENNReal.ofReal_mul (Real.exp_nonneg _), ← Real.exp_add]
    norm_num
  rw [hcancel, one_mul]

/-- Exact factorization of the raw likelihood product into its exponential
energy budget and compensated supermartingale. -/
theorem sparseLikelihoodProduct_eq_exp_energy_mul {n k : Nat}
    (V W : SparseAdaptiveParameters n k) : forall T (h : History n k T),
    sparseLikelihoodProduct V W T h =
      ENNReal.ofReal (Real.exp (128 * sparseCumulativeEnergy V W T h)) *
        sparseCompensatedLikelihood V W T h := by
  intro T
  induction T with
  | zero => intro h; simp [sparseCumulativeEnergy, sparseCompensatedLikelihood]
  | succ t ih =>
      intro h
      rw [sparseLikelihoodProduct_succ, ih h.1,
        sparseRoundLikelihood_eq_exp_mul_compensated]
      change
        (ENNReal.ofReal (Real.exp
            (128 * sparseCumulativeEnergy V W t h.1)) *
          sparseCompensatedLikelihood V W t h.1) *
          (ENNReal.ofReal (Real.exp
              (128 * sparseRoundEnergy V W t (h.1, h.2.1))) *
            sparseCompensatedRoundLikelihood V W t h) =
        ENNReal.ofReal (Real.exp
          (128 * (sparseCumulativeEnergy V W t h.1 +
            sparseRoundEnergy V W t (h.1, h.2.1)))) *
          (sparseCompensatedLikelihood V W t h.1 *
            sparseCompensatedRoundLikelihood V W t h)
      rw [show ENNReal.ofReal (Real.exp
            (128 * (sparseCumulativeEnergy V W t h.1 +
              sparseRoundEnergy V W t (h.1, h.2.1)))) =
          ENNReal.ofReal (Real.exp
            (128 * sparseCumulativeEnergy V W t h.1)) *
          ENNReal.ofReal (Real.exp
            (128 * sparseRoundEnergy V W t (h.1, h.2.1))) by
        rw [← ENNReal.ofReal_mul (Real.exp_nonneg _), ← Real.exp_add]
        congr 2
        ring]
      ac_rfl

/-- Adaptive temporal part of `eq:lower-likelihood-diagonal`: a pathwise
energy budget implies the corresponding exponential second-moment bound.
No independence of the learner's actions is used. -/
theorem lower_likelihood_diagonal_temporal
    {n k : Nat} (P : Policy n k)
    (V W : SparseAdaptiveParameters n k) (T : Nat) (C : Real)
    (henergy : forall h : History n k T,
      sparseCumulativeEnergy V W T h <= C) :
    (∫⁻ h, sparseLikelihoodProduct V W T h
      ∂(sparseAdaptiveProcess P V).law T) <=
      ENNReal.ofReal (Real.exp (128 * C)) := by
  calc
    (∫⁻ h, sparseLikelihoodProduct V W T h
        ∂(sparseAdaptiveProcess P V).law T) =
      ∫⁻ h, ENNReal.ofReal
          (Real.exp (128 * sparseCumulativeEnergy V W T h)) *
        sparseCompensatedLikelihood V W T h
        ∂(sparseAdaptiveProcess P V).law T := by
          apply lintegral_congr
          intro h
          exact sparseLikelihoodProduct_eq_exp_energy_mul V W T h
    _ <= ∫⁻ h, ENNReal.ofReal (Real.exp (128 * C)) *
        sparseCompensatedLikelihood V W T h
        ∂(sparseAdaptiveProcess P V).law T := by
          apply lintegral_mono
          intro h
          apply mul_le_mul_left
          exact ENNReal.ofReal_le_ofReal <| Real.exp_le_exp.mpr <|
            mul_le_mul_of_nonneg_left (henergy h) (by norm_num)
    _ = ENNReal.ofReal (Real.exp (128 * C)) *
        (∫⁻ h, sparseCompensatedLikelihood V W T h
          ∂(sparseAdaptiveProcess P V).law T) := by
          rw [lintegral_const_mul _
            (measurable_sparseCompensatedLikelihood V W T)]
    _ <= ENNReal.ofReal (Real.exp (128 * C)) * 1 :=
      mul_le_mul_right (lintegral_sparseCompensatedLikelihood_le_one
        P V W T) _
    _ = ENNReal.ofReal (Real.exp (128 * C)) := mul_one _

/-! ### Hidden-coordinate Jacobian factor -/

/-- The Jacobian contribution of the map `T_a(u)=u+a*g(u)` for one hidden
coordinate. -/
def sparseHiddenJacobianFactor (a u : Real) : Real :=
  1 / (1 - 2 * a * u)

private theorem intervalIntegrable_sparseHiddenJacobianFactor
    {a : Real} (ha : |a| <= (1 : Real) / 4) :
    IntervalIntegrable (sparseHiddenJacobianFactor a) volume (-1) 1 := by
  unfold sparseHiddenJacobianFactor
  apply intervalIntegral.intervalIntegrable_one_div
  · intro u hu
    have hu' : u ∈ Icc (-1 : Real) 1 := by
      simpa [uIcc_of_le (by norm_num : (-1 : Real) <= 1)] using hu
    have hau : |a * u| <= (1 : Real) / 4 := by
      calc
        |a * u| = |a| * |u| := abs_mul a u
        _ <= (1 / 4 : Real) * 1 :=
          mul_le_mul ha ((abs_le).2 hu') (abs_nonneg _) (by norm_num)
        _ = 1 / 4 := by norm_num
    exact ne_of_gt (by have := (abs_le.mp hau).2; nlinarith)
  · fun_prop

private theorem intervalIntegral_hidden_neg_eq (a : Real) :
    (∫ u in (-1 : Real)..1, sparseHiddenJacobianFactor a (-u)) =
      ∫ u in (-1 : Real)..1, sparseHiddenJacobianFactor a u := by
  have hcomp := intervalIntegral.integral_comp_mul_add
    (f := sparseHiddenJacobianFactor a) (a := (-1 : Real)) (b := 1)
    (c := (-1 : Real)) (by norm_num) 0
  simpa using hcomp

private theorem hidden_jacobian_average_pointwise_le
    {a u : Real} (ha : |a| <= (1 : Real) / 4)
    (hu : u ∈ Icc (-1 : Real) 1) :
    (sparseHiddenJacobianFactor a u +
        sparseHiddenJacobianFactor a (-u)) / 2 <=
      1 / (1 - 4 * a ^ 2) := by
  have hau : |a * u| <= (1 : Real) / 4 := by
    calc
      |a * u| = |a| * |u| := abs_mul a u
      _ <= (1 / 4 : Real) * 1 :=
        mul_le_mul ha ((abs_le).2 hu) (abs_nonneg _) (by norm_num)
      _ = 1 / 4 := by norm_num
  have hminus : 0 < 1 - 2 * a * u := by
    have := (abs_le.mp hau).2
    nlinarith
  have hplus : 0 < 1 + 2 * a * u := by
    have := (abs_le.mp hau).1
    nlinarith
  have huSq : u ^ 2 <= 1 := by
    simpa only [sq_abs, one_pow] using
      ((sq_le_sq₀ (abs_nonneg u) (by norm_num)).2 ((abs_le).2 hu))
  have haSq : a ^ 2 <= (1 / 4 : Real) ^ 2 := by
    simpa only [sq_abs] using
      ((sq_le_sq₀ (abs_nonneg a) (by norm_num)).2 ha)
  have hDpos : 0 < 1 - 4 * a ^ 2 := by nlinarith
  have hscale : 4 * a ^ 2 * u ^ 2 <= 4 * a ^ 2 := by
    simpa only [mul_one] using
      (mul_le_mul_of_nonneg_left huSq
        (by positivity : 0 <= 4 * a ^ 2))
  have hden : 1 - 4 * a ^ 2 <= 1 - 4 * a ^ 2 * u ^ 2 := by
    linarith
  have hsmallpos : 0 < 1 - 4 * a ^ 2 * u ^ 2 := hDpos.trans_le hden
  have heq :
      (sparseHiddenJacobianFactor a u +
          sparseHiddenJacobianFactor a (-u)) / 2 =
        1 / (1 - 4 * a ^ 2 * u ^ 2) := by
    unfold sparseHiddenJacobianFactor
    have hfac : (1 - 2 * a * u) * (1 + 2 * a * u) =
        1 - 4 * a ^ 2 * u ^ 2 := by ring
    rw [← hfac]
    field_simp [ne_of_gt hminus, ne_of_gt hplus]
    ring
  rw [heq]
  exact one_div_le_one_div_of_le hDpos hden

/-- One hidden Jacobian has expectation at most the rational bound used in
the manuscript.  The proof uses the symmetry of the uniform interval, so the
linear term in `a` genuinely cancels. -/
theorem integral_sparseHiddenJacobianFactor_le
    {a : Real} (ha : |a| <= (1 : Real) / 4) :
    (∫ u, sparseHiddenJacobianFactor a u ∂sourceUniformMeasure) <=
      1 / (1 - 4 * a ^ 2) := by
  have hf := intervalIntegrable_sparseHiddenJacobianFactor ha
  have hfneg : IntervalIntegrable
      (fun u : Real => sparseHiddenJacobianFactor a (-u)) volume (-1) 1 := by
    simpa only [neg_neg] using
      ((IntervalIntegrable.iff_comp_neg).mp hf).symm
  have havg :
      (∫ u in (-1 : Real)..1, sparseHiddenJacobianFactor a u) =
        ∫ u in (-1 : Real)..1,
          (sparseHiddenJacobianFactor a u +
            sparseHiddenJacobianFactor a (-u)) / 2 := by
    rw [intervalIntegral.integral_div,
      intervalIntegral.integral_add hf hfneg,
      intervalIntegral_hidden_neg_eq a]
    ring
  unfold sourceUniformMeasure
  rw [integral_smul_measure]
  simp only [ENNReal.toReal_ofReal (by norm_num : (0 : Real) <= 1 / 2),
    smul_eq_mul]
  change (1 / 2 : Real) *
      (∫ u in Icc (-1 : Real) 1, sparseHiddenJacobianFactor a u) <= _
  rw [integral_Icc_eq_integral_Ioc,
    ← intervalIntegral.integral_of_le (by norm_num : (-1 : Real) <= 1),
    havg]
  have hmono :
      (∫ u in (-1 : Real)..1,
          (sparseHiddenJacobianFactor a u +
            sparseHiddenJacobianFactor a (-u)) / 2) <=
        ∫ _u in (-1 : Real)..1, (1 / (1 - 4 * a ^ 2) : Real) := by
    apply intervalIntegral.integral_mono_on (by norm_num)
    · exact hf.add hfneg |>.div_const 2
    · exact (continuous_const : Continuous
        (fun _ : Real => 1 / (1 - 4 * a ^ 2))).intervalIntegrable _ _
    · intro u hu
      exact hidden_jacobian_average_pointwise_le ha hu
  calc
    (1 / 2 : Real) *
        (∫ u in (-1 : Real)..1,
          (sparseHiddenJacobianFactor a u +
            sparseHiddenJacobianFactor a (-u)) / 2) <=
      (1 / 2 : Real) *
        (∫ _u in (-1 : Real)..1, (1 / (1 - 4 * a ^ 2) : Real)) :=
          mul_le_mul_of_nonneg_left hmono (by norm_num)
    _ = 1 / (1 - 4 * a ^ 2) := by
      rw [intervalIntegral.integral_const]
      ring

theorem one_div_one_sub_four_sq_le_exp
    {a : Real} (ha : |a| <= (1 : Real) / 4) :
    1 / (1 - 4 * a ^ 2) <= Real.exp (8 * a ^ 2) := by
  have haSq : a ^ 2 <= (1 / 4 : Real) ^ 2 :=
    by simpa only [sq_abs] using
      ((sq_le_sq₀ (abs_nonneg a) (by norm_num)).2 ha)
  have hden : 0 < 1 - 4 * a ^ 2 := by nlinarith
  have hrat : 1 / (1 - 4 * a ^ 2) <= 1 + 8 * a ^ 2 := by
    rw [div_le_iff₀ hden]
    nlinarith [sq_nonneg (a ^ 2)]
  exact hrat.trans (by simpa [add_comm] using Real.add_one_le_exp (8 * a ^ 2))

/-- The complete independent hidden-coordinate factor over `B` blocks has
expectation at most `exp(8*a^2*B)`. -/
theorem integral_sparseHiddenJacobianProduct_le
    {B : Nat} {a : Real} (ha : |a| <= (1 : Real) / 4) :
    (∫ U : Fin B -> Real,
        ∏ b, sparseHiddenJacobianFactor a (U b)
      ∂Measure.pi (fun _ : Fin B => sourceUniformMeasure)) <=
      Real.exp (8 * a ^ 2 * B) := by
  rw [integral_fintype_prod_eq_pow]
  simp only [Fintype.card_fin]
  have hscalar :
      (∫ u, sparseHiddenJacobianFactor a u ∂sourceUniformMeasure) <=
        Real.exp (8 * a ^ 2) :=
    (integral_sparseHiddenJacobianFactor_le ha).trans
      (one_div_one_sub_four_sq_le_exp ha)
  have hscalar0 : 0 <=
      ∫ u, sparseHiddenJacobianFactor a u ∂sourceUniformMeasure := by
    apply integral_nonneg_of_ae
    filter_upwards [ae_sourceUniformMeasure_mem_Icc] with u hu
    unfold sparseHiddenJacobianFactor
    have hau : |a * u| <= (1 : Real) / 4 := by
      calc
        |a * u| = |a| * |u| := abs_mul a u
        _ <= (1 / 4 : Real) * 1 :=
          mul_le_mul ha ((abs_le).2 hu) (abs_nonneg _) (by norm_num)
        _ = 1 / 4 := by norm_num
    have hden : 0 < 1 - 2 * a * u := by
      have := (abs_le.mp hau).2
      nlinarith
    exact (one_div_pos.mpr hden).le
  calc
    (∫ u, sparseHiddenJacobianFactor a u ∂sourceUniformMeasure) ^ B <=
        (Real.exp (8 * a ^ 2)) ^ B := by
      exact pow_le_pow_left₀ hscalar0 hscalar B
    _ = Real.exp (8 * a ^ 2 * B) := by
      rw [← Real.exp_nat_mul]
      congr 1
      ring

/-! ## The four-corner (cross) likelihood term

The change of two hidden coordinates produces four feedback parameters at
each round.  The following rectangle packages the base, the two one-coordinate
changes, and the simultaneous change.  The sole compatibility field says that
the four parameters form the additive rectangle used in the manuscript; all
domain and measurability facts are inherited from the four genuine adaptive
parameter fields.
-/

/-- Four adaptive parameter fields forming a pointwise additive rectangle. -/
structure SparseAdaptiveRectangle (n k : Nat) where
  base : SparseAdaptiveParameters n k
  left : SparseAdaptiveParameters n k
  right : SparseAdaptiveParameters n k
  both : SparseAdaptiveParameters n k
  rectangle : forall t h A,
    both.value t h A + base.value t h A =
      left.value t h A + right.value t h A

/-- The logarithmic four-corner feedback contribution at one round.  Outside
the support of every feedback law it is set to zero; on the support this is
exactly the expression displayed immediately before
`eq:lower-likelihood-cross`. -/
def sparseCrossLogIncrement {n k : Nat}
    (R : SparseAdaptiveRectangle n k) (t : Nat)
    (hAy : History n k t × (MSetAction n k × Real)) : Real :=
  if hAy.2.2 ∈ Icc (-1 / 2 : Real) (1 / 2 : Real) then
    feedbackLogJacobian (R.both.value t hAy.1 hAy.2.1) hAy.2.2 -
      feedbackLogJacobian (R.right.value t hAy.1 hAy.2.1) hAy.2.2 -
      feedbackLogJacobian (R.left.value t hAy.1 hAy.2.1) hAy.2.2 +
      feedbackLogJacobian (R.base.value t hAy.1 hAy.2.1) hAy.2.2
  else 0

/-- Absolute product of the two parameter displacements at one round. -/
def sparseCrossRoundEnergy {n k : Nat}
    (R : SparseAdaptiveRectangle n k) (t : Nat)
    (hA : History n k t × MSetAction n k) : Real :=
  |(R.left.value t hA.1 hA.2 - R.base.value t hA.1 hA.2) *
    (R.right.value t hA.1 hA.2 - R.base.value t hA.1 hA.2)|

theorem measurable_feedbackLogJacobian_uncurry :
    Measurable (fun p : Real × Real =>
      feedbackLogJacobian p.1 p.2) := by
  unfold feedbackLogJacobian feedbackJacobian
  apply Measurable.log
  exact (measurable_const.sub
    ((measurable_fst.const_mul 2).mul
      measurable_feedbackInverse_uncurry))

theorem measurable_sparseCrossLogIncrement {n k : Nat}
    (R : SparseAdaptiveRectangle n k) (t : Nat) :
    Measurable (sparseCrossLogIncrement R t) := by
  unfold sparseCrossLogIncrement
  apply Measurable.ite
  · exact measurable_snd.snd measurableSet_Icc
  · let y : History n k t × (MSetAction n k × Real) -> Real :=
      fun hAy => hAy.2.2
    let parameter : SparseAdaptiveParameters n k ->
        History n k t × (MSetAction n k × Real) -> Real :=
      fun V hAy => V.value t hAy.1 hAy.2.1
    have hy : Measurable y := measurable_snd.snd
    have hp : forall V, Measurable (parameter V) := by
      intro V
      exact (V.measurable_value t).comp
        (measurable_fst.prodMk measurable_snd.fst)
    exact (((measurable_feedbackLogJacobian_uncurry.comp
          ((hp R.both).prodMk hy)).sub
        (measurable_feedbackLogJacobian_uncurry.comp
          ((hp R.right).prodMk hy))).sub
        (measurable_feedbackLogJacobian_uncurry.comp
          ((hp R.left).prodMk hy))).add
        (measurable_feedbackLogJacobian_uncurry.comp
          ((hp R.base).prodMk hy))
  · exact measurable_const

theorem measurable_sparseCrossRoundEnergy {n k : Nat}
    (R : SparseAdaptiveRectangle n k) (t : Nat) :
    Measurable (sparseCrossRoundEnergy R t) := by
  unfold sparseCrossRoundEnergy
  exact continuous_abs.measurable.comp <|
    (((R.left.measurable_value t).sub
      (R.base.measurable_value t)).mul
    ((R.right.measurable_value t).sub
      (R.base.measurable_value t)))

/-- The Hessian estimate applied to one adaptive four-corner increment. -/
theorem abs_sparseCrossLogIncrement_le {n k : Nat}
    (R : SparseAdaptiveRectangle n k) (t : Nat)
    (hAy : History n k t × (MSetAction n k × Real)) :
    |sparseCrossLogIncrement R t hAy| <=
      128 * sparseCrossRoundEnergy R t (hAy.1, hAy.2.1) := by
  by_cases hy : hAy.2.2 ∈ Icc (-1 / 2 : Real) (1 / 2 : Real)
  · let u := R.base.value t hAy.1 hAy.2.1
    let s := R.left.value t hAy.1 hAy.2.1 - u
    let r := R.right.value t hAy.1 hAy.2.1 - u
    have hus : u + s = R.left.value t hAy.1 hAy.2.1 := by
      simp [u, s]
    have hur : u + r = R.right.value t hAy.1 hAy.2.1 := by
      simp [u, r]
    have husr : u + s + r = R.both.value t hAy.1 hAy.2.1 := by
      dsimp [u, s, r]
      have hrect := R.rectangle t hAy.1 hAy.2.1
      linarith
    have hfour := feedback_density_four_term
      (u := u) (s := s) (t := r) (y := hAy.2.2)
      (R.base.abs_le t hAy.1 hAy.2.1)
      (by simpa only [hus] using R.left.abs_le t hAy.1 hAy.2.1)
      (by simpa only [hur] using R.right.abs_le t hAy.1 hAy.2.1)
      (by simpa only [husr] using R.both.abs_le t hAy.1 hAy.2.1)
      hy
    rw [husr, hus, hur] at hfour
    rw [sparseCrossLogIncrement, if_pos hy, sparseCrossRoundEnergy]
    have heq :
        R.both.value t hAy.1 hAy.2.1 |> fun q =>
          feedbackLogJacobian q hAy.2.2 -
            feedbackLogJacobian (R.right.value t hAy.1 hAy.2.1) hAy.2.2 -
            feedbackLogJacobian (R.left.value t hAy.1 hAy.2.1) hAy.2.2 +
            feedbackLogJacobian (R.base.value t hAy.1 hAy.2.1) hAy.2.2 =
          -(feedbackLogJacobian (R.left.value t hAy.1 hAy.2.1) hAy.2.2 +
            feedbackLogJacobian (R.right.value t hAy.1 hAy.2.1) hAy.2.2 -
            feedbackLogJacobian (R.base.value t hAy.1 hAy.2.1) hAy.2.2 -
            feedbackLogJacobian (R.both.value t hAy.1 hAy.2.1) hAy.2.2) := by
      dsimp
      ring
    rw [heq, abs_neg]
    simpa only [s, r] using hfour
  · rw [sparseCrossLogIncrement, if_neg hy]
    norm_num [sparseCrossRoundEnergy]
    exact mul_nonneg (abs_nonneg _) (abs_nonneg _)

/-- On the common feedback support, exponentiating the four-corner logarithm
is exactly the product of the two scalar density ratios that remains after
the hidden-coordinate factors cancel. -/
theorem exp_sparseCrossLogIncrement_eq_density_ratios
    {n k : Nat} (R : SparseAdaptiveRectangle n k) (t : Nat)
    (hAy : History n k t × (MSetAction n k × Real))
    (hy : hAy.2.2 ∈ Icc (-1 / 2 : Real) (1 / 2 : Real)) :
    Real.exp (sparseCrossLogIncrement R t hAy) =
      (feedbackDensity (R.left.value t hAy.1 hAy.2.1) hAy.2.2 /
        feedbackDensity (R.both.value t hAy.1 hAy.2.1) hAy.2.2) *
      (feedbackDensity (R.right.value t hAy.1 hAy.2.1) hAy.2.2 /
        feedbackDensity (R.base.value t hAy.1 hAy.2.1) hAy.2.2) := by
  let ub := R.base.value t hAy.1 hAy.2.1
  let ul := R.left.value t hAy.1 hAy.2.1
  let ur := R.right.value t hAy.1 hAy.2.1
  let ubl := R.both.value t hAy.1 hAy.2.1
  let y := hAy.2.2
  have hJb : 0 < feedbackJacobian ub y :=
    lt_of_lt_of_le (by norm_num) (feedbackJacobian_mem_Icc
      (R.base.abs_le t hAy.1 hAy.2.1) hy).1
  have hJl : 0 < feedbackJacobian ul y :=
    lt_of_lt_of_le (by norm_num) (feedbackJacobian_mem_Icc
      (R.left.abs_le t hAy.1 hAy.2.1) hy).1
  have hJr : 0 < feedbackJacobian ur y :=
    lt_of_lt_of_le (by norm_num) (feedbackJacobian_mem_Icc
      (R.right.abs_le t hAy.1 hAy.2.1) hy).1
  have hJbl : 0 < feedbackJacobian ubl y :=
    lt_of_lt_of_le (by norm_num) (feedbackJacobian_mem_Icc
      (R.both.abs_le t hAy.1 hAy.2.1) hy).1
  rw [sparseCrossLogIncrement, if_pos hy]
  change Real.exp
      (feedbackLogJacobian ubl y - feedbackLogJacobian ur y -
        feedbackLogJacobian ul y + feedbackLogJacobian ub y) =
      (feedbackDensity ul y / feedbackDensity ubl y) *
        (feedbackDensity ur y / feedbackDensity ub y)
  rw [show feedbackLogJacobian ubl y - feedbackLogJacobian ur y -
        feedbackLogJacobian ul y + feedbackLogJacobian ub y =
      (feedbackLogJacobian ubl y + feedbackLogJacobian ub y) -
        (feedbackLogJacobian ur y + feedbackLogJacobian ul y) by ring,
    Real.exp_sub, Real.exp_add, Real.exp_add]
  unfold feedbackLogJacobian
  rw [Real.exp_log hJbl, Real.exp_log hJb,
    Real.exp_log hJr, Real.exp_log hJl]
  rw [feedbackDensity_eq_core hy, feedbackDensity_eq_core hy,
    feedbackDensity_eq_core hy, feedbackDensity_eq_core hy]
  unfold feedbackDensityCore
  dsimp only [y] at hJb hJl hJr hJbl ⊢
  field_simp [ne_of_gt hJb, ne_of_gt hJl, ne_of_gt hJr, ne_of_gt hJbl]

/-- ENNReal form of the preceding exact one-round density identity. -/
theorem sparseCrossRoundLikelihood_eq_densityRatios
    {n k : Nat} (R : SparseAdaptiveRectangle n k) (t : Nat)
    (hAy : History n k t × (MSetAction n k × Real))
    (hy : hAy.2.2 ∈ Icc (-1 / 2 : Real) (1 / 2 : Real)) :
    ENNReal.ofReal (Real.exp (sparseCrossLogIncrement R t hAy)) =
      feedbackDensityRatio
          (R.left.value t hAy.1 hAy.2.1)
          (R.both.value t hAy.1 hAy.2.1) hAy.2.2 *
        feedbackDensityRatio
          (R.right.value t hAy.1 hAy.2.1)
          (R.base.value t hAy.1 hAy.2.1) hAy.2.2 := by
  unfold feedbackDensityRatio
  have hleft0 : 0 <=
      feedbackDensity (R.left.value t hAy.1 hAy.2.1) hAy.2.2 /
        feedbackDensity (R.both.value t hAy.1 hAy.2.1) hAy.2.2 := by
    exact div_nonneg
      (feedbackDensity_nonneg (R.left.abs_le t hAy.1 hAy.2.1))
      (feedbackDensity_nonneg (R.both.abs_le t hAy.1 hAy.2.1))
  rw [← ENNReal.ofReal_mul hleft0,
    exp_sparseCrossLogIncrement_eq_density_ratios R t hAy hy]

/-- Cumulative four-corner logarithm along a realized adaptive history. -/
def sparseCrossLog {n k : Nat} (R : SparseAdaptiveRectangle n k) :
    (T : Nat) -> History n k T -> Real
  | 0, _ => 0
  | t + 1, h => sparseCrossLog R t h.1 + sparseCrossLogIncrement R t h

/-- Cumulative overlap energy of the two parameter perturbations. -/
def sparseCrossEnergy {n k : Nat} (R : SparseAdaptiveRectangle n k) :
    (T : Nat) -> History n k T -> Real
  | 0, _ => 0
  | t + 1, h => sparseCrossEnergy R t h.1 +
      sparseCrossRoundEnergy R t (h.1, h.2.1)

theorem measurable_sparseCrossLog {n k : Nat}
    (R : SparseAdaptiveRectangle n k) : forall T,
    Measurable (sparseCrossLog R T) := by
  intro T
  induction T with
  | zero => exact measurable_const
  | succ t ih =>
      exact (ih.comp measurable_fst).add
        (measurable_sparseCrossLogIncrement R t)

theorem measurable_sparseCrossEnergy {n k : Nat}
    (R : SparseAdaptiveRectangle n k) : forall T,
    Measurable (sparseCrossEnergy R T) := by
  intro T
  induction T with
  | zero => exact measurable_const
  | succ t ih =>
      exact (ih.comp measurable_fst).add
        ((measurable_sparseCrossRoundEnergy R t).comp
          (measurable_fst.prodMk measurable_snd.fst))

theorem sparseCrossEnergy_nonneg {n k : Nat}
    (R : SparseAdaptiveRectangle n k) : forall T (h : History n k T),
    0 <= sparseCrossEnergy R T h := by
  intro T
  induction T with
  | zero => intro h; rfl
  | succ t ih =>
      intro h
      exact add_nonneg (ih h.1) (abs_nonneg _)

/-- Pathwise form of the four-term density estimate in the sparse adaptive
experiment.  In the concrete construction the right-hand side is
`128 * a^2 * eta^2 * N_jl`. -/
theorem abs_sparseCrossLog_le {n k : Nat}
    (R : SparseAdaptiveRectangle n k) : forall T (h : History n k T),
    |sparseCrossLog R T h| <= 128 * sparseCrossEnergy R T h := by
  intro T
  induction T with
  | zero => intro h; norm_num [sparseCrossLog, sparseCrossEnergy]
  | succ t ih =>
      intro h
      calc
        |sparseCrossLog R (t + 1) h| <=
            |sparseCrossLog R t h.1| +
              |sparseCrossLogIncrement R t h| := by
                simpa only [sparseCrossLog] using
                  abs_add_le (sparseCrossLog R t h.1)
                    (sparseCrossLogIncrement R t h)
        _ <= 128 * sparseCrossEnergy R t h.1 +
              128 * sparseCrossRoundEnergy R t (h.1, h.2.1) :=
            add_le_add (ih h.1) (abs_sparseCrossLogIncrement_le R t h)
        _ = 128 * sparseCrossEnergy R (t + 1) h := by
            simp only [sparseCrossEnergy]
            ring

/-- Elementary exponential remainder bound used in
`eq:lower-likelihood-cross`. -/
theorem exp_sub_one_le_self_mul_exp {x : Real} :
    Real.exp x - 1 <= x * Real.exp x := by
  have h := Real.add_one_le_exp (-x)
  have hmul := mul_le_mul_of_nonneg_left h (Real.exp_pos x).le
  rw [← Real.exp_add] at hmul
  norm_num at hmul
  nlinarith

/-- The positive four-corner likelihood factor. -/
def sparseCrossLikelihood {n k : Nat}
    (R : SparseAdaptiveRectangle n k) (T : Nat)
    (h : History n k T) : ENNReal :=
  ENNReal.ofReal (Real.exp (sparseCrossLog R T h))

theorem measurable_sparseCrossLikelihood {n k : Nat}
    (R : SparseAdaptiveRectangle n k) (T : Nat) :
    Measurable (sparseCrossLikelihood R T) := by
  exact Measurable.ennreal_ofReal <|
    Measurable.exp (measurable_sparseCrossLog R T)

/-- Pointwise exponential conversion of the Hessian estimate. -/
theorem sparseCrossLikelihood_le {n k : Nat}
    (R : SparseAdaptiveRectangle n k) (T : Nat)
    (C : Real) (hC : forall h : History n k T,
      sparseCrossEnergy R T h <= C) (h : History n k T) :
    sparseCrossLikelihood R T h <=
      1 + ENNReal.ofReal (128 * Real.exp (128 * C)) *
        ENNReal.ofReal (sparseCrossEnergy R T h) := by
  let E := sparseCrossEnergy R T h
  let L := sparseCrossLog R T h
  have hE : 0 <= E := sparseCrossEnergy_nonneg R T h
  have hL : L <= 128 * E :=
    le_trans (le_abs_self L) (abs_sparseCrossLog_le R T h)
  have hEC : E <= C := hC h
  have hexpL : Real.exp L <= Real.exp (128 * E) :=
    Real.exp_le_exp.mpr hL
  have hrem : Real.exp (128 * E) - 1 <=
      (128 * E) * Real.exp (128 * E) :=
    exp_sub_one_le_self_mul_exp
  have hexpEC : Real.exp (128 * E) <= Real.exp (128 * C) := by
    apply Real.exp_le_exp.mpr
    exact mul_le_mul_of_nonneg_left hEC (by norm_num)
  have hreal : Real.exp L <=
      1 + (128 * Real.exp (128 * C)) * E := by
    have hmul : (128 * E) * Real.exp (128 * E) <=
        (128 * E) * Real.exp (128 * C) :=
      mul_le_mul_of_nonneg_left hexpEC
        (mul_nonneg (by norm_num) hE)
    calc
      Real.exp L <= Real.exp (128 * E) := hexpL
      _ <= 1 + (128 * E) * Real.exp (128 * E) := by linarith
      _ <= 1 + (128 * E) * Real.exp (128 * C) :=
        by nlinarith
      _ = 1 + (128 * Real.exp (128 * C)) * E := by ring
  unfold sparseCrossLikelihood
  calc
    ENNReal.ofReal (Real.exp L) <=
        ENNReal.ofReal (1 + (128 * Real.exp (128 * C)) * E) :=
      ENNReal.ofReal_le_ofReal hreal
    _ = 1 + ENNReal.ofReal (128 * Real.exp (128 * C)) *
          ENNReal.ofReal E := by
      rw [ENNReal.ofReal_add
          (by norm_num)
          (mul_nonneg (mul_nonneg (by norm_num) (Real.exp_pos _).le) hE),
        ENNReal.ofReal_mul
          (mul_nonneg (by norm_num) (Real.exp_pos _).le)]
      norm_num

/-! ### Identification of the overlap energy with `N_{jl}`

The preceding rectangle argument was deliberately independent of the
particular sparse table.  We now insert the manuscript's actual displacement
`delta_{t,j}=-(a*eta/k)m_{t,j}g(U_{b(t),j})` and recover its literal
`a^2 eta^2 N_{jl}` energy budget.
-/

/-- Apply the manuscript's one-dimensional hidden-coordinate map
`T_a(u)=u+a*g(u)` to one signal column in every block. -/
def sparseTransformTableCoordinate {n n' : Nat}
    (a : Real) (hn' : n' <= n) (U : Nat -> Fin n -> Real)
    (j : Fin n') (b : Nat) (i : Fin n) : Real :=
  if i = sparseSignalCoordinate hn' j then
    U b i + a * Feedback.shape (U b i)
  else U b i

/-- Transforming one table column adds exactly one selected active score
term. -/
theorem sparseActionScore_transform_coordinate
    {n n' k q c0 : Nat} (a : Real) (hn' : n' <= n)
    (U : Nat -> Fin n -> Real) (j : Fin n')
    (t : Nat) (h : History n k t) (A : MSetAction n k) :
    sparseActionScore n' q c0
        (sparseTransformTableCoordinate a hn' U j) t h A =
      sparseActionScore n' q c0 U t h A +
        a * sparsePullIndicator hn' q c0 j t h A *
          Feedback.shape (U (t / q) (sparseSignalCoordinate hn' j)) := by
  classical
  let i0 : Fin n := sparseSignalCoordinate hn' j
  let g0 : Real := Feedback.shape (U (t / q) i0)
  have hi0 : i0.1 < n' := by
    simpa [i0, sparseSignalCoordinate] using j.2
  have hpoint : (fun i : Fin n =>
      sparseActive q c0 i t h *
        sparseSignalWeight n' q
          (sparseTransformTableCoordinate a hn' U j) t i) =
      fun i =>
        sparseActive q c0 i t h * sparseSignalWeight n' q U t i +
          if i = i0 then sparseActive q c0 i0 t h * (a * g0) else 0 := by
    funext i
    by_cases hi : i = i0
    · subst i
      simp [sparseSignalWeight, sparseTransformTableCoordinate,
        i0, g0, hi0]
      ring
    · by_cases hin : i.1 < n'
      · simp [sparseSignalWeight, sparseTransformTableCoordinate,
          i0, g0, hin, hi]
      · simp [sparseSignalWeight, i0, hin, hi]
  unfold sparseActionScore
  rw [hpoint, actionLoss_add]
  congr 1
  unfold actionLoss sparsePullIndicator History.selectedIndicator
  by_cases hmem : i0 ∈ A.1
  · simp [i0, g0, hmem]
    ring
  · simp [i0, g0, hmem]

/-- Exact parameter change `u_t -> u_t + delta_{t,j}` under the concrete
table transformation. -/
theorem sparseFeedbackParameter_transform_coordinate_sub
    {n n' k q c0 : Nat} (a eta : Real) (hn' : n' <= n)
    (U : Nat -> Fin n -> Real) (j : Fin n')
    (t : Nat) (h : History n k t) (A : MSetAction n k) :
    sparseFeedbackParameter eta n' q c0
        (sparseTransformTableCoordinate a hn' U j) t h A -
      sparseFeedbackParameter eta n' q c0 U t h A =
      -(a * eta / (k : Real)) * sparsePullIndicator hn' q c0 j t h A *
        Feedback.shape (U (t / q) (sparseSignalCoordinate hn' j)) := by
  unfold sparseFeedbackParameter
  rw [sparseActionScore_transform_coordinate]
  ring

theorem measurable_sparseFeedbackParameter_joint
    {n k : Nat} (eta : Real) (n' q c0 : Nat)
    (U : Nat -> Fin n -> Real) (t : Nat) :
    Measurable (fun hA : History n k t × MSetAction n k =>
      sparseFeedbackParameter eta n' q c0 U t hA.1 hA.2) := by
  have hitem : Measurable (fun h : History n k t => fun i : Fin n =>
      sparseActive q c0 i t h * sparseSignalWeight n' q U t i) := by
    refine Measurable.of_eval fun i => ?_
    exact (measurable_sparseActive i t).mul measurable_const
  unfold sparseFeedbackParameter sparseActionScore
  exact measurable_const.mul (measurable_actionLoss_joint hitem)

/-- A fixed sparse hidden table defines a genuine adaptive density parameter
field.  Its domain bound is derived from the construction's score estimate. -/
def sparseAdaptiveParametersOfTable
    {n k : Nat} (hk : 1 <= k) (eta : Real)
    (heta0 : 0 <= eta) (heta : eta <= (1 : Real) / 16)
    (n' q c0 : Nat) (U : Nat -> Fin n -> Real)
    (hU : forall b i, |U b i| <= 1) : SparseAdaptiveParameters n k where
  value t h A := sparseFeedbackParameter eta n' q c0 U t h A
  measurable_value t := measurable_sparseFeedbackParameter_joint eta n' q c0 U t
  abs_le t h A := (sparseFeedbackParameter_abs_le hk heta0 hU t h A).trans heta

theorem sparseTransformTableCoordinate_other
    {n n' : Nat} (a : Real) (hn' : n' <= n)
    (U : Nat -> Fin n -> Real) {j l : Fin n'} (hjl : j ≠ l)
    (b : Nat) :
    sparseTransformTableCoordinate a hn' U l b
        (sparseSignalCoordinate hn' j) =
      U b (sparseSignalCoordinate hn' j) := by
  have hcoord : sparseSignalCoordinate hn' j ≠
      sparseSignalCoordinate hn' l := by
    exact fun h => hjl ((sparseSignalCoordinate_injective hn') h)
  simp [sparseTransformTableCoordinate, hcoord]

/-- The four concrete tables form the additive feedback-parameter rectangle
needed by the Hessian calculation. -/
theorem sparseFeedbackParameter_transform_rectangle
    {n n' k q c0 : Nat} (a eta : Real) (hn' : n' <= n)
    (U : Nat -> Fin n -> Real) {j l : Fin n'} (hjl : j ≠ l)
    (t : Nat) (h : History n k t) (A : MSetAction n k) :
    sparseFeedbackParameter eta n' q c0
        (sparseTransformTableCoordinate a hn'
          (sparseTransformTableCoordinate a hn' U l) j) t h A +
      sparseFeedbackParameter eta n' q c0 U t h A =
    sparseFeedbackParameter eta n' q c0
        (sparseTransformTableCoordinate a hn' U j) t h A +
      sparseFeedbackParameter eta n' q c0
        (sparseTransformTableCoordinate a hn' U l) t h A := by
  have hboth := sparseFeedbackParameter_transform_coordinate_sub
    (q := q) (c0 := c0) a eta hn'
      (sparseTransformTableCoordinate a hn' U l) j t h A
  have hleft := sparseFeedbackParameter_transform_coordinate_sub
    (q := q) (c0 := c0) a eta hn' U j t h A
  rw [sparseTransformTableCoordinate_other a hn' U hjl] at hboth
  linarith

/-- The parameter displacement caused by transforming one hidden signal
coordinate. -/
def sparseCoordinatePerturbation {n n' k : Nat}
    (a eta : Real) (hn' : n' <= n) (q c0 : Nat)
    (U : Nat -> Fin n -> Real) (j : Fin n')
    (t : Nat) (h : History n k t) (A : MSetAction n k) : Real :=
  -(a * eta / (k : Real)) * sparsePullIndicator hn' q c0 j t h A *
    Feedback.shape (U (t / q) (sparseSignalCoordinate hn' j))

/-- The concrete four-table adaptive rectangle. -/
def sparseAdaptiveRectangleOfTable
    {n n' k q c0 : Nat} (hk : 1 <= k)
    (eta : Real) (heta0 : 0 <= eta)
    (heta : eta <= (1 : Real) / 16)
    (a : Real) (hn' : n' <= n) (U : Nat -> Fin n -> Real)
    (j l : Fin n') (hjl : j ≠ l)
    (hU : forall b i, |U b i| <= 1)
    (hUj : forall b i,
      |sparseTransformTableCoordinate a hn' U j b i| <= 1)
    (hUl : forall b i,
      |sparseTransformTableCoordinate a hn' U l b i| <= 1)
    (hUjl : forall b i,
      |sparseTransformTableCoordinate a hn'
        (sparseTransformTableCoordinate a hn' U l) j b i| <= 1) :
    SparseAdaptiveRectangle n k where
  base := sparseAdaptiveParametersOfTable hk eta heta0 heta n' q c0 U hU
  left := sparseAdaptiveParametersOfTable hk eta heta0 heta n' q c0
    (sparseTransformTableCoordinate a hn' U j) hUj
  right := sparseAdaptiveParametersOfTable hk eta heta0 heta n' q c0
    (sparseTransformTableCoordinate a hn' U l) hUl
  both := sparseAdaptiveParametersOfTable hk eta heta0 heta n' q c0
    (sparseTransformTableCoordinate a hn'
      (sparseTransformTableCoordinate a hn' U l) j) hUjl
  rectangle t h A := sparseFeedbackParameter_transform_rectangle
    a eta hn' U hjl t h A

@[simp] theorem sparseAdaptiveRectangleOfTable_left_sub
    {n n' k q c0 : Nat} (hk : 1 <= k)
    (eta : Real) (heta0 : 0 <= eta)
    (heta : eta <= (1 : Real) / 16)
    (a : Real) (hn' : n' <= n) (U : Nat -> Fin n -> Real)
    (j l : Fin n') (hjl : j ≠ l)
    (hU : forall b i, |U b i| <= 1)
    (hUj : forall b i,
      |sparseTransformTableCoordinate a hn' U j b i| <= 1)
    (hUl : forall b i,
      |sparseTransformTableCoordinate a hn' U l b i| <= 1)
    (hUjl : forall b i,
      |sparseTransformTableCoordinate a hn'
        (sparseTransformTableCoordinate a hn' U l) j b i| <= 1)
    (t : Nat) (h : History n k t) (A : MSetAction n k) :
    (sparseAdaptiveRectangleOfTable (q := q) (c0 := c0)
      hk eta heta0 heta a hn' U j l hjl
      hU hUj hUl hUjl).left.value t h A -
      (sparseAdaptiveRectangleOfTable (q := q) (c0 := c0)
        hk eta heta0 heta a hn' U j l hjl
        hU hUj hUl hUjl).base.value t h A =
      sparseCoordinatePerturbation a eta hn' q c0 U j t h A := by
  exact sparseFeedbackParameter_transform_coordinate_sub
    (q := q) (c0 := c0) a eta hn' U j t h A

@[simp] theorem sparseAdaptiveRectangleOfTable_right_sub
    {n n' k q c0 : Nat} (hk : 1 <= k)
    (eta : Real) (heta0 : 0 <= eta)
    (heta : eta <= (1 : Real) / 16)
    (a : Real) (hn' : n' <= n) (U : Nat -> Fin n -> Real)
    (j l : Fin n') (hjl : j ≠ l)
    (hU : forall b i, |U b i| <= 1)
    (hUj : forall b i,
      |sparseTransformTableCoordinate a hn' U j b i| <= 1)
    (hUl : forall b i,
      |sparseTransformTableCoordinate a hn' U l b i| <= 1)
    (hUjl : forall b i,
      |sparseTransformTableCoordinate a hn'
        (sparseTransformTableCoordinate a hn' U l) j b i| <= 1)
    (t : Nat) (h : History n k t) (A : MSetAction n k) :
    (sparseAdaptiveRectangleOfTable (q := q) (c0 := c0)
      hk eta heta0 heta a hn' U j l hjl
      hU hUj hUl hUjl).right.value t h A -
      (sparseAdaptiveRectangleOfTable (q := q) (c0 := c0)
        hk eta heta0 heta a hn' U j l hjl
        hU hUj hUl hUjl).base.value t h A =
      sparseCoordinatePerturbation a eta hn' q c0 U l t h A := by
  exact sparseFeedbackParameter_transform_coordinate_sub
    (q := q) (c0 := c0) a eta hn' U l t h A

private theorem abs_scaled_indicator_product_le
    (c mj ml gj gl : Real)
    (hmj : mj ∈ Icc (0 : Real) 1) (hml : ml ∈ Icc (0 : Real) 1)
    (hgj : gj ∈ Icc (0 : Real) 1) (hgl : gl ∈ Icc (0 : Real) 1) :
    |(-c * mj * gj) * (-c * ml * gl)| <= c ^ 2 * (mj * ml) := by
  have hgg : gj * gl <= 1 := by
    calc
      gj * gl <= 1 * gl := mul_le_mul_of_nonneg_right hgj.2 hgl.1
      _ <= 1 := by simpa using hgl.2
  rw [abs_mul, abs_mul, abs_mul, abs_neg, abs_mul, abs_mul, abs_neg,
    abs_of_nonneg hmj.1, abs_of_nonneg hml.1,
    abs_of_nonneg hgj.1, abs_of_nonneg hgl.1]
  calc
    |c| * mj * gj * (|c| * ml * gl) =
        |c| ^ 2 * (mj * ml) * (gj * gl) := by ring
    _ <= |c| ^ 2 * (mj * ml) * 1 :=
      mul_le_mul_of_nonneg_left hgg
        (mul_nonneg (sq_nonneg _) (mul_nonneg hmj.1 hml.1))
    _ = c ^ 2 * (mj * ml) := by rw [sq_abs]; ring

theorem abs_sparseCoordinatePerturbation_mul_le
    {n n' k q c0 t : Nat} (a eta : Real) (hn' : n' <= n)
    (U : Nat -> Fin n -> Real)
    (hU : forall b i, U b i ∈ Icc (-1 : Real) 1)
    (j l : Fin n') (h : History n k t) (A : MSetAction n k) :
    |sparseCoordinatePerturbation a eta hn' q c0 U j t h A *
        sparseCoordinatePerturbation a eta hn' q c0 U l t h A| <=
      (a * eta / (k : Real)) ^ 2 *
        (sparsePullIndicator hn' q c0 j t h A *
          sparsePullIndicator hn' q c0 l t h A) := by
  unfold sparseCoordinatePerturbation
  exact abs_scaled_indicator_product_le
    (a * eta / (k : Real))
    (sparsePullIndicator hn' q c0 j t h A)
    (sparsePullIndicator hn' q c0 l t h A)
    (Feedback.shape (U (t / q) (sparseSignalCoordinate hn' j)))
    (Feedback.shape (U (t / q) (sparseSignalCoordinate hn' l)))
    (sparsePullIndicator_mem_Icc hn' j h A)
    (sparsePullIndicator_mem_Icc hn' l h A)
    (Feedback.shape_mem_Icc (hU _ _))
    (Feedback.shape_mem_Icc (hU _ _))

/-- The concrete perturbation equations imply the exact cumulative overlap
budget before normalization by `k^2`. -/
theorem sparseCrossEnergy_le_scaledPairPullSum
    {n n' k q c0 : Nat} (a eta : Real) (hn' : n' <= n)
    (U : Nat -> Fin n -> Real)
    (hU : forall b i, U b i ∈ Icc (-1 : Real) 1)
    (j l : Fin n') (R : SparseAdaptiveRectangle n k)
    (hleft : forall t h A,
      R.left.value t h A - R.base.value t h A =
        sparseCoordinatePerturbation a eta hn' q c0 U j t h A)
    (hright : forall t h A,
      R.right.value t h A - R.base.value t h A =
        sparseCoordinatePerturbation a eta hn' q c0 U l t h A) :
    forall T (h : History n k T),
      sparseCrossEnergy R T h <=
        (a * eta / (k : Real)) ^ 2 *
          sparsePairPullSum hn' q c0 j l T h := by
  intro T
  induction T with
  | zero => intro h; norm_num [sparseCrossEnergy]
  | succ t ih =>
      intro h
      have hround : sparseCrossRoundEnergy R t (h.1, h.2.1) <=
          (a * eta / (k : Real)) ^ 2 *
            (sparsePullIndicator hn' q c0 j t h.1 h.2.1 *
              sparsePullIndicator hn' q c0 l t h.1 h.2.1) := by
        rw [sparseCrossRoundEnergy, hleft, hright]
        exact abs_sparseCoordinatePerturbation_mul_le
          a eta hn' U hU j l h.1 h.2.1
      rw [sparseCrossEnergy, sparsePairPullSum_succ]
      calc
        sparseCrossEnergy R t h.1 +
            sparseCrossRoundEnergy R t (h.1, h.2.1) <=
          (a * eta / (k : Real)) ^ 2 *
              sparsePairPullSum hn' q c0 j l t h.1 +
            (a * eta / (k : Real)) ^ 2 *
              (sparsePullIndicator hn' q c0 j t h.1 h.2.1 *
                sparsePullIndicator hn' q c0 l t h.1 h.2.1) :=
          add_le_add (ih h.1) hround
        _ = (a * eta / (k : Real)) ^ 2 *
            (sparsePairPullSum hn' q c0 j l t h.1 +
              sparsePullIndicator hn' q c0 j t h.1 h.2.1 *
                sparsePullIndicator hn' q c0 l t h.1 h.2.1) := by ring

/-- Literal normalization of the preceding estimate by the manuscript's
`N_{jl}=k^{-2} sum_t m_{t,j}m_{t,l}`. -/
theorem sparseCrossEnergy_le_a_eta_sq_mul_sparseN
    {n n' k q c0 : Nat} (hk : 1 <= k)
    (a eta : Real) (hn' : n' <= n)
    (U : Nat -> Fin n -> Real)
    (hU : forall b i, U b i ∈ Icc (-1 : Real) 1)
    (j l : Fin n') (R : SparseAdaptiveRectangle n k)
    (hleft : forall t h A,
      R.left.value t h A - R.base.value t h A =
        sparseCoordinatePerturbation a eta hn' q c0 U j t h A)
    (hright : forall t h A,
      R.right.value t h A - R.base.value t h A =
        sparseCoordinatePerturbation a eta hn' q c0 U l t h A)
    (T : Nat) (h : History n k T) :
    sparseCrossEnergy R T h <=
      a ^ 2 * eta ^ 2 * sparseN hn' q c0 j l T h := by
  have hk0 : (k : Real) ≠ 0 := by
    exact_mod_cast (Nat.ne_of_gt hk)
  calc
    sparseCrossEnergy R T h <=
        (a * eta / (k : Real)) ^ 2 *
          sparsePairPullSum hn' q c0 j l T h :=
      sparseCrossEnergy_le_scaledPairPullSum
        a eta hn' U hU j l R hleft hright T h
    _ = a ^ 2 * eta ^ 2 * sparseN hn' q c0 j l T h := by
      unfold sparseN
      field_simp [hk0]

/-- Integrated form of `eq:lower-likelihood-cross`.  It is stated for the
actual adaptive base law, so the expectation still allows arbitrary
history-dependent learner actions.  Subtracting one from the two sides gives
the manuscript's displayed excess-likelihood bound. -/
theorem lower_likelihood_cross_temporal
    {n k : Nat} (P : Policy n k)
    (R : SparseAdaptiveRectangle n k) (T : Nat) (C : Real)
    (henergy : forall h : History n k T,
      sparseCrossEnergy R T h <= C) :
    (∫⁻ h, sparseCrossLikelihood R T h
      ∂(sparseAdaptiveProcess P R.base).law T) <=
      1 + ENNReal.ofReal (128 * Real.exp (128 * C)) *
        (∫⁻ h, ENNReal.ofReal (sparseCrossEnergy R T h)
          ∂(sparseAdaptiveProcess P R.base).law T) := by
  calc
    (∫⁻ h, sparseCrossLikelihood R T h
        ∂(sparseAdaptiveProcess P R.base).law T) <=
      ∫⁻ h, (1 + ENNReal.ofReal (128 * Real.exp (128 * C)) *
          ENNReal.ofReal (sparseCrossEnergy R T h))
        ∂(sparseAdaptiveProcess P R.base).law T := by
          apply lintegral_mono
          exact sparseCrossLikelihood_le R T C henergy
    _ = (∫⁻ _h : History n k T, (1 : ENNReal)
          ∂(sparseAdaptiveProcess P R.base).law T) +
        ∫⁻ h, ENNReal.ofReal (128 * Real.exp (128 * C)) *
          ENNReal.ofReal (sparseCrossEnergy R T h)
          ∂(sparseAdaptiveProcess P R.base).law T := by
            rw [lintegral_add_left]
            exact measurable_const
    _ = 1 + ENNReal.ofReal (128 * Real.exp (128 * C)) *
        (∫⁻ h, ENNReal.ofReal (sparseCrossEnergy R T h)
          ∂(sparseAdaptiveProcess P R.base).law T) := by
      rw [lintegral_const_mul]
      · simp
      · exact Measurable.ennreal_ofReal (measurable_sparseCrossEnergy R T)

/-- Concrete `eq:lower-likelihood-cross`: after identifying the two
displacements with the transformed hidden coordinates, the right-hand side is
the manuscript's constant times `E N_{jl}`.  Taking
`C = a^2 * rho * B` gives the displayed exponential factor verbatim. -/
theorem lower_likelihood_cross_sparse
    {n n' k q c0 : Nat} (hk : 1 <= k) (P : Policy n k)
    (a eta : Real) (hn' : n' <= n)
    (U : Nat -> Fin n -> Real)
    (hU : forall b i, U b i ∈ Icc (-1 : Real) 1)
    (j l : Fin n') (R : SparseAdaptiveRectangle n k)
    (hleft : forall t h A,
      R.left.value t h A - R.base.value t h A =
        sparseCoordinatePerturbation a eta hn' q c0 U j t h A)
    (hright : forall t h A,
      R.right.value t h A - R.base.value t h A =
        sparseCoordinatePerturbation a eta hn' q c0 U l t h A)
    (T : Nat) (C : Real)
    (hbudget : forall h : History n k T,
      a ^ 2 * eta ^ 2 * sparseN hn' q c0 j l T h <= C) :
    (∫⁻ h, sparseCrossLikelihood R T h
      ∂(sparseAdaptiveProcess P R.base).law T) <=
      1 + ENNReal.ofReal
          (128 * a ^ 2 * eta ^ 2 * Real.exp (128 * C)) *
        (∫⁻ h, ENNReal.ofReal (sparseN hn' q c0 j l T h)
          ∂(sparseAdaptiveProcess P R.base).law T) := by
  let mu := (sparseAdaptiveProcess P R.base).law T
  let c : Real := a ^ 2 * eta ^ 2
  have hc : 0 <= c := mul_nonneg (sq_nonneg _) (sq_nonneg _)
  have henergy : forall h : History n k T,
      sparseCrossEnergy R T h <= C := by
    intro h
    exact (sparseCrossEnergy_le_a_eta_sq_mul_sparseN
      hk a eta hn' U hU j l R hleft hright T h).trans (hbudget h)
  have hNmeas : Measurable (fun h : History n k T =>
      ENNReal.ofReal (sparseN hn' q c0 j l T h)) :=
    Measurable.ennreal_ofReal (measurable_sparseN hn' j l T)
  have hlin :
      (∫⁻ h, ENNReal.ofReal (sparseCrossEnergy R T h) ∂mu) <=
        ENNReal.ofReal c *
          (∫⁻ h, ENNReal.ofReal (sparseN hn' q c0 j l T h) ∂mu) := by
    calc
      (∫⁻ h, ENNReal.ofReal (sparseCrossEnergy R T h) ∂mu) <=
          ∫⁻ h, ENNReal.ofReal
            (c * sparseN hn' q c0 j l T h) ∂mu := by
              apply lintegral_mono
              intro h
              apply ENNReal.ofReal_le_ofReal
              exact sparseCrossEnergy_le_a_eta_sq_mul_sparseN
                hk a eta hn' U hU j l R hleft hright T h
      _ = ∫⁻ h, ENNReal.ofReal c *
          ENNReal.ofReal (sparseN hn' q c0 j l T h) ∂mu := by
            apply lintegral_congr
            intro h
            rw [ENNReal.ofReal_mul hc]
      _ = ENNReal.ofReal c *
          (∫⁻ h, ENNReal.ofReal (sparseN hn' q c0 j l T h) ∂mu) := by
            rw [lintegral_const_mul _ hNmeas]
  calc
    (∫⁻ h, sparseCrossLikelihood R T h ∂mu) <=
      1 + ENNReal.ofReal (128 * Real.exp (128 * C)) *
        (∫⁻ h, ENNReal.ofReal (sparseCrossEnergy R T h) ∂mu) :=
      lower_likelihood_cross_temporal P R T C henergy
    _ <= 1 + ENNReal.ofReal (128 * Real.exp (128 * C)) *
        (ENNReal.ofReal c *
          (∫⁻ h, ENNReal.ofReal (sparseN hn' q c0 j l T h) ∂mu)) := by
            gcongr
    _ = 1 + ENNReal.ofReal
          (128 * a ^ 2 * eta ^ 2 * Real.exp (128 * C)) *
        (∫⁻ h, ENNReal.ofReal (sparseN hn' q c0 j l T h) ∂mu) := by
      rw [← mul_assoc, ← ENNReal.ofReal_mul
        (mul_nonneg (by norm_num) (Real.exp_pos _).le)]
      congr 3
      dsimp [c]
      ring

end

end MsetsLower.Lower.Sparse

#print axioms MsetsLower.Lower.Sparse.lower_single_likelihood_product_adaptive
#print axioms MsetsLower.Lower.Sparse.lower_likelihood_diagonal_temporal
#print axioms MsetsLower.Lower.Sparse.integral_sparseHiddenJacobianProduct_le
#print axioms MsetsLower.Lower.Sparse.abs_sparseCrossLog_le
#print axioms MsetsLower.Lower.Sparse.sparseFeedbackParameter_transform_coordinate_sub
#print axioms MsetsLower.Lower.Sparse.sparseCrossEnergy_le_a_eta_sq_mul_sparseN
#print axioms MsetsLower.Lower.Sparse.lower_likelihood_cross_sparse
