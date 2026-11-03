import MsetsLower.Lower.Sparse.Likelihood
import Mathlib.MeasureTheory.Function.JacobianOneDim

/-!
# Joint hidden-table and adaptive-history likelihoods

This file supplies the joint-law layer behind the sparse likelihood formulas.
The hidden coordinates are sampled first and the learner/feedback history is
then generated conditionally on them.  A measurable change of hidden
coordinates leaves the observed history component fixed; its total density is
the product of the hidden Jacobian and the adaptive feedback likelihood from
`Lower.Sparse.Likelihood`.
-/

namespace MsetsLower.Lower.Sparse

open MsetsLower Feedback Set
open MeasureTheory ProbabilityTheory
open scoped BigOperators ENNReal ProbabilityTheory

noncomputable section

/-! ## Measurable families of adaptive feedback experiments -/

/-- A feedback parameter field jointly measurable in an external hidden
state, the observable past, and the learner action. -/
structure SparseAdaptiveParameterFamily
    (Omega : Type*) [MeasurableSpace Omega] (n k : Nat) where
  value : (t : Nat) -> Omega -> History n k t -> MSetAction n k -> Real
  measurable_value : forall t,
    Measurable (fun z : (Omega × History n k t) × MSetAction n k =>
      value t z.1.1 z.1.2 z.2)
  abs_le : forall t omega h A, |value t omega h A| <= (1 : Real) / 16

/-- Freeze the external hidden state. -/
def SparseAdaptiveParameterFamily.at
    {Omega : Type*} [MeasurableSpace Omega] {n k : Nat}
    (F : SparseAdaptiveParameterFamily Omega n k) (omega : Omega) :
    SparseAdaptiveParameters n k where
  value t h A := F.value t omega h A
  measurable_value t := by
    exact (F.measurable_value t).comp <|
      (measurable_const.prodMk measurable_fst).prodMk measurable_snd
  abs_le t h A := F.abs_le t omega h A

/-- One adaptive round, with the hidden state carried in the kernel domain. -/
def sparseFamilyRoundKernel
    {Omega : Type*} [MeasurableSpace Omega] {n k : Nat}
    (P : Policy n k) (F : SparseAdaptiveParameterFamily Omega n k)
    (t : Nat) :
    Kernel (Omega × History n k t) (MSetAction n k × Real) :=
  (P.kernel t).comap Prod.snd measurable_snd ⊗ₖ
    sparseParamFeedbackKernel
      (fun z : (Omega × History n k t) × MSetAction n k =>
        F.value t z.1.1 z.1.2 z.2)

theorem sparseFamilyRoundKernel_isMarkov
    {Omega : Type*} [MeasurableSpace Omega] {n k : Nat}
    (P : Policy n k) (F : SparseAdaptiveParameterFamily Omega n k)
    (t : Nat) : IsMarkovKernel (sparseFamilyRoundKernel P F t) := by
  unfold sparseFamilyRoundKernel
  letI : IsMarkovKernel (sparseParamFeedbackKernel
      (fun z : (Omega × History n k t) × MSetAction n k =>
        F.value t z.1.1 z.1.2 z.2)) :=
    sparseParamFeedbackKernel_isMarkov _ (F.measurable_value t)
      (fun z => F.abs_le t z.1.1 z.1.2 z.2)
  infer_instance

theorem sparseFamilyRoundKernel_apply
    {Omega : Type*} [MeasurableSpace Omega] {n k : Nat}
    (P : Policy n k) (F : SparseAdaptiveParameterFamily Omega n k)
    (t : Nat) (omega : Omega) (h : History n k t) :
    sparseFamilyRoundKernel P F t (omega, h) =
      sparseAdaptiveRoundKernel P (F.at omega) t h := by
  letI := sparseFamilyRoundKernel_isMarkov P F t
  letI : IsMarkovKernel (sparseParamFeedbackKernel
      (fun z : (Omega × History n k t) × MSetAction n k =>
        F.value t z.1.1 z.1.2 z.2)) :=
    sparseParamFeedbackKernel_isMarkov _ (F.measurable_value t)
      (fun z => F.abs_le t z.1.1 z.1.2 z.2)
  letI : IsMarkovKernel (sparseParamFeedbackKernel
      (fun ha : History n k t × MSetAction n k =>
        (F.at omega).value t ha.1 ha.2)) :=
    sparseParamFeedbackKernel_isMarkov _ ((F.at omega).measurable_value t)
      (fun ha => (F.at omega).abs_le t ha.1 ha.2)
  ext s hs
  rw [sparseFamilyRoundKernel, Kernel.compProd_apply hs,
    sparseAdaptiveRoundKernel, Kernel.compProd_apply hs]
  rw [Kernel.comap_apply]
  apply lintegral_congr
  intro A
  rw [sparseParamFeedbackKernel_apply _ (F.measurable_value t) _
      (F.abs_le t omega h A),
    sparseParamFeedbackKernel_apply _ ((F.at omega).measurable_value t) _
      ((F.at omega).abs_le t h A)]
  rfl

/-- Conditional history law as a Markov kernel of the hidden state. -/
def sparseFamilyLawKernel
    {Omega : Type*} [MeasurableSpace Omega] {n k : Nat}
    (P : Policy n k) (F : SparseAdaptiveParameterFamily Omega n k) :
    (T : Nat) -> Kernel Omega (History n k T)
  | 0 => Kernel.const Omega (Measure.dirac ())
  | t + 1 => sparseFamilyLawKernel P F t ⊗ₖ sparseFamilyRoundKernel P F t

theorem sparseFamilyLawKernel_isMarkov
    {Omega : Type*} [MeasurableSpace Omega] {n k : Nat}
    (P : Policy n k) (F : SparseAdaptiveParameterFamily Omega n k) :
    forall T, IsMarkovKernel (sparseFamilyLawKernel P F T) := by
  intro T
  induction T with
  | zero =>
      unfold sparseFamilyLawKernel
      infer_instance
  | succ t ih =>
      change IsMarkovKernel
        (sparseFamilyLawKernel P F t ⊗ₖ sparseFamilyRoundKernel P F t)
      letI := ih
      letI := sparseFamilyRoundKernel_isMarkov P F t
      infer_instance

instance sparseFamilyLawKernel.instIsMarkovKernel
    {Omega : Type*} [MeasurableSpace Omega] {n k : Nat}
    (P : Policy n k) (F : SparseAdaptiveParameterFamily Omega n k)
    (T : Nat) : IsMarkovKernel (sparseFamilyLawKernel P F T) :=
  sparseFamilyLawKernel_isMarkov P F T

/-- Evaluating the family kernel gives the previously constructed adaptive
history law exactly. -/
theorem sparseFamilyLawKernel_apply
    {Omega : Type*} [MeasurableSpace Omega] {n k : Nat}
    (P : Policy n k) (F : SparseAdaptiveParameterFamily Omega n k) :
    forall T (omega : Omega),
      sparseFamilyLawKernel P F T omega =
        (sparseAdaptiveProcess P (F.at omega)).law T := by
  intro T
  induction T with
  | zero => intro omega; rfl
  | succ t ih =>
      intro omega
      letI := sparseFamilyRoundKernel_isMarkov P F t
      change (sparseFamilyLawKernel P F t ⊗ₖ
          sparseFamilyRoundKernel P F t) omega = _
      rw [HistoryKernelProcess.law_succ]
      ext s hs
      rw [Kernel.compProd_apply hs, Measure.compProd_apply hs, ih]
      apply lintegral_congr
      intro h
      rw [sparseFamilyRoundKernel_apply]
      rfl

/-- Joint law: hidden state first, then the conditional adaptive history. -/
def sparseJointLaw
    {Omega : Type*} [MeasurableSpace Omega] {n k : Nat}
    (mu : Measure Omega) (P : Policy n k)
    (F : SparseAdaptiveParameterFamily Omega n k) (T : Nat) :
    Measure (Omega × History n k T) :=
  mu ⊗ₘ sparseFamilyLawKernel P F T

/-! ## Reindexing the hidden state and the total likelihood -/

/-- The chronological feedback likelihood when a hidden state is reindexed
by a measurable equivalence.  At the image point `omega`, the numerator is
the experiment at `e.symm omega` and the denominator is the experiment at
`omega`. -/
def sparseFamilyLikelihoodProduct
    {Omega : Type*} [MeasurableSpace Omega] {n k : Nat}
    (F : SparseAdaptiveParameterFamily Omega n k) (e : Omega ≃ᵐ Omega) :
    (T : Nat) -> Omega × History n k T -> ENNReal
  | 0, _ => 1
  | t + 1, z =>
      sparseFamilyLikelihoodProduct F e t (z.1, z.2.1) *
        feedbackDensityRatio
          (F.value t (e.symm z.1) z.2.1 z.2.2.1)
          (F.value t z.1 z.2.1 z.2.2.1) z.2.2.2

@[simp] theorem sparseFamilyLikelihoodProduct_zero
    {Omega : Type*} [MeasurableSpace Omega] {n k : Nat}
    (F : SparseAdaptiveParameterFamily Omega n k) (e : Omega ≃ᵐ Omega)
    (z : Omega × History n k 0) :
    sparseFamilyLikelihoodProduct F e 0 z = 1 := rfl

@[simp] theorem sparseFamilyLikelihoodProduct_succ
    {Omega : Type*} [MeasurableSpace Omega] {n k t : Nat}
    (F : SparseAdaptiveParameterFamily Omega n k) (e : Omega ≃ᵐ Omega)
    (z : Omega × History n k (t + 1)) :
    sparseFamilyLikelihoodProduct F e (t + 1) z =
      sparseFamilyLikelihoodProduct F e t (z.1, z.2.1) *
        feedbackDensityRatio
          (F.value t (e.symm z.1) z.2.1 z.2.2.1)
          (F.value t z.1 z.2.1 z.2.2.1) z.2.2.2 := rfl

theorem measurable_sparseFamilyLikelihoodProduct
    {Omega : Type*} [MeasurableSpace Omega] {n k : Nat}
    (F : SparseAdaptiveParameterFamily Omega n k) (e : Omega ≃ᵐ Omega) :
    forall T, Measurable (sparseFamilyLikelihoodProduct F e T) := by
  intro T
  induction T with
  | zero => exact measurable_const
  | succ t ih =>
      have hnum : Measurable (fun z : Omega × History n k (t + 1) =>
          F.value t (e.symm z.1) z.2.1 z.2.2.1) := by
        exact (F.measurable_value t).comp <|
          (((e.symm.measurable.comp measurable_fst).prodMk
            (measurable_fst.comp measurable_snd)).prodMk
              (measurable_fst.comp (measurable_snd.comp measurable_snd)))
      have hden : Measurable (fun z : Omega × History n k (t + 1) =>
          F.value t z.1 z.2.1 z.2.2.1) := by
        exact (F.measurable_value t).comp <|
          ((measurable_fst.prodMk
            (measurable_fst.comp measurable_snd)).prodMk
              (measurable_fst.comp (measurable_snd.comp measurable_snd)))
      have hy : Measurable (fun z : Omega × History n k (t + 1) =>
          z.2.2.2) := measurable_snd.comp (measurable_snd.comp measurable_snd)
      exact
        (ih.comp (measurable_fst.prodMk
          (measurable_fst.comp measurable_snd))).mul
          (measurable_feedbackDensityRatio_joint.comp
            ((hnum.prodMk hden).prodMk hy))

/-- Pointwise identification with the fixed-hidden-state likelihood already
proved in `Likelihood.lean`. -/
theorem sparseFamilyLikelihoodProduct_eq_sparseLikelihoodProduct
    {Omega : Type*} [MeasurableSpace Omega] {n k : Nat}
    (F : SparseAdaptiveParameterFamily Omega n k) (e : Omega ≃ᵐ Omega) :
    forall T (omega : Omega) (h : History n k T),
      sparseFamilyLikelihoodProduct F e T (omega, h) =
        sparseLikelihoodProduct (F.at (e.symm omega)) (F.at omega) T h := by
  intro T
  induction T with
  | zero => intro omega h; rfl
  | succ t ih =>
      intro omega h
      rw [sparseFamilyLikelihoodProduct_succ,
        sparseLikelihoodProduct_succ, ih]
      rfl

/-- Mapping only the hidden component of a composition-product reindexes its
conditional kernel by the inverse measurable equivalence. -/
theorem map_compProd_hidden_equiv
    {Omega H : Type*} [MeasurableSpace Omega] [MeasurableSpace H]
    (mu : Measure Omega) [SFinite mu]
    (K : Kernel Omega H) [IsSFiniteKernel K] (e : Omega ≃ᵐ Omega) :
    Measure.map (fun z : Omega × H => (e z.1, z.2)) (mu ⊗ₘ K) =
      Measure.map e mu ⊗ₘ K.comap e.symm e.symm.measurable := by
  have hphi : Measurable (fun z : Omega × H => (e z.1, z.2)) :=
    (e.measurable.comp measurable_fst).prodMk measurable_snd
  ext s hs
  rw [Measure.map_apply hphi hs,
    Measure.compProd_apply (hs.preimage hphi),
    Measure.compProd_apply hs]
  rw [lintegral_map (Kernel.measurable_kernel_prodMk_left hs)
    e.measurable]
  apply lintegral_congr
  intro omega
  rw [Kernel.comap_apply]
  congr 1
  ext h
  simp

/-- Exact Radon--Nikodym formula for the joint hidden-state/history law.
The hidden image density and the adaptive feedback product appear as the two
literal factors of the total derivative. -/
theorem sparseJointLaw_map_eq_withDensity
    {Omega : Type*} [MeasurableSpace Omega] {n k : Nat}
    (mu : Measure Omega) [SFinite mu] (P : Policy n k)
    (F : SparseAdaptiveParameterFamily Omega n k) (T : Nat)
    (e : Omega ≃ᵐ Omega) (d : Omega -> ENNReal) (hd : Measurable d)
    (hhidden : Measure.map e mu = mu.withDensity d) :
    Measure.map (fun z : Omega × History n k T => (e z.1, z.2))
        (sparseJointLaw mu P F T) =
      (sparseJointLaw mu P F T).withDensity (fun z =>
        d z.1 * sparseFamilyLikelihoodProduct F e T z) := by
  let K := sparseFamilyLawKernel P F T
  let Ke := K.comap e.symm e.symm.measurable
  have hKe : forall omega,
      Ke omega = (K omega).withDensity
        (fun h => sparseFamilyLikelihoodProduct F e T (omega, h)) := by
    intro omega
    change K (e.symm omega) = (K omega).withDensity _
    rw [sparseFamilyLawKernel_apply, sparseFamilyLawKernel_apply]
    convert lower_single_likelihood_product_adaptive P
      (F.at (e.symm omega)) (F.at omega) T using 1
    congr 1
    funext h
    exact sparseFamilyLikelihoodProduct_eq_sparseLikelihoodProduct
      F e T omega h
  have hcond : mu.withDensity d ⊗ₘ Ke =
      (mu.withDensity d ⊗ₘ K).withDensity
        (sparseFamilyLikelihoodProduct F e T) := by
    exact MsetsLower.Lower.Dense.compProd_eq_withDensity_of_apply
      (mu.withDensity d) Ke K
      (fun omega h => sparseFamilyLikelihoodProduct F e T (omega, h))
      (measurable_sparseFamilyLikelihoodProduct F e T) hKe
  rw [sparseJointLaw, map_compProd_hidden_equiv, hhidden, hcond,
    compProd_withDensity_left mu K d hd]
  exact (withDensity_mul (mu ⊗ₘ K)
    (hd.comp measurable_fst)
    (measurable_sparseFamilyLikelihoodProduct F e T)).symm

/-! ## The manuscript's hidden-coordinate diffeomorphism -/

/-- The polynomial part of the hidden-coordinate change of variables. -/
def sparseHiddenMapCore (a u : Real) : Real :=
  u + a * Feedback.shape u

theorem sparseHiddenMapCore_eq_two_feedbackMap (a u : Real) :
    sparseHiddenMapCore a u = 2 * Feedback.feedbackMap (a / 2) u := by
  unfold sparseHiddenMapCore Feedback.feedbackMap
  ring

theorem hasDerivAt_sparseHiddenMapCore (a u : Real) :
    HasDerivAt (sparseHiddenMapCore a) (1 - 2 * a * u) u := by
  have h := (Feedback.hasDerivAt_feedbackMap (a / 2) u).const_mul 2
  have hfun : sparseHiddenMapCore a =
      fun x => 2 * Feedback.feedbackMap (a / 2) x := by
    funext x
    exact sparseHiddenMapCore_eq_two_feedbackMap a x
  have h' : HasDerivAt (sparseHiddenMapCore a)
      (2 * Feedback.feedbackSlope (a / 2) u) u := by
    rw [hfun]
    exact h
  apply h'.congr_deriv
  unfold Feedback.feedbackSlope
  ring

theorem sparseHiddenMapCore_mem_Icc
    {a u : Real} (ha : |a| <= (1 : Real) / 8)
    (hu : u ∈ Icc (-1 : Real) 1) :
    sparseHiddenMapCore a u ∈ Icc (-1 : Real) 1 := by
  have ha2 : |a / 2| <= (1 : Real) / 16 := by
    rw [abs_div]
    norm_num at *
    linarith
  have hm := (Feedback.feedbackMap_bijOn ha2).mapsTo hu
  rw [sparseHiddenMapCore_eq_two_feedbackMap]
  constructor <;> nlinarith [hm.1, hm.2]

theorem sparseHiddenMapCore_image_Icc
    {a : Real} (ha : |a| <= (1 : Real) / 8) :
    sparseHiddenMapCore a '' Icc (-1 : Real) 1 = Icc (-1 : Real) 1 := by
  have ha2 : |a / 2| <= (1 : Real) / 16 := by
    rw [abs_div]
    norm_num at *
    linarith
  rw [show sparseHiddenMapCore a =
      fun u => 2 * Feedback.feedbackMap (a / 2) u by
        funext u; exact sparseHiddenMapCore_eq_two_feedbackMap a u,
    ← Set.image_image, Feedback.feedbackMap_image_Icc ha2]
  ext u
  constructor
  · rintro ⟨v, hv, rfl⟩
    constructor <;> nlinarith [hv.1, hv.2]
  · intro hu
    refine ⟨u / 2, ?_, by ring⟩
    constructor <;> nlinarith [hu.1, hu.2]

/-- Total extension of `T_a`: outside the support interval it is the
identity.  This makes the paper's interval diffeomorphism a genuine
equivalence of the ambient real measurable space. -/
def sparseHiddenMap (a u : Real) : Real :=
  if u ∈ Icc (-1 : Real) 1 then sparseHiddenMapCore a u else u

def sparseHiddenMapInv (a v : Real) : Real :=
  if v ∈ Icc (-1 : Real) 1 then
    Feedback.feedbackInverse (a / 2) (v / 2)
  else v

theorem measurable_sparseHiddenMap (a : Real) :
    Measurable (sparseHiddenMap a) := by
  unfold sparseHiddenMap sparseHiddenMapCore Feedback.shape
  exact Measurable.ite measurableSet_Icc (by fun_prop) measurable_id

theorem measurable_sparseHiddenMapInv (a : Real) :
    Measurable (sparseHiddenMapInv a) := by
  unfold sparseHiddenMapInv
  exact Measurable.ite measurableSet_Icc
    ((Feedback.measurable_feedbackInverse (a / 2)).comp (by fun_prop))
    measurable_id

theorem sparseHiddenMapInv_sparseHiddenMap
    {a : Real} (ha : |a| <= (1 : Real) / 8) (u : Real) :
    sparseHiddenMapInv a (sparseHiddenMap a u) = u := by
  by_cases hu : u ∈ Icc (-1 : Real) 1
  · have ha2 : |a / 2| <= (1 : Real) / 16 := by
      rw [abs_div]
      norm_num at *
      linarith
    have hmap := sparseHiddenMapCore_mem_Icc ha hu
    rw [sparseHiddenMap, if_pos hu, sparseHiddenMapInv, if_pos hmap,
      sparseHiddenMapCore_eq_two_feedbackMap]
    have hhalf : (2 * Feedback.feedbackMap (a / 2) u) / 2 =
        Feedback.feedbackMap (a / 2) u := by ring
    rw [hhalf, Feedback.feedbackInverse_feedbackMap ha2 hu]
  · simp [sparseHiddenMap, sparseHiddenMapInv, hu]

theorem sparseHiddenMap_sparseHiddenMapInv
    {a : Real} (ha : |a| <= (1 : Real) / 8) (v : Real) :
    sparseHiddenMap a (sparseHiddenMapInv a v) = v := by
  by_cases hv : v ∈ Icc (-1 : Real) 1
  · have ha2 : |a / 2| <= (1 : Real) / 16 := by
      rw [abs_div]
      norm_num at *
      linarith
    have hvhalf : v / 2 ∈ Icc (-1 / 2 : Real) (1 / 2 : Real) := by
      constructor <;> nlinarith [hv.1, hv.2]
    have hinv := Feedback.feedbackInverse_mem_Icc ha2 hvhalf
    simp only [sparseHiddenMapInv, if_pos hv, sparseHiddenMap,
      if_pos hinv, sparseHiddenMapCore_eq_two_feedbackMap]
    rw [Feedback.feedbackMap_feedbackInverse ha2 hvhalf]
    ring
  · simp [sparseHiddenMap, sparseHiddenMapInv, hv]

/-- Measurable equivalence implementing the paper's `T_a` on the hidden
support and fixing its complement. -/
def sparseHiddenEquiv (a : Real) (ha : |a| <= (1 : Real) / 8) : Real ≃ᵐ Real where
  toEquiv :=
    { toFun := sparseHiddenMap a
      invFun := sparseHiddenMapInv a
      left_inv := sparseHiddenMapInv_sparseHiddenMap ha
      right_inv := sparseHiddenMap_sparseHiddenMapInv ha }
  measurable_toFun := measurable_sparseHiddenMap a
  measurable_invFun := measurable_sparseHiddenMapInv a

@[simp] theorem sparseHiddenEquiv_apply_of_mem
    {a u : Real} (ha : |a| <= (1 : Real) / 8)
    (hu : u ∈ Icc (-1 : Real) 1) :
    sparseHiddenEquiv a ha u = sparseHiddenMapCore a u := by
  simp [sparseHiddenEquiv, sparseHiddenMap, hu]

def sparseHiddenJacobianDensity (a u : Real) : ENNReal :=
  ENNReal.ofReal (1 - 2 * a * u)

def sparseHiddenImageDensity
    (a : Real) (ha : |a| <= (1 : Real) / 8) (v : Real) : ENNReal :=
  ENNReal.ofReal (sparseHiddenJacobianFactor a
    ((sparseHiddenEquiv a ha).symm v))

theorem measurable_sparseHiddenJacobianDensity (a : Real) :
    Measurable (sparseHiddenJacobianDensity a) := by
  unfold sparseHiddenJacobianDensity
  fun_prop

theorem measurable_sparseHiddenImageDensity
    (a : Real) (ha : |a| <= (1 : Real) / 8) :
    Measurable (sparseHiddenImageDensity a ha) := by
  unfold sparseHiddenImageDensity sparseHiddenJacobianFactor
  fun_prop

theorem sparseHiddenDerivative_pos
    {a u : Real} (ha : |a| <= (1 : Real) / 8)
    (hu : u ∈ Icc (-1 : Real) 1) :
    0 < 1 - 2 * a * u := by
  have hau : |a * u| <= (1 : Real) / 8 := by
    calc
      |a * u| = |a| * |u| := abs_mul a u
      _ <= (1 / 8 : Real) * 1 :=
        mul_le_mul ha ((abs_le).2 hu) (abs_nonneg _) (by norm_num)
      _ = 1 / 8 := by norm_num
  have := (abs_le.mp hau).2
  nlinarith

theorem sparseHiddenMapCore_injOn
    {a : Real} (ha : |a| <= (1 : Real) / 8) :
    Set.InjOn (sparseHiddenMapCore a) (Icc (-1 : Real) 1) := by
  have ha2 : |a / 2| <= (1 : Real) / 16 := by
    rw [abs_div]
    norm_num at *
    linarith
  intro x hx y hy hxy
  apply (Feedback.feedbackMap_strictMonoOn ha2).injOn hx hy
  rw [sparseHiddenMapCore_eq_two_feedbackMap,
    sparseHiddenMapCore_eq_two_feedbackMap] at hxy
  linarith

/-- Jacobian-weighted source volume is carried exactly to source volume by
the polynomial interval map. -/
theorem map_sparseHiddenMapCore_withDensity_jacobian
    {a : Real} (ha : |a| <= (1 : Real) / 8) :
    Measure.map (sparseHiddenMapCore a)
        ((volume.restrict (Icc (-1 : Real) 1)).withDensity
          (sparseHiddenJacobianDensity a)) =
      volume.restrict (Icc (-1 : Real) 1) := by
  have hcov := MeasureTheory.map_withDensity_abs_det_fderiv_eq_addHaar
    (E := Real) (f := sparseHiddenMapCore a)
    (s := Icc (-1 : Real) 1) volume measurableSet_Icc.nullMeasurableSet
    (fun u _hu => (hasDerivAt_sparseHiddenMapCore a u).hasFDerivAt.hasFDerivWithinAt)
    (sparseHiddenMapCore_injOn ha)
  rw [sparseHiddenMapCore_image_Icc ha] at hcov
  have hdens :
      (volume.restrict (Icc (-1 : Real) 1)).withDensity
          (sparseHiddenJacobianDensity a) =
        (volume.restrict (Icc (-1 : Real) 1)).withDensity (fun u =>
          ENNReal.ofReal
            |(ContinuousLinearMap.toSpanSingleton Real
              (1 - 2 * a * u)).det|) := by
    apply withDensity_congr_ae
    filter_upwards [ae_restrict_mem measurableSet_Icc] with u hu
    unfold sparseHiddenJacobianDensity
    simp only [ContinuousLinearMap.det_toSpanSingleton]
    rw [abs_of_pos (sparseHiddenDerivative_pos ha hu)]
  rw [hdens]
  exact hcov

/-- The Jacobian-weighted uniform source law is invariant under the total
measurable equivalence. -/
theorem map_sparseHiddenEquiv_withDensity_jacobian
    {a : Real} (ha : |a| <= (1 : Real) / 8) :
    Measure.map (sparseHiddenEquiv a ha)
        (sourceUniformMeasure.withDensity
          (sparseHiddenJacobianDensity a)) =
      sourceUniformMeasure := by
  have hcore : Measure.map (sparseHiddenMapCore a)
      (sourceUniformMeasure.withDensity
        (sparseHiddenJacobianDensity a)) = sourceUniformMeasure := by
    have hf : Measurable (sparseHiddenMapCore a) := by
      unfold sparseHiddenMapCore Feedback.shape
      fun_prop
    unfold sourceUniformMeasure
    rw [withDensity_smul_measure, Measure.map_smul _ hf.aemeasurable,
      map_sparseHiddenMapCore_withDensity_jacobian ha]
  calc
    Measure.map (sparseHiddenEquiv a ha)
        (sourceUniformMeasure.withDensity
          (sparseHiddenJacobianDensity a)) =
      Measure.map (sparseHiddenMapCore a)
        (sourceUniformMeasure.withDensity
          (sparseHiddenJacobianDensity a)) := by
        apply MeasureTheory.Measure.map_congr
        apply (withDensity_absolutelyContinuous sourceUniformMeasure
          (sparseHiddenJacobianDensity a)).ae_le
        filter_upwards [ae_sourceUniformMeasure_mem_Icc] with u hu
        exact sparseHiddenEquiv_apply_of_mem ha hu
    _ = sourceUniformMeasure := hcore

@[simp] theorem sparseHiddenImageDensity_apply_equiv
    {a u : Real} (ha : |a| <= (1 : Real) / 8) :
    sparseHiddenImageDensity a ha (sparseHiddenEquiv a ha u) =
      ENNReal.ofReal (sparseHiddenJacobianFactor a u) := by
  unfold sparseHiddenImageDensity
  rw [MeasurableEquiv.symm_apply_apply]

/-- Literal scalar hidden-coordinate Radon--Nikodym derivative.  This is the
one-block Jacobian factor `1/(1-2*a*u)`, expressed at the image point through
the inverse map. -/
theorem map_sparseHiddenEquiv_sourceUniformMeasure
    {a : Real} (ha : |a| <= (1 : Real) / 8) :
    Measure.map (sparseHiddenEquiv a ha) sourceUniformMeasure =
      sourceUniformMeasure.withDensity
        (sparseHiddenImageDensity a ha) := by
  let e := sparseHiddenEquiv a ha
  let J := sparseHiddenJacobianDensity a
  let d := sparseHiddenImageDensity a ha
  have hJ : Measure.map e (sourceUniformMeasure.withDensity J) =
      sourceUniformMeasure :=
    map_sparseHiddenEquiv_withDensity_jacobian ha
  have hJmeas : Measurable J := measurable_sparseHiddenJacobianDensity a
  have hdmeas : Measurable d := measurable_sparseHiddenImageDensity a ha
  apply Measure.ext_of_lintegral
  intro f hf
  rw [lintegral_map hf e.measurable,
    lintegral_withDensity_eq_lintegral_mul sourceUniformMeasure hdmeas hf]
  conv_rhs =>
    rw [← hJ]
  rw [lintegral_map (hdmeas.mul hf) e.measurable]
  change (∫⁻ u, f (e u) ∂sourceUniformMeasure) =
    ∫⁻ u, d (e u) * f (e u) ∂sourceUniformMeasure.withDensity J
  have hdint :
      (∫⁻ u, d (e u) * f (e u) ∂sourceUniformMeasure.withDensity J) =
        ∫⁻ u, J u * (d (e u) * f (e u)) ∂sourceUniformMeasure :=
    lintegral_withDensity_eq_lintegral_mul sourceUniformMeasure hJmeas
      ((hdmeas.comp e.measurable).mul (hf.comp e.measurable))
  rw [hdint]
  apply lintegral_congr_ae
  filter_upwards [ae_sourceUniformMeasure_mem_Icc] with u hu
  have hpos := sparseHiddenDerivative_pos ha hu
  have hcancel :
      ENNReal.ofReal (1 - 2 * a * u) *
          ENNReal.ofReal (sparseHiddenJacobianFactor a u) = 1 := by
    rw [← ENNReal.ofReal_mul hpos.le]
    unfold sparseHiddenJacobianFactor
    have hne : 1 - 2 * a * u ≠ 0 := ne_of_gt hpos
    rw [mul_one_div_cancel hne, ENNReal.ofReal_one]
  change f (e u) = J u * (d (e u) * f (e u))
  rw [show d (e u) = ENNReal.ofReal (sparseHiddenJacobianFactor a u) by
    exact sparseHiddenImageDensity_apply_equiv ha]
  unfold J sparseHiddenJacobianDensity
  rw [← mul_assoc, hcancel, one_mul]

/-! ## A finite independent hidden column -/

/-- A recursively parenthesized column of `B` real hidden coordinates.  The
recursive presentation lets the exact product change-of-measure theorem use
binary Fubini without any additional finite-product axioms. -/
@[reducible] def SparseHiddenColumn : Nat -> Type
  | 0 => Unit
  | Nat.succ B => SparseHiddenColumn B × Real

instance instMeasurableSpaceSparseHiddenColumn :
    (B : Nat) -> MeasurableSpace (SparseHiddenColumn B)
  | 0 => inferInstanceAs (MeasurableSpace Unit)
  | Nat.succ B => by
      letI := instMeasurableSpaceSparseHiddenColumn B
      exact inferInstanceAs
        (MeasurableSpace (SparseHiddenColumn B × Real))

def sparseHiddenColumnMeasure :
    (B : Nat) -> Measure (SparseHiddenColumn B)
  | 0 => Measure.dirac ()
  | Nat.succ B => (sparseHiddenColumnMeasure B).prod sourceUniformMeasure

instance instSFiniteSparseHiddenColumnMeasure :
    (B : Nat) -> SFinite (sparseHiddenColumnMeasure B)
  | 0 => by
      change SFinite (Measure.dirac ())
      infer_instance
  | Nat.succ B => by
      letI := instSFiniteSparseHiddenColumnMeasure B
      change SFinite ((sparseHiddenColumnMeasure B).prod sourceUniformMeasure)
      infer_instance

instance instIsProbabilityMeasureSparseHiddenColumnMeasure :
    (B : Nat) -> IsProbabilityMeasure (sparseHiddenColumnMeasure B)
  | 0 => by
      change IsProbabilityMeasure (Measure.dirac ())
      infer_instance
  | Nat.succ B => by
      letI := instIsProbabilityMeasureSparseHiddenColumnMeasure B
      letI : IsProbabilityMeasure sourceUniformMeasure := inferInstance
      change IsProbabilityMeasure
        ((sparseHiddenColumnMeasure B).prod sourceUniformMeasure)
      infer_instance

def sparseHiddenColumnEquiv
    (B : Nat) (a : Real) (ha : |a| <= (1 : Real) / 8) :
    SparseHiddenColumn B ≃ᵐ SparseHiddenColumn B := by
  induction B with
  | zero => exact MeasurableEquiv.refl Unit
  | succ B ih =>
      exact MeasurableEquiv.prodCongr ih (sparseHiddenEquiv a ha)

def sparseHiddenColumnImageDensity
    (a : Real) (ha : |a| <= (1 : Real) / 8) :
    (B : Nat) -> SparseHiddenColumn B -> ENNReal
  | 0, _ => 1
  | Nat.succ B, U => sparseHiddenColumnImageDensity a ha B U.1 *
      sparseHiddenImageDensity a ha U.2

def sparseHiddenColumnJacobianAtSource (a : Real) :
    (B : Nat) -> SparseHiddenColumn B -> ENNReal
  | 0, _ => 1
  | Nat.succ B, U => sparseHiddenColumnJacobianAtSource a B U.1 *
      ENNReal.ofReal (sparseHiddenJacobianFactor a U.2)

theorem measurable_sparseHiddenJacobianFactor (a : Real) :
    Measurable (sparseHiddenJacobianFactor a) := by
  unfold sparseHiddenJacobianFactor
  fun_prop

theorem measurable_sparseHiddenColumnImageDensity
    (a : Real) (ha : |a| <= (1 : Real) / 8) :
    forall B, Measurable (sparseHiddenColumnImageDensity a ha B) := by
  intro B
  induction B with
  | zero => exact measurable_const
  | succ B ih =>
      exact (ih.comp measurable_fst).mul
        ((measurable_sparseHiddenImageDensity a ha).comp measurable_snd)

theorem measurable_sparseHiddenColumnJacobianAtSource (a : Real) :
    forall B, Measurable (sparseHiddenColumnJacobianAtSource a B) := by
  intro B
  induction B with
  | zero => exact measurable_const
  | succ B ih =>
      exact (ih.comp measurable_fst).mul
        ((measurable_sparseHiddenJacobianFactor a).ennreal_ofReal.comp
          measurable_snd)

theorem map_sparseHiddenColumnEquiv_measure
    (a : Real) (ha : |a| <= (1 : Real) / 8) : forall B,
    Measure.map (sparseHiddenColumnEquiv B a ha)
        (sparseHiddenColumnMeasure B) =
      (sparseHiddenColumnMeasure B).withDensity
        (sparseHiddenColumnImageDensity a ha B) := by
  intro B
  induction B with
  | zero =>
      change Measure.map (MeasurableEquiv.refl Unit) (Measure.dirac ()) =
        (Measure.dirac ()).withDensity (fun _ => 1)
      simp
  | succ B ih =>
      let eB := sparseHiddenColumnEquiv B a ha
      let e := sparseHiddenEquiv a ha
      let muB := sparseHiddenColumnMeasure B
      let mu := sourceUniformMeasure
      let dB := sparseHiddenColumnImageDensity a ha B
      let d := sparseHiddenImageDensity a ha
      change Measure.map (Prod.map eB e) (muB.prod mu) =
        (muB.prod mu).withDensity (fun U => dB U.1 * d U.2)
      rw [← Measure.map_prod_map muB mu eB.measurable e.measurable,
        ih, map_sparseHiddenEquiv_sourceUniformMeasure ha,
        prod_withDensity
          (measurable_sparseHiddenColumnImageDensity a ha B)
          (measurable_sparseHiddenImageDensity a ha)]

@[simp] theorem sparseHiddenColumnImageDensity_apply_equiv
    (a : Real) (ha : |a| <= (1 : Real) / 8) : forall B
    (U : SparseHiddenColumn B),
    sparseHiddenColumnImageDensity a ha B
        (sparseHiddenColumnEquiv B a ha U) =
      sparseHiddenColumnJacobianAtSource a B U := by
  intro B
  induction B with
  | zero => intro U; simp [sparseHiddenColumnImageDensity,
      sparseHiddenColumnJacobianAtSource]
  | succ B ih =>
      intro U
      change sparseHiddenColumnImageDensity a ha B
            (sparseHiddenColumnEquiv B a ha U.1) *
          sparseHiddenImageDensity a ha (sparseHiddenEquiv a ha U.2) =
        sparseHiddenColumnJacobianAtSource a B U.1 *
          ENNReal.ofReal (sparseHiddenJacobianFactor a U.2)
      rw [ih, sparseHiddenImageDensity_apply_equiv]

theorem lintegral_sparseHiddenColumnJacobianAtSource_eq_pow
    (a : Real) : forall B,
    (∫⁻ U, sparseHiddenColumnJacobianAtSource a B U
        ∂sparseHiddenColumnMeasure B) =
      (∫⁻ u, ENNReal.ofReal (sparseHiddenJacobianFactor a u)
        ∂sourceUniformMeasure) ^ B := by
  intro B
  induction B with
  | zero =>
      change (∫⁻ _ : Unit, (1 : ENNReal) ∂Measure.dirac ()) = _ ^ 0
      simp
  | succ B ih =>
      change (∫⁻ U : SparseHiddenColumn B × Real,
          sparseHiddenColumnJacobianAtSource a B U.1 *
            ENNReal.ofReal (sparseHiddenJacobianFactor a U.2)
          ∂(sparseHiddenColumnMeasure B).prod sourceUniformMeasure) = _
      have hprod := lintegral_prod_mul
        (μ := sparseHiddenColumnMeasure B) (ν := sourceUniformMeasure)
        (measurable_sparseHiddenColumnJacobianAtSource a B).aemeasurable
        (measurable_sparseHiddenJacobianFactor a).ennreal_ofReal.aemeasurable
      rw [hprod, ih, pow_succ]

/-- The recursively represented hidden-column product has the same sharp
`exp(8*a^2*B)` expectation bound as the manuscript's independent table
column. -/
theorem integral_sparseHiddenColumnJacobianAtSource_le
    {B : Nat} {a : Real} (ha : |a| <= (1 : Real) / 4) :
    (∫⁻ U, sparseHiddenColumnJacobianAtSource a B U
        ∂sparseHiddenColumnMeasure B) <=
      ENNReal.ofReal (Real.exp (8 * a ^ 2 * B)) := by
  rw [lintegral_sparseHiddenColumnJacobianAtSource_eq_pow]
  have hfactorIntegrable : Integrable (sparseHiddenJacobianFactor a)
      sourceUniformMeasure := by
    have hcont : ContinuousOn (sparseHiddenJacobianFactor a)
        (Icc (-1 : Real) 1) := by
      unfold sparseHiddenJacobianFactor
      apply ContinuousOn.div continuousOn_const
        (by fun_prop)
      intro u hu
      have hau : |a * u| <= (1 : Real) / 4 := by
        calc
          |a * u| = |a| * |u| := abs_mul a u
          _ <= (1 / 4 : Real) * 1 :=
            mul_le_mul ha ((abs_le).2 hu) (abs_nonneg _) (by norm_num)
          _ = 1 / 4 := by norm_num
      have := (abs_le.mp hau).2
      nlinarith
    unfold sourceUniformMeasure
    exact hcont.integrableOn_Icc.smul_measure
      (by simp : ENNReal.ofReal (1 / 2 : Real) ≠ ∞)
  have hfactorNonneg : ∀ᵐ u ∂sourceUniformMeasure,
      0 <= sparseHiddenJacobianFactor a u := by
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
  rw [← ofReal_integral_eq_lintegral_ofReal hfactorIntegrable hfactorNonneg]
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
    ENNReal.ofReal
        (∫ u, sparseHiddenJacobianFactor a u ∂sourceUniformMeasure) ^ B <=
      ENNReal.ofReal (Real.exp (8 * a ^ 2)) ^ B := by
        exact pow_le_pow_left₀ (by positivity)
          (ENNReal.ofReal_le_ofReal hscalar) B
    _ = ENNReal.ofReal (Real.exp (8 * a ^ 2 * B)) := by
      rw [← ENNReal.ofReal_pow (Real.exp_nonneg _) B,
        ← Real.exp_nat_mul]
      congr 2
      ring

/-! ## Total joint likelihood and the diagonal capstone -/

def sparseHiddenJointMap
    {n k B T : Nat} (a : Real) (ha : |a| <= (1 : Real) / 8) :
    SparseHiddenColumn B × History n k T ->
      SparseHiddenColumn B × History n k T :=
  fun z => (sparseHiddenColumnEquiv B a ha z.1, z.2)

def sparseHiddenJointLikelihood
    {n k B : Nat} (F : SparseAdaptiveParameterFamily
      (SparseHiddenColumn B) n k)
    (a : Real) (ha : |a| <= (1 : Real) / 8) (T : Nat) :
    SparseHiddenColumn B × History n k T -> ENNReal :=
  fun z => sparseHiddenColumnImageDensity a ha B z.1 *
    sparseFamilyLikelihoodProduct F (sparseHiddenColumnEquiv B a ha) T z

theorem measurable_sparseHiddenJointLikelihood
    {n k B : Nat} (F : SparseAdaptiveParameterFamily
      (SparseHiddenColumn B) n k)
    (a : Real) (ha : |a| <= (1 : Real) / 8) (T : Nat) :
    Measurable (sparseHiddenJointLikelihood F a ha T) :=
  (measurable_sparseHiddenColumnImageDensity a ha B).comp measurable_fst |>.mul
    (measurable_sparseFamilyLikelihoodProduct F
      (sparseHiddenColumnEquiv B a ha) T)

/-- Joint hidden-column plus adaptive-history version of
`eq:lower-single-likelihood-product`: the total push-forward density is the
hidden Jacobian product times the chronological feedback-density product. -/
theorem sparseHiddenJointLaw_map_eq_withDensity
    {n k B : Nat} (P : Policy n k)
    (F : SparseAdaptiveParameterFamily (SparseHiddenColumn B) n k)
    (a : Real) (ha : |a| <= (1 : Real) / 8) (T : Nat) :
    Measure.map (sparseHiddenJointMap a ha)
        (sparseJointLaw (sparseHiddenColumnMeasure B) P F T) =
      (sparseJointLaw (sparseHiddenColumnMeasure B) P F T).withDensity
        (sparseHiddenJointLikelihood F a ha T) := by
  exact sparseJointLaw_map_eq_withDensity
    (sparseHiddenColumnMeasure B) P F T
    (sparseHiddenColumnEquiv B a ha)
    (sparseHiddenColumnImageDensity a ha B)
    (measurable_sparseHiddenColumnImageDensity a ha B)
    (map_sparseHiddenColumnEquiv_measure a ha B)

/-- The preceding total derivative, evaluated at the image of a base point,
is literally the product displayed in `eq:lower-single-likelihood-product`. -/
theorem sparseHiddenJointLikelihood_apply_map
    {n k B : Nat} (F : SparseAdaptiveParameterFamily
      (SparseHiddenColumn B) n k)
    (a : Real) (ha : |a| <= (1 : Real) / 8) (T : Nat)
    (U : SparseHiddenColumn B) (h : History n k T) :
    sparseHiddenJointLikelihood F a ha T
        (sparseHiddenJointMap a ha (U, h)) =
      sparseHiddenColumnJacobianAtSource a B U *
        sparseLikelihoodProduct (F.at U)
          (F.at (sparseHiddenColumnEquiv B a ha U)) T h := by
  unfold sparseHiddenJointLikelihood sparseHiddenJointMap
  rw [sparseHiddenColumnImageDensity_apply_equiv,
    sparseFamilyLikelihoodProduct_eq_sparseLikelihoodProduct]
  simp

/-- General change-of-variables identity behind
`E_P[Lambda^2]=E_P[Lambda o Phi]`. -/
theorem lintegral_likelihood_sq_eq_map_comp
    {Omega : Type*} [MeasurableSpace Omega]
    (mu : Measure Omega) (e : Omega ≃ᵐ Omega)
    (L : Omega -> ENNReal) (hL : Measurable L)
    (hmap : Measure.map e mu = mu.withDensity L) :
    (∫⁻ z, L z ^ 2 ∂mu) = ∫⁻ z, L (e z) ∂mu := by
  have hdensity :
      (∫⁻ z, L z ∂mu.withDensity L) = ∫⁻ z, L z * L z ∂mu :=
    lintegral_withDensity_eq_lintegral_mul mu hL hL
  calc
    (∫⁻ z, L z ^ 2 ∂mu) = ∫⁻ z, L z * L z ∂mu := by
      apply lintegral_congr
      intro z
      rw [pow_two]
    _ = ∫⁻ z, L z ∂mu.withDensity L := hdensity.symm
    _ = ∫⁻ z, L z ∂Measure.map e mu := by rw [hmap]
    _ = ∫⁻ z, L (e z) ∂mu := lintegral_map hL e.measurable

/-- Second moment of the literal joint RN derivative is the expectation of
the exact manuscript product at a base point. -/
theorem sparseHiddenJointLikelihood_secondMoment_eq
    {n k B : Nat} (P : Policy n k)
    (F : SparseAdaptiveParameterFamily (SparseHiddenColumn B) n k)
    (a : Real) (ha : |a| <= (1 : Real) / 8) (T : Nat) :
    (∫⁻ z, sparseHiddenJointLikelihood F a ha T z ^ 2
        ∂sparseJointLaw (sparseHiddenColumnMeasure B) P F T) =
      ∫⁻ z, sparseHiddenColumnJacobianAtSource a B z.1 *
          sparseLikelihoodProduct (F.at z.1)
            (F.at (sparseHiddenColumnEquiv B a ha z.1)) T z.2
        ∂sparseJointLaw (sparseHiddenColumnMeasure B) P F T := by
  rw [lintegral_likelihood_sq_eq_map_comp
    (sparseJointLaw (sparseHiddenColumnMeasure B) P F T)
    (MeasurableEquiv.prodCongr (sparseHiddenColumnEquiv B a ha)
      (MeasurableEquiv.refl (History n k T)))
    (sparseHiddenJointLikelihood F a ha T)
    (measurable_sparseHiddenJointLikelihood F a ha T)]
  · apply lintegral_congr
    intro z
    exact sparseHiddenJointLikelihood_apply_map F a ha T z.1 z.2
  · exact sparseHiddenJointLaw_map_eq_withDensity P F a ha T

/-- Full joint diagonal estimate.  The premise is the manuscript's pathwise
temporal energy budget; the hidden Jacobian contribution is integrated here
from its actual independent law. -/
theorem lower_likelihood_diagonal_joint
    {n k B : Nat} (P : Policy n k)
    (F : SparseAdaptiveParameterFamily (SparseHiddenColumn B) n k)
    (a rho : Real) (ha : |a| <= (1 : Real) / 8)
    (hrho0 : 0 <= rho) (hrho : 8 + 128 * rho <= (10 : Real))
    (T : Nat)
    (henergy : forall (U : SparseHiddenColumn B) (h : History n k T),
      sparseCumulativeEnergy (F.at U)
          (F.at (sparseHiddenColumnEquiv B a ha U)) T h <=
        a ^ 2 * rho * B) :
    (∫⁻ z, sparseHiddenJointLikelihood F a ha T z ^ 2
        ∂sparseJointLaw (sparseHiddenColumnMeasure B) P F T) <=
      ENNReal.ofReal (Real.exp (10 * a ^ 2 * B)) := by
  rw [sparseHiddenJointLikelihood_secondMoment_eq P F a ha T]
  let e := sparseHiddenColumnEquiv B a ha
  let K := sparseFamilyLawKernel P F T
  let J := sparseHiddenColumnJacobianAtSource a B
  let Lsrc : SparseHiddenColumn B × History n k T -> ENNReal :=
    fun z => sparseFamilyLikelihoodProduct F e T (e z.1, z.2)
  have hLsrc : Measurable Lsrc :=
    (measurable_sparseFamilyLikelihoodProduct F e T).comp <|
      (e.measurable.comp measurable_fst).prodMk measurable_snd
  have hJ : Measurable J :=
    measurable_sparseHiddenColumnJacobianAtSource a B
  have hfun : (fun z : SparseHiddenColumn B × History n k T =>
      J z.1 * sparseLikelihoodProduct (F.at z.1) (F.at (e z.1)) T z.2) =
      fun z => J z.1 * Lsrc z := by
    funext z
    congr 1
    unfold Lsrc
    rw [sparseFamilyLikelihoodProduct_eq_sparseLikelihoodProduct]
    simp
  rw [hfun]
  change (∫⁻ z, J z.1 * Lsrc z
      ∂sparseHiddenColumnMeasure B ⊗ₘ K) <= _
  rw [Measure.lintegral_compProd]
  swap
  · exact (hJ.comp measurable_fst).mul hLsrc
  let C : Real := a ^ 2 * rho * B
  let E : ENNReal := ENNReal.ofReal (Real.exp (128 * C))
  calc
    (∫⁻ U, ∫⁻ h, J U * Lsrc (U, h) ∂K U
        ∂sparseHiddenColumnMeasure B) <=
      ∫⁻ U, J U * E ∂sparseHiddenColumnMeasure B := by
        apply lintegral_mono
        intro U
        have hinner : (∫⁻ h, Lsrc (U, h) ∂K U) <= E := by
          have hLU : (fun h => Lsrc (U, h)) =
              sparseLikelihoodProduct (F.at U) (F.at (e U)) T := by
            funext h
            unfold Lsrc
            rw [sparseFamilyLikelihoodProduct_eq_sparseLikelihoodProduct]
            simp
          rw [hLU, sparseFamilyLawKernel_apply]
          exact lower_likelihood_diagonal_temporal P (F.at U) (F.at (e U))
            T C (henergy U)
        change (∫⁻ h, J U * Lsrc (U, h) ∂K U) <= J U * E
        have hconstint :
            (∫⁻ h, J U * Lsrc (U, h) ∂K U) =
              J U * (∫⁻ h, Lsrc (U, h) ∂K U) := by
          rw [lintegral_const_mul (J U)]
          exact hLsrc.comp (measurable_const.prodMk measurable_id)
        rw [hconstint]
        exact mul_le_mul_right hinner (J U)
    _ = E * (∫⁻ U, J U ∂sparseHiddenColumnMeasure B) := by
      rw [show (fun U => J U * E) = fun U => E * J U by
        funext U; ac_rfl, lintegral_const_mul E hJ]
    _ <= E * ENNReal.ofReal (Real.exp (8 * a ^ 2 * B)) := by
      apply mul_le_mul_right
      apply integral_sparseHiddenColumnJacobianAtSource_le
      exact ha.trans (by norm_num)
    _ = ENNReal.ofReal (Real.exp ((8 + 128 * rho) * a ^ 2 * B)) := by
      unfold E C
      rw [← ENNReal.ofReal_mul (Real.exp_nonneg _), ← Real.exp_add]
      congr 2
      ring
    _ <= ENNReal.ofReal (Real.exp (10 * a ^ 2 * B)) := by
      apply ENNReal.ofReal_le_ofReal
      apply Real.exp_le_exp.mpr
      have hab : 0 <= a ^ 2 * (B : Real) :=
        mul_nonneg (sq_nonneg a) (Nat.cast_nonneg B)
      nlinarith

/-- Manuscript constants `a=1/64` and `rho=2^-36`, yielding the displayed
capstone `E Lambda_j^2 <= exp(10 a^2 B)` verbatim. -/
theorem lower_likelihood_diagonal_joint_sparseConstants
    {n k B : Nat} (P : Policy n k)
    (F : SparseAdaptiveParameterFamily (SparseHiddenColumn B) n k)
    (T : Nat)
    (henergy : forall (U : SparseHiddenColumn B) (h : History n k T),
      sparseCumulativeEnergy (F.at U)
          (F.at (sparseHiddenColumnEquiv B sparseA
            (by norm_num [sparseA]) U)) T h <=
        sparseA ^ 2 * sparseRho * B) :
    (∫⁻ z, sparseHiddenJointLikelihood F sparseA
          (by norm_num [sparseA]) T z ^ 2
        ∂sparseJointLaw (sparseHiddenColumnMeasure B) P F T) <=
      ENNReal.ofReal (Real.exp (10 * sparseA ^ 2 * B)) := by
  exact lower_likelihood_diagonal_joint P F sparseA sparseRho
    (by norm_num [sparseA]) (le_of_lt sparseRho_pos)
    (by norm_num [sparseRho]) T henergy

/-! ## Support-safe four-corner identities -/

def sparseHistoryInFeedbackSupport {n k : Nat} :
    (T : Nat) -> History n k T -> Prop
  | 0, _ => True
  | t + 1, h => sparseHistoryInFeedbackSupport t h.1 ∧
      h.2.2 ∈ Icc (-1 / 2 : Real) (1 / 2 : Real)

theorem measurableSet_sparseHistoryInFeedbackSupport {n k : Nat} :
    forall T, MeasurableSet
      {h : History n k T | sparseHistoryInFeedbackSupport T h} := by
  intro T
  induction T with
  | zero =>
      simpa [sparseHistoryInFeedbackSupport] using
        (measurableSet_univ : MeasurableSet (Set.univ : Set (History n k 0)))
  | succ t ih =>
      change MeasurableSet
        ({h : History n k (t + 1) |
          h.1 ∈ {h : History n k t | sparseHistoryInFeedbackSupport t h}} ∩
          {h : History n k (t + 1) | h.2.2 ∈ Icc (-1 / 2 : Real) (1 / 2 : Real)})
      exact (measurable_fst ih).inter
        (measurable_snd.snd measurableSet_Icc)

theorem ae_feedbackDensityMeasure_mem_support
    {u : Real} (hu : |u| <= (1 : Real) / 16) :
    ∀ᵐ y ∂feedbackDensityMeasure u,
      y ∈ Icc (-1 / 2 : Real) (1 / 2 : Real) := by
  rw [← feedbackPushforwardMeasure_eq_densityMeasure hu]
  unfold feedbackPushforwardMeasure
  apply (MeasureTheory.ae_map_iff
    (μ := sourceUniformMeasure) (f := Feedback.feedbackMap u)
    (p := fun y => y ∈ Icc (-1 / 2 : Real) (1 / 2 : Real))
    (Feedback.continuous_feedbackMap u).measurable.aemeasurable
    measurableSet_Icc).2
  filter_upwards [ae_sourceUniformMeasure_mem_Icc] with z hz
  exact (Feedback.feedbackMap_bijOn hu).mapsTo hz

theorem ae_sparseAdaptiveRoundKernel_feedback_mem_support
    {n k : Nat} (P : Policy n k) (V : SparseAdaptiveParameters n k)
    (t : Nat) (h : History n k t) :
    ∀ᵐ Ay ∂sparseAdaptiveRoundKernel P V t h,
      Ay.2 ∈ Icc (-1 / 2 : Real) (1 / 2 : Real) := by
  let feedbackK := sparseParamFeedbackKernel
    (fun hA : History n k t × MSetAction n k =>
      V.value t hA.1 hA.2)
  letI : IsMarkovKernel feedbackK := by
    dsimp [feedbackK]
    exact sparseParamFeedbackKernel_isMarkov _ (V.measurable_value t)
      (fun hA => V.abs_le t hA.1 hA.2)
  change ∀ᵐ Ay ∂(P.kernel t ⊗ₖ feedbackK) h,
      Ay.2 ∈ Icc (-1 / 2 : Real) (1 / 2 : Real)
  apply Kernel.ae_compProd_of_ae_ae
  · exact measurable_snd measurableSet_Icc
  · apply ae_of_all
    intro A
    rw [show feedbackK (h, A) =
        feedbackDensityMeasure (V.value t h A) by
      exact sparseParamFeedbackKernel_apply _ (V.measurable_value t) _
        (V.abs_le t h A)]
    exact ae_feedbackDensityMeasure_mem_support (V.abs_le t h A)

theorem ae_sparseAdaptiveProcess_history_support
    {n k : Nat} (P : Policy n k) (V : SparseAdaptiveParameters n k) :
    forall T, ∀ᵐ h ∂(sparseAdaptiveProcess P V).law T,
      sparseHistoryInFeedbackSupport T h := by
  intro T
  induction T with
  | zero => simp [sparseHistoryInFeedbackSupport]
  | succ t ih =>
      rw [HistoryKernelProcess.law_succ]
      apply Measure.ae_compProd_of_ae_ae
      · exact measurableSet_sparseHistoryInFeedbackSupport (n := n) (k := k) (t + 1)
      · filter_upwards [ih] with h hh
        filter_upwards [ae_sparseAdaptiveRoundKernel_feedback_mem_support
          P V t h] with Ay hAy
        exact ⟨hh, hAy⟩

theorem feedbackDensityRatio_trans_on_support
    {u v w y : Real}
    (hu : |u| <= (1 : Real) / 16)
    (hv : |v| <= (1 : Real) / 16)
    (hw : |w| <= (1 : Real) / 16)
    (hy : y ∈ Icc (-1 / 2 : Real) (1 / 2 : Real)) :
    feedbackDensityRatio u w y =
      feedbackDensityRatio u v y * feedbackDensityRatio v w y := by
  have hpu : 0 < feedbackDensity u y := by
    rw [feedbackDensity_eq_core hy]
    exact lt_of_lt_of_le (by norm_num)
      (feedbackDensityCore_mem_Icc hu hy).1
  have hpv : 0 < feedbackDensity v y := by
    rw [feedbackDensity_eq_core hy]
    exact lt_of_lt_of_le (by norm_num)
      (feedbackDensityCore_mem_Icc hv hy).1
  have hpw : 0 < feedbackDensity w y := by
    rw [feedbackDensity_eq_core hy]
    exact lt_of_lt_of_le (by norm_num)
      (feedbackDensityCore_mem_Icc hw hy).1
  unfold feedbackDensityRatio
  rw [← ENNReal.ofReal_mul (div_nonneg hpu.le hpv.le)]
  congr 1
  field_simp [ne_of_gt hpu, ne_of_gt hpv, ne_of_gt hpw]

theorem sparseCrossRoundLikelihood_balance
    {n k : Nat} (R : SparseAdaptiveRectangle n k) (t : Nat)
    (hAy : History n k t × (MSetAction n k × Real))
    (hy : hAy.2.2 ∈ Icc (-1 / 2 : Real) (1 / 2 : Real)) :
    sparseRoundLikelihood R.right R.both t hAy *
        sparseRoundLikelihood R.left R.both t hAy =
      sparseRoundLikelihood R.base R.both t hAy *
        ENNReal.ofReal (Real.exp (sparseCrossLogIncrement R t hAy)) := by
  have htrans := feedbackDensityRatio_trans_on_support
    (R.right.abs_le t hAy.1 hAy.2.1)
    (R.base.abs_le t hAy.1 hAy.2.1)
    (R.both.abs_le t hAy.1 hAy.2.1) hy
  rw [sparseCrossRoundLikelihood_eq_densityRatios R t hAy hy]
  unfold sparseRoundLikelihood
  rw [htrans]
  ac_rfl

theorem sparseLikelihoodProduct_cross_balance
    {n k : Nat} (R : SparseAdaptiveRectangle n k) : forall T
    (h : History n k T), sparseHistoryInFeedbackSupport T h ->
    sparseLikelihoodProduct R.right R.both T h *
        sparseLikelihoodProduct R.left R.both T h =
      sparseLikelihoodProduct R.base R.both T h *
        sparseCrossLikelihood R T h := by
  intro T
  induction T with
  | zero => intro h _; simp [sparseCrossLikelihood, sparseCrossLog]
  | succ t ih =>
      intro h hsupp
      have hprev := ih h.1 hsupp.1
      have hround := sparseCrossRoundLikelihood_balance R t h hsupp.2
      have hcross : sparseCrossLikelihood R (t + 1) h =
          sparseCrossLikelihood R t h.1 *
            ENNReal.ofReal (Real.exp (sparseCrossLogIncrement R t h)) := by
        unfold sparseCrossLikelihood
        change ENNReal.ofReal (Real.exp
            (sparseCrossLog R t h.1 + sparseCrossLogIncrement R t h)) = _
        rw [Real.exp_add, ENNReal.ofReal_mul (Real.exp_nonneg _)]
      rw [sparseLikelihoodProduct_succ, sparseLikelihoodProduct_succ,
        sparseLikelihoodProduct_succ, hcross]
      calc
        sparseLikelihoodProduct R.right R.both t h.1 *
              sparseRoundLikelihood R.right R.both t h *
            (sparseLikelihoodProduct R.left R.both t h.1 *
              sparseRoundLikelihood R.left R.both t h) =
          (sparseLikelihoodProduct R.right R.both t h.1 *
              sparseLikelihoodProduct R.left R.both t h.1) *
            (sparseRoundLikelihood R.right R.both t h *
              sparseRoundLikelihood R.left R.both t h) := by ac_rfl
        _ = (sparseLikelihoodProduct R.base R.both t h.1 *
              sparseCrossLikelihood R t h.1) *
            (sparseRoundLikelihood R.base R.both t h *
              ENNReal.ofReal (Real.exp
                (sparseCrossLogIncrement R t h))) := by
          rw [hprev, hround]
        _ = sparseLikelihoodProduct R.base R.both t h.1 *
              sparseRoundLikelihood R.base R.both t h *
            (sparseCrossLikelihood R t h.1 *
              ENNReal.ofReal (Real.exp
                (sparseCrossLogIncrement R t h))) := by ac_rfl

/-! ## The literal two-coordinate joint cross likelihood

The temporal identity above is the conditional part of
`eq:lower-likelihood-cross`.  We now put back the two independent hidden
columns.  This is the point at which both one-coordinate Jacobians occur in
the numerator and the two-coordinate Jacobian occurs in the denominator;
the following construction proves their cancellation from the actual
push-forward laws.
-/

/-- The hidden law of the two columns indexed by the manuscript's distinct
coordinates `j,l`. -/
def sparseHiddenPairMeasure (B : Nat) :
    Measure (SparseHiddenColumn B × SparseHiddenColumn B) :=
  (sparseHiddenColumnMeasure B).prod (sparseHiddenColumnMeasure B)

instance instSFiniteSparseHiddenPairMeasure (B : Nat) :
    SFinite (sparseHiddenPairMeasure B) := by
  unfold sparseHiddenPairMeasure
  infer_instance

instance instIsProbabilityMeasureSparseHiddenPairMeasure (B : Nat) :
    IsProbabilityMeasure (sparseHiddenPairMeasure B) := by
  unfold sparseHiddenPairMeasure
  infer_instance

/-- Change only the first of two hidden columns. -/
def sparseHiddenPairLeftEquiv (B : Nat) (a : Real)
    (ha : |a| <= (1 : Real) / 8) :
    (SparseHiddenColumn B × SparseHiddenColumn B) ≃ᵐ
      (SparseHiddenColumn B × SparseHiddenColumn B) :=
  MeasurableEquiv.prodCongr (sparseHiddenColumnEquiv B a ha)
    (MeasurableEquiv.refl (SparseHiddenColumn B))

/-- Change only the second of two hidden columns. -/
def sparseHiddenPairRightEquiv (B : Nat) (a : Real)
    (ha : |a| <= (1 : Real) / 8) :
    (SparseHiddenColumn B × SparseHiddenColumn B) ≃ᵐ
      (SparseHiddenColumn B × SparseHiddenColumn B) :=
  MeasurableEquiv.prodCongr (MeasurableEquiv.refl (SparseHiddenColumn B))
    (sparseHiddenColumnEquiv B a ha)

/-- Simultaneously change the two hidden columns. -/
def sparseHiddenPairBothEquiv (B : Nat) (a : Real)
    (ha : |a| <= (1 : Real) / 8) :
    (SparseHiddenColumn B × SparseHiddenColumn B) ≃ᵐ
      (SparseHiddenColumn B × SparseHiddenColumn B) :=
  MeasurableEquiv.prodCongr (sparseHiddenColumnEquiv B a ha)
    (sparseHiddenColumnEquiv B a ha)

@[simp] theorem sparseHiddenPairLeftEquiv_apply
    (B : Nat) (a : Real) (ha : |a| <= (1 : Real) / 8)
    (U : SparseHiddenColumn B × SparseHiddenColumn B) :
    sparseHiddenPairLeftEquiv B a ha U =
      (sparseHiddenColumnEquiv B a ha U.1, U.2) := rfl

@[simp] theorem sparseHiddenPairRightEquiv_apply
    (B : Nat) (a : Real) (ha : |a| <= (1 : Real) / 8)
    (U : SparseHiddenColumn B × SparseHiddenColumn B) :
    sparseHiddenPairRightEquiv B a ha U =
      (U.1, sparseHiddenColumnEquiv B a ha U.2) := rfl

@[simp] theorem sparseHiddenPairBothEquiv_apply
    (B : Nat) (a : Real) (ha : |a| <= (1 : Real) / 8)
    (U : SparseHiddenColumn B × SparseHiddenColumn B) :
    sparseHiddenPairBothEquiv B a ha U =
      (sparseHiddenColumnEquiv B a ha U.1,
        sparseHiddenColumnEquiv B a ha U.2) := rfl

@[simp] theorem sparseHiddenPairLeftEquiv_symm_both
    (B : Nat) (a : Real) (ha : |a| <= (1 : Real) / 8)
    (U : SparseHiddenColumn B × SparseHiddenColumn B) :
    (sparseHiddenPairLeftEquiv B a ha).symm
        (sparseHiddenPairBothEquiv B a ha U) =
      sparseHiddenPairRightEquiv B a ha U := by
  change
    ((sparseHiddenColumnEquiv B a ha).symm
        (sparseHiddenColumnEquiv B a ha U.1),
      sparseHiddenColumnEquiv B a ha U.2) =
    (U.1, sparseHiddenColumnEquiv B a ha U.2)
  simp

@[simp] theorem sparseHiddenPairRightEquiv_symm_both
    (B : Nat) (a : Real) (ha : |a| <= (1 : Real) / 8)
    (U : SparseHiddenColumn B × SparseHiddenColumn B) :
    (sparseHiddenPairRightEquiv B a ha).symm
        (sparseHiddenPairBothEquiv B a ha U) =
      sparseHiddenPairLeftEquiv B a ha U := by
  change
    (sparseHiddenColumnEquiv B a ha U.1,
      (sparseHiddenColumnEquiv B a ha).symm
        (sparseHiddenColumnEquiv B a ha U.2)) =
    (sparseHiddenColumnEquiv B a ha U.1, U.2)
  simp

/-- Image density for the first-coordinate change. -/
def sparseHiddenPairLeftImageDensity (B : Nat) (a : Real)
    (ha : |a| <= (1 : Real) / 8)
    (U : SparseHiddenColumn B × SparseHiddenColumn B) : ENNReal :=
  sparseHiddenColumnImageDensity a ha B U.1

/-- Image density for the second-coordinate change. -/
def sparseHiddenPairRightImageDensity (B : Nat) (a : Real)
    (ha : |a| <= (1 : Real) / 8)
    (U : SparseHiddenColumn B × SparseHiddenColumn B) : ENNReal :=
  sparseHiddenColumnImageDensity a ha B U.2

/-- Image density for the simultaneous two-coordinate change. -/
def sparseHiddenPairBothImageDensity (B : Nat) (a : Real)
    (ha : |a| <= (1 : Real) / 8)
    (U : SparseHiddenColumn B × SparseHiddenColumn B) : ENNReal :=
  sparseHiddenColumnImageDensity a ha B U.1 *
    sparseHiddenColumnImageDensity a ha B U.2

theorem measurable_sparseHiddenPairLeftImageDensity
    (B : Nat) (a : Real) (ha : |a| <= (1 : Real) / 8) :
    Measurable (sparseHiddenPairLeftImageDensity B a ha) :=
  (measurable_sparseHiddenColumnImageDensity a ha B).comp measurable_fst

theorem measurable_sparseHiddenPairRightImageDensity
    (B : Nat) (a : Real) (ha : |a| <= (1 : Real) / 8) :
    Measurable (sparseHiddenPairRightImageDensity B a ha) :=
  (measurable_sparseHiddenColumnImageDensity a ha B).comp measurable_snd

theorem measurable_sparseHiddenPairBothImageDensity
    (B : Nat) (a : Real) (ha : |a| <= (1 : Real) / 8) :
    Measurable (sparseHiddenPairBothImageDensity B a ha) :=
  (measurable_sparseHiddenPairLeftImageDensity B a ha).mul
    (measurable_sparseHiddenPairRightImageDensity B a ha)

theorem map_sparseHiddenPairLeftEquiv_measure
    (B : Nat) (a : Real) (ha : |a| <= (1 : Real) / 8) :
    Measure.map (sparseHiddenPairLeftEquiv B a ha)
        (sparseHiddenPairMeasure B) =
      (sparseHiddenPairMeasure B).withDensity
        (sparseHiddenPairLeftImageDensity B a ha) := by
  unfold sparseHiddenPairMeasure sparseHiddenPairLeftEquiv
  change Measure.map
      (Prod.map (sparseHiddenColumnEquiv B a ha) id)
        ((sparseHiddenColumnMeasure B).prod (sparseHiddenColumnMeasure B)) = _
  rw [← Measure.map_prod_map _ _
      (sparseHiddenColumnEquiv B a ha).measurable measurable_id,
    map_sparseHiddenColumnEquiv_measure, Measure.map_id]
  change ((sparseHiddenColumnMeasure B).withDensity
      (sparseHiddenColumnImageDensity a ha B)).prod
        (sparseHiddenColumnMeasure B) =
    ((sparseHiddenColumnMeasure B).prod
      (sparseHiddenColumnMeasure B)).withDensity
        (fun z => sparseHiddenColumnImageDensity a ha B z.1)
  simpa using
    (prod_withDensity (μ := sparseHiddenColumnMeasure B)
      (ν := sparseHiddenColumnMeasure B)
      (measurable_sparseHiddenColumnImageDensity a ha B)
      (measurable_const : Measurable
        (fun _ : SparseHiddenColumn B => (1 : ENNReal))))

theorem map_sparseHiddenPairRightEquiv_measure
    (B : Nat) (a : Real) (ha : |a| <= (1 : Real) / 8) :
    Measure.map (sparseHiddenPairRightEquiv B a ha)
        (sparseHiddenPairMeasure B) =
      (sparseHiddenPairMeasure B).withDensity
        (sparseHiddenPairRightImageDensity B a ha) := by
  unfold sparseHiddenPairMeasure sparseHiddenPairRightEquiv
  change Measure.map
      (Prod.map id (sparseHiddenColumnEquiv B a ha))
        ((sparseHiddenColumnMeasure B).prod (sparseHiddenColumnMeasure B)) = _
  rw [← Measure.map_prod_map _ _ measurable_id
      (sparseHiddenColumnEquiv B a ha).measurable,
    Measure.map_id, map_sparseHiddenColumnEquiv_measure]
  change (sparseHiddenColumnMeasure B).prod
      ((sparseHiddenColumnMeasure B).withDensity
        (sparseHiddenColumnImageDensity a ha B)) =
    ((sparseHiddenColumnMeasure B).prod
      (sparseHiddenColumnMeasure B)).withDensity
        (fun z => sparseHiddenColumnImageDensity a ha B z.2)
  simpa using
    (prod_withDensity (μ := sparseHiddenColumnMeasure B)
      (ν := sparseHiddenColumnMeasure B)
      (measurable_const : Measurable
        (fun _ : SparseHiddenColumn B => (1 : ENNReal)))
      (measurable_sparseHiddenColumnImageDensity a ha B))

theorem map_sparseHiddenPairBothEquiv_measure
    (B : Nat) (a : Real) (ha : |a| <= (1 : Real) / 8) :
    Measure.map (sparseHiddenPairBothEquiv B a ha)
        (sparseHiddenPairMeasure B) =
      (sparseHiddenPairMeasure B).withDensity
        (sparseHiddenPairBothImageDensity B a ha) := by
  unfold sparseHiddenPairMeasure sparseHiddenPairBothEquiv
  change Measure.map
      (Prod.map (sparseHiddenColumnEquiv B a ha)
        (sparseHiddenColumnEquiv B a ha))
        ((sparseHiddenColumnMeasure B).prod (sparseHiddenColumnMeasure B)) = _
  rw [← Measure.map_prod_map _ _
      (sparseHiddenColumnEquiv B a ha).measurable
      (sparseHiddenColumnEquiv B a ha).measurable,
    map_sparseHiddenColumnEquiv_measure,
    prod_withDensity
      (measurable_sparseHiddenColumnImageDensity a ha B)
      (measurable_sparseHiddenColumnImageDensity a ha B)]
  rfl

@[simp] theorem sparseHiddenPairLeftImageDensity_apply_both
    (B : Nat) (a : Real) (ha : |a| <= (1 : Real) / 8)
    (U : SparseHiddenColumn B × SparseHiddenColumn B) :
    sparseHiddenPairLeftImageDensity B a ha
        (sparseHiddenPairBothEquiv B a ha U) =
      sparseHiddenColumnJacobianAtSource a B U.1 := by
  simp [sparseHiddenPairLeftImageDensity]

@[simp] theorem sparseHiddenPairRightImageDensity_apply_both
    (B : Nat) (a : Real) (ha : |a| <= (1 : Real) / 8)
    (U : SparseHiddenColumn B × SparseHiddenColumn B) :
    sparseHiddenPairRightImageDensity B a ha
        (sparseHiddenPairBothEquiv B a ha U) =
      sparseHiddenColumnJacobianAtSource a B U.2 := by
  simp [sparseHiddenPairRightImageDensity]

@[simp] theorem sparseHiddenPairBothImageDensity_apply_both
    (B : Nat) (a : Real) (ha : |a| <= (1 : Real) / 8)
    (U : SparseHiddenColumn B × SparseHiddenColumn B) :
    sparseHiddenPairBothImageDensity B a ha
        (sparseHiddenPairBothEquiv B a ha U) =
      sparseHiddenColumnJacobianAtSource a B U.1 *
        sparseHiddenColumnJacobianAtSource a B U.2 := by
  simp [sparseHiddenPairBothImageDensity]

/-- Total RN density of the first-coordinate changed joint law with respect
to the unchanged two-column/history law. -/
def sparseHiddenPairLeftJointLikelihood
    {n k B : Nat}
    (F : SparseAdaptiveParameterFamily
      (SparseHiddenColumn B × SparseHiddenColumn B) n k)
    (a : Real) (ha : |a| <= (1 : Real) / 8) (T : Nat) :
    (SparseHiddenColumn B × SparseHiddenColumn B) × History n k T -> ENNReal :=
  fun z => sparseHiddenPairLeftImageDensity B a ha z.1 *
    sparseFamilyLikelihoodProduct F
      (sparseHiddenPairLeftEquiv B a ha) T z

/-- Total RN density of the second-coordinate changed joint law. -/
def sparseHiddenPairRightJointLikelihood
    {n k B : Nat}
    (F : SparseAdaptiveParameterFamily
      (SparseHiddenColumn B × SparseHiddenColumn B) n k)
    (a : Real) (ha : |a| <= (1 : Real) / 8) (T : Nat) :
    (SparseHiddenColumn B × SparseHiddenColumn B) × History n k T -> ENNReal :=
  fun z => sparseHiddenPairRightImageDensity B a ha z.1 *
    sparseFamilyLikelihoodProduct F
      (sparseHiddenPairRightEquiv B a ha) T z

/-- Total RN density of the simultaneous two-coordinate changed joint law. -/
def sparseHiddenPairBothJointLikelihood
    {n k B : Nat}
    (F : SparseAdaptiveParameterFamily
      (SparseHiddenColumn B × SparseHiddenColumn B) n k)
    (a : Real) (ha : |a| <= (1 : Real) / 8) (T : Nat) :
    (SparseHiddenColumn B × SparseHiddenColumn B) × History n k T -> ENNReal :=
  fun z => sparseHiddenPairBothImageDensity B a ha z.1 *
    sparseFamilyLikelihoodProduct F
      (sparseHiddenPairBothEquiv B a ha) T z

theorem measurable_sparseHiddenPairLeftJointLikelihood
    {n k B : Nat}
    (F : SparseAdaptiveParameterFamily
      (SparseHiddenColumn B × SparseHiddenColumn B) n k)
    (a : Real) (ha : |a| <= (1 : Real) / 8) (T : Nat) :
    Measurable (sparseHiddenPairLeftJointLikelihood F a ha T) :=
  (measurable_sparseHiddenPairLeftImageDensity B a ha).comp measurable_fst |>.mul
    (measurable_sparseFamilyLikelihoodProduct F
      (sparseHiddenPairLeftEquiv B a ha) T)

theorem measurable_sparseHiddenPairRightJointLikelihood
    {n k B : Nat}
    (F : SparseAdaptiveParameterFamily
      (SparseHiddenColumn B × SparseHiddenColumn B) n k)
    (a : Real) (ha : |a| <= (1 : Real) / 8) (T : Nat) :
    Measurable (sparseHiddenPairRightJointLikelihood F a ha T) :=
  (measurable_sparseHiddenPairRightImageDensity B a ha).comp measurable_fst |>.mul
    (measurable_sparseFamilyLikelihoodProduct F
      (sparseHiddenPairRightEquiv B a ha) T)

theorem measurable_sparseHiddenPairBothJointLikelihood
    {n k B : Nat}
    (F : SparseAdaptiveParameterFamily
      (SparseHiddenColumn B × SparseHiddenColumn B) n k)
    (a : Real) (ha : |a| <= (1 : Real) / 8) (T : Nat) :
    Measurable (sparseHiddenPairBothJointLikelihood F a ha T) :=
  (measurable_sparseHiddenPairBothImageDensity B a ha).comp measurable_fst |>.mul
    (measurable_sparseFamilyLikelihoodProduct F
      (sparseHiddenPairBothEquiv B a ha) T)

/-- Exact first-coordinate push-forward formula; in particular the declared
function is an actual RN density, not a postulated likelihood. -/
theorem sparseHiddenPairLeftJointLaw_map_eq_withDensity
    {n k B : Nat} (P : Policy n k)
    (F : SparseAdaptiveParameterFamily
      (SparseHiddenColumn B × SparseHiddenColumn B) n k)
    (a : Real) (ha : |a| <= (1 : Real) / 8) (T : Nat) :
    Measure.map
        (fun z : (SparseHiddenColumn B × SparseHiddenColumn B) × History n k T =>
          (sparseHiddenPairLeftEquiv B a ha z.1, z.2))
        (sparseJointLaw (sparseHiddenPairMeasure B) P F T) =
      (sparseJointLaw (sparseHiddenPairMeasure B) P F T).withDensity
        (sparseHiddenPairLeftJointLikelihood F a ha T) := by
  exact sparseJointLaw_map_eq_withDensity
    (sparseHiddenPairMeasure B) P F T
    (sparseHiddenPairLeftEquiv B a ha)
    (sparseHiddenPairLeftImageDensity B a ha)
    (measurable_sparseHiddenPairLeftImageDensity B a ha)
    (map_sparseHiddenPairLeftEquiv_measure B a ha)

/-- Exact second-coordinate push-forward formula. -/
theorem sparseHiddenPairRightJointLaw_map_eq_withDensity
    {n k B : Nat} (P : Policy n k)
    (F : SparseAdaptiveParameterFamily
      (SparseHiddenColumn B × SparseHiddenColumn B) n k)
    (a : Real) (ha : |a| <= (1 : Real) / 8) (T : Nat) :
    Measure.map
        (fun z : (SparseHiddenColumn B × SparseHiddenColumn B) × History n k T =>
          (sparseHiddenPairRightEquiv B a ha z.1, z.2))
        (sparseJointLaw (sparseHiddenPairMeasure B) P F T) =
      (sparseJointLaw (sparseHiddenPairMeasure B) P F T).withDensity
        (sparseHiddenPairRightJointLikelihood F a ha T) := by
  exact sparseJointLaw_map_eq_withDensity
    (sparseHiddenPairMeasure B) P F T
    (sparseHiddenPairRightEquiv B a ha)
    (sparseHiddenPairRightImageDensity B a ha)
    (measurable_sparseHiddenPairRightImageDensity B a ha)
    (map_sparseHiddenPairRightEquiv_measure B a ha)

/-- Exact simultaneous two-coordinate push-forward formula. -/
theorem sparseHiddenPairBothJointLaw_map_eq_withDensity
    {n k B : Nat} (P : Policy n k)
    (F : SparseAdaptiveParameterFamily
      (SparseHiddenColumn B × SparseHiddenColumn B) n k)
    (a : Real) (ha : |a| <= (1 : Real) / 8) (T : Nat) :
    Measure.map
        (fun z : (SparseHiddenColumn B × SparseHiddenColumn B) × History n k T =>
          (sparseHiddenPairBothEquiv B a ha z.1, z.2))
        (sparseJointLaw (sparseHiddenPairMeasure B) P F T) =
      (sparseJointLaw (sparseHiddenPairMeasure B) P F T).withDensity
        (sparseHiddenPairBothJointLikelihood F a ha T) := by
  exact sparseJointLaw_map_eq_withDensity
    (sparseHiddenPairMeasure B) P F T
    (sparseHiddenPairBothEquiv B a ha)
    (sparseHiddenPairBothImageDensity B a ha)
    (measurable_sparseHiddenPairBothImageDensity B a ha)
    (map_sparseHiddenPairBothEquiv_measure B a ha)

/-- The four conditional parameter fields obtained at a base point, after
changing the first column, the second column, or both. -/
def sparseHiddenPairRectangle
    {n k B : Nat}
    (F : SparseAdaptiveParameterFamily
      (SparseHiddenColumn B × SparseHiddenColumn B) n k)
    (a : Real) (ha : |a| <= (1 : Real) / 8)
    (hrectangle : forall U t h A,
      F.value t (sparseHiddenPairBothEquiv B a ha U) h A +
          F.value t U h A =
        F.value t (sparseHiddenPairLeftEquiv B a ha U) h A +
          F.value t (sparseHiddenPairRightEquiv B a ha U) h A)
    (U : SparseHiddenColumn B × SparseHiddenColumn B) :
    SparseAdaptiveRectangle n k where
  base := F.at U
  left := F.at (sparseHiddenPairLeftEquiv B a ha U)
  right := F.at (sparseHiddenPairRightEquiv B a ha U)
  both := F.at (sparseHiddenPairBothEquiv B a ha U)
  rectangle := hrectangle U

/-- The four-corner factor evaluated at the unchanged base point. -/
def sparseHiddenPairCrossLikelihood
    {n k B : Nat}
    (F : SparseAdaptiveParameterFamily
      (SparseHiddenColumn B × SparseHiddenColumn B) n k)
    (a : Real) (ha : |a| <= (1 : Real) / 8)
    (hrectangle : forall U t h A,
      F.value t (sparseHiddenPairBothEquiv B a ha U) h A +
          F.value t U h A =
        F.value t (sparseHiddenPairLeftEquiv B a ha U) h A +
          F.value t (sparseHiddenPairRightEquiv B a ha U) h A)
    (T : Nat)
    (z : (SparseHiddenColumn B × SparseHiddenColumn B) × History n k T) :
    ENNReal :=
  sparseCrossLikelihood
    (sparseHiddenPairRectangle F a ha hrectangle z.1) T z.2

private theorem measurable_sparseHiddenPairCrossLogIncrement
    {n k B t : Nat}
    (F : SparseAdaptiveParameterFamily
      (SparseHiddenColumn B × SparseHiddenColumn B) n k)
    (a : Real) (ha : |a| <= (1 : Real) / 8)
    (hrectangle : forall U t h A,
      F.value t (sparseHiddenPairBothEquiv B a ha U) h A +
          F.value t U h A =
        F.value t (sparseHiddenPairLeftEquiv B a ha U) h A +
          F.value t (sparseHiddenPairRightEquiv B a ha U) h A) :
    Measurable (fun z :
        (SparseHiddenColumn B × SparseHiddenColumn B) × History n k (t + 1) =>
      sparseCrossLogIncrement
        (sparseHiddenPairRectangle F a ha hrectangle z.1) t z.2) := by
  let eL := sparseHiddenPairLeftEquiv B a ha
  let eR := sparseHiddenPairRightEquiv B a ha
  let eB := sparseHiddenPairBothEquiv B a ha
  let parameter := fun (e :
      (SparseHiddenColumn B × SparseHiddenColumn B) ≃ᵐ
        (SparseHiddenColumn B × SparseHiddenColumn B))
      (z : (SparseHiddenColumn B × SparseHiddenColumn B) ×
        History n k (t + 1)) =>
    F.value t (e z.1) z.2.1 z.2.2.1
  have hp : forall e :
      (SparseHiddenColumn B × SparseHiddenColumn B) ≃ᵐ
        (SparseHiddenColumn B × SparseHiddenColumn B),
      Measurable (parameter e) := by
    intro e
    exact (F.measurable_value t).comp <|
      (((e.measurable.comp measurable_fst).prodMk
        (measurable_fst.comp measurable_snd)).prodMk
          (measurable_fst.comp (measurable_snd.comp measurable_snd)))
  let y := fun z :
      (SparseHiddenColumn B × SparseHiddenColumn B) × History n k (t + 1) =>
    z.2.2.2
  have hy : Measurable y :=
    measurable_snd.comp (measurable_snd.comp measurable_snd)
  change Measurable (fun z :
      (SparseHiddenColumn B × SparseHiddenColumn B) × History n k (t + 1) =>
    if y z ∈ Icc (-1 / 2 : Real) (1 / 2 : Real) then
      feedbackLogJacobian (parameter eB z) (y z) -
        feedbackLogJacobian (parameter eR z) (y z) -
        feedbackLogJacobian (parameter eL z) (y z) +
        feedbackLogJacobian
          (F.value t z.1 z.2.1 z.2.2.1) (y z)
    else 0)
  apply Measurable.ite
  · exact hy measurableSet_Icc
  · have hbase : Measurable (fun z :
        (SparseHiddenColumn B × SparseHiddenColumn B) × History n k (t + 1) =>
      F.value t z.1 z.2.1 z.2.2.1) :=
      (F.measurable_value t).comp <|
        ((measurable_fst.prodMk (measurable_fst.comp measurable_snd)).prodMk
          (measurable_fst.comp (measurable_snd.comp measurable_snd)))
    exact (((measurable_feedbackLogJacobian_uncurry.comp
          ((hp eB).prodMk hy)).sub
        (measurable_feedbackLogJacobian_uncurry.comp
          ((hp eR).prodMk hy))).sub
        (measurable_feedbackLogJacobian_uncurry.comp
          ((hp eL).prodMk hy))).add
        (measurable_feedbackLogJacobian_uncurry.comp
          (hbase.prodMk hy))
  · exact measurable_const

theorem measurable_sparseHiddenPairCrossLikelihood
    {n k B : Nat}
    (F : SparseAdaptiveParameterFamily
      (SparseHiddenColumn B × SparseHiddenColumn B) n k)
    (a : Real) (ha : |a| <= (1 : Real) / 8)
    (hrectangle : forall U t h A,
      F.value t (sparseHiddenPairBothEquiv B a ha U) h A +
          F.value t U h A =
        F.value t (sparseHiddenPairLeftEquiv B a ha U) h A +
          F.value t (sparseHiddenPairRightEquiv B a ha U) h A) :
    forall T, Measurable
      (sparseHiddenPairCrossLikelihood F a ha hrectangle T) := by
  intro T
  have hlog : Measurable (fun z :
      (SparseHiddenColumn B × SparseHiddenColumn B) × History n k T =>
    sparseCrossLog
      (sparseHiddenPairRectangle F a ha hrectangle z.1) T z.2) := by
    induction T with
    | zero => exact measurable_const
    | succ t ih =>
        change Measurable (fun z :
            (SparseHiddenColumn B × SparseHiddenColumn B) × History n k (t + 1) =>
          sparseCrossLog
              (sparseHiddenPairRectangle F a ha hrectangle z.1) t z.2.1 +
            sparseCrossLogIncrement
              (sparseHiddenPairRectangle F a ha hrectangle z.1) t z.2)
        exact (ih.comp
          (measurable_fst.prodMk
            (measurable_fst.comp measurable_snd))).add
          (measurable_sparseHiddenPairCrossLogIncrement
            F a ha hrectangle)
  exact hlog.exp.ennreal_ofReal

@[simp] theorem sparseHiddenPairLeftJointLikelihood_apply_both
    {n k B : Nat}
    (F : SparseAdaptiveParameterFamily
      (SparseHiddenColumn B × SparseHiddenColumn B) n k)
    (a : Real) (ha : |a| <= (1 : Real) / 8) (T : Nat)
    (U : SparseHiddenColumn B × SparseHiddenColumn B) (h : History n k T) :
    sparseHiddenPairLeftJointLikelihood F a ha T
        (sparseHiddenPairBothEquiv B a ha U, h) =
      sparseHiddenColumnJacobianAtSource a B U.1 *
        sparseLikelihoodProduct
          (F.at (sparseHiddenPairRightEquiv B a ha U))
          (F.at (sparseHiddenPairBothEquiv B a ha U)) T h := by
  unfold sparseHiddenPairLeftJointLikelihood
  rw [sparseHiddenPairLeftImageDensity_apply_both,
    sparseFamilyLikelihoodProduct_eq_sparseLikelihoodProduct,
    sparseHiddenPairLeftEquiv_symm_both]

@[simp] theorem sparseHiddenPairRightJointLikelihood_apply_both
    {n k B : Nat}
    (F : SparseAdaptiveParameterFamily
      (SparseHiddenColumn B × SparseHiddenColumn B) n k)
    (a : Real) (ha : |a| <= (1 : Real) / 8) (T : Nat)
    (U : SparseHiddenColumn B × SparseHiddenColumn B) (h : History n k T) :
    sparseHiddenPairRightJointLikelihood F a ha T
        (sparseHiddenPairBothEquiv B a ha U, h) =
      sparseHiddenColumnJacobianAtSource a B U.2 *
        sparseLikelihoodProduct
          (F.at (sparseHiddenPairLeftEquiv B a ha U))
          (F.at (sparseHiddenPairBothEquiv B a ha U)) T h := by
  unfold sparseHiddenPairRightJointLikelihood
  rw [sparseHiddenPairRightImageDensity_apply_both,
    sparseFamilyLikelihoodProduct_eq_sparseLikelihoodProduct,
    sparseHiddenPairRightEquiv_symm_both]

@[simp] theorem sparseHiddenPairBothJointLikelihood_apply_both
    {n k B : Nat}
    (F : SparseAdaptiveParameterFamily
      (SparseHiddenColumn B × SparseHiddenColumn B) n k)
    (a : Real) (ha : |a| <= (1 : Real) / 8) (T : Nat)
    (U : SparseHiddenColumn B × SparseHiddenColumn B) (h : History n k T) :
    sparseHiddenPairBothJointLikelihood F a ha T
        (sparseHiddenPairBothEquiv B a ha U, h) =
      (sparseHiddenColumnJacobianAtSource a B U.1 *
          sparseHiddenColumnJacobianAtSource a B U.2) *
        sparseLikelihoodProduct (F.at U)
          (F.at (sparseHiddenPairBothEquiv B a ha U)) T h := by
  unfold sparseHiddenPairBothJointLikelihood
  rw [sparseHiddenPairBothImageDensity_apply_both,
    sparseFamilyLikelihoodProduct_eq_sparseLikelihoodProduct]
  change
    (sparseHiddenColumnJacobianAtSource a B U.1 *
        sparseHiddenColumnJacobianAtSource a B U.2) *
      sparseLikelihoodProduct
        (F.at ((sparseHiddenPairBothEquiv B a ha).symm
          (sparseHiddenPairBothEquiv B a ha U)))
        (F.at (sparseHiddenPairBothEquiv B a ha U)) T h = _
  rw [(sparseHiddenPairBothEquiv B a ha).symm_apply_apply]

/-- At the image of a base point the product of the two one-coordinate RN
densities equals the simultaneous RN density times the manuscript's
four-corner factor.  Both hidden Jacobians cancel by literal multiplication;
no quotient of RN derivatives is assumed. -/
theorem sparseHiddenPairJointLikelihood_cross_balance_apply_both
    {n k B : Nat}
    (F : SparseAdaptiveParameterFamily
      (SparseHiddenColumn B × SparseHiddenColumn B) n k)
    (a : Real) (ha : |a| <= (1 : Real) / 8)
    (hrectangle : forall U t h A,
      F.value t (sparseHiddenPairBothEquiv B a ha U) h A +
          F.value t U h A =
        F.value t (sparseHiddenPairLeftEquiv B a ha U) h A +
          F.value t (sparseHiddenPairRightEquiv B a ha U) h A)
    (T : Nat) (U : SparseHiddenColumn B × SparseHiddenColumn B)
    (h : History n k T) (hsupp : sparseHistoryInFeedbackSupport T h) :
    sparseHiddenPairLeftJointLikelihood F a ha T
          (sparseHiddenPairBothEquiv B a ha U, h) *
        sparseHiddenPairRightJointLikelihood F a ha T
          (sparseHiddenPairBothEquiv B a ha U, h) =
      sparseHiddenPairBothJointLikelihood F a ha T
          (sparseHiddenPairBothEquiv B a ha U, h) *
        sparseHiddenPairCrossLikelihood F a ha hrectangle T (U, h) := by
  let R := sparseHiddenPairRectangle F a ha hrectangle U
  have hbalance := sparseLikelihoodProduct_cross_balance R T h hsupp
  rw [sparseHiddenPairLeftJointLikelihood_apply_both,
    sparseHiddenPairRightJointLikelihood_apply_both,
    sparseHiddenPairBothJointLikelihood_apply_both]
  change
    (sparseHiddenColumnJacobianAtSource a B U.1 *
          sparseLikelihoodProduct R.right R.both T h) *
        (sparseHiddenColumnJacobianAtSource a B U.2 *
          sparseLikelihoodProduct R.left R.both T h) =
      ((sparseHiddenColumnJacobianAtSource a B U.1 *
            sparseHiddenColumnJacobianAtSource a B U.2) *
          sparseLikelihoodProduct R.base R.both T h) *
        sparseCrossLikelihood R T h
  calc
    (sparseHiddenColumnJacobianAtSource a B U.1 *
          sparseLikelihoodProduct R.right R.both T h) *
        (sparseHiddenColumnJacobianAtSource a B U.2 *
          sparseLikelihoodProduct R.left R.both T h) =
      (sparseHiddenColumnJacobianAtSource a B U.1 *
          sparseHiddenColumnJacobianAtSource a B U.2) *
        (sparseLikelihoodProduct R.right R.both T h *
          sparseLikelihoodProduct R.left R.both T h) := by ac_rfl
    _ = (sparseHiddenColumnJacobianAtSource a B U.1 *
          sparseHiddenColumnJacobianAtSource a B U.2) *
        (sparseLikelihoodProduct R.base R.both T h *
          sparseCrossLikelihood R T h) := by rw [hbalance]
    _ = (sparseHiddenColumnJacobianAtSource a B U.1 *
          sparseHiddenColumnJacobianAtSource a B U.2) *
        sparseLikelihoodProduct R.base R.both T h *
          sparseCrossLikelihood R T h := by ac_rfl

/-- The cross factor pulled back from a target point to the unchanged base
hidden coordinates. -/
def sparseHiddenPairTargetCrossLikelihood
    {n k B : Nat}
    (F : SparseAdaptiveParameterFamily
      (SparseHiddenColumn B × SparseHiddenColumn B) n k)
    (a : Real) (ha : |a| <= (1 : Real) / 8)
    (hrectangle : forall U t h A,
      F.value t (sparseHiddenPairBothEquiv B a ha U) h A +
          F.value t U h A =
        F.value t (sparseHiddenPairLeftEquiv B a ha U) h A +
          F.value t (sparseHiddenPairRightEquiv B a ha U) h A)
    (T : Nat)
    (z : (SparseHiddenColumn B × SparseHiddenColumn B) × History n k T) :
    ENNReal :=
  sparseHiddenPairCrossLikelihood F a ha hrectangle T
    ((sparseHiddenPairBothEquiv B a ha).symm z.1, z.2)

theorem measurable_sparseHiddenPairTargetCrossLikelihood
    {n k B : Nat}
    (F : SparseAdaptiveParameterFamily
      (SparseHiddenColumn B × SparseHiddenColumn B) n k)
    (a : Real) (ha : |a| <= (1 : Real) / 8)
    (hrectangle : forall U t h A,
      F.value t (sparseHiddenPairBothEquiv B a ha U) h A +
          F.value t U h A =
        F.value t (sparseHiddenPairLeftEquiv B a ha U) h A +
          F.value t (sparseHiddenPairRightEquiv B a ha U) h A)
    (T : Nat) :
    Measurable
      (sparseHiddenPairTargetCrossLikelihood F a ha hrectangle T) :=
  (measurable_sparseHiddenPairCrossLikelihood F a ha hrectangle T).comp <|
    (((sparseHiddenPairBothEquiv B a ha).symm.measurable.comp
      measurable_fst).prodMk measurable_snd)

theorem ae_sparseJointLaw_history_support
    {Omega : Type*} [MeasurableSpace Omega]
    {n k : Nat} (mu : Measure Omega) [SFinite mu]
    (P : Policy n k) (F : SparseAdaptiveParameterFamily Omega n k)
    (T : Nat) :
    ∀ᵐ z ∂sparseJointLaw mu P F T,
      sparseHistoryInFeedbackSupport T z.2 := by
  unfold sparseJointLaw
  apply Measure.ae_compProd_of_ae_ae
  · exact measurable_snd
      (measurableSet_sparseHistoryInFeedbackSupport (n := n) (k := k) T)
  · apply ae_of_all
    intro omega
    rw [sparseFamilyLawKernel_apply]
    exact ae_sparseAdaptiveProcess_history_support P (F.at omega) T

/-- Exact change-of-variables identity in the first two lines of
`eq:lower-likelihood-cross`:
`E_P[Lambda_j Lambda_l] = E_P[(Lambda_j Lambda_l/Lambda_jl) o Phi_jl]`.
The quotient notation is represented by the support-safe four-corner factor,
and the equality is derived from the three genuine push-forward densities. -/
theorem sparseHiddenPairJointLikelihood_cross_integral_eq
    {n k B : Nat} (P : Policy n k)
    (F : SparseAdaptiveParameterFamily
      (SparseHiddenColumn B × SparseHiddenColumn B) n k)
    (a : Real) (ha : |a| <= (1 : Real) / 8)
    (hrectangle : forall U t h A,
      F.value t (sparseHiddenPairBothEquiv B a ha U) h A +
          F.value t U h A =
        F.value t (sparseHiddenPairLeftEquiv B a ha U) h A +
          F.value t (sparseHiddenPairRightEquiv B a ha U) h A)
    (T : Nat) :
    (∫⁻ z, sparseHiddenPairLeftJointLikelihood F a ha T z *
          sparseHiddenPairRightJointLikelihood F a ha T z
        ∂sparseJointLaw (sparseHiddenPairMeasure B) P F T) =
      ∫⁻ z, sparseHiddenPairCrossLikelihood F a ha hrectangle T z
        ∂sparseJointLaw (sparseHiddenPairMeasure B) P F T := by
  let mu := sparseJointLaw (sparseHiddenPairMeasure B) P F T
  let e : (SparseHiddenColumn B × SparseHiddenColumn B) × History n k T ->
      (SparseHiddenColumn B × SparseHiddenColumn B) × History n k T :=
    fun z => (sparseHiddenPairBothEquiv B a ha z.1, z.2)
  have he : Measurable e :=
    ((sparseHiddenPairBothEquiv B a ha).measurable.comp
      measurable_fst).prodMk measurable_snd
  let target := sparseHiddenPairTargetCrossLikelihood F a ha hrectangle T
  let both := sparseHiddenPairBothJointLikelihood F a ha T
  have htarget : Measurable target :=
    measurable_sparseHiddenPairTargetCrossLikelihood F a ha hrectangle T
  have hboth : Measurable both :=
    measurable_sparseHiddenPairBothJointLikelihood F a ha T
  have hmap : Measure.map e mu = mu.withDensity both := by
    exact sparseHiddenPairBothJointLaw_map_eq_withDensity P F a ha T
  have hbalance : ∀ᵐ z ∂mu,
      sparseHiddenPairLeftJointLikelihood F a ha T z *
          sparseHiddenPairRightJointLikelihood F a ha T z =
        both z * target z := by
    filter_upwards [ae_sparseJointLaw_history_support
      (sparseHiddenPairMeasure B) P F T] with z hz
    have h := sparseHiddenPairJointLikelihood_cross_balance_apply_both
      F a ha hrectangle T
      ((sparseHiddenPairBothEquiv B a ha).symm z.1) z.2 hz
    change sparseHiddenPairLeftJointLikelihood F a ha T z *
          sparseHiddenPairRightJointLikelihood F a ha T z =
      sparseHiddenPairBothJointLikelihood F a ha T z *
        sparseHiddenPairCrossLikelihood F a ha hrectangle T
          ((sparseHiddenPairBothEquiv B a ha).symm z.1, z.2)
    simpa using h
  calc
    (∫⁻ z, sparseHiddenPairLeftJointLikelihood F a ha T z *
          sparseHiddenPairRightJointLikelihood F a ha T z ∂mu) =
        ∫⁻ z, both z * target z ∂mu := lintegral_congr_ae hbalance
    _ = ∫⁻ z, target z ∂mu.withDensity both :=
      (lintegral_withDensity_eq_lintegral_mul mu hboth htarget).symm
    _ = ∫⁻ z, target z ∂Measure.map e mu := by rw [hmap]
    _ = ∫⁻ z, target (e z) ∂mu := lintegral_map htarget he
    _ = ∫⁻ z, sparseHiddenPairCrossLikelihood F a ha hrectangle T z ∂mu := by
      apply lintegral_congr
      intro z
      change sparseHiddenPairCrossLikelihood F a ha hrectangle T
          ((sparseHiddenPairBothEquiv B a ha).symm
            (sparseHiddenPairBothEquiv B a ha z.1), z.2) =
        sparseHiddenPairCrossLikelihood F a ha hrectangle T z
      rw [(sparseHiddenPairBothEquiv B a ha).symm_apply_apply]

/-- Full joint form of `eq:lower-likelihood-cross`, with the exact manuscript
constant.  The two hypotheses are the two pathwise estimates proved from the
concrete sparse table: the four-corner energy is bounded by
`a^2*eta^2*N_jl`, and this quantity is at most the block budget `C`.
Everything involving likelihoods and change of variables is discharged by
the preceding theorems. -/
theorem lower_likelihood_cross_joint
    {n n' k q c0 B : Nat} (P : Policy n k)
    (F : SparseAdaptiveParameterFamily
      (SparseHiddenColumn B × SparseHiddenColumn B) n k)
    (a eta : Real) (ha : |a| <= (1 : Real) / 8)
    (hn' : n' <= n) (j l : Fin n')
    (hrectangle : forall U t h A,
      F.value t (sparseHiddenPairBothEquiv B a ha U) h A +
          F.value t U h A =
        F.value t (sparseHiddenPairLeftEquiv B a ha U) h A +
          F.value t (sparseHiddenPairRightEquiv B a ha U) h A)
    (T : Nat) (C : Real)
    (henergyN : forall U (h : History n k T),
      sparseCrossEnergy
          (sparseHiddenPairRectangle F a ha hrectangle U) T h <=
        a ^ 2 * eta ^ 2 * sparseN hn' q c0 j l T h)
    (hbudget : forall h : History n k T,
      a ^ 2 * eta ^ 2 * sparseN hn' q c0 j l T h <= C) :
    (∫⁻ z, sparseHiddenPairLeftJointLikelihood F a ha T z *
          sparseHiddenPairRightJointLikelihood F a ha T z
        ∂sparseJointLaw (sparseHiddenPairMeasure B) P F T) <=
      1 + ENNReal.ofReal
          (128 * a ^ 2 * eta ^ 2 * Real.exp (128 * C)) *
        (∫⁻ z, ENNReal.ofReal (sparseN hn' q c0 j l T z.2)
          ∂sparseJointLaw (sparseHiddenPairMeasure B) P F T) := by
  rw [sparseHiddenPairJointLikelihood_cross_integral_eq
    P F a ha hrectangle T]
  let mu := sparseJointLaw (sparseHiddenPairMeasure B) P F T
  let c : Real := a ^ 2 * eta ^ 2
  let K : ENNReal := ENNReal.ofReal (128 * Real.exp (128 * C))
  let D : ENNReal := ENNReal.ofReal
    (128 * a ^ 2 * eta ^ 2 * Real.exp (128 * C))
  have hc : 0 <= c := mul_nonneg (sq_nonneg a) (sq_nonneg eta)
  have hfactor : K * ENNReal.ofReal c = D := by
    change ENNReal.ofReal (128 * Real.exp (128 * C)) *
        ENNReal.ofReal c =
      ENNReal.ofReal (128 * a ^ 2 * eta ^ 2 * Real.exp (128 * C))
    rw [← ENNReal.ofReal_mul
      (mul_nonneg (by norm_num) (Real.exp_pos _).le)]
    apply congrArg ENNReal.ofReal
    dsimp [c]
    ring
  have hpoint : forall z :
      (SparseHiddenColumn B × SparseHiddenColumn B) × History n k T,
      sparseHiddenPairCrossLikelihood F a ha hrectangle T z <=
        1 + D * ENNReal.ofReal (sparseN hn' q c0 j l T z.2) := by
    intro z
    let R := sparseHiddenPairRectangle F a ha hrectangle z.1
    have hEC : forall h : History n k T,
        sparseCrossEnergy R T h <= C := by
      intro h
      exact (henergyN z.1 h).trans (hbudget h)
    have hbase := sparseCrossLikelihood_le R T C hEC z.2
    have hEN : ENNReal.ofReal (sparseCrossEnergy R T z.2) <=
        ENNReal.ofReal c *
          ENNReal.ofReal (sparseN hn' q c0 j l T z.2) := by
      calc
        ENNReal.ofReal (sparseCrossEnergy R T z.2) <=
            ENNReal.ofReal
              (c * sparseN hn' q c0 j l T z.2) :=
          ENNReal.ofReal_le_ofReal (henergyN z.1 z.2)
        _ = ENNReal.ofReal c *
            ENNReal.ofReal (sparseN hn' q c0 j l T z.2) := by
          rw [ENNReal.ofReal_mul hc]
    change sparseCrossLikelihood R T z.2 <= _
    calc
      sparseCrossLikelihood R T z.2 <=
          1 + K * ENNReal.ofReal (sparseCrossEnergy R T z.2) := hbase
      _ <= 1 + K * (ENNReal.ofReal c *
          ENNReal.ofReal (sparseN hn' q c0 j l T z.2)) :=
        add_le_add le_rfl (mul_le_mul_right hEN K)
      _ = 1 + D * ENNReal.ofReal
          (sparseN hn' q c0 j l T z.2) := by
        rw [← mul_assoc, hfactor]
  have hNmeas : Measurable (fun z :
      (SparseHiddenColumn B × SparseHiddenColumn B) × History n k T =>
      ENNReal.ofReal (sparseN hn' q c0 j l T z.2)) :=
    (Measurable.ennreal_ofReal (measurable_sparseN hn' j l T)).comp
      measurable_snd
  letI : IsProbabilityMeasure mu := by
    dsimp [mu, sparseJointLaw]
    infer_instance
  calc
    (∫⁻ z, sparseHiddenPairCrossLikelihood F a ha hrectangle T z ∂mu) <=
        ∫⁻ z, (1 + D *
          ENNReal.ofReal (sparseN hn' q c0 j l T z.2)) ∂mu :=
      lintegral_mono hpoint
    _ = (∫⁻ _z : (SparseHiddenColumn B × SparseHiddenColumn B) ×
          History n k T, (1 : ENNReal) ∂mu) +
        ∫⁻ z, D * ENNReal.ofReal
          (sparseN hn' q c0 j l T z.2) ∂mu := by
      rw [lintegral_add_left]
      exact measurable_const
    _ = 1 + D *
        (∫⁻ z, ENNReal.ofReal (sparseN hn' q c0 j l T z.2) ∂mu) := by
      rw [lintegral_const_mul D hNmeas]
      simp
    _ = 1 + ENNReal.ofReal
          (128 * a ^ 2 * eta ^ 2 * Real.exp (128 * C)) *
        (∫⁻ z, ENNReal.ofReal (sparseN hn' q c0 j l T z.2) ∂mu) := rfl

#print axioms sparseJointLaw_map_eq_withDensity
#print axioms lower_likelihood_diagonal_joint
#print axioms lower_likelihood_diagonal_joint_sparseConstants
#print axioms sparseHiddenPairJointLikelihood_cross_integral_eq
#print axioms lower_likelihood_cross_joint

end

end MsetsLower.Lower.Sparse
