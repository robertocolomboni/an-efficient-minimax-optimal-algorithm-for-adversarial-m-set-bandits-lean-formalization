import MsetsLower.Lower.Dense.OneStepKL
import Mathlib.Probability.Kernel.Composition.Lemmas

/-!
# Adaptive stochastic law for the dense paired construction

This file constructs the action--feedback law `P_θ` directly from an
arbitrary history-measurable randomized policy.  The latent binary statistic
is mapped to the exact affine scalar feedback in
`eq:lower-dense-action-loss`; the map is proved to be a measurable embedding.
-/

namespace MsetsLower.Lower.Dense

open MsetsLower
open MeasureTheory ProbabilityTheory InformationTheory
open scoped BigOperators ENNReal NNReal ProbabilityTheory

noncomputable section

/-! ## KL invariance under lossless measurable encodings -/

/-- Absolute continuity is reflected, as well as preserved, by a measurable
embedding. -/
theorem absolutelyContinuous_map_embedding_iff
    {α β : Type*} [MeasurableSpace α] [MeasurableSpace β]
    {f : α → β} (hf : MeasurableEmbedding f) (μ ν : Measure α) :
    μ.map f ≪ ν.map f ↔ μ ≪ ν := by
  constructor
  · intro h s hνs
    have hmapν : ν.map f (f '' s) = 0 := by
      rw [hf.map_apply, hf.injective.preimage_image]
      exact hνs
    have hmapμ := h hmapν
    rwa [hf.map_apply, hf.injective.preimage_image] at hmapμ
  · exact hf.absolutelyContinuous_map

/-- Kullback--Leibler divergence is invariant under a measurable embedding.
This is the lossless-data-processing fact used twice below: once for the
Boolean-to-real encoding and once for reassociation of product histories. -/
theorem klDiv_map_measurableEmbedding
    {α β : Type*} [MeasurableSpace α] [MeasurableSpace β]
    {f : α → β} (hf : MeasurableEmbedding f) (μ ν : Measure α)
    [IsFiniteMeasure μ] [IsFiniteMeasure ν] :
    klDiv (μ.map f) (ν.map f) = klDiv μ ν := by
  by_cases hac : μ ≪ ν
  · have hmapac : μ.map f ≪ ν.map f := hf.absolutelyContinuous_map hac
    rw [klDiv_eq_lintegral_klFun_of_ac hac,
      klDiv_eq_lintegral_klFun_of_ac hmapac]
    rw [lintegral_map' (by fun_prop) hf.measurable.aemeasurable]
    apply lintegral_congr_ae
    filter_upwards [hf.rnDeriv_map μ ν] with x hx
    rw [hx]
  · have hmapac : ¬ μ.map f ≪ ν.map f := by
      rwa [absolutelyContinuous_map_embedding_iff hf]
    rw [klDiv_of_not_ac hac, klDiv_of_not_ac hmapac]

/-! ## Conditional Bernoulli feedback kernels -/

/-- Encode a Boolean feedback statistic in the protocol's real coordinate. -/
def boolFeedbackReal : Bool → Real
  | false => 0
  | true => 1

theorem boolFeedbackReal_injective : Function.Injective boolFeedbackReal := by
  intro a b h
  cases a <;> cases b <;> simp [boolFeedbackReal] at h ⊢

theorem measurable_boolFeedbackReal : Measurable boolFeedbackReal :=
  measurable_of_finite _

theorem measurableEmbedding_boolFeedbackReal :
    MeasurableEmbedding boolFeedbackReal where
  injective := boolFeedbackReal_injective
  measurable := measurable_boolFeedbackReal
  measurableSet_image' := by
    intro s _
    exact (Set.finite_univ.subset (Set.subset_univ s)).image _ |>.measurableSet

/-- Lossless encoding of an action and its Boolean feedback. -/
def encodeActionFeedback {n k : Nat} : MSetAction n k × Bool → MSetAction n k × Real :=
  Prod.map id boolFeedbackReal

theorem measurable_encodeActionFeedback {n k : Nat} :
    Measurable (encodeActionFeedback : MSetAction n k × Bool → MSetAction n k × Real) :=
  (MeasurableEmbedding.id.prodMap measurableEmbedding_boolFeedbackReal).measurable

theorem measurableEmbedding_encodeActionFeedback {n k : Nat} :
    MeasurableEmbedding
      (encodeActionFeedback : MSetAction n k × Bool → MSetAction n k × Real) :=
  MeasurableEmbedding.id.prodMap measurableEmbedding_boolFeedbackReal

/-- Exact affine scalar feedback from `eq:lower-dense-action-loss`, as a
function of the chosen action and the latent event indicator. -/
def pairedScalarFeedback {n k : Nat} (hD : 2 * k ≤ n)
    (A : MSetAction n k) (b : Bool) : Real :=
  (1 : Real) / 3 + (2 / 3 : Real) *
    (boolFeedbackReal b -
      (pairedSectionCard hD A : Real) / (2 * (k : Real)))

/-- Retain the action and encode its latent event by the manuscript's
literal scalar action loss. -/
def encodePairedActionFeedback {n k : Nat} (hD : 2 * k ≤ n) :
    MSetAction n k × Bool → MSetAction n k × Real
  | (A, b) => (A, pairedScalarFeedback hD A b)

theorem injective_encodePairedActionFeedback {n k : Nat}
    (hD : 2 * k ≤ n) :
    Function.Injective (encodePairedActionFeedback hD) := by
  rintro ⟨A, b⟩ ⟨A', b'⟩ h
  have hA : A = A' := congrArg Prod.fst h
  subst A'
  have hb : pairedScalarFeedback hD A b =
      pairedScalarFeedback hD A b' := congrArg Prod.snd h
  have : b = b' := by
    cases b <;> cases b'
    · rfl
    · simp only [pairedScalarFeedback, boolFeedbackReal] at hb
      exfalso
      linarith
    · simp only [pairedScalarFeedback, boolFeedbackReal] at hb
      exfalso
      linarith
    · rfl
  subst b'
  rfl

theorem measurable_encodePairedActionFeedback {n k : Nat}
    (hD : 2 * k ≤ n) :
    Measurable (encodePairedActionFeedback hD) :=
  measurable_of_finite _

theorem measurableEmbedding_encodePairedActionFeedback {n k : Nat}
    (hD : 2 * k ≤ n) :
    MeasurableEmbedding (encodePairedActionFeedback hD) where
  injective := injective_encodePairedActionFeedback hD
  measurable := measurable_encodePairedActionFeedback hD
  measurableSet_image' := by
    intro s _
    exact (Set.finite_univ.subset (Set.subset_univ s)).image _ |>.measurableSet

/-- For the actual sampled pair item, the affine encoding is literally the
action loss proved in `lower_dense_action_loss`. -/
theorem pairedScalarFeedback_selected_eq_actionLoss {n k : Nat}
    (hk : 1 ≤ k) (hD : 2 * k ≤ n) (A : MSetAction n k)
    (J : PairItem k) :
    pairedScalarFeedback hD A
        (decide (pairCoordinate hD J ∈ pairedSection hD A)) =
      actionLoss A (pairedLoss hD J) := by
  rw [lower_dense_action_loss hk hD A J]
  have hb : boolFeedbackReal
        (decide (pairCoordinate hD J ∈ pairedSection hD A)) =
      pairedSelected hD A J := by
    by_cases hJ : pairCoordinate hD J ∈ pairedSection hD A
    · simp [hJ, boolFeedbackReal, pairedSelected]
    · simp [hJ, boolFeedbackReal, pairedSelected]
  simp only [pairedScalarFeedback, hb]

/-- Bernoulli feedback kernel indexed by the learner action. -/
def pairedActionBoolKernel {n k : Nat} (hk : 1 ≤ k) (hD : 2 * k ≤ n)
    (θ : Fin k → PairSign) (ε : Real) : Kernel (MSetAction n k) Bool :=
  Kernel.ofFunOfCountable fun A =>
    bernoulliLaw (pairedBernoulliParameter hD θ ε A)

theorem pairedActionBoolKernel_apply {n k : Nat} (hk : 1 ≤ k)
    (hD : 2 * k ≤ n) (θ : Fin k → PairSign) (ε : Real)
    (A : MSetAction n k) :
    pairedActionBoolKernel hk hD θ ε A =
      bernoulliLaw (pairedBernoulliParameter hD θ ε A) :=
  rfl

theorem pairedActionBoolKernel_isMarkov {n k : Nat}
    (hk : 1 ≤ k) (hD : 2 * k ≤ n) (θ : Fin k → PairSign) (ε : Real)
    (hε0 : 0 ≤ ε) (hε1 : ε ≤ 1) :
    IsMarkovKernel (pairedActionBoolKernel hk hD θ ε) := by
  constructor
  intro A
  constructor
  rw [pairedActionBoolKernel_apply,
    bernoulliLaw_apply_univ
      (pairedBernoulliParameter_mem_Icc hk hD θ hε0 hε1 A).1
      (pairedBernoulliParameter_mem_Icc hk hD θ hε0 hε1 A).2]

/-- Conditional Boolean feedback after retaining the preceding history and
sampled action. -/
def pairedHistoryActionBoolKernel {n k : Nat} (hk : 1 ≤ k)
    (hD : 2 * k ≤ n) (θ : Fin k → PairSign) (ε : Real) (t : Nat) :
    Kernel (History n k t × MSetAction n k) Bool :=
  (pairedActionBoolKernel hk hD θ ε).comap Prod.snd measurable_snd

theorem pairedHistoryActionBoolKernel_isMarkov {n k : Nat}
    (hk : 1 ≤ k) (hD : 2 * k ≤ n) (θ : Fin k → PairSign) (ε : Real)
    (hε0 : 0 ≤ ε) (hε1 : ε ≤ 1) (t : Nat) :
    IsMarkovKernel (pairedHistoryActionBoolKernel hk hD θ ε t) := by
  unfold pairedHistoryActionBoolKernel
  letI : IsMarkovKernel (pairedActionBoolKernel hk hD θ ε) :=
    pairedActionBoolKernel_isMarkov hk hD θ ε hε0 hε1
  infer_instance

@[simp] theorem pairedHistoryActionBoolKernel_apply {n k : Nat}
    (hk : 1 ≤ k) (hD : 2 * k ≤ n) (θ : Fin k → PairSign) (ε : Real)
    (t : Nat) (h : History n k t) (A : MSetAction n k) :
    pairedHistoryActionBoolKernel hk hD θ ε t (h, A) =
      bernoulliLaw (pairedBernoulliParameter hD θ ε A) := by
  rw [pairedHistoryActionBoolKernel, Kernel.comap_apply]
  rfl

/-- First sample the policy action, then its Bernoulli feedback statistic. -/
def pairedLatentRoundKernel {n k : Nat} (P : Policy n k) (hk : 1 ≤ k)
    (hD : 2 * k ≤ n) (θ : Fin k → PairSign) (ε : Real) (t : Nat) :
    Kernel (History n k t) (MSetAction n k × Bool) :=
  P.kernel t ⊗ₖ pairedHistoryActionBoolKernel hk hD θ ε t

theorem pairedLatentRoundKernel_isMarkov {n k : Nat}
    (P : Policy n k) (hk : 1 ≤ k) (hD : 2 * k ≤ n)
    (θ : Fin k → PairSign) (ε : Real) (hε0 : 0 ≤ ε) (hε1 : ε ≤ 1)
    (t : Nat) : IsMarkovKernel (pairedLatentRoundKernel P hk hD θ ε t) := by
  unfold pairedLatentRoundKernel
  letI : IsMarkovKernel (pairedHistoryActionBoolKernel hk hD θ ε t) :=
    pairedHistoryActionBoolKernel_isMarkov hk hD θ ε hε0 hε1 t
  infer_instance

/-- Observable round kernel: the Boolean statistic is mapped to the exact
scalar feedback from the manuscript's action-loss identity. -/
def pairedAdaptiveRoundKernel {n k : Nat} (P : Policy n k) (hk : 1 ≤ k)
    (hD : 2 * k ≤ n) (θ : Fin k → PairSign) (ε : Real) (t : Nat) :
    Kernel (History n k t) (MSetAction n k × Real) :=
  (pairedLatentRoundKernel P hk hD θ ε t).map
    (encodePairedActionFeedback hD)

theorem pairedAdaptiveRoundKernel_isMarkov {n k : Nat}
    (P : Policy n k) (hk : 1 ≤ k) (hD : 2 * k ≤ n)
    (θ : Fin k → PairSign) (ε : Real) (hε0 : 0 ≤ ε) (hε1 : ε ≤ 1)
    (t : Nat) : IsMarkovKernel (pairedAdaptiveRoundKernel P hk hD θ ε t) := by
  unfold pairedAdaptiveRoundKernel
  letI : IsMarkovKernel (pairedLatentRoundKernel P hk hD θ ε t) :=
    pairedLatentRoundKernel_isMarkov P hk hD θ ε hε0 hε1 t
  exact Kernel.IsMarkovKernel.map _
    (measurable_encodePairedActionFeedback hD)

/-- The adaptive stochastic process `P_θ` on the recursive protocol history. -/
def pairedAdaptiveProcess {n k : Nat} (P : Policy n k) (hk : 1 ≤ k)
    (hD : 2 * k ≤ n) (θ : Fin k → PairSign) (ε : Real)
    (hε0 : 0 ≤ ε) (hε1 : ε ≤ 1) : HistoryKernelProcess n k where
  kernel t := pairedAdaptiveRoundKernel P hk hD θ ε t
  isMarkov t :=
    pairedAdaptiveRoundKernel_isMarkov P hk hD θ ε hε0 hε1 t

/-- Literal conditional-feedback identification before the lossless
Boolean-to-real encoding. -/
theorem pairedAdaptive_conditional_bool_feedback {n k : Nat}
    (P : Policy n k) (hk : 1 ≤ k) (hD : 2 * k ≤ n)
    (θ : Fin k → PairSign) (ε : Real) (t : Nat)
    (h : History n k t) (A : MSetAction n k) :
    pairedHistoryActionBoolKernel hk hD θ ε t (h, A) =
      bernoulliLaw (pairedBernoulliParameter hD θ ε A) :=
  pairedHistoryActionBoolKernel_apply hk hD θ ε t h A

/-! ## Adjacent-hypothesis likelihood ratio -/

/-- Likelihood ratio of the feedback law under `θ` relative to `θ^(g)`.
When the chosen action sees no paired coordinate, both laws are `Ber(0)` and
the correct ratio on their common support is one. -/
def pairedBoolLikelihoodRatio {n k : Nat} (hD : 2 * k ≤ n)
    (θ : Fin k → PairSign) (ε : Real) (g : Fin k)
    (A : MSetAction n k) (b : Bool) : ℝ≥0∞ :=
  if pairedSectionCard hD A = 0 then 1
  else bernoulliDensityRatio
    (pairedBernoulliParameter hD θ ε A)
    (pairedBernoulliParameter hD (flipHypothesis θ g) ε A) b

theorem measurable_uncurry_pairedBoolLikelihoodRatio {n k : Nat}
    (hD : 2 * k ≤ n) (θ : Fin k → PairSign) (ε : Real) (g : Fin k) :
    Measurable (Function.uncurry (pairedBoolLikelihoodRatio hD θ ε g)) :=
  measurable_of_finite _

/-- Pointwise reweighting identity for the adjacent Bernoulli feedback
laws, including the degenerate `h=0` case. -/
theorem bernoulliLaw_parameter_eq_withDensity_flip {n k : Nat}
    (hk : 1 ≤ k) (hD : 2 * k ≤ n) (θ : Fin k → PairSign)
    {ε : Real} (hε0 : 0 ≤ ε) (hε16 : ε ≤ (1 : Real) / 16)
    (A : MSetAction n k) (g : Fin k) :
    bernoulliLaw (pairedBernoulliParameter hD θ ε A) =
      (bernoulliLaw
        (pairedBernoulliParameter hD (flipHypothesis θ g) ε A)).withDensity
          (pairedBoolLikelihoodRatio hD θ ε g A) := by
  have hε1 : ε ≤ 1 := hε16.trans (by norm_num)
  by_cases hh0 : pairedSectionCard hD A = 0
  · have ha := pairedBernoulliParameter_eq_zero_of_card_eq_zero
      hk hD θ hε0 hε1 A hh0
    have hb := pairedBernoulliParameter_eq_zero_of_card_eq_zero
      hk hD (flipHypothesis θ g) hε0 hε1 A hh0
    rw [ha, hb]
    have hr : pairedBoolLikelihoodRatio hD θ ε g A = 1 := by
      funext b
      simp [pairedBoolLikelihoodRatio, hh0]
    rw [hr, withDensity_one]
  · have hh : 0 < pairedSectionCard hD A := Nat.pos_of_ne_zero hh0
    have hhR : 0 < (pairedSectionCard hD A : Real) := by exact_mod_cast hh
    have hkR : 0 < (k : Real) := by exact_mod_cast hk
    have hb_bounds := pairedBernoulliParameter_denominator_bounds
      hk hD (flipHypothesis θ g) hε0 hε16 A
    have hb0 :
        0 < pairedBernoulliParameter hD (flipHypothesis θ g) ε A := by
      have : 0 < 3 * (pairedSectionCard hD A : Real) /
          (8 * (k : Real)) := by positivity
      exact this.trans_le hb_bounds.1
    have hb1 :
        pairedBernoulliParameter hD (flipHypothesis θ g) ε A < 1 := by
      linarith [hb_bounds.2]
    have hr : pairedBoolLikelihoodRatio hD θ ε g A =
        bernoulliDensityRatio
          (pairedBernoulliParameter hD θ ε A)
          (pairedBernoulliParameter hD (flipHypothesis θ g) ε A) := by
      funext b
      simp [pairedBoolLikelihoodRatio, hh0]
    rw [hr]
    exact bernoulliLaw_withDensity_ratio hb0 hb1

/-- A pointwise conditional reweighting identity lifts through a
composition-product.  This specialized lemma avoids any hidden assumption
about measurability of conditional KL. -/
theorem compProd_eq_withDensity_of_apply
    {α β : Type*} [MeasurableSpace α] [MeasurableSpace β]
    (μ : Measure α) (κ η : Kernel α β) [SFinite μ]
    [IsSFiniteKernel κ] [IsSFiniteKernel η]
    (f : α → β → ℝ≥0∞) (hf : Measurable (Function.uncurry f))
    (happly : ∀ a, κ a = (η a).withDensity (f a)) :
    μ ⊗ₘ κ = (μ ⊗ₘ η).withDensity (Function.uncurry f) := by
  ext s hs
  rw [Measure.compProd_apply hs, withDensity_apply _ hs,
    ← lintegral_indicator hs, Measure.lintegral_compProd]
  · apply lintegral_congr
    intro a
    rw [happly a, withDensity_apply _ (measurable_prodMk_left hs),
      ← lintegral_indicator (measurable_prodMk_left hs)]
    rfl
  · exact hf.indicator hs

/-! ## One adaptive round -/

/-- Removing the lossless Boolean-to-real encoding leaves the latent
action--Boolean law without changing the one-round KL divergence. -/
theorem pairedAdaptive_roundKL_eq_latent {n k : Nat}
    (P : Policy n k) (hk : 1 ≤ k) (hD : 2 * k ≤ n)
    (θ : Fin k → PairSign) {ε : Real} (hε0 : 0 ≤ ε)
    (hε16 : ε ≤ (1 : Real) / 16) (g : Fin k) (t : Nat) :
    (pairedAdaptiveProcess P hk hD θ ε hε0
        (hε16.trans (by norm_num))).roundKL
      (pairedAdaptiveProcess P hk hD (flipHypothesis θ g) ε hε0
        (hε16.trans (by norm_num))) t =
      klDiv
        ((pairedAdaptiveProcess P hk hD θ ε hε0
            (hε16.trans (by norm_num))).law t ⊗ₘ
          pairedLatentRoundKernel P hk hD θ ε t)
        ((pairedAdaptiveProcess P hk hD θ ε hε0
            (hε16.trans (by norm_num))).law t ⊗ₘ
          pairedLatentRoundKernel P hk hD (flipHypothesis θ g) ε t) := by
  letI : IsMarkovKernel (pairedLatentRoundKernel P hk hD θ ε t) :=
    pairedLatentRoundKernel_isMarkov P hk hD θ ε hε0
      (hε16.trans (by norm_num)) t
  letI : IsMarkovKernel
      (pairedLatentRoundKernel P hk hD (flipHypothesis θ g) ε t) :=
    pairedLatentRoundKernel_isMarkov P hk hD (flipHypothesis θ g) ε hε0
      (hε16.trans (by norm_num)) t
  unfold HistoryKernelProcess.roundKL
  change klDiv
      ((pairedAdaptiveProcess P hk hD θ ε hε0
          (hε16.trans (by norm_num))).law t ⊗ₘ
        pairedAdaptiveRoundKernel P hk hD θ ε t)
      ((pairedAdaptiveProcess P hk hD θ ε hε0
          (hε16.trans (by norm_num))).law t ⊗ₘ
        pairedAdaptiveRoundKernel P hk hD (flipHypothesis θ g) ε t) = _
  rw [pairedAdaptiveRoundKernel, pairedAdaptiveRoundKernel,
    Measure.compProd_map (measurable_encodePairedActionFeedback hD),
    Measure.compProd_map (measurable_encodePairedActionFeedback hD)]
  exact klDiv_map_measurableEmbedding
    (MeasurableEmbedding.id.prodMap
      (measurableEmbedding_encodePairedActionFeedback hD)) _ _

/-- Reassociate the latent round into the common history--action law followed
by the environment-dependent Boolean feedback kernel. -/
theorem pairedAdaptive_roundKL_eq_twoStage {n k : Nat}
    (P : Policy n k) (hk : 1 ≤ k) (hD : 2 * k ≤ n)
    (θ : Fin k → PairSign) {ε : Real} (hε0 : 0 ≤ ε)
    (hε16 : ε ≤ (1 : Real) / 16) (g : Fin k) (t : Nat) :
    (pairedAdaptiveProcess P hk hD θ ε hε0
        (hε16.trans (by norm_num))).roundKL
      (pairedAdaptiveProcess P hk hD (flipHypothesis θ g) ε hε0
        (hε16.trans (by norm_num))) t =
      klDiv
        (((pairedAdaptiveProcess P hk hD θ ε hε0
            (hε16.trans (by norm_num))).law t ⊗ₘ P.kernel t) ⊗ₘ
          pairedHistoryActionBoolKernel hk hD θ ε t)
        (((pairedAdaptiveProcess P hk hD θ ε hε0
            (hε16.trans (by norm_num))).law t ⊗ₘ P.kernel t) ⊗ₘ
          pairedHistoryActionBoolKernel hk hD (flipHypothesis θ g) ε t) := by
  letI : IsMarkovKernel
      (pairedHistoryActionBoolKernel hk hD θ ε t) :=
    pairedHistoryActionBoolKernel_isMarkov hk hD θ ε hε0
      (hε16.trans (by norm_num)) t
  letI : IsMarkovKernel
      (pairedHistoryActionBoolKernel hk hD (flipHypothesis θ g) ε t) :=
    pairedHistoryActionBoolKernel_isMarkov hk hD (flipHypothesis θ g) ε hε0
      (hε16.trans (by norm_num)) t
  letI : IsMarkovKernel (pairedLatentRoundKernel P hk hD θ ε t) :=
    pairedLatentRoundKernel_isMarkov P hk hD θ ε hε0
      (hε16.trans (by norm_num)) t
  letI : IsMarkovKernel
      (pairedLatentRoundKernel P hk hD (flipHypothesis θ g) ε t) :=
    pairedLatentRoundKernel_isMarkov P hk hD (flipHypothesis θ g) ε hε0
      (hε16.trans (by norm_num)) t
  rw [pairedAdaptive_roundKL_eq_latent P hk hD θ hε0 hε16 g t]
  unfold pairedLatentRoundKernel
  rw [← klDiv_map_measurableEmbedding
    MeasurableEquiv.prodAssoc.symm.measurableEmbedding]
  simp only [Measure.compProd_assoc]

/-- The adjacent two-stage law is obtained by reweighting only the final
Boolean feedback coordinate. -/
theorem pairedTwoStage_eq_withDensity {n k t : Nat}
    (μ : Measure (History n k t × MSetAction n k)) [SFinite μ]
    (hk : 1 ≤ k) (hD : 2 * k ≤ n) (θ : Fin k → PairSign)
    {ε : Real} (hε0 : 0 ≤ ε) (hε16 : ε ≤ (1 : Real) / 16)
    (g : Fin k) :
    μ ⊗ₘ pairedHistoryActionBoolKernel hk hD θ ε t =
      (μ ⊗ₘ pairedHistoryActionBoolKernel hk hD
        (flipHypothesis θ g) ε t).withDensity
        (fun x => pairedBoolLikelihoodRatio hD θ ε g x.1.2 x.2) := by
  letI : IsMarkovKernel
      (pairedHistoryActionBoolKernel hk hD θ ε t) :=
    pairedHistoryActionBoolKernel_isMarkov hk hD θ ε hε0
      (hε16.trans (by norm_num)) t
  letI : IsMarkovKernel
      (pairedHistoryActionBoolKernel hk hD (flipHypothesis θ g) ε t) :=
    pairedHistoryActionBoolKernel_isMarkov hk hD (flipHypothesis θ g) ε hε0
      (hε16.trans (by norm_num)) t
  apply compProd_eq_withDensity_of_apply μ _ _
      (fun ha b => pairedBoolLikelihoodRatio hD θ ε g ha.2 b)
  · exact (measurable_uncurry_pairedBoolLikelihoodRatio hD θ ε g).comp
      (measurable_fst.snd.prodMk measurable_snd)
  · intro ha
    rw [pairedHistoryActionBoolKernel_apply,
      pairedHistoryActionBoolKernel_apply]
    exact bernoulliLaw_parameter_eq_withDensity_flip
      hk hD θ hε0 hε16 ha.2 g

/-- KL against a finite base measure, when the first measure is presented
by an explicit measurable density. -/
theorem klDiv_withDensity_eq_lintegral_klFun
    {α : Type*} [MeasurableSpace α] (ν : Measure α) [IsFiniteMeasure ν]
    (f : α → ℝ≥0∞) (hf : Measurable f) [IsFiniteMeasure (ν.withDensity f)] :
    klDiv (ν.withDensity f) ν =
      ∫⁻ x, ENNReal.ofReal (klFun (f x).toReal) ∂ν := by
  rw [klDiv_eq_lintegral_klFun_of_ac
    (MeasureTheory.withDensity_absolutelyContinuous ν f)]
  apply lintegral_congr_ae
  filter_upwards [Measure.rnDeriv_withDensity ν hf] with x hx
  rw [hx]

/-- The Boolean likelihood-ratio integrand is exactly the adjacent
Bernoulli KL, including the common degenerate law when no paired coordinate
is selected. -/
theorem lintegral_pairedBoolLikelihoodRatio_eq_klDiv {n k : Nat}
    (hk : 1 ≤ k) (hD : 2 * k ≤ n) (θ : Fin k → PairSign)
    {ε : Real} (hε0 : 0 ≤ ε) (hε16 : ε ≤ (1 : Real) / 16)
    (A : MSetAction n k) (g : Fin k) :
    (∫⁻ b, ENNReal.ofReal
        (klFun ((pairedBoolLikelihoodRatio hD θ ε g A b).toReal))
      ∂bernoulliLaw
        (pairedBernoulliParameter hD (flipHypothesis θ g) ε A)) =
      klDiv
        (bernoulliLaw (pairedBernoulliParameter hD θ ε A))
        (bernoulliLaw
          (pairedBernoulliParameter hD (flipHypothesis θ g) ε A)) := by
  have hε1 : ε ≤ 1 := hε16.trans (by norm_num)
  letI : IsProbabilityMeasure
      (bernoulliLaw (pairedBernoulliParameter hD θ ε A)) :=
    ⟨bernoulliLaw_apply_univ
      (pairedBernoulliParameter_mem_Icc hk hD θ hε0 hε1 A).1
      (pairedBernoulliParameter_mem_Icc hk hD θ hε0 hε1 A).2⟩
  letI : IsProbabilityMeasure
      (bernoulliLaw
        (pairedBernoulliParameter hD (flipHypothesis θ g) ε A)) :=
    ⟨bernoulliLaw_apply_univ
      (pairedBernoulliParameter_mem_Icc hk hD (flipHypothesis θ g)
        hε0 hε1 A).1
      (pairedBernoulliParameter_mem_Icc hk hD (flipHypothesis θ g)
        hε0 hε1 A).2⟩
  letI : IsFiniteMeasure
      ((bernoulliLaw
          (pairedBernoulliParameter hD (flipHypothesis θ g) ε A)).withDensity
        (pairedBoolLikelihoodRatio hD θ ε g A)) := by
    rw [← bernoulliLaw_parameter_eq_withDensity_flip
      hk hD θ hε0 hε16 A g]
    infer_instance
  symm
  rw [bernoulliLaw_parameter_eq_withDensity_flip
    hk hD θ hε0 hε16 A g]
  exact klDiv_withDensity_eq_lintegral_klFun _ _
    (measurable_of_finite _)

/-- Exact conditional-KL formula for a common arbitrary history--action
law followed by the two adjacent Bernoulli feedback kernels. -/
theorem klDiv_pairedTwoStage_eq_lintegral {n k t : Nat}
    (μ : Measure (History n k t × MSetAction n k)) [IsProbabilityMeasure μ]
    (hk : 1 ≤ k) (hD : 2 * k ≤ n) (θ : Fin k → PairSign)
    {ε : Real} (hε0 : 0 ≤ ε) (hε16 : ε ≤ (1 : Real) / 16)
    (g : Fin k) :
    klDiv
        (μ ⊗ₘ pairedHistoryActionBoolKernel hk hD θ ε t)
        (μ ⊗ₘ pairedHistoryActionBoolKernel hk hD
          (flipHypothesis θ g) ε t) =
      ∫⁻ ha,
        klDiv
          (bernoulliLaw (pairedBernoulliParameter hD θ ε ha.2))
          (bernoulliLaw
            (pairedBernoulliParameter hD (flipHypothesis θ g) ε ha.2)) ∂μ := by
  letI : IsMarkovKernel
      (pairedHistoryActionBoolKernel hk hD θ ε t) :=
    pairedHistoryActionBoolKernel_isMarkov hk hD θ ε hε0
      (hε16.trans (by norm_num)) t
  letI : IsMarkovKernel
      (pairedHistoryActionBoolKernel hk hD (flipHypothesis θ g) ε t) :=
    pairedHistoryActionBoolKernel_isMarkov hk hD (flipHypothesis θ g) ε hε0
      (hε16.trans (by norm_num)) t
  let ratio : (History n k t × MSetAction n k) × Bool → ℝ≥0∞ :=
    fun x => pairedBoolLikelihoodRatio hD θ ε g x.1.2 x.2
  have hratio : Measurable ratio :=
    (measurable_uncurry_pairedBoolLikelihoodRatio hD θ ε g).comp
      (measurable_fst.snd.prodMk measurable_snd)
  have hden := pairedTwoStage_eq_withDensity
    μ hk hD θ hε0 hε16 g
  letI : IsFiniteMeasure
      ((μ ⊗ₘ pairedHistoryActionBoolKernel hk hD
          (flipHypothesis θ g) ε t).withDensity ratio) := by
    rw [← hden]
    infer_instance
  calc
    klDiv
        (μ ⊗ₘ pairedHistoryActionBoolKernel hk hD θ ε t)
        (μ ⊗ₘ pairedHistoryActionBoolKernel hk hD
          (flipHypothesis θ g) ε t) =
        klDiv
          ((μ ⊗ₘ pairedHistoryActionBoolKernel hk hD
            (flipHypothesis θ g) ε t).withDensity ratio)
          (μ ⊗ₘ pairedHistoryActionBoolKernel hk hD
            (flipHypothesis θ g) ε t) := by rw [hden]
    _ = ∫⁻ x, ENNReal.ofReal (klFun (ratio x).toReal)
          ∂(μ ⊗ₘ pairedHistoryActionBoolKernel hk hD
            (flipHypothesis θ g) ε t) :=
      klDiv_withDensity_eq_lintegral_klFun _ ratio hratio
    _ = ∫⁻ ha, ∫⁻ b,
          ENNReal.ofReal
            (klFun ((pairedBoolLikelihoodRatio hD θ ε g ha.2 b).toReal))
          ∂pairedHistoryActionBoolKernel hk hD
            (flipHypothesis θ g) ε t ha ∂μ := by
      rw [Measure.lintegral_compProd (by fun_prop)]
    _ = ∫⁻ ha,
          klDiv
            (bernoulliLaw (pairedBernoulliParameter hD θ ε ha.2))
            (bernoulliLaw
              (pairedBernoulliParameter hD (flipHypothesis θ g) ε ha.2)) ∂μ := by
      apply lintegral_congr
      intro ha
      rw [pairedHistoryActionBoolKernel_apply]
      exact lintegral_pairedBoolLikelihoodRatio_eq_klDiv
        hk hD θ hε0 hε16 ha.2 g

/-- Exact one-round information identity for the adaptive process.  The
outer measure is the actual prefix law under `θ`, followed by the arbitrary
history-measurable policy's action kernel. -/
theorem pairedAdaptive_roundKL_eq_lintegral {n k : Nat}
    (P : Policy n k) (hk : 1 ≤ k) (hD : 2 * k ≤ n)
    (θ : Fin k → PairSign) {ε : Real} (hε0 : 0 ≤ ε)
    (hε16 : ε ≤ (1 : Real) / 16) (g : Fin k) (t : Nat) :
    (pairedAdaptiveProcess P hk hD θ ε hε0
        (hε16.trans (by norm_num))).roundKL
      (pairedAdaptiveProcess P hk hD (flipHypothesis θ g) ε hε0
        (hε16.trans (by norm_num))) t =
      ∫⁻ ha,
        klDiv
          (bernoulliLaw (pairedBernoulliParameter hD θ ε ha.2))
          (bernoulliLaw
            (pairedBernoulliParameter hD (flipHypothesis θ g) ε ha.2))
        ∂((pairedAdaptiveProcess P hk hD θ ε hε0
            (hε16.trans (by norm_num))).law t ⊗ₘ P.kernel t) := by
  rw [pairedAdaptive_roundKL_eq_twoStage P hk hD θ hε0 hε16 g t]
  exact klDiv_pairedTwoStage_eq_lintegral _ hk hD θ hε0 hε16 g

/-- Adjacent Bernoulli KL as a function of the chosen action. -/
def pairedAdjacentActionKL {n k : Nat} (hD : 2 * k ≤ n)
    (θ : Fin k → PairSign) (ε : Real) (g : Fin k)
    (A : MSetAction n k) : ℝ≥0∞ :=
  klDiv
    (bernoulliLaw (pairedBernoulliParameter hD θ ε A))
    (bernoulliLaw
      (pairedBernoulliParameter hD (flipHypothesis θ g) ε A))

theorem measurable_pairedAdjacentActionKL {n k : Nat} (hD : 2 * k ≤ n)
    (θ : Fin k → PairSign) (ε : Real) (g : Fin k) :
    Measurable (pairedAdjacentActionKL hD θ ε g) :=
  measurable_of_finite _

/-- The sum over all adjacent hypotheses of the adaptive one-round KL costs
obeys exactly the manuscript's one-step information budget, independently
of the randomized history-measurable policy. -/
theorem sum_pairedAdaptive_roundKL_le {n k : Nat}
    (P : Policy n k) (hk : 1 ≤ k) (hD : 2 * k ≤ n)
    (θ : Fin k → PairSign) {ε : Real} (hε0 : 0 ≤ ε)
    (hε16 : ε ≤ (1 : Real) / 16) (t : Nat) :
    (∑ g : Fin k,
      (pairedAdaptiveProcess P hk hD θ ε hε0
          (hε16.trans (by norm_num))).roundKL
        (pairedAdaptiveProcess P hk hD (flipHypothesis θ g) ε hε0
          (hε16.trans (by norm_num))) t) ≤
      ENNReal.ofReal (16 * ε ^ 2 / (2 * (k : Real))) := by
  let μ : Measure (History n k t × MSetAction n k) :=
    (pairedAdaptiveProcess P hk hD θ ε hε0
      (hε16.trans (by norm_num))).law t ⊗ₘ P.kernel t
  letI : IsProbabilityMeasure μ := by
    dsimp [μ]
    infer_instance
  calc
    (∑ g : Fin k,
      (pairedAdaptiveProcess P hk hD θ ε hε0
          (hε16.trans (by norm_num))).roundKL
        (pairedAdaptiveProcess P hk hD (flipHypothesis θ g) ε hε0
          (hε16.trans (by norm_num))) t) =
        ∑ g : Fin k, ∫⁻ ha, pairedAdjacentActionKL hD θ ε g ha.2 ∂μ := by
      apply Finset.sum_congr rfl
      intro g _
      exact pairedAdaptive_roundKL_eq_lintegral
        P hk hD θ hε0 hε16 g t
    _ = ∫⁻ ha, ∑ g : Fin k, pairedAdjacentActionKL hD θ ε g ha.2 ∂μ := by
      symm
      exact MeasureTheory.lintegral_finsetSum Finset.univ fun g _ =>
        (measurable_pairedAdjacentActionKL hD θ ε g).comp measurable_snd
    _ ≤ ∫⁻ _ha, ENNReal.ofReal (16 * ε ^ 2 / (2 * (k : Real))) ∂μ := by
      apply lintegral_mono
      intro ha
      exact lower_dense_one_step_measure_kl_ennreal
        hk hD θ hε0 hε16 ha.2
    _ = ENNReal.ofReal (16 * ε ^ 2 / (2 * (k : Real))) := by simp

/-! ## Sequential information budget -/

/-- `eq:paired-sequential-kl`: after `T` adaptive rounds, the sum of KL
divergences from `θ` to all one-coordinate flips is at most `T` times the
exact dense one-step budget.  The policy is arbitrary and may randomize as
a measurable function of the complete observable history. -/
theorem paired_sequential_kl_ennreal {n k : Nat}
    (P : Policy n k) (hk : 1 ≤ k) (hD : 2 * k ≤ n)
    (θ : Fin k → PairSign) {ε : Real} (hε0 : 0 ≤ ε)
    (hε16 : ε ≤ (1 : Real) / 16) (T : Nat) :
    (∑ g : Fin k,
      klDiv
        ((pairedAdaptiveProcess P hk hD θ ε hε0
          (hε16.trans (by norm_num))).law T)
        ((pairedAdaptiveProcess P hk hD (flipHypothesis θ g) ε hε0
          (hε16.trans (by norm_num))).law T)) ≤
      T * ENNReal.ofReal (16 * ε ^ 2 / (2 * (k : Real))) := by
  calc
    (∑ g : Fin k,
      klDiv
        ((pairedAdaptiveProcess P hk hD θ ε hε0
          (hε16.trans (by norm_num))).law T)
        ((pairedAdaptiveProcess P hk hD (flipHypothesis θ g) ε hε0
          (hε16.trans (by norm_num))).law T)) =
        ∑ g : Fin k, ∑ t ∈ Finset.range T,
          (pairedAdaptiveProcess P hk hD θ ε hε0
            (hε16.trans (by norm_num))).roundKL
          (pairedAdaptiveProcess P hk hD (flipHypothesis θ g) ε hε0
            (hε16.trans (by norm_num))) t := by
      apply Finset.sum_congr rfl
      intro g _
      exact (pairedAdaptiveProcess P hk hD θ ε hε0
        (hε16.trans (by norm_num))).klDiv_law_eq_sum_roundKL
          (pairedAdaptiveProcess P hk hD (flipHypothesis θ g) ε hε0
            (hε16.trans (by norm_num))) T
    _ = ∑ t ∈ Finset.range T, ∑ g : Fin k,
          (pairedAdaptiveProcess P hk hD θ ε hε0
            (hε16.trans (by norm_num))).roundKL
          (pairedAdaptiveProcess P hk hD (flipHypothesis θ g) ε hε0
            (hε16.trans (by norm_num))) t := by
      rw [Finset.sum_comm]
    _ ≤ ∑ _t ∈ Finset.range T,
          ENNReal.ofReal (16 * ε ^ 2 / (2 * (k : Real))) := by
      exact Finset.sum_le_sum fun t _ =>
        sum_pairedAdaptive_roundKL_le P hk hD θ hε0 hε16 t
    _ = T * ENNReal.ofReal (16 * ε ^ 2 / (2 * (k : Real))) := by simp

/-- The same theorem with the paper's displayed right-hand side
`16 ε² T / D`, specialized to `D = 2k`. -/
theorem paired_sequential_kl {n k : Nat}
    (P : Policy n k) (hk : 1 ≤ k) (hD : 2 * k ≤ n)
    (θ : Fin k → PairSign) {ε : Real} (hε0 : 0 ≤ ε)
    (hε16 : ε ≤ (1 : Real) / 16) (T : Nat) :
    (∑ g : Fin k,
      klDiv
        ((pairedAdaptiveProcess P hk hD θ ε hε0
          (hε16.trans (by norm_num))).law T)
        ((pairedAdaptiveProcess P hk hD (flipHypothesis θ g) ε hε0
          (hε16.trans (by norm_num))).law T)) ≤
      ENNReal.ofReal
        (16 * ε ^ 2 * (T : Real) / (2 * (k : Real))) := by
  calc
    (∑ g : Fin k,
      klDiv
        ((pairedAdaptiveProcess P hk hD θ ε hε0
          (hε16.trans (by norm_num))).law T)
        ((pairedAdaptiveProcess P hk hD (flipHypothesis θ g) ε hε0
          (hε16.trans (by norm_num))).law T)) ≤
        T * ENNReal.ofReal (16 * ε ^ 2 / (2 * (k : Real))) :=
      paired_sequential_kl_ennreal P hk hD θ hε0 hε16 T
    _ = ENNReal.ofReal
        ((T : Real) * (16 * ε ^ 2 / (2 * (k : Real)))) := by
      rw [← ENNReal.ofReal_natCast T,
        ← ENNReal.ofReal_mul (Nat.cast_nonneg T)]
    _ = ENNReal.ofReal
        (16 * ε ^ 2 * (T : Real) / (2 * (k : Real))) := by
      congr 1
      ring

#print axioms bernoulliLaw_parameter_eq_withDensity_flip
#print axioms compProd_eq_withDensity_of_apply

#print axioms klDiv_map_measurableEmbedding
#print axioms pairedScalarFeedback_selected_eq_actionLoss
#print axioms pairedAdaptiveProcess
#print axioms pairedAdaptive_conditional_bool_feedback
#print axioms pairedAdaptive_roundKL_eq_lintegral
#print axioms sum_pairedAdaptive_roundKL_le
#print axioms paired_sequential_kl

end


end MsetsLower.Lower.Dense
