import MsetsLower.Lower.Dense.OneStepKL
import MsetsLower.Probability.ChangedLawMaximum
import Mathlib.InformationTheory.KullbackLeibler.Basic
import Mathlib.Algebra.Order.Chebyshev

/-!
# Assouad's hypercube argument for the dense lower bound

This file formalizes the random-round/estimation block at manuscript lines
5216--5303.  The laws are abstract probability measures indexed by the paired
hypercube; consequently the results can be instantiated by the adaptive laws
without making this file depend on their construction.

The project's total-variation convention is
`TV(μ,ν) = (1/2) |μ-ν|(univ)`.  In particular the event bound below has no
additional factor two.
-/

namespace MsetsLower.Lower.Dense

open MsetsLower
open MsetsLower.Probability
open MeasureTheory ProbabilityTheory InformationTheory
open scoped BigOperators ENNReal NNReal

noncomputable section

/-! ## Event errors and the probability-theory normalization of TV -/

/-- The real-valued probability of an event. -/
def eventProbability {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) (B : Set Ω) : Real :=
  μ.real B

/-- A centered indicator proves the sharp event consequence of the project's
Jordan-normalized total variation: `|μ(B)-ν(B)| ≤ TV(μ,ν)`. -/
theorem abs_eventProbability_sub_le_totalVariationDistance
    {Ω : Type*} [MeasurableSpace Ω]
    (μ ν : Measure Ω) [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    {B : Set Ω} (hB : MeasurableSet B) :
    |eventProbability μ B - eventProbability ν B| ≤
      totalVariationDistance μ ν := by
  let f : Ω → Real :=
    fun ω => B.indicator (fun _ => (1 : Real)) ω - 1 / 2
  have hf : Measurable f :=
    (measurable_const.indicator hB).sub measurable_const
  have hbound : ∀ ω, |f ω| ≤ (1 : Real) / 2 := by
    intro ω
    by_cases hω : ω ∈ B <;>
      simp [f, Set.indicator, hω] <;> norm_num
  have hμint : ∫ ω, f ω ∂μ = eventProbability μ B - 1 / 2 := by
    rw [show f = fun ω => B.indicator (fun _ => (1 : Real)) ω - 1 / 2 by rfl,
      integral_sub]
    · rw [integral_indicator_const (1 : Real) hB, integral_const]
      simp [eventProbability]
    · exact Integrable.indicator (integrable_const _) hB
    · exact integrable_const _
  have hνint : ∫ ω, f ω ∂ν = eventProbability ν B - 1 / 2 := by
    rw [show f = fun ω => B.indicator (fun _ => (1 : Real)) ω - 1 / 2 by rfl,
      integral_sub]
    · rw [integral_indicator_const (1 : Real) hB, integral_const]
      simp [eventProbability]
    · exact Integrable.indicator (integrable_const _) hB
    · exact integrable_const _
  have h :=
    abs_integral_sub_integral_le_two_mul_totalVariationDistance
      μ ν hf hbound
  rw [hμint, hνint] at h
  norm_num at h ⊢
  simpa only [sub_sub_sub_cancel_right] using h

/-- The binary testing inequality used for every adjacent pair in Assouad's
argument.  If `B` denotes the decision "the first hypothesis is true", the
sum of the two error probabilities is at least `1-TV`. -/
theorem decision_error_pair_ge_one_sub_totalVariationDistance
    {Ω : Type*} [MeasurableSpace Ω]
    (μ ν : Measure Ω) [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    {B : Set Ω} (hB : MeasurableSet B) :
    eventProbability μ Bᶜ + eventProbability ν B ≥
      1 - totalVariationDistance μ ν := by
  have htv := abs_eventProbability_sub_le_totalVariationDistance μ ν hB
  have hdiff : eventProbability μ B - eventProbability ν B ≤
      totalVariationDistance μ ν :=
    (le_abs_self _).trans htv
  simp only [eventProbability, probReal_compl_eq_one_sub hB]
  dsimp [eventProbability] at hdiff
  linarith

/-! ## The paired hypercube and coordinate risks -/

/-- Flipping the same coordinate twice recovers the original hypothesis. -/
@[simp] theorem PairSign.flip_flip (s : PairSign) : s.flip.flip = s := by
  cases s <;> rfl

@[simp] theorem flipHypothesis_flipHypothesis {k : Nat}
    (θ : Fin k → PairSign) (g : Fin k) :
    flipHypothesis (flipHypothesis θ g) g = θ := by
  funext i
  by_cases hi : i = g
  · subst i
    simp [flipHypothesis]
  · simp [flipHypothesis, hi]

/-- Coordinate flip as an equivalence of the hypothesis hypercube. -/
def flipHypothesisEquiv {k : Nat} (g : Fin k) :
    (Fin k → PairSign) ≃ (Fin k → PairSign) where
  toFun θ := flipHypothesis θ g
  invFun θ := flipHypothesis θ g
  left_inv θ := flipHypothesis_flipHypothesis θ g
  right_inv θ := flipHypothesis_flipHypothesis θ g

/-- The event that the estimator makes an error in coordinate `g`. -/
def coordinateErrorEvent {Ω : Type*} {k : Nat}
    (estimate : Ω → Fin k → PairSign)
    (θ : Fin k → PairSign) (g : Fin k) : Set Ω :=
  {ω | estimate ω g ≠ θ g}

/-- Coordinate error probability under the law indexed by `θ`. -/
def coordinateErrorProbability {Ω : Type*} [MeasurableSpace Ω] {k : Nat}
    (P : (Fin k → PairSign) → Measure Ω)
    (estimate : Ω → Fin k → PairSign)
    (θ : Fin k → PairSign) (g : Fin k) : Real :=
  eventProbability (P θ) (coordinateErrorEvent estimate θ g)

/-- Expected Hamming loss, written as the sum of its coordinate error
probabilities. -/
def expectedHammingLoss {Ω : Type*} [MeasurableSpace Ω] {k : Nat}
    (P : (Fin k → PairSign) → Measure Ω)
    (estimate : Ω → Fin k → PairSign)
    (θ : Fin k → PairSign) : Real :=
  ∑ g : Fin k, coordinateErrorProbability P estimate θ g

/-! ### The manuscript's random-round/Rademacher estimator -/

/-- The contribution `1 - θ_g z_g(A)` of one pair to the mean-comparator
gap. -/
def pairedCoordinateDisagreement {n k : Nat} (hD : 2 * k ≤ n)
    (θ : Fin k → PairSign) (A : MSetAction n k) (g : Fin k) : Real :=
  1 - PairSign.value (θ g) * pairedZ hD A g

/-- The estimator of `θ_g` from one sampled action.  A uniquely selected
left (respectively right) item produces `+1` (respectively `-1`); a tie uses
the independent Rademacher fallback. -/
def pairedCoordinateEstimate {n k : Nat} (hD : 2 * k ≤ n)
    (A : MSetAction n k) (fallback : PairSign) (g : Fin k) : PairSign :=
  if pairCoordinate hD (g, false) ∈ A.1 then
    if pairCoordinate hD (g, true) ∈ A.1 then fallback else PairSign.pos
  else
    if pairCoordinate hD (g, true) ∈ A.1 then PairSign.neg else fallback

/-- Error probability after averaging the one relevant fallback sign over
its two equiprobable values. -/
def fairCoordinateError {n k : Nat} (hD : 2 * k ≤ n)
    (θ : Fin k → PairSign) (A : MSetAction n k) (g : Fin k) : Real :=
  ((if pairedCoordinateEstimate hD A PairSign.neg g ≠ θ g then 1 else 0) +
    (if pairedCoordinateEstimate hD A PairSign.pos g ≠ θ g then 1 else 0)) / 2

/-- The conditional calculation at manuscript lines 5234--5244, with all
four selection patterns and both hypothesis signs discharged explicitly. -/
theorem fairCoordinateError_eq_half_disagreement
    {n k : Nat} (hD : 2 * k ≤ n)
    (θ : Fin k → PairSign) (A : MSetAction n k) (g : Fin k) :
    fairCoordinateError hD θ A g =
      (1 : Real) / 2 * pairedCoordinateDisagreement hD θ A g := by
  by_cases hl : pairCoordinate hD (g, false) ∈ A.1
  · by_cases hr : pairCoordinate hD (g, true) ∈ A.1
    · cases hθ : θ g <;>
        simp [fairCoordinateError, pairedCoordinateEstimate,
          pairedCoordinateDisagreement, pairedZ, pairedSelected,
          pairCoordinate_mem_pairedSection_iff, hl, hr, hθ]
    · cases hθ : θ g <;>
        simp [fairCoordinateError, pairedCoordinateEstimate,
          pairedCoordinateDisagreement, pairedZ, pairedSelected,
          pairCoordinate_mem_pairedSection_iff, hl, hr, hθ] <;> norm_num
  · by_cases hr : pairCoordinate hD (g, true) ∈ A.1
    · cases hθ : θ g <;>
        simp [fairCoordinateError, pairedCoordinateEstimate,
          pairedCoordinateDisagreement, pairedZ, pairedSelected,
          pairCoordinate_mem_pairedSection_iff, hl, hr, hθ] <;> norm_num
    · cases hθ : θ g <;>
        simp [fairCoordinateError, pairedCoordinateEstimate,
          pairedCoordinateDisagreement, pairedZ, pairedSelected,
          pairCoordinate_mem_pairedSection_iff, hl, hr, hθ]

/-- The coordinate contributions sum to the paper's `h_θ(A)`. -/
theorem sum_pairedCoordinateDisagreement
    {n k : Nat} (hD : 2 * k ≤ n)
    (θ : Fin k → PairSign) (A : MSetAction n k) :
    (∑ g : Fin k, pairedCoordinateDisagreement hD θ A g) =
      pairedDisagreement hD θ A := by
  rw [pairedDisagreement]
  simp only [pairedCoordinateDisagreement, Finset.sum_sub_distrib]
  simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin,
    nsmul_eq_mul, mul_one]

/-- Coordinate error after choosing a round uniformly and then using the
fair fallback sign. -/
def randomRoundCoordinateError {n k T : Nat} (hD : 2 * k ≤ n)
    (θ : Fin k → PairSign) (actions : Fin T → MSetAction n k)
    (g : Fin k) : Real :=
  (T : Real)⁻¹ *
    ∑ t : Fin T, fairCoordinateError hD θ (actions t) g

/-- Conditional expected Hamming loss of the random-round estimator. -/
def randomRoundExpectedHamming {n k T : Nat} (hD : 2 * k ≤ n)
    (θ : Fin k → PairSign) (actions : Fin T → MSetAction n k) : Real :=
  ∑ g : Fin k, randomRoundCoordinateError hD θ actions g

/-- Equation `eq:lower-dense-estimation-regret-link`, conditional on a
realized action trajectory.  Averaging this pointwise identity under any
history law gives the manuscript's expectation identity. -/
theorem lower_dense_estimation_regret_link
    {n k T : Nat} (hT : 1 ≤ T) (hD : 2 * k ≤ n)
    (θ : Fin k → PairSign) (actions : Fin T → MSetAction n k) :
    randomRoundExpectedHamming hD θ actions =
      1 / (2 * (T : Real)) *
        ∑ t : Fin T, pairedDisagreement hD θ (actions t) := by
  have hT0 : (T : Real) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt hT)
  rw [randomRoundExpectedHamming]
  simp_rw [randomRoundCoordinateError,
    fairCoordinateError_eq_half_disagreement]
  rw [← Finset.mul_sum, Finset.sum_comm]
  simp_rw [← Finset.mul_sum, sum_pairedCoordinateDisagreement]
  field_simp [hT0]

/-- Expectation form of `lower_dense_estimation_regret_link`.  This is valid
under every finite or infinite base measure; in the intended instantiation
`μ` is the adaptive history law and `actions ω` extracts its action path. -/
theorem lower_dense_estimation_regret_link_integral
    {Ω : Type*} [MeasurableSpace Ω] {n k T : Nat}
    (μ : Measure Ω) (hT : 1 ≤ T) (hD : 2 * k ≤ n)
    (θ : Fin k → PairSign)
    (actions : Ω → Fin T → MSetAction n k) :
    (∫ ω, randomRoundExpectedHamming hD θ (actions ω) ∂μ) =
      1 / (2 * (T : Real)) *
        ∫ ω, ∑ t : Fin T, pairedDisagreement hD θ (actions ω t) ∂μ := by
  calc
    (∫ ω, randomRoundExpectedHamming hD θ (actions ω) ∂μ) =
        ∫ ω, 1 / (2 * (T : Real)) *
          ∑ t : Fin T, pairedDisagreement hD θ (actions ω t) ∂μ := by
      apply integral_congr_ae
      exact ae_of_all μ fun ω => lower_dense_estimation_regret_link hT hD θ (actions ω)
    _ = 1 / (2 * (T : Real)) *
        ∫ ω, ∑ t : Fin T, pairedDisagreement hD θ (actions ω t) ∂μ := by
      rw [integral_const_mul]

theorem measurableSet_coordinateCorrect
    {Ω : Type*} [MeasurableSpace Ω] {k : Nat}
    (estimate : Ω → Fin k → PairSign)
    (hestimate : ∀ g s, MeasurableSet {ω | estimate ω g = s})
    (θ : Fin k → PairSign) (g : Fin k) :
    MeasurableSet {ω | estimate ω g = θ g} :=
  hestimate g (θ g)

theorem measurableSet_coordinateErrorEvent
    {Ω : Type*} [MeasurableSpace Ω] {k : Nat}
    (estimate : Ω → Fin k → PairSign)
    (hestimate : ∀ g s, MeasurableSet {ω | estimate ω g = s})
    (θ : Fin k → PairSign) (g : Fin k) :
    MeasurableSet (coordinateErrorEvent estimate θ g) := by
  have h := (measurableSet_coordinateCorrect estimate hestimate θ g).compl
  simpa only [coordinateErrorEvent, Set.compl_setOf] using h

/-- For a binary sign, being unequal to the flipped sign is the same as
being equal to the original sign. -/
theorem ne_flip_iff_eq (a b : PairSign) : a ≠ b.flip ↔ a = b := by
  cases a <;> cases b <;> simp [PairSign.flip]

/-- The exact adjacent-hypothesis decision-error inequality from lines
5253--5261. -/
theorem coordinateErrorProbability_add_flip_ge
    {Ω : Type*} [MeasurableSpace Ω] {k : Nat}
    (P : (Fin k → PairSign) → Measure Ω)
    [∀ θ, IsProbabilityMeasure (P θ)]
    (estimate : Ω → Fin k → PairSign)
    (hestimate : ∀ g s, MeasurableSet {ω | estimate ω g = s})
    (θ : Fin k → PairSign) (g : Fin k) :
    coordinateErrorProbability P estimate θ g +
        coordinateErrorProbability P estimate (flipHypothesis θ g) g ≥
      1 - totalVariationDistance (P θ) (P (flipHypothesis θ g)) := by
  let B : Set Ω := {ω | estimate ω g = θ g}
  have hB : MeasurableSet B := hestimate g (θ g)
  have hpair :=
    decision_error_pair_ge_one_sub_totalVariationDistance
      (P θ) (P (flipHypothesis θ g)) hB
  have herr : coordinateErrorEvent estimate θ g = Bᶜ := by
    ext ω
    simp [coordinateErrorEvent, B]
  have hflip :
      coordinateErrorEvent estimate (flipHypothesis θ g) g = B := by
    ext ω
    simp only [coordinateErrorEvent, Set.mem_setOf_eq, flipHypothesis_same]
    exact ne_flip_iff_eq (estimate ω g) (θ g)
  simpa [coordinateErrorProbability, herr, hflip] using hpair

/-! ## Hypercube pairing -/

/-- Abstract summation form of the hypercube-pairing step.  It is separated
from probability so it can be reused for any coordinate testing risk. -/
theorem hypercube_pairing_sum
    {Θ G : Type*} [Fintype Θ] [Fintype G]
    (flip : G → Θ ≃ Θ) (err tv : Θ → G → Real)
    (hpair : ∀ θ g, 1 - tv θ g ≤ err θ g + err (flip g θ) g) :
    (Fintype.card Θ : Real) * (Fintype.card G : Real) -
        ∑ θ : Θ, ∑ g : G, tv θ g ≤
      2 * ∑ θ : Θ, ∑ g : G, err θ g := by
  classical
  have hg (g : G) :
      (Fintype.card Θ : Real) - ∑ θ : Θ, tv θ g ≤
        2 * ∑ θ : Θ, err θ g := by
    have hs := Finset.sum_le_sum fun θ (_ : θ ∈ (Finset.univ : Finset Θ)) =>
      hpair θ g
    rw [Finset.sum_sub_distrib] at hs
    simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul] at hs
    have hperm : (∑ θ : Θ, err (flip g θ) g) = ∑ θ : Θ, err θ g := by
      exact Equiv.sum_comp (flip g) (fun θ => err θ g)
    rw [Finset.sum_add_distrib, hperm] at hs
    linarith
  have hsum := Finset.sum_le_sum fun g (_ : g ∈ (Finset.univ : Finset G)) => hg g
  rw [Finset.sum_sub_distrib] at hsum
  simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul] at hsum
  calc
    (Fintype.card Θ : Real) * (Fintype.card G : Real) -
        ∑ θ : Θ, ∑ g : G, tv θ g =
      (Fintype.card G : Real) * (Fintype.card Θ : Real) -
        ∑ g : G, ∑ θ : Θ, tv θ g := by
          rw [mul_comm, Finset.sum_comm]
    _ ≤ ∑ g : G, 2 * ∑ θ : Θ, err θ g := hsum
    _ = 2 * ∑ θ : Θ, ∑ g : G, err θ g := by
      rw [← Finset.mul_sum, Finset.sum_comm]

/-- Averaged form of `hypercube_pairing_sum`, matching lines 5263--5273. -/
theorem hypercube_pairing_average
    {Θ G : Type*} [Fintype Θ] [Fintype G] [Nonempty Θ]
    (flip : G → Θ ≃ Θ) (err tv : Θ → G → Real)
    (hpair : ∀ θ g, 1 - tv θ g ≤ err θ g + err (flip g θ) g) :
    (Fintype.card Θ : Real)⁻¹ * ∑ θ : Θ, ∑ g : G, err θ g ≥
      (Fintype.card G : Real) / 2 -
        (Fintype.card Θ : Real)⁻¹ / 2 *
          ∑ θ : Θ, ∑ g : G, tv θ g := by
  have hcard : (0 : Real) < Fintype.card Θ := by
    exact_mod_cast Fintype.card_pos
  have h := hypercube_pairing_sum flip err tv hpair
  field_simp [ne_of_gt hcard]
  nlinarith

/-- Assouad's averaged Hamming-risk inequality for the paired hypothesis
cube, before invoking Pinsker. -/
theorem lower_dense_hypercube_pairing
    {Ω : Type*} [MeasurableSpace Ω] {k : Nat} (hk : 1 ≤ k)
    (P : (Fin k → PairSign) → Measure Ω)
    [∀ θ, IsProbabilityMeasure (P θ)]
    (estimate : Ω → Fin k → PairSign)
    (hestimate : ∀ g s, MeasurableSet {ω | estimate ω g = s}) :
    (Fintype.card (Fin k → PairSign) : Real)⁻¹ *
        ∑ θ : Fin k → PairSign, expectedHammingLoss P estimate θ ≥
      (k : Real) / 2 -
        (Fintype.card (Fin k → PairSign) : Real)⁻¹ / 2 *
          ∑ θ : Fin k → PairSign, ∑ g : Fin k,
            totalVariationDistance (P θ) (P (flipHypothesis θ g)) := by
  letI : Nonempty (Fin k → PairSign) := ⟨fun _ => PairSign.neg⟩
  let flip : Fin k → (Fin k → PairSign) ≃ (Fin k → PairSign) :=
    fun g => flipHypothesisEquiv g
  let err : (Fin k → PairSign) → Fin k → Real :=
    coordinateErrorProbability P estimate
  let tv : (Fin k → PairSign) → Fin k → Real :=
    fun θ g => totalVariationDistance (P θ) (P (flipHypothesis θ g))
  have hp : ∀ θ g, 1 - tv θ g ≤ err θ g + err (flip g θ) g := by
    intro θ g
    exact coordinateErrorProbability_add_flip_ge P estimate hestimate θ g
  have h := hypercube_pairing_average flip err tv hp
  simpa [expectedHammingLoss, flip, err, tv] using h

/-! ## Pinsker from `klDiv`

Mathlib's `klDiv` is an `ENNReal`, whereas the manuscript uses the real
finite value.  We prove the exact squared Pinsker inequality needed below,
rather than taking it as an analytic input.  The proof first coarse-grains
to a measurable event attaining TV and then proves the Bernoulli inequality.
-/

/-- KL divergence after coarse-graining two probabilities to an event and
its complement. -/
def binaryCoarseKL (a b : Real) : Real :=
  b * klFun (a / b) + (1 - b) * klFun ((1 - a) / (1 - b))

/-- The gap between binary KL and its Pinsker quadratic lower bound. -/
def pinskerGap (b x : Real) : Real :=
  x * Real.log x + (1 - x) * Real.log (1 - x) -
    x * Real.log b - (1 - x) * Real.log (1 - b) -
      2 * (x - b) ^ 2

def pinskerGapDeriv (b x : Real) : Real :=
  Real.log x - Real.log (1 - x) - Real.log b + Real.log (1 - b) -
    4 * (x - b)

def pinskerGapDeriv2 (x : Real) : Real :=
  x⁻¹ + (1 - x)⁻¹ - 4

theorem hasDerivAt_pinskerGap {b x : Real} (hx0 : x ≠ 0) (hx1 : x ≠ 1) :
    HasDerivAt (pinskerGap b) (pinskerGapDeriv b x) x := by
  have honeSub : HasDerivAt (fun y : Real => 1 - y) (-1) x := by
    convert! (hasDerivAt_const x (1 : Real)).sub (hasDerivAt_id x) using 1
    ring
  have hxOneSub : 1 - x ≠ 0 := sub_ne_zero.mpr hx1.symm
  have hfirst := Real.hasDerivAt_mul_log hx0
  have hsecond := (Real.hasDerivAt_mul_log hxOneSub).comp x honeSub
  have hthird := (hasDerivAt_id x).mul_const (Real.log b)
  have hfourth := honeSub.mul_const (Real.log (1 - b))
  have hdiff : HasDerivAt (fun y : Real => y - b) 1 x := by
    convert! (hasDerivAt_id x).sub (hasDerivAt_const x b) using 1
    ring
  have hsquare := (hdiff.pow 2).const_mul (2 : Real)
  convert! ((((hfirst.add hsecond).sub hthird).sub hfourth).sub hsquare) using 1
  simp only [pinskerGapDeriv, Nat.cast_ofNat, one_mul]
  ring

theorem hasDerivAt_pinskerGapDeriv {b x : Real}
    (hx0 : x ≠ 0) (hx1 : x ≠ 1) :
    HasDerivAt (pinskerGapDeriv b) (pinskerGapDeriv2 x) x := by
  have honeSub : HasDerivAt (fun y : Real => 1 - y) (-1) x := by
    convert! (hasDerivAt_const x (1 : Real)).sub (hasDerivAt_id x) using 1
    ring
  have hxOneSub : 1 - x ≠ 0 := sub_ne_zero.mpr hx1.symm
  have hlogx := Real.hasDerivAt_log hx0
  have hlogOneSub := (Real.hasDerivAt_log hxOneSub).comp x honeSub
  have hconstb := hasDerivAt_const x (Real.log b)
  have hconstOneSubb := hasDerivAt_const x (Real.log (1 - b))
  have hdiff : HasDerivAt (fun y : Real => y - b) 1 x := by
    convert! (hasDerivAt_id x).sub (hasDerivAt_const x b) using 1
    ring
  have hlinear := hdiff.const_mul (4 : Real)
  convert! ((((hlogx.sub hlogOneSub).sub hconstb).add hconstOneSubb).sub hlinear) using 1
  dsimp [pinskerGapDeriv2]
  ring

/-- The binary Pinsker gap is convex on the closed probability interval. -/
theorem pinskerGap_convexOn (b : Real) :
    ConvexOn Real (Set.Icc (0 : Real) 1) (pinskerGap b) := by
  refine convexOn_of_hasDerivWithinAt2_nonneg
    (f' := pinskerGapDeriv b) (f'' := pinskerGapDeriv2)
    (convex_Icc 0 1) ?_ ?_ ?_ ?_
  · unfold pinskerGap
    fun_prop
  · intro x hx
    rw [interior_Icc] at hx
    exact (hasDerivAt_pinskerGap (b := b) (x := x)
      (ne_of_gt hx.1) (ne_of_lt hx.2)).hasDerivWithinAt
  · intro x hx
    rw [interior_Icc] at hx
    exact (hasDerivAt_pinskerGapDeriv (b := b) (x := x)
      (ne_of_gt hx.1) (ne_of_lt hx.2)).hasDerivWithinAt
  · intro x hx
    rw [interior_Icc] at hx
    have hprod : 0 < x * (1 - x) := mul_pos hx.1 (sub_pos.mpr hx.2)
    have hprod_le : x * (1 - x) ≤ (1 : Real) / 4 := by
      nlinarith [sq_nonneg (x - 1 / 2)]
    have hinv : (4 : Real) ≤ 1 / (x * (1 - x)) := by
      apply (le_div_iff₀ hprod).2
      nlinarith
    have heq : x⁻¹ + (1 - x)⁻¹ = 1 / (x * (1 - x)) := by
      field_simp [ne_of_gt hx.1, ne_of_gt (sub_pos.mpr hx.2)]
      ring
    rw [pinskerGapDeriv2, heq]
    linarith

theorem pinskerGap_nonneg {a b : Real}
    (ha : a ∈ Set.Icc (0 : Real) 1) (hb0 : 0 < b) (hb1 : b < 1) :
    0 ≤ pinskerGap b a := by
  have hbmem : b ∈ interior (Set.Icc (0 : Real) 1) := by
    rw [interior_Icc]
    exact ⟨hb0, hb1⟩
  have hright : derivWithin (pinskerGap b) (Set.Ioi b) b = 0 := by
    have hd : HasDerivWithinAt (pinskerGap b) (pinskerGapDeriv b b)
        (Set.Ioi b) b :=
      (hasDerivAt_pinskerGap (b := b) (x := b)
        (ne_of_gt hb0) (ne_of_lt hb1)).hasDerivWithinAt
    rw [hd.derivWithin (uniqueDiffWithinAt_Ioi b)]
    simp [pinskerGapDeriv]
  have hmin :=
    (pinskerGap_convexOn b).isMinOn_of_rightDeriv_eq_zero hbmem hright
  have h := hmin ha
  have hzero : pinskerGap b b = 0 := by simp [pinskerGap]
  rwa [hzero] at h

theorem binaryCoarseKL_eq_pinskerGap_add_sq {a b : Real}
    (ha : a ∈ Set.Icc (0 : Real) 1) (hb0 : 0 < b) (hb1 : b < 1) :
    binaryCoarseKL a b = pinskerGap b a + 2 * (a - b) ^ 2 := by
  have hbne : b ≠ 0 := ne_of_gt hb0
  have h1bne : 1 - b ≠ 0 := ne_of_gt (sub_pos.mpr hb1)
  rcases eq_or_ne a 0 with rfl | ha0
  · simp [binaryCoarseKL, pinskerGap, klFun, hbne, h1bne]
    field_simp [h1bne]
    ring
  rcases eq_or_ne a 1 with rfl | ha1
  · simp [binaryCoarseKL, pinskerGap, klFun, hbne, h1bne]
    field_simp [hbne]
    ring
  have h1ane : 1 - a ≠ 0 := sub_ne_zero.mpr ha1.symm
  simp only [binaryCoarseKL, pinskerGap, klFun]
  rw [Real.log_div ha0 hbne, Real.log_div h1ane h1bne]
  field_simp [hbne, h1bne]
  ring

/-- Pinsker's inequality for two Bernoulli probabilities. -/
theorem binary_pinsker {a b : Real}
    (ha : a ∈ Set.Icc (0 : Real) 1) (hb0 : 0 < b) (hb1 : b < 1) :
    2 * (a - b) ^ 2 ≤ binaryCoarseKL a b := by
  rw [binaryCoarseKL_eq_pinskerGap_add_sq ha hb0 hb1]
  exact le_add_of_nonneg_left (pinskerGap_nonneg ha hb0 hb1)

/-- Jensen on one measurable cell.  This is the analytic core of binary
coarse-graining for KL. -/
theorem set_klFun_jensen
    {Ω : Type*} [MeasurableSpace Ω]
    (μ ν : Measure Ω) [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    (hμν : μ ≪ ν)
    (hphi : Integrable (fun x => klFun (μ.rnDeriv ν x).toReal) ν)
    {B : Set Ω} (hB : MeasurableSet B) (hνB : 0 < ν.real B) :
    ν.real B * klFun (μ.real B / ν.real B) ≤
      ∫ x in B, klFun (μ.rnDeriv ν x).toReal ∂ν := by
  let r : Ω → Real := fun x => (μ.rnDeriv ν x).toReal
  have hνBne : ν.restrict B ≠ 0 := by
    rw [← Measure.measure_univ_ne_zero, Measure.restrict_apply_univ]
    exact ne_of_gt (ENNReal.toReal_pos_iff.mp hνB).1
  letI : NeZero (ν.restrict B) := ⟨hνBne⟩
  have hrint : Integrable r (ν.restrict B) :=
    (Measure.integrable_toReal_rnDeriv (μ := μ) (ν := ν)).integrableOn
  have hφint : Integrable (klFun ∘ r) (ν.restrict B) := hphi.integrableOn
  have hrange : ∀ᵐ x ∂ν.restrict B, r x ∈ Set.Ici (0 : Real) :=
    ae_of_all _ fun _ => ENNReal.toReal_nonneg
  have hj := convexOn_klFun.map_average_le
    continuous_klFun.continuousOn isClosed_Ici hrange hrint hφint
  have havg : (⨍ x in B, r x ∂ν) = μ.real B / ν.real B := by
    rw [setAverage_eq, smul_eq_mul]
    have hint := Measure.setIntegral_toReal_rnDeriv_eq_withDensity'
      (μ := μ) (ν := ν) hB
    rw [Measure.withDensity_rnDeriv_eq μ ν hμν] at hint
    rw [hint, div_eq_inv_mul]
  rw [havg] at hj
  have hmul := mul_le_mul_of_nonneg_left hj hνB.le
  have hscale := measure_smul_average
    (μ := ν.restrict B) (fun x => klFun (r x))
  calc
    ν.real B * klFun (μ.real B / ν.real B) ≤
        ν.real B * ⨍ x in B, klFun (r x) ∂ν := hmul
    _ = ∫ x in B, klFun (μ.rnDeriv ν x).toReal ∂ν := by
      simpa [r, measureReal_restrict_apply_univ, smul_eq_mul,
        Function.comp_def] using hscale

theorem set_klFun_jensen_all
    {Ω : Type*} [MeasurableSpace Ω]
    (μ ν : Measure Ω) [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    (hμν : μ ≪ ν)
    (hphi : Integrable (fun x => klFun (μ.rnDeriv ν x).toReal) ν)
    {B : Set Ω} (hB : MeasurableSet B) :
    ν.real B * klFun (μ.real B / ν.real B) ≤
      ∫ x in B, klFun (μ.rnDeriv ν x).toReal ∂ν := by
  rcases (show 0 ≤ ν.real B from measureReal_nonneg).eq_or_lt with hzero | hpos
  · rw [← hzero, zero_mul]
    exact setIntegral_nonneg hB fun _ _ => klFun_nonneg ENNReal.toReal_nonneg
  · exact set_klFun_jensen μ ν hμν hphi hB hpos

/-- Data processing for the two-cell partition `{B,Bᶜ}`. -/
theorem binaryCoarseKL_le_klDiv
    {Ω : Type*} [MeasurableSpace Ω]
    (μ ν : Measure Ω) [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    {B : Set Ω} (hB : MeasurableSet B)
    (hfinite : klDiv μ ν ≠ ∞) :
    binaryCoarseKL (μ.real B) (ν.real B) ≤ (klDiv μ ν).toReal := by
  have hfin := klDiv_ne_top_iff.mp hfinite
  have hμν : μ ≪ ν := hfin.1
  have hphi : Integrable (fun x => klFun (μ.rnDeriv ν x).toReal) ν :=
    (integrable_klFun_rnDeriv_iff hμν).2 hfin.2
  have hBpart := set_klFun_jensen_all μ ν hμν hphi hB
  have hBcpart := set_klFun_jensen_all μ ν hμν hphi hB.compl
  rw [probReal_compl_eq_one_sub hB, probReal_compl_eq_one_sub hB] at hBcpart
  have hadd := add_le_add hBpart hBcpart
  rw [integral_add_compl hB hphi] at hadd
  rw [toReal_klDiv_eq_integral_klFun hμν]
  exact hadd

/-- For two probability measures, a measurable event attains the project's
Jordan-normalized total variation, with a chosen nonnegative orientation. -/
theorem exists_event_totalVariationDistance_eq
    {Ω : Type*} [MeasurableSpace Ω]
    (μ ν : Measure Ω) [IsProbabilityMeasure μ] [IsProbabilityMeasure ν] :
    ∃ B : Set Ω, MeasurableSet B ∧
      totalVariationDistance μ ν = μ.real B - ν.real B := by
  let s : SignedMeasure Ω := μ.toSignedMeasure - ν.toSignedMeasure
  let j : JordanDecomposition Ω := s.toJordanDecomposition
  obtain ⟨S, hS, _hneg, _hpos, hposS, hnegSc⟩ :=
    j.exists_compl_positive_negative
  refine ⟨Sᶜ, hS.compl, ?_⟩
  have hj : j.toSignedMeasure = s :=
    SignedMeasure.toSignedMeasure_toJordanDecomposition s
  have hs_univ : s Set.univ = 0 := by
    dsimp [s]
    rw [_root_.sub_apply,
      Measure.toSignedMeasure_apply_measurable MeasurableSet.univ,
      Measure.toSignedMeasure_apply_measurable MeasurableSet.univ]
    simp [measureReal_def]
  have hj_univ : j.posPart.real Set.univ = j.negPart.real Set.univ := by
    have h := congrArg (fun q : SignedMeasure Ω => q Set.univ) hj
    rw [JordanDecomposition.toSignedMeasure, hs_univ] at h
    rw [_root_.sub_apply,
      Measure.toSignedMeasure_apply_measurable MeasurableSet.univ,
      Measure.toSignedMeasure_apply_measurable MeasurableSet.univ] at h
    linarith
  have hposSc : j.posPart.real Sᶜ = j.posPart.real Set.univ := by
    have hsum := measureReal_add_measureReal_compl (μ := j.posPart) hS
    have hz : j.posPart.real S = 0 := by simp [measureReal_def, hposS]
    linarith
  have hdiff : μ.real Sᶜ - ν.real Sᶜ = j.posPart.real Sᶜ := by
    have h := congrArg (fun q : SignedMeasure Ω => q Sᶜ) hj
    rw [JordanDecomposition.toSignedMeasure] at h
    rw [_root_.sub_apply,
      Measure.toSignedMeasure_apply_measurable hS.compl,
      Measure.toSignedMeasure_apply_measurable hS.compl] at h
    have hsSc : s Sᶜ = μ.real Sᶜ - ν.real Sᶜ := by
      dsimp [s]
      exact Measure.toSignedMeasure_sub_apply hS.compl
    rw [hsSc] at h
    have hz : j.negPart.real Sᶜ = 0 := by simp [measureReal_def, hnegSc]
    linarith
  unfold totalVariationDistance
  change (1 / 2 : Real) * s.totalVariation.real Set.univ = _
  rw [SignedMeasure.totalVariation, measureReal_add_apply]
  change (1 / 2 : Real) *
    (j.posPart.real Set.univ + j.negPart.real Set.univ) =
      μ.real Sᶜ - ν.real Sᶜ
  rw [← hj_univ, ← hposSc, ← hdiff]
  ring

/-- Pinsker's inequality with the normalization
`TV = (1/2)|μ-ν|(univ)`: `2 TV² ≤ KL`.  Finiteness is explicit because
`ENNReal.toReal ∞ = 0`; all later KL budgets imply or provide it. -/
theorem totalVariationDistance_pinsker_sq
    {Ω : Type*} [MeasurableSpace Ω]
    (μ ν : Measure Ω) [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    (hfinite : klDiv μ ν ≠ ∞) :
    2 * totalVariationDistance μ ν ^ 2 ≤ (klDiv μ ν).toReal := by
  obtain ⟨B, hB, hTV⟩ := exists_event_totalVariationDistance_eq μ ν
  have hμν : μ ≪ ν := (klDiv_ne_top_iff.mp hfinite).1
  have ha : μ.real B ∈ Set.Icc (0 : Real) 1 := by
    refine ⟨measureReal_nonneg, ?_⟩
    simpa using measureReal_mono (μ := μ) (Set.subset_univ B)
  have hb : ν.real B ∈ Set.Icc (0 : Real) 1 := by
    refine ⟨measureReal_nonneg, ?_⟩
    simpa using measureReal_mono (μ := ν) (Set.subset_univ B)
  rcases eq_or_ne (ν.real B) 0 with hν0 | hν0
  · have hνB : ν B = 0 := (measureReal_eq_zero_iff).mp hν0
    have hμB : μ B = 0 := hμν hνB
    have hμ0 : μ.real B = 0 := (measureReal_eq_zero_iff).mpr hμB
    rw [hTV, hμ0, hν0]
    norm_num
  rcases eq_or_ne (ν.real B) 1 with hν1 | hν1
  · have hνBc0 : ν.real Bᶜ = 0 := by
      rw [probReal_compl_eq_one_sub hB, hν1]
      norm_num
    have hνBc : ν Bᶜ = 0 := (measureReal_eq_zero_iff).mp hνBc0
    have hμBc : μ Bᶜ = 0 := hμν hνBc
    have hμBc0 : μ.real Bᶜ = 0 := (measureReal_eq_zero_iff).mpr hμBc
    have hμ1 : μ.real B = 1 := by
      rw [probReal_compl_eq_one_sub hB] at hμBc0
      linarith
    rw [hTV, hμ1, hν1]
    norm_num
  · have hνpos : 0 < ν.real B := lt_of_le_of_ne hb.1 hν0.symm
    have hνlt : ν.real B < 1 := lt_of_le_of_ne hb.2 hν1
    calc
      2 * totalVariationDistance μ ν ^ 2 =
          2 * (μ.real B - ν.real B) ^ 2 := by rw [hTV]
      _ ≤ binaryCoarseKL (μ.real B) (ν.real B) :=
        binary_pinsker ha hνpos hνlt
      _ ≤ (klDiv μ ν).toReal := binaryCoarseKL_le_klDiv μ ν hB hfinite

/-! ## Pinsker plus Cauchy--Schwarz -/

/-- The exact Cauchy--Schwarz calculation used at lines 5275--5285.  The
argument is stated in terms of Mathlib's measure-theoretic `klDiv`; its
`hPinsker` input is the squared form `2 TV² ≤ KL`, with the same normalized
TV as the rest of this file. -/
theorem sum_totalVariationDistance_le_of_pinsker_kl_budget
    {Ω : Type*} [MeasurableSpace Ω] {k T : Nat} (hk : 1 ≤ k)
    (ε : Real) (hε0 : 0 ≤ ε)
    (μ ν : Fin k → Measure Ω)
    [∀ g, IsProbabilityMeasure (μ g)]
    [∀ g, IsProbabilityMeasure (ν g)]
    (hPinsker : ∀ g,
      2 * totalVariationDistance (μ g) (ν g) ^ 2 ≤
        (klDiv (μ g) (ν g)).toReal)
    (hKL : (∑ g : Fin k, (klDiv (μ g) (ν g)).toReal) ≤
      8 * ε ^ 2 * (T : Real) / (k : Real)) :
    (∑ g : Fin k, totalVariationDistance (μ g) (ν g)) ≤
      2 * ε * Real.sqrt T := by
  let tv : Fin k → Real := fun g => totalVariationDistance (μ g) (ν g)
  let K : Fin k → Real := fun g => (klDiv (μ g) (ν g)).toReal
  have hkreal : (0 : Real) < k := by exact_mod_cast hk
  have htv0 : ∀ g, 0 ≤ tv g := fun g => totalVariationDistance_nonneg _ _
  have hsumtv0 : 0 ≤ ∑ g : Fin k, tv g :=
    Finset.sum_nonneg fun g _ => htv0 g
  have hsqsum : 2 * ∑ g : Fin k, tv g ^ 2 ≤ ∑ g : Fin k, K g := by
    calc
      2 * ∑ g : Fin k, tv g ^ 2 = ∑ g : Fin k, 2 * tv g ^ 2 := by
        rw [Finset.mul_sum]
      _ ≤ ∑ g : Fin k, K g :=
        Finset.sum_le_sum fun g _ => hPinsker g
  have hcs : (∑ g : Fin k, tv g) ^ 2 ≤
      (k : Real) * ∑ g : Fin k, tv g ^ 2 := by
    simpa using
      (sq_sum_le_card_mul_sum_sq
        (s := (Finset.univ : Finset (Fin k))) (f := tv))
  have hsquare : (∑ g : Fin k, tv g) ^ 2 ≤ 4 * ε ^ 2 * (T : Real) := by
    have hKL' : (∑ g : Fin k, K g) ≤
        8 * ε ^ 2 * (T : Real) / (k : Real) := hKL
    calc
      (∑ g : Fin k, tv g) ^ 2 ≤
          (k : Real) * ∑ g : Fin k, tv g ^ 2 := hcs
      _ ≤ (k : Real) / 2 * ∑ g : Fin k, K g := by
        nlinarith
      _ ≤ (k : Real) / 2 *
          (8 * ε ^ 2 * (T : Real) / (k : Real)) := by
        gcongr
      _ = 4 * ε ^ 2 * (T : Real) := by
        field_simp [ne_of_gt hkreal]
        ring
  have hsqrt0 : 0 ≤ Real.sqrt T := Real.sqrt_nonneg _
  have hsqrtSq : Real.sqrt (T : Real) ^ 2 = (T : Real) :=
    Real.sq_sqrt (Nat.cast_nonneg T)
  change (∑ g : Fin k, tv g) ≤ 2 * ε * Real.sqrt T
  apply (sq_le_sq₀ hsumtv0 (by positivity : 0 ≤ 2 * ε * Real.sqrt T)).mp
  calc
    (∑ g : Fin k, tv g) ^ 2 ≤ 4 * ε ^ 2 * (T : Real) := hsquare
    _ = (2 * ε * Real.sqrt T) ^ 2 := by
      symm
      calc
        (2 * ε * Real.sqrt T) ^ 2 =
            4 * ε ^ 2 * Real.sqrt T ^ 2 := by ring
        _ = 4 * ε ^ 2 * (T : Real) := by rw [hsqrtSq]

/-- Real-valued KL-budget interface after discharging Pinsker internally.
The finiteness assumptions are mathematically necessary at this interface,
since `ENNReal.toReal ∞ = 0`. -/
theorem sum_totalVariationDistance_le_of_finite_kl_budget
    {Ω : Type*} [MeasurableSpace Ω] {k T : Nat} (hk : 1 ≤ k)
    (ε : Real) (hε0 : 0 ≤ ε)
    (μ ν : Fin k → Measure Ω)
    [∀ g, IsProbabilityMeasure (μ g)]
    [∀ g, IsProbabilityMeasure (ν g)]
    (hfinite : ∀ g, klDiv (μ g) (ν g) ≠ ∞)
    (hKL : (∑ g : Fin k, (klDiv (μ g) (ν g)).toReal) ≤
      8 * ε ^ 2 * (T : Real) / (k : Real)) :
    (∑ g : Fin k, totalVariationDistance (μ g) (ν g)) ≤
      2 * ε * Real.sqrt T := by
  exact sum_totalVariationDistance_le_of_pinsker_kl_budget
    hk ε hε0 μ ν
    (fun g => totalVariationDistance_pinsker_sq (μ g) (ν g) (hfinite g)) hKL

/-- Primary, directly instantiable form of lines 5275--5285.  An
`ENNReal` KL budget simultaneously supplies finiteness and, after `toReal`,
the real budget. -/
theorem sum_totalVariationDistance_le_kl_budget
    {Ω : Type*} [MeasurableSpace Ω] {k T : Nat} (hk : 1 ≤ k)
    (ε : Real) (hε0 : 0 ≤ ε)
    (μ ν : Fin k → Measure Ω)
    [∀ g, IsProbabilityMeasure (μ g)]
    [∀ g, IsProbabilityMeasure (ν g)]
    (hKL : (∑ g : Fin k, klDiv (μ g) (ν g)) ≤
      ENNReal.ofReal (8 * ε ^ 2 * (T : Real) / (k : Real))) :
    (∑ g : Fin k, totalVariationDistance (μ g) (ν g)) ≤
      2 * ε * Real.sqrt T := by
  have hkreal : (0 : Real) < k := by exact_mod_cast hk
  have hfinite : ∀ g, klDiv (μ g) (ν g) ≠ ∞ := by
    intro g
    apply ne_top_of_le_ne_top ENNReal.ofReal_ne_top
    exact (Finset.single_le_sum
      (fun i (_ : i ∈ (Finset.univ : Finset (Fin k))) =>
        (show (0 : ENNReal) ≤ klDiv (μ i) (ν i) from bot_le))
      (Finset.mem_univ g)).trans hKL
  have hbound0 : 0 ≤ 8 * ε ^ 2 * (T : Real) / (k : Real) := by
    positivity
  have hKLreal :
      (∑ g : Fin k, (klDiv (μ g) (ν g)).toReal) ≤
        8 * ε ^ 2 * (T : Real) / (k : Real) := by
    rw [← ENNReal.toReal_sum (fun g _ => hfinite g)]
    calc
      (∑ g : Fin k, klDiv (μ g) (ν g)).toReal ≤
          (ENNReal.ofReal
            (8 * ε ^ 2 * (T : Real) / (k : Real))).toReal :=
        ENNReal.toReal_mono ENNReal.ofReal_ne_top hKL
      _ = 8 * ε ^ 2 * (T : Real) / (k : Real) :=
        ENNReal.toReal_ofReal hbound0
  exact sum_totalVariationDistance_le_of_finite_kl_budget
    hk ε hε0 μ ν hfinite hKLreal

/-- The paired sign cube has exactly `2^k` hypotheses. -/
theorem card_pairSign_hypercube (k : Nat) :
    Fintype.card (Fin k → PairSign) = 2 ^ k := by
  let e : PairSign ≃ Bool :=
    { toFun := fun
        | PairSign.neg => false
        | PairSign.pos => true
      invFun := fun
        | false => PairSign.neg
        | true => PairSign.pos
      left_inv := fun s => by cases s <;> rfl
      right_inv := fun b => by cases b <;> rfl }
  rw [Fintype.card_fun, Fintype.card_congr e]
  simp

/-- Algebraic extraction used when combining the estimation--regret link
with Assouad: if every Hamming risk is `gap/(2T)`, an average Hamming risk of
`3k/8` forces one mean gap to be at least `3kT/4`. -/
theorem exists_large_gap_of_average_hamming
    {k T : Nat} (hk : 1 ≤ k) (hT : 1 ≤ T)
    (ham gap : (Fin k → PairSign) → Real)
    (hlink : ∀ θ, ham θ = 1 / (2 * (T : Real)) * gap θ)
    (haverage :
      (Fintype.card (Fin k → PairSign) : Real)⁻¹ *
          ∑ θ : Fin k → PairSign, ham θ ≥ 3 * (k : Real) / 8) :
    ∃ θ : Fin k → PairSign,
      3 * (k : Real) * (T : Real) / 4 ≤ gap θ := by
  letI : Nonempty (Fin k → PairSign) := ⟨fun _ => PairSign.neg⟩
  let cardH : Real := Fintype.card (Fin k → PairSign)
  have hcard : 0 < cardH := by
    dsimp [cardH]
    exact_mod_cast Fintype.card_pos
  have hinv : cardH * cardH⁻¹ = 1 := mul_inv_cancel₀ (ne_of_gt hcard)
  have hsumReal :
      cardH * (3 * (k : Real) / 8) ≤
        ∑ θ : Fin k → PairSign, ham θ := by
    change cardH⁻¹ * (∑ θ : Fin k → PairSign, ham θ) ≥ _ at haverage
    calc
      cardH * (3 * (k : Real) / 8) ≤
          cardH * (cardH⁻¹ * ∑ θ : Fin k → PairSign, ham θ) :=
        mul_le_mul_of_nonneg_left haverage hcard.le
      _ = ∑ θ : Fin k → PairSign, ham θ := by
        rw [← mul_assoc, hinv, one_mul]
  have hsum :
      (∑ _θ : Fin k → PairSign, 3 * (k : Real) / 8) ≤
        ∑ θ : Fin k → PairSign, ham θ := by
    simpa [cardH] using hsumReal
  obtain ⟨θ, _hθmem, hθ⟩ := Finset.exists_le_of_sum_le
    (s := (Finset.univ : Finset (Fin k → PairSign)))
    Finset.univ_nonempty hsum
  rw [hlink θ] at hθ
  have hden : 0 < 2 * (T : Real) := by
    positivity
  have hθ' : 3 * (k : Real) / 8 ≤ gap θ / (2 * (T : Real)) := by
    simpa [div_eq_mul_inv, mul_comm] using hθ
  refine ⟨θ, ?_⟩
  have hmul := (le_div_iff₀ hden).mp hθ'
  calc
    3 * (k : Real) * (T : Real) / 4 =
        (3 * (k : Real) / 8) * (2 * (T : Real)) := by ring
    _ ≤ gap θ := hmul

/-- Equation `eq:lower-dense-assouad`, conditional only on the adjacent-law
KL budget proved by the sequential information argument.  Pinsker, pairing,
averaging, all constants, and the substitution `ε=k/(8√T)` are discharged
here. -/
theorem lower_dense_assouad
    {Ω : Type*} [MeasurableSpace Ω] {k T : Nat}
    (hk : 1 ≤ k) (hT : 1 ≤ T)
    (P : (Fin k → PairSign) → Measure Ω)
    [∀ θ, IsProbabilityMeasure (P θ)]
    (estimate : Ω → Fin k → PairSign)
    (hestimate : ∀ g s, MeasurableSet {ω | estimate ω g = s})
    (hKL : ∀ θ,
      (∑ g : Fin k, klDiv (P θ) (P (flipHypothesis θ g))) ≤
        ENNReal.ofReal
          (16 * denseEpsilon k T ^ 2 * (T : Real) /
            (2 * (k : Real)))) :
    (Fintype.card (Fin k → PairSign) : Real)⁻¹ *
        ∑ θ : Fin k → PairSign, expectedHammingLoss P estimate θ ≥
      3 * (k : Real) / 8 := by
  letI : Nonempty (Fin k → PairSign) := ⟨fun _ => PairSign.neg⟩
  let cardH : Real := Fintype.card (Fin k → PairSign)
  let totalTV : Real :=
    ∑ θ : Fin k → PairSign, ∑ g : Fin k,
      totalVariationDistance (P θ) (P (flipHypothesis θ g))
  have hcard : 0 < cardH := by
    dsimp [cardH]
    exact_mod_cast Fintype.card_pos
  have hk0 : (k : Real) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt hk)
  have hθ (θ : Fin k → PairSign) :
      (∑ g : Fin k,
          totalVariationDistance (P θ) (P (flipHypothesis θ g))) ≤
        2 * denseEpsilon k T * Real.sqrt T := by
    apply sum_totalVariationDistance_le_kl_budget
      hk (denseEpsilon k T) (denseEpsilon_nonneg k T)
      (fun _ => P θ) (fun g => P (flipHypothesis θ g))
    calc
      (∑ g : Fin k, klDiv (P θ) (P (flipHypothesis θ g))) ≤
          ENNReal.ofReal
            (16 * denseEpsilon k T ^ 2 * (T : Real) /
              (2 * (k : Real))) := hKL θ
      _ = ENNReal.ofReal
          (8 * denseEpsilon k T ^ 2 * (T : Real) / (k : Real)) := by
        congr 1
        field_simp [hk0]
        ring
  have htotal : totalTV ≤ cardH *
      (2 * denseEpsilon k T * Real.sqrt T) := by
    dsimp [totalTV, cardH]
    calc
      (∑ θ : Fin k → PairSign, ∑ g : Fin k,
          totalVariationDistance (P θ) (P (flipHypothesis θ g))) ≤
          ∑ _θ : Fin k → PairSign,
            2 * denseEpsilon k T * Real.sqrt T :=
        Finset.sum_le_sum fun θ _ => hθ θ
      _ = (Fintype.card (Fin k → PairSign) : Real) *
          (2 * denseEpsilon k T * Real.sqrt T) := by simp
  have hpair := lower_dense_hypercube_pairing hk P estimate hestimate
  have hcorr : cardH⁻¹ / 2 * totalTV ≤
      denseEpsilon k T * Real.sqrt T := by
    calc
      cardH⁻¹ / 2 * totalTV ≤
          cardH⁻¹ / 2 *
            (cardH * (2 * denseEpsilon k T * Real.sqrt T)) :=
        mul_le_mul_of_nonneg_left htotal (by positivity)
      _ = denseEpsilon k T * Real.sqrt T := by
        field_simp [ne_of_gt hcard]
  have hsqrt_pos : 0 < Real.sqrt T := by
    exact Real.sqrt_pos.2 (by exact_mod_cast hT)
  have hepsilon : denseEpsilon k T * Real.sqrt T = (k : Real) / 8 := by
    rw [denseEpsilon]
    field_simp [ne_of_gt hsqrt_pos]
  change cardH⁻¹ *
      ∑ θ : Fin k → PairSign, expectedHammingLoss P estimate θ ≥ _
  change cardH⁻¹ / 2 * totalTV ≤ _ at hcorr
  change cardH⁻¹ *
      ∑ θ : Fin k → PairSign, expectedHammingLoss P estimate θ ≥
        (k : Real) / 2 - cardH⁻¹ / 2 * totalTV at hpair
  rw [hepsilon] at hcorr
  linarith

#print axioms abs_eventProbability_sub_le_totalVariationDistance
#print axioms decision_error_pair_ge_one_sub_totalVariationDistance
#print axioms fairCoordinateError_eq_half_disagreement
#print axioms lower_dense_estimation_regret_link
#print axioms lower_dense_estimation_regret_link_integral
#print axioms coordinateErrorProbability_add_flip_ge
#print axioms hypercube_pairing_sum
#print axioms lower_dense_hypercube_pairing
#print axioms binary_pinsker
#print axioms binaryCoarseKL_le_klDiv
#print axioms totalVariationDistance_pinsker_sq
#print axioms sum_totalVariationDistance_le_of_pinsker_kl_budget
#print axioms sum_totalVariationDistance_le_of_finite_kl_budget
#print axioms sum_totalVariationDistance_le_kl_budget
#print axioms exists_large_gap_of_average_hamming
#print axioms lower_dense_assouad

end

end MsetsLower.Lower.Dense
