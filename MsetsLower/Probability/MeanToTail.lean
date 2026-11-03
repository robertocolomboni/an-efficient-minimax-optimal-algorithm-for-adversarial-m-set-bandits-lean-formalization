import MsetsLower.Prelude
import Mathlib.MeasureTheory.Function.L2Space

/-!
# Turning positive means into positive-probability events

This module formalizes the two elementary tail conversions used by the lower
bound.  The bounded form is independent of any sign assumption on the random
variable.
-/

namespace MsetsLower.Probability

open MeasureTheory Set

noncomputable section

/-- The literal partition used in the definitive manuscript: split the
expectation between `X < a` and `a ≤ X`. No sign condition on `X` is used. -/
theorem integral_split_at_threshold
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    (X : Ω → Real) (hX : Measurable X) (hXi : Integrable X P) (a : Real) :
    (∫ ω, X ω ∂P) =
      (∫ ω, {ω | X ω < a}.indicator X ω ∂P) +
      ∫ ω, {ω | a ≤ X ω}.indicator X ω ∂P := by
  have hlo : MeasurableSet {ω | X ω < a} := measurableSet_lt hX measurable_const
  have hhi : MeasurableSet {ω | a ≤ X ω} := measurableSet_le measurable_const hX
  rw [← integral_add (hXi.indicator hlo) (hXi.indicator hhi)]
  apply integral_congr_ae
  exact ae_of_all _ fun ω => by
    by_cases h : X ω < a
    · simp [h, not_le.mpr h]
    · simp [h, le_of_not_gt h]

/-- The two bounds after that partition, retaining the paper's exact
`μ/2 + M P(X ≥ μ/2)` expression. -/
theorem integral_le_half_mean_add_tail
    {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P]
    (X : Ω → Real) (hX : Measurable X) (hXi : Integrable X P)
    {M μ : Real} (hμ : 0 ≤ μ) (hupper : ∀ᵐ ω ∂P, X ω ≤ M) :
    (∫ ω, X ω ∂P) ≤ μ / 2 + M * P.real {ω | μ / 2 ≤ X ω} := by
  have hlo : MeasurableSet {ω | X ω < μ / 2} :=
    measurableSet_lt hX measurable_const
  have hhi : MeasurableSet {ω | μ / 2 ≤ X ω} :=
    measurableSet_le measurable_const hX
  have hlow : (∫ ω, {ω | X ω < μ / 2}.indicator X ω ∂P) ≤ μ / 2 := by
    calc
      _ ≤ ∫ _ω : Ω, μ / 2 ∂P := by
        apply integral_mono (hXi.indicator hlo) (integrable_const _)
        intro ω
        by_cases h : X ω < μ / 2
        · simpa [h] using h.le
        · simpa [h] using (show (0 : Real) ≤ μ / 2 by positivity)
      _ = μ / 2 := by simp
  have hhigh : (∫ ω, {ω | μ / 2 ≤ X ω}.indicator X ω ∂P) ≤
      M * P.real {ω | μ / 2 ≤ X ω} := by
    calc
      _ ≤ ∫ ω, {ω | μ / 2 ≤ X ω}.indicator (fun _ => M) ω ∂P := by
        apply integral_mono_ae (hXi.indicator hhi) ((integrable_const M).indicator hhi)
        filter_upwards [hupper] with ω hω
        by_cases h : μ / 2 ≤ X ω <;> simp [h, hω]
      _ = _ := by rw [integral_indicator_const M hhi]; simp [mul_comm]
  rw [integral_split_at_threshold P X hX hXi (μ / 2)]
  exact add_le_add hlow hhigh

/-- First clause of `lem:lower-mean-to-probability`: an almost-sure upper
bound and a positive mean force a one-half-mean event. -/
theorem probability_ge_half_mean_of_ae_le
    {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P]
    (X : Ω → Real) (hX_measurable : Measurable X)
    (hX_integrable : Integrable X P)
    {M μ : Real} (hμ : 0 < μ)
    (hmean : μ ≤ ∫ ω, X ω ∂P)
    (hupper : ∀ᵐ ω ∂P, X ω ≤ M) :
    μ / (2 * M) ≤ P.real {ω | μ / 2 ≤ X ω} := by
  have hM_integrable : Integrable (fun _ω : Ω => M) P :=
    integrable_const M
  have hintegral_le_M : (∫ ω, X ω ∂P) ≤ M := by
    have h := integral_mono_ae hX_integrable hM_integrable hupper
    simpa using h
  have hM : 0 < M := hμ.trans_le (hmean.trans hintegral_le_M)
  have hintegral_upper := integral_le_half_mean_add_tail
    P X hX_measurable hX_integrable hμ.le hupper
  have hdenom : 0 < 2 * M := mul_pos (by norm_num) hM
  apply (div_le_iff₀ hdenom).2
  nlinarith

/-- L13 with exactly the paper's one-sided bound and positive mean. The
integrability needed for splitting the expectation follows from its strictly
positive real integral; it is not an additional hypothesis. -/
theorem probability_ge_half_mean_paper
    {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P]
    (X : Ω → Real) (hX : Measurable X)
    {M μ : Real} (hμ : 0 < μ) (_hμM : μ ≤ M)
    (hupper : ∀ᵐ ω ∂P, X ω ≤ M) (hmean : μ ≤ ∫ ω, X ω ∂P) :
    μ / (2 * M) ≤ P.real {ω | μ / 2 ≤ X ω} := by
  have hXi : Integrable X P :=
    Integrable.of_integral_ne_zero (ne_of_gt (hμ.trans_le hmean))
  exact probability_ge_half_mean_of_ae_le P X hX hXi hμ hmean hupper

/-- Second clause of `lem:lower-mean-to-probability`: square integrability and
a positive mean give the one-half-mean Paley--Zygmund bound.  No global
nonnegativity assumption on `X` is needed. -/
theorem probability_ge_half_mean_of_second_moment
    {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P]
    (X : Ω → Real) (hX_measurable : Measurable X)
    (hX_square_integrable : Integrable (fun ω => (X ω) ^ 2) P)
    (hmean_pos : 0 < ∫ ω, X ω ∂P) :
    (∫ ω, X ω ∂P) ^ 2 /
        (4 * ∫ ω, (X ω) ^ 2 ∂P) ≤
      P.real {ω | (∫ ω, X ω ∂P) / 2 ≤ X ω} := by
  let mean : Real := ∫ ω, X ω ∂P
  let second : Real := ∫ ω, (X ω) ^ 2 ∂P
  let E : Set Ω := {ω | mean / 2 ≤ X ω}
  let u : Ω → Real := E.indicator X
  let v : Ω → Real := E.indicator fun _ω => (1 : Real)
  have hE : MeasurableSet E :=
    measurableSet_le measurable_const hX_measurable
  have hX_ae : AEStronglyMeasurable X P :=
    hX_measurable.aestronglyMeasurable
  have hX_L2 : MemLp X 2 P := by
    rw [memLp_two_iff_integrable_sq hX_ae]
    exact hX_square_integrable
  have hu_L2 : MemLp u 2 P := by
    simpa [u] using hX_L2.indicator hE.nullMeasurableSet
  have hv_L2 : MemLp v 2 P := by
    simpa [v] using
      ((memLp_const (μ := P) (p := (2 : ENNReal)) (1 : Real)).indicator hE.nullMeasurableSet)
  have hu_nonneg : 0 ≤ᵐ[P] u := by
    apply ae_of_all
    intro ω
    change 0 ≤ u ω
    by_cases hω : ω ∈ E
    · rw [show u ω = X ω by simp [u, Set.indicator_of_mem hω]]
      have hthreshold : mean / 2 ≤ X ω := by simpa [E] using hω
      have hmean : 0 < mean := by simpa [mean] using hmean_pos
      linarith
    · simp [u, Set.indicator_of_notMem hω]
  have hv_nonneg : 0 ≤ᵐ[P] v := by
    apply ae_of_all
    intro ω
    change 0 ≤ v ω
    by_cases hω : ω ∈ E <;> simp [v, Set.indicator_of_mem,
      Set.indicator_of_notMem, hω]
  have hholder : (2 : Real).HolderConjugate 2 := by
    rw [Real.holderConjugate_iff]
    norm_num
  have hu_L2' : MemLp u (ENNReal.ofReal (2 : Real)) P := by
    simpa using hu_L2
  have hv_L2' : MemLp v (ENNReal.ofReal (2 : Real)) P := by
    simpa using hv_L2
  have hCS := integral_mul_le_Lp_mul_Lq_of_nonneg
    (μ := P) (f := u) (g := v) hholder hu_nonneg hv_nonneg hu_L2' hv_L2'
  simp only [Real.rpow_two] at hCS
  rw [show (1 / (2 : Real)) = (1 / 2 : Real) by norm_num,
    ← Real.sqrt_eq_rpow, ← Real.sqrt_eq_rpow] at hCS
  have huv : (fun ω => u ω * v ω) = u := by
    funext ω
    by_cases hω : ω ∈ E <;>
      simp [u, v, Set.indicator_of_mem, Set.indicator_of_notMem, hω]
  rw [huv] at hCS
  have hu_sq_integrable : Integrable (fun ω => (u ω) ^ 2) P :=
    hu_L2.integrable_sq
  have hX_integrable : Integrable X P := hX_L2.integrable (by norm_num)
  have hu_integrable : Integrable u P := hu_L2.integrable (by norm_num)
  have hu_sq_le :
      (∫ ω, (u ω) ^ 2 ∂P) ≤ second := by
    dsimp [second]
    apply integral_mono hu_sq_integrable hX_square_integrable
    intro ω
    by_cases hω : ω ∈ E
    · simp [u, Set.indicator_of_mem hω]
    · simp [u, Set.indicator_of_notMem hω, sq_nonneg]
  have hv_sq_eq : (∫ ω, (v ω) ^ 2 ∂P) = P.real E := by
    have hvpoint : (fun ω => (v ω) ^ 2) = E.indicator 1 := by
      funext ω
      by_cases hω : ω ∈ E <;>
        simp [v, Set.indicator_of_mem, Set.indicator_of_notMem, hω]
    rw [hvpoint]
    exact integral_indicator_one hE
  rw [hv_sq_eq] at hCS
  have hsecond_nonneg : 0 ≤ second := by
    dsimp [second]
    exact integral_nonneg fun ω => sq_nonneg (X ω)
  have hprob_nonneg : 0 ≤ P.real E := measureReal_nonneg
  have hu_integral_upper :
      (∫ ω, u ω ∂P) ≤ Real.sqrt (second * P.real E) := by
    calc
      (∫ ω, u ω ∂P) ≤
          Real.sqrt (∫ ω, (u ω) ^ 2 ∂P) *
            Real.sqrt (P.real E) := hCS
      _ ≤ Real.sqrt second * Real.sqrt (P.real E) := by
        gcongr
      _ = Real.sqrt (second * P.real E) := by
        rw [Real.sqrt_mul hsecond_nonneg]
  have hpoint_mean : X ≤ᵐ[P] fun ω => mean / 2 + u ω := by
    apply ae_of_all
    intro ω
    change X ω ≤ mean / 2 + u ω
    by_cases hω : ω ∈ E
    · rw [show u ω = X ω by simp [u, Set.indicator_of_mem hω]]
      have hmean : 0 < mean := by simpa [mean] using hmean_pos
      linarith
    · rw [show u ω = 0 by simp [u, Set.indicator_of_notMem hω]]
      have hnot : ¬mean / 2 ≤ X ω := by simpa [E] using hω
      simpa using le_of_lt (not_le.mp hnot)
  have hmean_upper : mean ≤ mean / 2 + ∫ ω, u ω ∂P := by
    have hmono := integral_mono_ae hX_integrable
      ((integrable_const (mean / 2)).add hu_integrable) hpoint_mean
    calc
      mean = ∫ ω, X ω ∂P := rfl
      _ ≤ ∫ ω, (mean / 2 + u ω) ∂P := hmono
      _ = mean / 2 + ∫ ω, u ω ∂P := by
        rw [integral_add (integrable_const (mean / 2)) hu_integrable]
        simp
  have hmean_sqrt : mean / 2 ≤ Real.sqrt (second * P.real E) :=
    le_trans (by linarith [hmean_upper]) hu_integral_upper
  have hproduct_nonneg : 0 ≤ second * P.real E :=
    mul_nonneg hsecond_nonneg hprob_nonneg
  have hsq : (mean / 2) ^ 2 ≤ second * P.real E := by
    have hmean_half_nonneg : 0 ≤ mean / 2 := by
      have : 0 < mean := by simpa [mean] using hmean_pos
      positivity
    nlinarith [Real.sq_sqrt hproduct_nonneg]
  have hsecond_pos : 0 < second := by
    by_contra hnot
    have hzero : second = 0 := le_antisymm (le_of_not_gt hnot) hsecond_nonneg
    have hmean : 0 < mean := by simpa [mean] using hmean_pos
    rw [hzero] at hsq
    nlinarith
  have hdenom : 0 < 4 * second := mul_pos (by norm_num) hsecond_pos
  change mean ^ 2 / (4 * second) ≤ P.real E
  apply (div_le_iff₀ hdenom).2
  nlinarith

end

end MsetsLower.Probability
