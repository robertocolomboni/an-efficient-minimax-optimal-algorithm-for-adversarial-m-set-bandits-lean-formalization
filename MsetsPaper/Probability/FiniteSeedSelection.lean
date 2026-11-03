import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.Tactic

/-! # Strict finite averaging before selecting a hidden candidate

The order of quantifiers is essential: integrate over the learner seed first,
then select one candidate independently of that seed. These elementary lemmas
make both strictness and measurability requirements explicit.
-/

namespace MsetsPaper.Probability

open MeasureTheory Set
open scoped BigOperators

noncomputable section

variable {Ω ι : Type*} [MeasurableSpace Ω]

theorem integral_strictly_above_constant
    (μ : Measure Ω) [IsProbabilityMeasure μ] (f : Ω → ℝ)
    (hf : Integrable f μ) {delta : ℝ} (h : ∀ r, delta < f r) :
    delta < ∫ r, f r ∂μ := by
  have hgap : Integrable (fun r ↦ f r - delta) μ := hf.sub (integrable_const delta)
  have hpos : 0 < ∫ r, (f r - delta) ∂μ := by
    apply (integral_pos_iff_support_of_nonneg (fun r ↦ (sub_pos.mpr (h r)).le) hgap).2
    have hs : Function.support (fun r ↦ f r - delta) = Set.univ := by
      ext r
      simp only [Function.mem_support, Set.mem_univ, iff_true]
      exact (sub_pos.mpr (h r)).ne'
    rw [hs]
    simp
  rw [integral_sub hf (integrable_const delta)] at hpos
  simpa only [integral_const, probReal_univ, one_smul, sub_pos] using hpos

/-- A strict mean lower bound gives a strict witness, not merely a weak one. -/
theorem exists_strict_of_integral_strict
    (μ : Measure Ω) [IsProbabilityMeasure μ] (f : Ω → ℝ)
    (hf : Integrable f μ) {delta : ℝ} (h : delta < ∫ r, f r ∂μ) :
    ∃ r, delta < f r := by
  by_contra hn
  push Not at hn
  have hmono := integral_mono hf (integrable_const delta) hn
  simp only [integral_const, probReal_univ, one_smul] at hmono
  exact (not_lt_of_ge hmono) h

/-- Average the private seed before choosing an index. There is no claim
that the same index attains a pointwise lower bound for every seed. -/
theorem exists_index_integral_gt_of_average_gt
    (μ : Measure Ω) [IsProbabilityMeasure μ]
    (s : Finset ι) (hs : s.Nonempty) (f : ι → Ω → ℝ)
    (hf : ∀ i ∈ s, Measurable (f i))
    (hrange : ∀ i ∈ s, ∀ r, f i r ∈ Icc (0 : ℝ) 1)
    {delta : ℝ} (h : ∀ r, delta < (∑ i ∈ s, f i r) / s.card) :
    ∃ i ∈ s, delta < ∫ r, f i r ∂μ := by
  classical
  have hcard : (0 : ℝ) < s.card := by exact_mod_cast hs.card_pos
  have hfi (i : ι) (hi : i ∈ s) : Integrable (f i) μ :=
    Integrable.of_mem_Icc 0 1 (hf i hi).aemeasurable (ae_of_all _ (hrange i hi))
  have hsum : Integrable (fun r ↦ ∑ i ∈ s, f i r) μ := integrable_finsetSum s hfi
  have havg := integral_strictly_above_constant μ
    (fun r ↦ (∑ i ∈ s, f i r) / s.card) (hsum.div_const _) h
  rw [integral_div, integral_finsetSum _ hfi] at havg
  have hstrict : (s.card : ℝ) * delta < ∑ i ∈ s, ∫ r, f i r ∂μ := by
    have hh := (lt_div_iff₀ hcard).1 havg
    simpa only [mul_comm] using hh
  by_contra hn
  push Not at hn
  have hupper := Finset.sum_le_sum (s := s) hn
  simp only [Finset.sum_const, nsmul_eq_mul] at hupper
  exact (not_lt_of_ge hupper) hstrict

end

end MsetsPaper.Probability
