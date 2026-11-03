import Mathlib.Probability.Distributions.Uniform
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Tactic

/-! The expectation lower bound alone does not give a constant-probability
square-root lower tail. The probability space has n+1 equally likely points. -/
namespace MsetsPaper.Alignment.LowerMeanCounterexample
open MeasureTheory Filter Set
open scoped ENNReal Topology BigOperators
noncomputable section

def law (n : ℕ) : Measure (Fin (n + 1)) := Measure.uniformOfFinset Finset.univ

def reward (n : ℕ) (i : Fin (n + 1)) : ℝ := if i = 0 then (n + 1 : ℝ) ^ 2 else 0

instance law_probability (n : ℕ) : IsProbabilityMeasure (law n) where
  measure_univ := by
    simp [law, Measure.uniformOfFinset_apply, ENNReal.div_self]

theorem reward_bounds (n : ℕ) (i : Fin (n + 1)) :
    0 ≤ reward n i ∧ reward n i ≤ (n + 1 : ℝ) ^ 2 := by
  unfold reward
  split_ifs
  · exact ⟨sq_nonneg _, le_rfl⟩
  · exact ⟨le_rfl, sq_nonneg _⟩

theorem reward_mean (n : ℕ) : ∫ i, reward n i ∂law n = (n + 1 : ℝ) := by
  rw [integral_fintype .of_finite]
  simp [reward, law, measureReal_def, Measure.uniformOfFinset_apply_singleton,
    ENNReal.toReal_inv, ENNReal.toReal_add, smul_eq_mul]
  have hn : (n + 1 : ℝ) ≠ 0 := by positivity
  field_simp

theorem reward_mean_eq_sqrt_horizon (n : ℕ) :
    ∫ i, reward n i ∂law n = Real.sqrt ((n + 1 : ℝ) ^ 2) := by
  rw [reward_mean, Real.sqrt_sq (by positivity)]

theorem half_mean_tail (n : ℕ) :
    (law n).real {i | (n + 1 : ℝ) / 2 ≤ reward n i} = 1 / (n + 1 : ℝ) := by
  have hevent : {i | (n + 1 : ℝ) / 2 ≤ reward n i} = ({0} : Set (Fin (n + 1))) := by
    ext i
    have hn : (1 : ℝ) ≤ n + 1 := by linarith [Nat.cast_nonneg (α := ℝ) n]
    by_cases hi : i = 0
    · subst i
      have hh : (n + 1 : ℝ) / 2 ≤ (n + 1 : ℝ) ^ 2 := by nlinarith
      simp [reward, hh]
    · have hh : ¬ (n + 1 : ℝ) / 2 ≤ 0 := not_le.mpr (by positivity)
      simp [reward, hi, hh]
  rw [hevent]
  simp [law, measureReal_def, Measure.uniformOfFinset_apply_singleton,
    ENNReal.toReal_inv, ENNReal.toReal_add, one_div]

theorem half_mean_tail_tendsto_zero :
    Tendsto (fun n => (law n).real {i | (n + 1 : ℝ) / 2 ≤ reward n i}) atTop (𝓝 0) := by
  simp_rw [half_mean_tail]
  exact tendsto_one_div_add_atTop_nhds_zero_nat

/-- In fact every fixed positive multiple of sqrt(T) has vanishing tail. -/
theorem scaled_sqrt_tail_tendsto_zero (a : ℝ) (ha : 0 < a) :
    Tendsto (fun n => (law n).real {i | a * (n + 1 : ℝ) ≤ reward n i}) atTop (𝓝 0) := by
  apply squeeze_zero (fun n => measureReal_nonneg) (g := fun n : ℕ => 1 / (n + 1 : ℝ))
  · intro n
    have hsub : {i | a * (n + 1 : ℝ) ≤ reward n i} ⊆ ({0} : Set (Fin (n + 1))) := by
      intro i hi
      by_contra hnot
      have hi0 : i ≠ 0 := by simpa only [mem_singleton_iff] using hnot
      have hpos : 0 < a * (n + 1 : ℝ) := mul_pos ha (by positivity)
      simp only [mem_setOf_eq, reward, if_neg hi0] at hi
      exact (not_le_of_gt hpos) hi
    have hh := measureReal_mono (μ := law n) hsub
    simpa [law, measureReal_def, Measure.uniformOfFinset_apply_singleton,
      ENNReal.toReal_inv, ENNReal.toReal_add, one_div] using hh
  · exact tendsto_one_div_add_atTop_nhds_zero_nat

theorem no_eventual_sqrt_tail_lower_bound (a p : ℝ) (ha : 0 < a) (hp : 0 < p) :
    ¬ ∀ᶠ n in atTop, p ≤ (law n).real {i | a * (n + 1 : ℝ) ≤ reward n i} := by
  intro h
  have hsmall := (scaled_sqrt_tail_tendsto_zero a ha).eventually (gt_mem_nhds hp)
  obtain ⟨n, hn, hnp⟩ := (h.and hsmall).exists
  exact (not_lt_of_ge hn) hnp

/-- No positive constant lower bound on these square-root tail probabilities
can hold even eventually, although the means are exactly sqrt(T). -/
theorem no_eventual_positive_tail (c : ℝ) (hc : 0 < c) :
    ¬ ∀ᶠ n in atTop, c ≤ (law n).real {i | (n + 1 : ℝ) / 2 ≤ reward n i} := by
  intro h
  have hsmall := half_mean_tail_tendsto_zero.eventually (gt_mem_nhds hc)
  obtain ⟨n, hn, hnc⟩ := (h.and hsmall).exists
  exact (not_lt_of_ge hn) hnc

end
end MsetsPaper.Alignment.LowerMeanCounterexample
