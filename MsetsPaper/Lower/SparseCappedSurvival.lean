import MsetsPaper.Lower.SparseCappedSeedJensen
import MsetsPaper.Lower.SparseCappedSurvivalArithmetic

/-! # The actual sparse survival probability -/

namespace MsetsPaper.Lower.SparseCapped

open MsetsLower MeasureTheory ProbabilityTheory Set
open MsetsPaper.Probability
open scoped ENNReal ProbabilityTheory

noncomputable section

theorem average_false_le_three_sixtyfour {d m T : ℕ}
    (P : Policy d m) (hm : 0 < m) (hmd : m ≤ d) (hT : 64 * d ^ 2 ≤ T + 1)
    (hcut : ratio d m ≤ 1 / (2 : ℝ) ^ 32) :
    averageTestProbability P hm (selectionCap d m (T + 1)) (perturbation d m (T + 1))
      (perturbation_nonneg d m (T + 1)) (perturbation_lt_sixteenth hm hmd hT).le T false ≤
      3 / 64 := by
  let c := selectionCap d m (T + 1)
  let eta := perturbation d m (T + 1)
  have he := perturbation_nonneg d m (T + 1)
  have hs := (perturbation_lt_sixteenth hm hmd hT).le
  let a := averageTestProbability P hm c eta he hs T false
  let b := averageTestProbability P hm c eta he hs T true
  have ha := averageTestProbability_mem_Icc P hm hmd c eta he hs T false
  have hb := averageTestProbability_mem_Icc P hm hmd c eta he hs T true
  have hbsmall : b ≤ 256 * ratio d m := average_true_le_ratio P hm hmd c eta he hs T
  have hcomp : BinaryCompatible a b := averageTestProbability_compatible P hm hmd c eta he hs T
  change a ≤ 3 / 64
  by_cases hzero : b = 0
  · rw [hcomp.1 hzero]
    norm_num
  have hbpos : 0 < b := lt_of_le_of_ne hb.1 (Ne.symm hzero)
  have hblt : b < 1 := by
    have hbound := mul_le_mul_of_nonneg_left hcut (by norm_num : (0 : ℝ) ≤ 256)
    norm_num at hbound
    linarith
  apply sparse_entropy_probability_le ha.1 hbpos (ratio_pos hm hmd) hcut hbsmall
  exact (binaryKL_lower_bound ha.1 ha.2 hbpos hblt).trans
    (binaryKL_average_le_log_via_private_seeds P hm hmd hT)

/-- P(N<m)<=1/16 in the true bit/history marginal of the table experiment. -/
theorem badSurvival_probability_le {d m T : ℕ}
    (P : Policy d m) (hm : 0 < m) (hmd : m ≤ d) (hT : 64 * d ^ 2 ≤ T + 1)
    (hcut : ratio d m ≤ 1 / (2 : ℝ) ^ 32) :
    (bitsHistoryLaw P hm (selectionCap d m (T + 1)) (perturbation d m (T + 1))
      (perturbation_nonneg d m (T + 1)) (perturbation_lt_sixteenth hm hmd hT).le (T + 1)).real
      (badSurvival (selectionCap d m (T + 1)) T) ≤ 1 / 16 := by
  let c := selectionCap d m (T + 1)
  let eta := perturbation d m (T + 1)
  have he := perturbation_nonneg d m (T + 1)
  have hs := (perturbation_lt_sixteenth hm hmd hT).le
  have hcount := average_false_controls_bad P hm hmd c (selectionCap_pos hm hmd hT)
    eta he hs T (selectionCap_budget hm hmd)
  have hsmall : ratio d m ≤ 1 / 8 := hcut.trans (by norm_num)
  obtain ⟨h₁, h₂⟩ := sparse_counting_probability_le measureReal_nonneg hsmall
    (average_false_le_three_sixtyfour P hm hmd hT hcut) hcount
  exact h₁.trans h₂

end

end MsetsPaper.Lower.SparseCapped
