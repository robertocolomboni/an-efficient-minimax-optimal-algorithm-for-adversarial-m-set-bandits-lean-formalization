import MsetsPaper.Lower.SparseCappedSurvival
import MsetsPaper.Lower.SparseCappedComparatorMean
import MsetsPaper.Lower.SparseCappedThreshold
import MsetsPaper.Lower.Foundations
import MsetsPaper.Probability.ProductFixingBridge

/-! # P2: the actual capped Bernoulli lower bound with exact constants -/

namespace MsetsPaper.Lower.SparseCapped

open MsetsLower MsetsLower.Lower MeasureTheory ProbabilityTheory Set
open scoped BigOperators ENNReal ProbabilityTheory

noncomputable section

theorem integral_topScore_ge_twenty_nine {d m T : ℕ}
    (P : Policy d m) (hm : 0 < m) (hmd : m ≤ d) (hT : 64 * d ^ 2 ≤ T + 1)
    (hcut : ratio d m ≤ 1 / (2 : ℝ) ^ 32) :
    (29 / 48 : ℝ) * m * (T + 1) ≤
      ∫ x, topScore m (itemScore (selectionCap d m (T + 1)) x.1 (T + 1) x.2)
        ∂jointLaw P hm (selectionCap d m (T + 1)) (perturbation d m (T + 1))
          (perturbation_nonneg d m (T + 1)) (perturbation_lt_sixteenth hm hmd hT).le
          (T + 1) (T + 1) := by
  have h := integral_topScore_ge_shape_sub_bad P hm hmd (selectionCap d m (T + 1))
    (perturbation d m (T + 1)) (perturbation_nonneg d m (T + 1))
    (perturbation_lt_sixteenth hm hmd hT).le T
  have hb := badSurvival_probability_le P hm hmd hT hcut
  have hmul := mul_le_mul_of_nonneg_left hb
    (by positivity : (0 : ℝ) ≤ m * (T + 1))
  nlinarith

theorem integral_deficit_ge_four_thirtyseven {d m T : ℕ}
    (P : Policy d m) (hm : 0 < m) (hmd : m ≤ d) (hT : 64 * d ^ 2 ≤ T + 1)
    (hcut : ratio d m ≤ 1 / (2 : ℝ) ^ 32) :
    (437 / 768 : ℝ) * m * (T + 1) ≤
      ∫ x, deficit (selectionCap d m (T + 1)) x.1 (T + 1) x.2
        ∂jointLaw P hm (selectionCap d m (T + 1)) (perturbation d m (T + 1))
          (perturbation_nonneg d m (T + 1)) (perturbation_lt_sixteenth hm hmd hT).le
          (T + 1) (T + 1) := by
  unfold deficit
  letI := jointLaw_isProbabilityMeasure P hm (selectionCap d m (T + 1))
    (perturbation d m (T + 1)) (perturbation_nonneg d m (T + 1))
    (perturbation_lt_sixteenth hm hmd hT).le (T + 1) (T + 1)
  rw [integral_sub (integrable_topScore hmd _ _) (integrable_learnerScore hmd _ _)]
  have htop := integral_topScore_ge_twenty_nine P hm hmd hT hcut
  have hlearner := integral_learnerScore_le_nine P hm hmd hT
  push_cast at hlearner
  linarith

/-- No nonnegativity assumption about the deficit is made. -/
theorem deficit_joint_tail {d m T : ℕ}
    (P : Policy d m) (hm : 0 < m) (hmd : m ≤ d) (hT : 64 * d ^ 2 ≤ T + 1)
    (hcut : ratio d m ≤ 1 / (2 : ℝ) ^ 32) :
    (1 : ℝ) / 8 ≤ (jointLaw P hm (selectionCap d m (T + 1)) (perturbation d m (T + 1))
      (perturbation_nonneg d m (T + 1)) (perturbation_lt_sixteenth hm hmd hT).le
      (T + 1) (T + 1)).real
      {x | (m : ℝ) * (T + 1) / 8 ≤ deficit (selectionCap d m (T + 1)) x.1 (T + 1) x.2} := by
  letI := jointLaw_isProbabilityMeasure P hm (selectionCap d m (T + 1))
    (perturbation d m (T + 1)) (perturbation_nonneg d m (T + 1))
    (perturbation_lt_sixteenth hm hmd hT).le (T + 1) (T + 1)
  apply MsetsPaper.Lower.deficit_tail_one_eighth _ _ (measurable_deficit _ _)
    (integrable_deficit hmd _ _)
  · positivity
  · have hmean := integral_deficit_ge_four_thirtyseven P hm hmd hT hcut
    have hmT : (0 : ℝ) ≤ m * (T + 1) := by positivity
    nlinarith
  · exact ae_of_all _ fun x => by
      simpa only [Nat.cast_add, Nat.cast_one] using deficit_le hmd _ x.1 (T + 1) x.2

theorem eta_scaled_threshold {m T : ℕ} (hm : 0 < m) (eta : ℝ) :
    eta / m * ((m : ℝ) * T / 8) = eta * T / 8 := by
  have hm0 : (m : ℝ) ≠ 0 := by exact_mod_cast Nat.ne_of_gt hm
  field_simp

/-- The deficit tail is transferred to the literal external-regret event. -/
theorem regret_joint_tail {d m T : ℕ}
    (P : Policy d m) (hm : 0 < m) (hmd : m ≤ d) (hT : 64 * d ^ 2 ≤ T + 1)
    (hcut : ratio d m ≤ 1 / (2 : ℝ) ^ 32) :
    (1 : ℝ) / 8 ≤ (jointLaw P hm (selectionCap d m (T + 1)) (perturbation d m (T + 1))
      (perturbation_nonneg d m (T + 1)) (perturbation_lt_sixteenth hm hmd hT).le
      (T + 1) (T + 1)).real
      (parametricRegretEvent
        (tableLossProcess hm (selectionCap d m (T + 1)) (perturbation d m (T + 1))
          (perturbation_nonneg d m (T + 1)) (perturbation_lt_sixteenth hm hmd hT).le (T + 1))
        (T + 1) ((1 / (2 : ℝ) ^ 24) *
          Real.sqrt ((d : ℝ) * (T + 1) * Real.log (d.choose m : ℝ)))) := by
  let c := selectionCap d m (T + 1)
  let eta := perturbation d m (T + 1)
  have he := perturbation_nonneg d m (T + 1)
  have hs := (perturbation_lt_sixteenth hm hmd hT).le
  let L := tableLossProcess (d := d) hm c eta he hs (T + 1)
  letI := jointLaw_isProbabilityMeasure P hm c eta he hs (T + 1) (T + 1)
  letI : Nonempty (MSetAction d m) := nonempty_MSetAction hmd
  have hpath (x : Table d (T + 1) × History d m (T + 1)) :
      parametricPathRegret L (T + 1) x = eta / m * deficit c x.1 (T + 1) x.2 := by
    rw [show x = (x.1, x.2) from rfl, parametricPathRegret_eq_at]
    exact pathRegret_eq_scaled_deficit hm hmd c eta he hs (T + 1) x.1 (T + 1) x.2
  have hcomp := sparse_threshold_comparisons hm hmd hT hcut
  have hthreshold : (1 / (2 : ℝ) ^ 24) *
      Real.sqrt ((d : ℝ) * (T + 1) * Real.log (d.choose m : ℝ)) ≤ eta * (T + 1) / 8 := by
    simpa only [Nat.cast_add, Nat.cast_one] using hcomp.2.trans hcomp.1
  have hsubset : {x : Table d (T + 1) × History d m (T + 1) |
      (m : ℝ) * (T + 1) / 8 ≤ deficit c x.1 (T + 1) x.2} ⊆
      parametricRegretEvent L (T + 1) ((1 / (2 : ℝ) ^ 24) *
        Real.sqrt ((d : ℝ) * (T + 1) * Real.log (d.choose m : ℝ))) := by
    intro x hx
    change _ ≤ parametricPathRegret L (T + 1) x
    rw [hpath]
    have hscaled := mul_le_mul_of_nonneg_left hx (div_nonneg he (Nat.cast_nonneg m))
    have heq : eta / m * ((m : ℝ) * (T + 1) / 8) = eta * (T + 1) / 8 := by
      have hm0 : (m : ℝ) ≠ 0 := by exact_mod_cast Nat.ne_of_gt hm
      field_simp
    rw [heq] at hscaled
    exact hthreshold.trans hscaled
  exact (deficit_joint_tail P hm hmd hT hcut).trans
    (ENNReal.toReal_mono (measure_ne_top _ _) (measure_mono hsubset))

/-- Fix the adversary table after all randomized-policy runs are averaged. The
resulting losses remain adaptive and non-anticipating, not falsely oblivious. -/
theorem exists_sparse_table_successor {d m T : ℕ}
    (P : Policy d m) (hm : 0 < m) (hmd : m ≤ d) (hT : 64 * d ^ 2 ≤ T + 1)
    (hcut : ratio d m ≤ 1 / (2 : ℝ) ^ 32) :
    ∃ L : LossProcess d m,
      (∀ t (h : History d m t) i, L.itemLoss t h i ∈ Icc (0 : ℝ) (1 / m)) ∧
      (1 : ℝ) / 8 ≤ (runLaw P L (T + 1)).real
        {h | (1 / (2 : ℝ) ^ 24) *
          Real.sqrt ((d : ℝ) * (T + 1) * Real.log (d.choose m : ℝ)) ≤ pathRegret L (T + 1) h} := by
  let c := selectionCap d m (T + 1)
  let eta := perturbation d m (T + 1)
  have he := perturbation_nonneg d m (T + 1)
  have hs := (perturbation_lt_sixteenth hm hmd hT).le
  obtain ⟨xi, hxi⟩ := MsetsPaper.Probability.exists_fixed_parametric_regret_via_product
    hmd (tableMeasure d (T + 1)) P
    (tableLossProcess hm c eta he hs (T + 1)) (T + 1)
    ((1 / (2 : ℝ) ^ 24) * Real.sqrt ((d : ℝ) * (T + 1) * Real.log (d.choose m : ℝ)))
    ((1 : ℝ) / 8) (regret_joint_tail P hm hmd hT hcut)
  exact ⟨(tableLossProcess hm c eta he hs (T + 1)).at xi,
    tableLossProcess_item_mem_Icc hm c eta he hs (T + 1) xi, hxi⟩

/-- Stronger itemwise form of P2, proved by its capped Bernoulli experiment. -/
theorem lower_action_count_sparse {d m T : ℕ}
    (hm : 1 ≤ m) (h2m : 2 * m ≤ d) (hT : 64 * d ^ 2 ≤ T)
    (hr : (m : ℝ) / d ≤ (2 : ℝ) ^ (-32 : ℤ)) (P : Policy d m) :
    ∃ L : LossProcess d m,
      (∀ t (h : History d m t) i, L.itemLoss t h i ∈ Icc (0 : ℝ) (1 / m)) ∧
      (1 : ℝ) / 8 ≤ (runLaw P L T).real
        {h | (2 : ℝ) ^ (-24 : ℤ) *
          Real.sqrt ((d : ℝ) * T * Real.log (d.choose m : ℝ)) ≤ pathRegret L T h} := by
  have hm0 : 0 < m := by omega
  have hmd : m ≤ d := by omega
  have hcut : ratio d m ≤ 1 / (2 : ℝ) ^ 32 := by
    norm_num [ratio] at hr ⊢
    exact hr
  cases T with
  | zero =>
      have hd : 0 < d := by omega
      exact False.elim ((not_le_of_gt (show 0 < 64 * d ^ 2 by positivity)) hT)
  | succ T =>
      have h := exists_sparse_table_successor P hm0 hmd hT hcut
      norm_num only [zpow_neg, zpow_ofNat, pow_succ, pow_zero, one_mul, Nat.cast_add,
        Nat.cast_one] at h ⊢
      exact h

/-- Paper-facing P2: every action has loss in [0,1]. The stronger itemwise
construction remains available as `lower_action_count_sparse`. -/
theorem lower_action_count_sparse_action_losses {d m T : ℕ}
    (hm : 1 ≤ m) (h2m : 2 * m ≤ d) (hT : 64 * d ^ 2 ≤ T)
    (hr : (m : ℝ) / d ≤ (2 : ℝ) ^ (-32 : ℤ)) (P : Policy d m) :
    ∃ L : LossProcess d m,
      (∀ t (h : History d m t) (a : MSetAction d m),
        actionLoss a (L.itemLoss t h) ∈ Icc (0 : ℝ) 1) ∧
      (1 : ℝ) / 8 ≤ (runLaw P L T).real
        {h | (2 : ℝ) ^ (-24 : ℤ) *
          Real.sqrt ((d : ℝ) * T * Real.log (d.choose m : ℝ)) ≤ pathRegret L T h} := by
  obtain ⟨L, _hitem, htail⟩ := lower_action_count_sparse hm h2m hT hr P
  exact ⟨L, L.action_mem_Icc, htail⟩

end

end MsetsPaper.Lower.SparseCapped
