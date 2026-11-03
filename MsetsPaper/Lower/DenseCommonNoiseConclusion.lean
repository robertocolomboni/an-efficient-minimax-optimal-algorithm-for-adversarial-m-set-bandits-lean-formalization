import MsetsPaper.Lower.DenseCommonNoiseTail

/-! # P3: the new common-noise dense lower bound

This endpoint uses the losses, sign flip, common-noise tower, and fixed table
developed in the preceding modules. It does not invoke the old dense lower
bound or the old paired-Bernoulli witness.
-/

namespace MsetsPaper.Lower.DenseCommonNoise

open MsetsLower MsetsLower.Feedback MsetsLower.Lower MeasureTheory ProbabilityTheory Set
open scoped ENNReal ProbabilityTheory BigOperators

noncomputable section

theorem log_choose_le_dim_log_two {d m : ℕ} (hmd : m ≤ d) :
    Real.log (d.choose m : ℝ) ≤ (d : ℝ) * Real.log 2 := by
  have hpos : (0 : ℝ) < d.choose m := by exact_mod_cast Nat.choose_pos hmd
  have hchoose : (d.choose m : ℝ) ≤ (2 : ℝ) ^ d := by
    exact_mod_cast Nat.choose_le_two_pow d m
  have h := Real.log_le_log hpos hchoose
  rwa [Real.log_pow] at h

theorem log_choose_lt_dim {d m : ℕ} (hd : 0 < d) (hmd : m ≤ d) :
    Real.log (d.choose m : ℝ) < (d : ℝ) := by
  have hlogTwo : Real.log (2 : ℝ) < 1 := by
    have h := Real.log_lt_sub_one_of_pos (by norm_num : (0 : ℝ) < 2)
      (by norm_num : (2 : ℝ) ≠ 1)
    norm_num at h
    exact h
  calc
    _ ≤ (d : ℝ) * Real.log 2 := log_choose_le_dim_log_two hmd
    _ < (d : ℝ) * 1 := mul_lt_mul_of_pos_left
      hlogTwo (by exact_mod_cast hd)
    _ = _ := mul_one _

theorem sqrt_dim_time_log_choose_lt {d m T : ℕ}
    (hd : 0 < d) (hmd : m ≤ d) (hT : 0 < T) :
    Real.sqrt ((d : ℝ) * T * Real.log (d.choose m : ℝ)) <
      (d : ℝ) * Real.sqrt T := by
  have hinside : (d : ℝ) * T * Real.log (d.choose m : ℝ) < (d : ℝ) ^ 2 * T := by
    calc
      _ < (d : ℝ) * T * d := mul_lt_mul_of_pos_left (log_choose_lt_dim hd hmd) (by positivity)
      _ = _ := by ring
  calc
    _ < Real.sqrt ((d : ℝ) ^ 2 * T) := Real.sqrt_lt_sqrt (by positivity) hinside
    _ = (d : ℝ) * Real.sqrt T := by
      rw [Real.sqrt_mul (sq_nonneg (d : ℝ)), Real.sqrt_sq_eq_abs,
        abs_of_nonneg (Nat.cast_nonneg d)]

/-- Both strict comparisons displayed in the dense proof, not just their
weaker non-strict consequence used to transfer the tail event. -/
theorem dense_threshold_strict_comparisons {d m T : ℕ}
    (hm : 0 < m) (h2m : 2 * m ≤ d) (hT : 0 < T)
    (hr : (2 : ℝ) ^ (-32 : ℤ) < (m : ℝ) / d) :
    (2 : ℝ) ^ (-42 : ℤ) *
        Real.sqrt ((d : ℝ) * T * Real.log (d.choose m : ℝ)) <
      (2 : ℝ) ^ (-42 : ℤ) * d * Real.sqrt T ∧
    (2 : ℝ) ^ (-42 : ℤ) * d * Real.sqrt T < (m : ℝ) * Real.sqrt T / 1024 := by
  have hd : 0 < d := by omega
  have hdR : (0 : ℝ) < d := by exact_mod_cast hd
  have hmgt : (2 : ℝ) ^ (-32 : ℤ) * d < m := (lt_div_iff₀ hdR).1 hr
  have hc : (2 : ℝ) ^ (-42 : ℤ) * d < (m : ℝ) / 1024 := by
    norm_num at hmgt ⊢
    linarith
  constructor
  · simpa only [mul_assoc] using mul_lt_mul_of_pos_left
      (sqrt_dim_time_log_choose_lt hd (by omega) hT)
      (by positivity : (0 : ℝ) < (2 : ℝ) ^ (-42 : ℤ))
  · have hspos : 0 < Real.sqrt (T : ℝ) := by positivity
    simpa only [div_mul_eq_mul_div] using mul_lt_mul_of_pos_right hc hspos

/-- Stronger itemwise P3 guarantee for every randomized policy, with deterministic
oblivious item losses, exact horizon and numerical constants from the paper. -/
theorem lower_action_count_dense {d m T : ℕ}
    (hm : 1 ≤ m) (h2m : 2 * m ≤ d) (hT : 64 * d ^ 2 ≤ T)
    (hr : (2 : ℝ) ^ (-32 : ℤ) < (m : ℝ) / d) (P : Policy d m) :
    ∃ L : LossProcess d m,
      (∀ t (h h' : History d m t), L.itemLoss t h = L.itemLoss t h') ∧
      (∀ t (h : History d m t) i, L.itemLoss t h i ∈ Icc (0 : ℝ) (1 / m)) ∧
      (2 : ℝ) ^ (-14 : ℤ) ≤ (runLaw P L T).real
        {h | (2 : ℝ) ^ (-42 : ℤ) *
          Real.sqrt ((d : ℝ) * T * Real.log (d.choose m : ℝ)) ≤ pathRegret L T h} := by
  have hm0 : 0 < m := by omega
  have hd : 0 < d := by omega
  have hTweak : d ^ 2 ≤ T := by nlinarith
  have ht : 0 < T := lt_of_lt_of_le (pow_pos hd 2) hTweak
  obtain ⟨L, hobl, hitem, htail⟩ :=
    exists_oblivious_dense_table_natural_threshold P hm0 h2m hTweak
  refine ⟨L, hobl, hitem, ?_⟩
  have hcomparison := dense_threshold_strict_comparisons hm0 h2m ht hr
  have hsubset : {h : History d m T | (m : ℝ) * Real.sqrt T / 1024 ≤ pathRegret L T h} ⊆
      {h | (2 : ℝ) ^ (-42 : ℤ) *
        Real.sqrt ((d : ℝ) * T * Real.log (d.choose m : ℝ)) ≤ pathRegret L T h} := by
    intro h hh
    exact (hcomparison.1.trans hcomparison.2).le.trans hh
  calc
    (2 : ℝ) ^ (-14 : ℤ) ≤ (1 : ℝ) / 16 := by norm_num
    _ ≤ _ := htail
    _ ≤ _ := ENNReal.toReal_mono (measure_ne_top _ _) (measure_mono hsubset)

/-- Paper-facing P3: the deterministic oblivious witness has every action
loss in [0,1]. The itemwise construction remains available above. -/
theorem lower_action_count_dense_action_losses {d m T : ℕ}
    (hm : 1 ≤ m) (h2m : 2 * m ≤ d) (hT : 64 * d ^ 2 ≤ T)
    (hr : (2 : ℝ) ^ (-32 : ℤ) < (m : ℝ) / d) (P : Policy d m) :
    ∃ L : LossProcess d m,
      (∀ t (h h' : History d m t), L.itemLoss t h = L.itemLoss t h') ∧
      (∀ t (h : History d m t) (a : MSetAction d m),
        actionLoss a (L.itemLoss t h) ∈ Icc (0 : ℝ) 1) ∧
      (2 : ℝ) ^ (-14 : ℤ) ≤ (runLaw P L T).real
        {h | (2 : ℝ) ^ (-42 : ℤ) *
          Real.sqrt ((d : ℝ) * T * Real.log (d.choose m : ℝ)) ≤ pathRegret L T h} := by
  obtain ⟨L, ho, _hitem, htail⟩ := lower_action_count_dense hm h2m hT hr P
  exact ⟨L, ho, L.action_mem_Icc, htail⟩

end

end MsetsPaper.Lower.DenseCommonNoise
