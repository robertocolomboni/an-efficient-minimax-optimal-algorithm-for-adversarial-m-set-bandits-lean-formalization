import MsetsPaper.Lower.DenseCommonNoiseMean
import MsetsPaper.Lower.Foundations
import MsetsPaper.Probability.ProductFixingBridge

/-! # Positive deficit, regret tail, and fixing the dense noise table -/

namespace MsetsPaper.Lower.DenseCommonNoise

open MsetsLower MsetsLower.Feedback MsetsLower.Lower MeasureTheory ProbabilityTheory Set
open scoped ENNReal ProbabilityTheory BigOperators

noncomputable section

theorem integral_deficit_joint_ge {d m T : ℕ}
    (P : Policy d m) (hm : 0 < m) (h2m : 2 * m ≤ d) (hT : d ^ 2 ≤ T) :
    let ht : 0 < T := lt_of_lt_of_le (pow_pos (by omega : 0 < d) 2) hT
    let he := (eta_pos hm ht).le
    let hs := (eta_le_one_div_256 hm h2m hT).trans (by norm_num : (1:ℝ)/256 ≤ 1/16)
    (m : ℝ) * T / 4 ≤
      ∫ x, deficit h2m x.1 T x.2 ∂jointLaw P hm (eta m T) he hs T T := by
  dsimp only
  unfold deficit
  rw [integral_sub (integrable_comparatorScore h2m _) (integrable_learnerScore _),
    integral_comparatorScore_joint]
  have hlearner := integral_learnerScore_joint_le P hm h2m hT
  dsimp only at hlearner
  linarith

/-- The deficit need not be nonnegative. Its mean and its one-sided upper
bound suffice for the manuscript's `1/16` probability estimate. -/
theorem deficit_joint_tail {d m T : ℕ}
    (P : Policy d m) (hm : 0 < m) (h2m : 2 * m ≤ d) (hT : d ^ 2 ≤ T) :
    let ht : 0 < T := lt_of_lt_of_le (pow_pos (by omega : 0 < d) 2) hT
    let he := (eta_pos hm ht).le
    let hs := (eta_le_one_div_256 hm h2m hT).trans (by norm_num : (1:ℝ)/256 ≤ 1/16)
    (1 : ℝ) / 16 ≤ (jointLaw P hm (eta m T) he hs T T).real
      {x | (m : ℝ) * T / 8 ≤ deficit h2m x.1 T x.2} := by
  dsimp only
  apply MsetsPaper.Lower.deficit_tail_one_sixteenth _ _ (measurable_deficit h2m T)
    (integrable_deficit h2m _)
  · have ht : 0 < T := lt_of_lt_of_le (pow_pos (by omega : 0 < d) 2) hT
    positivity
  · exact integral_deficit_joint_ge P hm h2m hT
  · exact ae_of_all _ fun x => (le_abs_self _).trans (by
      simpa only [mul_assoc] using abs_deficit_le h2m x.1 T x.2)

theorem eta_scaled_threshold {m T : ℕ} (hm : 0 < m) (hT : 0 < T) :
    eta m T / m * ((m : ℝ) * T / 8) = (m : ℝ) * Real.sqrt T / 1024 := by
  have hm0 : (m : ℝ) ≠ 0 := by exact_mod_cast Nat.ne_of_gt hm
  have hs0 : Real.sqrt (T : ℝ) ≠ 0 := ne_of_gt (by positivity)
  have hsq := Real.sq_sqrt (show (0 : ℝ) ≤ T by positivity)
  unfold eta
  field_simp
  nlinarith

/-- The regret event is the actual external-regret event, not the deficit
event renamed. The transfer is proved by pointwise event containment. -/
theorem regret_joint_tail {d m T : ℕ}
    (P : Policy d m) (hm : 0 < m) (h2m : 2 * m ≤ d) (hT : d ^ 2 ≤ T) :
    let ht : 0 < T := lt_of_lt_of_le (pow_pos (by omega : 0 < d) 2) hT
    let he := (eta_pos hm ht).le
    let hs := (eta_le_one_div_256 hm h2m hT).trans (by norm_num : (1:ℝ)/256 ≤ 1/16)
    (1 : ℝ) / 16 ≤ (jointLaw P hm (eta m T) he hs T T).real
      (parametricRegretEvent (tableLossProcess hm (eta m T) he hs T) T
        ((m : ℝ) * Real.sqrt T / 1024)) := by
  dsimp only
  have ht : 0 < T := lt_of_lt_of_le (pow_pos (by omega : 0 < d) 2) hT
  have he := (eta_pos hm ht).le
  have hs := (eta_le_one_div_256 hm h2m hT).trans (by norm_num : (1:ℝ)/256 ≤ 1/16)
  letI : Nonempty (MSetAction d m) := nonempty_MSetAction (by omega)
  have hpath : ∀ x : Table m T × History d m T,
      eta m T / m * deficit h2m x.1 T x.2 ≤
        parametricPathRegret (tableLossProcess hm (eta m T) he hs T) T x := by
    intro x
    rw [show x = (x.1, x.2) from rfl, parametricPathRegret_eq_at]
    exact scaled_deficit_le_pathRegret hm h2m (eta m T) he hs T x.1 T x.2
  have htail := MsetsPaper.Lower.scaled_regret_tail_of_deficit_tail
    (jointLaw P hm (eta m T) he hs T T) (fun x => deficit h2m x.1 T x.2)
    (parametricPathRegret (tableLossProcess hm (eta m T) he hs T) T)
    (div_nonneg he (Nat.cast_nonneg m)) (ae_of_all _ hpath)
    (deficit_joint_tail P hm h2m hT)
  simpa only [eta_scaled_threshold hm ht, parametricRegretEvent] using htail

/-- Fix all signs and all common noises only after the policy's randomness
has been averaged. The resulting witness is deterministic and oblivious. -/
theorem exists_oblivious_dense_table_natural_threshold {d m T : ℕ}
    (P : Policy d m) (hm : 0 < m) (h2m : 2 * m ≤ d) (hT : d ^ 2 ≤ T) :
    ∃ L : LossProcess d m,
      (∀ t (h h' : History d m t), L.itemLoss t h = L.itemLoss t h') ∧
      (∀ t (h : History d m t) i, L.itemLoss t h i ∈ Icc (0 : ℝ) (1 / m)) ∧
      (1 : ℝ) / 16 ≤ (runLaw P L T).real
        {h | (m : ℝ) * Real.sqrt T / 1024 ≤ pathRegret L T h} := by
  have ht : 0 < T := lt_of_lt_of_le (pow_pos (by omega : 0 < d) 2) hT
  have he := (eta_pos hm ht).le
  have hs := (eta_le_one_div_256 hm h2m hT).trans (by norm_num : (1:ℝ)/256 ≤ 1/16)
  obtain ⟨xi, hxi⟩ := MsetsPaper.Probability.exists_fixed_parametric_regret_via_product
    (by omega : m ≤ d)
    (tableMeasure m T) P (tableLossProcess hm (eta m T) he hs T) T
    ((m : ℝ) * Real.sqrt T / 1024) ((1 : ℝ) / 16) (regret_joint_tail P hm h2m hT)
  refine ⟨(tableLossProcess hm (eta m T) he hs T).at xi, ?_, ?_, hxi⟩
  · exact tableLossProcess_oblivious hm (eta m T) he hs T xi
  · exact tableLossProcess_item_mem_Icc hm (eta m T) he hs T xi

end

end MsetsPaper.Lower.DenseCommonNoise
