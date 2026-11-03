import MsetsPaper.Lower.SparseCappedSurvivalProbability

/-! # Comparator mean from the actual survival event, without independence -/

namespace MsetsPaper.Lower.SparseCapped

open MsetsLower MsetsLower.Feedback MeasureTheory ProbabilityTheory Set
open scoped BigOperators ENNReal ProbabilityTheory

noncomputable section

theorem measurable_shapeSum {d T : ℕ} (t : ℕ) :
    Measurable (fun xi : Table d T => shapeSum xi t) := by
  unfold shapeSum
  exact Finset.measurable_sum _ (fun r _ => measurable_shape.comp (measurable_tableNoise r))

theorem integral_shapeSum_table (d T : ℕ) :
    (∫ xi : Table d T, shapeSum xi T ∂tableMeasure d T) = (2 / 3 : ℝ) * T := by
  let U₀ : DenseCommonNoise.Signs 0 := fun _ => false
  change (∫ xi : Bits d × (Fin T → Noise),
    DenseCommonNoise.shapeSum (U₀, xi.2) T
      ∂(bitsMeasure d).prod (DenseCommonNoise.noiseTableMeasure T)) = _
  have h := integral_prod_mul (μ := bitsMeasure d) (ν := DenseCommonNoise.noiseTableMeasure T)
    (fun _ : Bits d => (1 : ℝ)) (fun Z => DenseCommonNoise.shapeSum (U₀, Z) T)
  simpa only [one_mul, integral_const, probReal_univ, smul_eq_mul,
    DenseCommonNoise.integral_shapeSum] using h

theorem integral_shapeSum_joint {d m : ℕ} (P : Policy d m) (hm : 0 < m) (c : ℕ)
    (eta : ℝ) (heta : 0 ≤ eta) (hs : eta ≤ 1 / 16) (T t : ℕ) :
    (∫ x, shapeSum x.1 T ∂jointLaw P hm c eta heta hs T t) = (2 / 3 : ℝ) * T := by
  rw [← integral_shapeSum_table d T, ← jointLaw_map_table P hm c eta heta hs T t]
  exact (integral_map measurable_fst.aemeasurable
    (measurable_shapeSum T).aestronglyMeasurable).symm

theorem integrable_shapeSum_joint {d m T t : ℕ}
    (μ : Measure (Table d T × History d m t)) [IsFiniteMeasure μ] :
    Integrable (fun x => shapeSum x.1 T) μ :=
  Integrable.of_mem_Icc 0 T ((measurable_shapeSum T).comp measurable_fst).aemeasurable
    (ae_of_all _ fun x => shapeSum_mem_Icc x.1 T)

/-- A pointwise loss of at most mT on the bad event; no product of expectations
or independence between survival and the common noise is used. -/
theorem topScore_ge_shape_sub_bad {d m T : ℕ} (hmd : m ≤ d) (c : ℕ)
    (xi : Table d (T + 1)) (h : History d m (T + 1)) :
    (m : ℝ) * shapeSum xi (T + 1) - (m : ℝ) * (T + 1) *
      (badSurvival (d := d) (m := m) c T).indicator (fun _ => (1 : ℝ)) (xi.1, h) ≤
      topScore m (itemScore c xi (T + 1) h) := by
  classical
  by_cases hb : (xi.1, h) ∈ badSurvival (m := m) c T
  · rw [Set.indicator_of_mem hb]
    have hshape := (shapeSum_mem_Icc xi (T + 1)).2
    have hmul := mul_le_mul_of_nonneg_left hshape (Nat.cast_nonneg m)
    have htop := (topScore_mem_Icc hmd c xi (T + 1) h).1
    norm_num only [Nat.cast_add, Nat.cast_one] at hmul
    linarith
  · rw [Set.indicator_of_notMem hb]
    have hcount : m ≤ (favorableActiveItems c xi T h.1).card := by
      have hn : m ≤ finalCount c T (xi.1, h) := Nat.le_of_not_gt hb
      simpa only [finalCount, favorable_history_eq] using hn
    rw [topScore_eq_full_of_many_final_active hmd c xi T h hcount]
    simp

theorem integral_topScore_ge_shape_sub_bad {d m : ℕ}
    (P : Policy d m) (hm : 0 < m) (hmd : m ≤ d) (c : ℕ)
    (eta : ℝ) (heta : 0 ≤ eta) (hs : eta ≤ 1 / 16) (T : ℕ) :
    (2 / 3 : ℝ) * m * (T + 1) - (m : ℝ) * (T + 1) *
      (bitsHistoryLaw P hm c eta heta hs (T + 1)).real (badSurvival c T) ≤
      ∫ x, topScore m (itemScore c x.1 (T + 1) x.2)
        ∂jointLaw P hm c eta heta hs (T + 1) (T + 1) := by
  letI : IsProbabilityMeasure (jointLaw P hm c eta heta hs (T + 1) (T + 1)) :=
    jointLaw_isProbabilityMeasure P hm c eta heta hs (T + 1) (T + 1)
  let E := badSurvival (d := d) (m := m) c T
  let B : Bits d × History d m (T + 1) → ℝ := E.indicator (fun _ => 1)
  have hB : Measurable B := measurable_const.indicator (measurableSet_badSurvival c T)
  have hBi : Integrable (fun x : Table d (T + 1) × History d m (T + 1) => B (x.1.1, x.2))
      (jointLaw P hm c eta heta hs (T + 1) (T + 1)) := by
    apply Integrable.of_mem_Icc 0 1 (hB.comp (by fun_prop)).aemeasurable
    exact ae_of_all _ fun x => by dsimp [B, Set.indicator]; split_ifs <;> norm_num
  have hbint : (∫ x, B (x.1.1, x.2)
      ∂jointLaw P hm c eta heta hs (T + 1) (T + 1)) =
      (bitsHistoryLaw P hm c eta heta hs (T + 1)).real (badSurvival c T) := by
    rw [integral_joint_bitsHistory P hm c eta heta hs (T + 1) B hB]
    exact integral_indicator_one (measurableSet_badSurvival c T)
  calc
    _ = ∫ x, (m : ℝ) * shapeSum x.1 (T + 1) - (m : ℝ) * (T + 1) * B (x.1.1, x.2)
        ∂jointLaw P hm c eta heta hs (T + 1) (T + 1) := by
      rw [integral_sub ((integrable_shapeSum_joint _).const_mul _) (hBi.const_mul _),
        integral_const_mul, integral_const_mul, integral_shapeSum_joint, hbint]
      push_cast
      ring
    _ ≤ _ := integral_mono
      (((integrable_shapeSum_joint _).const_mul _).sub (hBi.const_mul _))
      (integrable_topScore hmd c _) (fun x => topScore_ge_shape_sub_bad hmd c x.1 x.2)

end

end MsetsPaper.Lower.SparseCapped
