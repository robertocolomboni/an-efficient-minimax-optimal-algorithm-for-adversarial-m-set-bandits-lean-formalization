import MsetsPaper.Lower.SparseCappedJoint

/-! # Conditional test probabilities in the genuine sparse experiment -/

namespace MsetsPaper.Lower.SparseCapped

open MsetsLower MeasureTheory ProbabilityTheory Set
open scoped BigOperators ENNReal ProbabilityTheory

noncomputable section

def finalSurvivalTest {d m : ℕ} (c T : ℕ) (U : Bits d) (i : Fin d) :
    Set (History d m (T + 1)) :=
  Prod.fst ⁻¹' historySurvivalTest c T U i

instance finalSurvivalTest_decidable {d m : ℕ} (c T : ℕ) (U : Bits d) (i : Fin d) :
    DecidablePred (finalSurvivalTest (m := m) c T U i) := fun h =>
  inferInstanceAs (Decidable (survivalTest m (historyActiveItems c T h.1) U i))

theorem measurableSet_finalSurvivalTest {d m : ℕ} (c T : ℕ) (U : Bits d) (i : Fin d) :
    MeasurableSet (finalSurvivalTest (m := m) c T U i) :=
  measurable_fst (measurableSet_historySurvivalTest c T U i)

theorem finalSurvivalTest_update {d m : ℕ} (c T : ℕ) (U : Bits d) (i : Fin d) (b : Bool) :
    finalSurvivalTest (m := m) c T (Function.update U i b) i = finalSurvivalTest c T U i := by
  unfold finalSurvivalTest
  rw [historySurvivalTest_update]

def finalCount {d m : ℕ} (c T : ℕ) (x : Bits d × History d m (T + 1)) : ℕ :=
  (favorable (historyActiveItems c T x.2.1) x.1).card

def badSurvival {d m : ℕ} (c T : ℕ) : Set (Bits d × History d m (T + 1)) :=
  {x | finalCount c T x < m}

theorem measurable_finalCount {d m : ℕ} (c T : ℕ) :
    Measurable (finalCount (d := d) (m := m) c T) :=
  (measurable_of_finite (fun x : Bits d × Finset (Fin d) => (favorable x.2 x.1).card)).comp
    (measurable_fst.prodMk ((measurable_historyActiveItems c T).comp measurable_snd.fst))

theorem measurableSet_badSurvival {d m : ℕ} (c T : ℕ) :
    MeasurableSet (badSurvival (d := d) (m := m) c T) :=
  (measurable_finalCount c T) (Set.to_countable {n : ℕ | n < m}).measurableSet

def testWitness {d m : ℕ} (c T : ℕ) (i : Fin d) (b : Bool)
    (x : Bits d × History d m (T + 1)) : ℝ :=
  if x.1 i = b ∧ survivalTest m (historyActiveItems c T x.2.1) x.1 i then 1 else 0

theorem measurable_testWitness {d m : ℕ} (c T : ℕ) (i : Fin d) (b : Bool) :
    Measurable (testWitness (m := m) c T i b) :=
  (measurable_of_finite (fun x : Bits d × Finset (Fin d) =>
    if x.1 i = b ∧ survivalTest m x.2 x.1 i then (1 : ℝ) else 0)).comp
      (measurable_fst.prodMk ((measurable_historyActiveItems c T).comp measurable_snd.fst))

theorem testWitness_mem_Icc {d m : ℕ} (c T : ℕ) (i : Fin d) (b : Bool)
    (x : Bits d × History d m (T + 1)) : testWitness c T i b x ∈ Icc (0 : ℝ) 1 := by
  unfold testWitness
  split_ifs <;> norm_num

theorem integrable_testWitness {d m : ℕ} (c T : ℕ) (i : Fin d) (b : Bool)
    (μ : Measure (Bits d × History d m (T + 1))) [IsFiniteMeasure μ] :
    Integrable (testWitness c T i b) μ :=
  Integrable.of_mem_Icc 0 1 (measurable_testWitness c T i b).aemeasurable
    (ae_of_all _ (testWitness_mem_Icc c T i b))

/-- The manuscript's a_i and b_i, with the other bits still sampled from their
original prior and with the actual policy/noise mixture in each section. -/
def conditionalTestProbability {d m : ℕ} (P : Policy d m) (hm : 0 < m) (c : ℕ)
    (eta : ℝ) (heta : 0 ≤ eta) (hs : eta ≤ 1 / 16) (T : ℕ) (i : Fin d) (b : Bool) : ℝ :=
  ∫ U : Bits d, (noiseMixture P hm c eta heta hs (Function.update U i b) (T + 1)).real
    (finalSurvivalTest c T U i) ∂bitsMeasure d

theorem integral_testWitness_eq_conditional {d m : ℕ}
    (P : Policy d m) (hm : 0 < m) (c : ℕ)
    (eta : ℝ) (heta : 0 ≤ eta) (hs : eta ≤ 1 / 16) (T : ℕ) (i : Fin d) (b : Bool) :
    (∫ x, testWitness c T i b x ∂bitsHistoryLaw P hm c eta heta hs (T + 1)) =
      bitWeight b * conditionalTestProbability P hm c eta heta hs T i b := by
  rw [integral_bitsHistoryLaw P hm c eta heta hs (T + 1) _
    (measurable_testWitness c T i b) 1
    (fun x => abs_le.mpr ⟨by linarith [(testWitness_mem_Icc c T i b x).1],
      (testWitness_mem_Icc c T i b x).2⟩)]
  have hinner (U : Bits d) :
      (∫ h, testWitness c T i b (U, h) ∂noiseMixture P hm c eta heta hs U (T + 1)) =
        if U i = b then (noiseMixture P hm c eta heta hs U (T + 1)).real
          (finalSurvivalTest c T U i) else 0 := by
    by_cases hb : U i = b
    · simp only [testWitness, hb, true_and, if_true]
      rw [← integral_indicator_one
        (μ := noiseMixture P hm c eta heta hs U (T + 1))
        (measurableSet_finalSurvivalTest (m := m) c T U i)]
      apply integral_congr_ae
      filter_upwards [] with h
      by_cases ht : survivalTest m (historyActiveItems c T h.1) U i <;>
        simp [Set.indicator, finalSurvivalTest, historySurvivalTest, ht]
    · simp [testWitness, hb]
  simp_rw [hinner]
  rw [integral_bit_condition i b]
  congr 1
  apply integral_congr_ae
  filter_upwards [] with U
  rw [finalSurvivalTest_update]

theorem conditionalTestProbability_mem_Icc {d m : ℕ}
    (P : Policy d m) (hm : 0 < m) (c : ℕ)
    (eta : ℝ) (heta : 0 ≤ eta) (hs : eta ≤ 1 / 16) (T : ℕ) (i : Fin d) (b : Bool) :
    conditionalTestProbability P hm c eta heta hs T i b ∈ Icc (0 : ℝ) 1 := by
  constructor
  · exact integral_nonneg fun _ => measureReal_nonneg
  · have hle := integral_mono (μ := bitsMeasure d) Integrable.of_finite
      (integrable_const (1 : ℝ)) (fun U => by
        letI := noiseMixture_isProbabilityMeasure P hm c eta heta hs
          (Function.update U i b) (T + 1)
        exact show (noiseMixture P hm c eta heta hs (Function.update U i b) (T + 1)).real
          (finalSurvivalTest c T U i) ≤ (1 : ℝ) from
          (measureReal_mono (subset_univ _)).trans_eq probReal_univ)
    convert! hle using 1
    simp only [integral_const, probReal_univ, smul_eq_mul, one_mul]

theorem conditional_true_sum_le {d m : ℕ}
    (P : Policy d m) (hm : 0 < m) (c : ℕ)
    (eta : ℝ) (heta : 0 ≤ eta) (hs : eta ≤ 1 / 16) (T : ℕ) :
    (1 / 256 : ℝ) * ∑ i : Fin d, conditionalTestProbability P hm c eta heta hs T i true ≤ m := by
  letI := bitsHistoryLaw_isProbabilityMeasure P hm c eta heta hs (T + 1)
  have hsum : (∫ x, ∑ i : Fin d, testWitness c T i true x
      ∂bitsHistoryLaw P hm c eta heta hs (T + 1)) =
      (1 / 256 : ℝ) * ∑ i : Fin d, conditionalTestProbability P hm c eta heta hs T i true := by
    rw [integral_finsetSum _ (fun i _ => integrable_testWitness c T i true _)]
    simp_rw [integral_testWitness_eq_conditional P hm c eta heta hs T]
    simp only [bitWeight, if_true, Finset.mul_sum]
  rw [← hsum]
  calc
    _ ≤ ∫ _x : Bits d × History d m (T + 1), (m : ℝ)
        ∂bitsHistoryLaw P hm c eta heta hs (T + 1) := by
      apply integral_mono (integrable_finsetSum _ (fun i _ => integrable_testWitness c T i true _))
        (integrable_const _)
      intro x
      exact sum_true_survivalTests_le (m := m) (historyActiveItems c T x.2.1) x.1
    _ = _ := by simp

theorem conditional_true_sum_eq_truncated_count {d m : ℕ}
    (P : Policy d m) (hm : 0 < m) (c : ℕ)
    (eta : ℝ) (heta : 0 ≤ eta) (hs : eta ≤ 1 / 16) (T : ℕ) :
    (1 / 256 : ℝ) * ∑ i : Fin d, conditionalTestProbability P hm c eta heta hs T i true =
      ∫ x, if finalCount c T x ≤ m then (finalCount c T x : ℝ) else 0
        ∂bitsHistoryLaw P hm c eta heta hs (T + 1) := by
  letI := bitsHistoryLaw_isProbabilityMeasure P hm c eta heta hs (T + 1)
  calc
    _ = ∫ x, ∑ i : Fin d, testWitness c T i true x
        ∂bitsHistoryLaw P hm c eta heta hs (T + 1) := by
      rw [integral_finsetSum _ (fun i _ => integrable_testWitness c T i true _)]
      simp_rw [integral_testWitness_eq_conditional P hm c eta heta hs T]
      simp only [bitWeight, if_true, Finset.mul_sum]
    _ = _ := integral_congr_ae (ae_of_all _ fun x =>
      sum_true_survivalTests (m := m) (historyActiveItems c T x.2.1) x.1)

theorem conditional_false_sum_ge_bad {d m : ℕ}
    (P : Policy d m) (hm : 0 < m) (hmd : m ≤ d) (c : ℕ) (hc : 0 < c)
    (eta : ℝ) (heta : 0 ≤ eta) (hs : eta ≤ 1 / 16) (T : ℕ)
    (hbudget : 8 * (T + 1) * m ≤ c * d) :
    ((7 / 8 : ℝ) * d - m) *
      (bitsHistoryLaw P hm c eta heta hs (T + 1)).real (badSurvival c T) ≤
      (255 / 256 : ℝ) * ∑ i : Fin d,
        conditionalTestProbability P hm c eta heta hs T i false := by
  letI := bitsHistoryLaw_isProbabilityMeasure P hm c eta heta hs (T + 1)
  have hsum : (∫ x, ∑ i : Fin d, testWitness c T i false x
      ∂bitsHistoryLaw P hm c eta heta hs (T + 1)) =
      (255 / 256 : ℝ) * ∑ i : Fin d, conditionalTestProbability P hm c eta heta hs T i false := by
    rw [integral_finsetSum _ (fun i _ => integrable_testWitness c T i false _)]
    simp_rw [integral_testWitness_eq_conditional P hm c eta heta hs T]
    simp only [bitWeight, Bool.false_eq_true, if_false, Finset.mul_sum]
  rw [← hsum]
  have hi : (∫ x, (badSurvival (d := d) (m := m) c T).indicator
      (fun _ => (7 / 8 : ℝ) * d - m) x
      ∂bitsHistoryLaw P hm c eta heta hs (T + 1)) =
      ((7 / 8 : ℝ) * d - m) *
        (bitsHistoryLaw P hm c eta heta hs (T + 1)).real (badSurvival c T) := by
    rw [integral_indicator_const _ (measurableSet_badSurvival c T), smul_eq_mul, mul_comm]
  rw [← hi]
  apply integral_mono ((integrable_const _).indicator (measurableSet_badSurvival c T))
    (integrable_finsetSum _ (fun i _ => integrable_testWitness c T i false _))
  intro x
  have hpoint := sum_false_survivalTests_ge (m := m) (historyActiveItems c T x.2.1) x.1
    (historyActiveItems_card_before_final hmd hc hbudget x.2)
  by_cases hbad : (favorable (historyActiveItems c T x.2.1) x.1).card < m <;>
    simpa [badSurvival, finalCount, Set.indicator, testWitness, hbad] using hpoint

def averageTestProbability {d m : ℕ} (P : Policy d m) (hm : 0 < m) (c : ℕ)
    (eta : ℝ) (heta : 0 ≤ eta) (hs : eta ≤ 1 / 16) (T : ℕ) (b : Bool) : ℝ :=
  (∑ i : Fin d, conditionalTestProbability P hm c eta heta hs T i b) / d

theorem average_true_le_ratio {d m : ℕ}
    (P : Policy d m) (hm : 0 < m) (hmd : m ≤ d) (c : ℕ)
    (eta : ℝ) (heta : 0 ≤ eta) (hs : eta ≤ 1 / 16) (T : ℕ) :
    averageTestProbability P hm c eta heta hs T true ≤ 256 * ratio d m := by
  have hd : (0 : ℝ) < d := by exact_mod_cast lt_of_lt_of_le hm hmd
  have hsum := conditional_true_sum_le P hm c eta heta hs T
  unfold averageTestProbability ratio
  rw [← mul_div_assoc]
  apply (div_le_div_iff_of_pos_right hd).2
  linarith

theorem average_false_controls_bad {d m : ℕ}
    (P : Policy d m) (hm : 0 < m) (hmd : m ≤ d) (c : ℕ) (hc : 0 < c)
    (eta : ℝ) (heta : 0 ≤ eta) (hs : eta ≤ 1 / 16) (T : ℕ)
    (hbudget : 8 * (T + 1) * m ≤ c * d) :
    ((7 / 8 : ℝ) - ratio d m) *
      (bitsHistoryLaw P hm c eta heta hs (T + 1)).real (badSurvival c T) ≤
      (255 / 256 : ℝ) * averageTestProbability P hm c eta heta hs T false := by
  have hd : (0 : ℝ) < d := by exact_mod_cast lt_of_lt_of_le hm hmd
  have hsum := conditional_false_sum_ge_bad P hm hmd c hc eta heta hs T hbudget
  have hdiv := div_le_div_of_nonneg_right hsum hd.le
  convert! hdiv using 1 <;> dsimp only [ratio, averageTestProbability] <;>
    field_simp

end

end MsetsPaper.Lower.SparseCapped
