import MsetsPaper.Lower.DenseCommonNoiseLaw
import MsetsLower.Lower.Confidence.Score
import MsetsLower.Lower.Confidence.Arithmetic

/-! # The new confidence construction uses oblivious, unstopped losses

Only the pointwise core/candidate combinatorics and literal item-loss formulas
are reused from the old confidence library. The old activity indicator and
adaptive loss process are not used in this construction. Stopping belongs to
the auxiliary learner, in a separate module.
-/

namespace MsetsPaper.Lower.ConfidenceOblivious

open MsetsLower MsetsLower.Feedback MsetsLower.Lower MsetsLower.Lower.Confidence
open MeasureTheory ProbabilityTheory Set
open scoped ENNReal ProbabilityTheory BigOperators

noncomputable section

abbrev Noise := DenseCommonNoise.Noise
abbrev Table (T : ℕ) := Fin T → Noise

def tableNoise {T : ℕ} (Z : Table T) (t : ℕ) : ℝ :=
  if ht : t < T then (Z ⟨t, ht⟩).val else 0

theorem tableNoise_mem_Icc {T : ℕ} (Z : Table T) (t : ℕ) :
    tableNoise Z t ∈ Icc (-1 : ℝ) 1 := by
  unfold tableNoise
  split
  · exact (Z _).property
  · norm_num

@[fun_prop] theorem measurable_tableNoise {T : ℕ} (t : ℕ) : Measurable (fun Z : Table T => tableNoise Z t) := by
  unfold tableNoise
  split
  · exact measurable_subtype_coe.comp (measurable_pi_apply _)
  · exact measurable_const

def referenceTableLossProcess {d m : ℕ} (hm : 1 ≤ m) (hmd : m ≤ d) (T : ℕ) :
    ParametricLossProcess (Table T) d m where
  itemLoss t Z _ := referenceItemLoss hmd (tableNoise Z t)
  measurable_itemLoss t := by
    apply measurable_pi_lambda
    intro i
    unfold referenceItemLoss
    fun_prop
  action_nonneg Z t _ a :=
    (by positivity : (0 : ℝ) ≤ 1 / 8 + 1 / (8 * (m : ℝ))).trans
      (actionLoss_referenceItemLoss_mem_Icc hm hmd (tableNoise_mem_Icc Z t) a).1
  action_le_one Z t _ a :=
    (actionLoss_referenceItemLoss_mem_Icc hm hmd (tableNoise_mem_Icc Z t) a).2.trans
      (by norm_num)

def plantedTableLossProcess {d m : ℕ} (hm : 1 ≤ m) (hmd : m ≤ d)
    (Delta : ℝ) (hDelta : 0 ≤ Delta) (hsmall : (m : ℝ) * Delta ≤ 1 / 2 ^ 13)
    (i : Fin d) (T : ℕ) : ParametricLossProcess (Table T) d m where
  itemLoss t Z _ := plantedItemLoss hmd (tableNoise Z t) Delta 1 i
  measurable_itemLoss t := by
    apply measurable_pi_lambda
    intro j
    unfold plantedItemLoss referenceItemLoss shape
    fun_prop
  action_nonneg Z t _ a :=
    (actionLoss_plantedItemLoss_mem_Icc hm hmd (tableNoise_mem_Icc Z t)
      hDelta hsmall (by norm_num) i a).1
  action_le_one Z t _ a :=
    (actionLoss_plantedItemLoss_mem_Icc hm hmd (tableNoise_mem_Icc Z t)
      hDelta hsmall (by norm_num) i a).2

theorem reference_oblivious {d m T : ℕ} (hm : 1 ≤ m) (hmd : m ≤ d)
    (Z : Table T) (t : ℕ) (h h' : History d m t) :
    ((referenceTableLossProcess hm hmd T).at Z).itemLoss t h =
      ((referenceTableLossProcess hm hmd T).at Z).itemLoss t h' := rfl

theorem planted_oblivious {d m T : ℕ} (hm : 1 ≤ m) (hmd : m ≤ d)
    (Delta : ℝ) (hDelta : 0 ≤ Delta) (hsmall : (m : ℝ) * Delta ≤ 1 / 2 ^ 13)
    (i : Fin d) (Z : Table T) (t : ℕ) (h h' : History d m t) :
    ((plantedTableLossProcess hm hmd Delta hDelta hsmall i T).at Z).itemLoss t h =
      ((plantedTableLossProcess hm hmd Delta hDelta hsmall i T).at Z).itemLoss t h' := rfl

theorem Delta_lt_one_div_eight_m {m : ℕ} (hm : 1 ≤ m) {Delta : ℝ}
    (hsmall : (m : ℝ) * Delta ≤ 1 / 2 ^ 13) : Delta < 1 / (8 * m) := by
  have hmR : (0 : ℝ) < m := by exact_mod_cast hm
  apply (lt_div_iff₀ (by positivity : (0 : ℝ) < 8 * m)).2
  nlinarith

theorem reference_core_lt_candidate {d m : ℕ} (hm : 1 ≤ m) (hmd : m ≤ d)
    (z : ℝ) {c j : Fin d} (hc : c ∈ confidenceCore d m hmd)
    (hj : j ∈ confidenceCandidates d m hmd) :
    referenceItemLoss hmd z c < referenceItemLoss hmd z j := by
  have hcV : c ∉ confidenceCandidates d m hmd := by simp [confidenceCandidates, hc]
  have hmpos : (0 : ℝ) < m := by exact_mod_cast hm
  simp only [referenceItemLoss, candidateIndicator, if_neg hcV, if_pos hj, mul_zero, add_zero, mul_one]
  have hp : (0 : ℝ) < 1 / (8 * m) := by positivity
  linarith

theorem planted_core_lt_candidate {d m : ℕ} (hm : 1 ≤ m) (hmd : m ≤ d)
    {z Delta : ℝ} (hz : z ∈ Icc (-1 : ℝ) 1) (hDelta : 0 ≤ Delta)
    (hsmall : (m : ℝ) * Delta ≤ 1 / 2 ^ 13)
    {i c j : Fin d} (hi : i ∈ confidenceCandidates d m hmd)
    (hc : c ∈ confidenceCore d m hmd) (hj : j ∈ confidenceCandidates d m hmd) :
    plantedItemLoss hmd z Delta 1 i c < plantedItemLoss hmd z Delta 1 i j := by
  have hcV : c ∉ confidenceCandidates d m hmd := by simp [confidenceCandidates, hc]
  have hci : c ≠ i := by intro heq; exact hcV (heq ▸ hi)
  have hg := shape_mem_Icc hz
  have hpert : Delta * shape z ≤ Delta := by nlinarith [hg.2]
  have hgap := Delta_lt_one_div_eight_m hm hsmall
  have hmpos : (0 : ℝ) < m := by exact_mod_cast hm
  by_cases hji : j = i
  · subst j
    simp only [plantedItemLoss, referenceItemLoss, candidateIndicator,
      if_neg hcV, if_pos hi, if_neg hci, if_pos rfl, ite_true, mul_zero, add_zero, sub_zero, mul_one]
    linarith
  · simpa only [plantedItemLoss, if_neg hci, if_neg hji, mul_zero, sub_zero] using
      reference_core_lt_candidate hm hmd z hc hj


theorem planted_candidate_minimal {d m : ℕ} (hmd : m ≤ d)
    {z Delta : ℝ} (hz : z ∈ Icc (-1 : ℝ) 1) (hDelta : 0 ≤ Delta)
    {i j : Fin d} (hi : i ∈ confidenceCandidates d m hmd)
    (hj : j ∈ confidenceCandidates d m hmd) :
    plantedItemLoss hmd z Delta 1 i i ≤ plantedItemLoss hmd z Delta 1 i j := by
  have hpert : 0 ≤ Delta * shape z := mul_nonneg hDelta (shape_mem_Icc hz).1
  simp only [plantedItemLoss, referenceItemLoss, candidateIndicator,
    if_pos hi, if_pos hj, if_pos rfl, mul_one]
  split_ifs <;> simp only [mul_one, mul_zero, sub_zero] <;> linarith

theorem planted_played_sub_comparator {d m : ℕ} (hm : 1 ≤ m) (hmd : m ≤ d)
    (i : Fin d) (hi : i ∈ confidenceCandidates d m hmd)
    (z Delta : ℝ) (a : MSetAction d m) :
    actionLoss a (plantedItemLoss hmd z Delta 1 i) -
      actionLoss (coreComparator hm hmd i hi) (plantedItemLoss hmd z Delta 1 i) =
        candidatePenalty hmd a + Delta * shape z * missedIndicator i a := by
  simpa only [mul_one] using planted_played_sub_coreComparator hm hmd i hi z Delta 1 a

theorem planted_core_optimal {d m : ℕ} (hm : 1 ≤ m) (hmd : m ≤ d)
    (i : Fin d) (hi : i ∈ confidenceCandidates d m hmd)
    {z Delta : ℝ} (hz : z ∈ Icc (-1 : ℝ) 1) (hDelta : 0 ≤ Delta)
    (a : MSetAction d m) :
    actionLoss (coreComparator hm hmd i hi) (plantedItemLoss hmd z Delta 1 i) ≤
      actionLoss a (plantedItemLoss hmd z Delta 1 i) := by
  have h := planted_played_sub_comparator hm hmd i hi z Delta a
  have hp := (candidatePenalty_mem_Ico hm hmd a).1
  have hg := (shape_mem_Icc hz).1
  have hmss := (missedIndicator_mem_Icc i a).1
  nlinarith [mul_nonneg (mul_nonneg hDelta hg) hmss]

/-- Exchange comparison for two equal-size selections. -/
theorem sum_le_sum_of_equal_card_exchange {α : Type*} [DecidableEq α]
    (f : α → ℝ) (s t : Finset α) (hcard : s.card = t.card)
    (horder : ∀ i ∈ s, ∀ j ∈ t, j ∉ s → f i ≤ f j) :
    ∑ i ∈ s, f i ≤ ∑ j ∈ t, f j := by
  have hcd : (s \ t).card = (t \ s).card := Finset.card_sdiff_comm hcard
  have hd : ∑ i ∈ s \ t, f i ≤ ∑ j ∈ t \ s, f j := by
    by_cases he : (s \ t).card = 0
    · have he' : (t \ s).card = 0 := hcd.symm.trans he
      simp [Finset.card_eq_zero.mp he, Finset.card_eq_zero.mp he']
    · have hp : (0 : ℝ) < (s \ t).card := by exact_mod_cast Nat.pos_of_ne_zero he
      have hh := Finset.sum_le_sum (s := s \ t) (fun i hi =>
        Finset.sum_le_sum (s := t \ s) (fun j hj =>
          horder i (Finset.mem_sdiff.mp hi).1 j (Finset.mem_sdiff.mp hj).1
            (Finset.mem_sdiff.mp hj).2))
      simp only [Finset.sum_const, nsmul_eq_mul, ← Finset.mul_sum, ← hcd] at hh
      exact (mul_le_mul_iff_of_pos_left hp).mp hh
  have hs := Finset.sum_sdiff (f := f) (Finset.inter_subset_left (s₁ := s) (s₂ := t))
  have ht := Finset.sum_sdiff (f := f) (Finset.inter_subset_right (s₁ := s) (s₂ := t))
  have hs' : s \ (s ∩ t) = s \ t := by ext i; simp
  have ht' : t \ (s ∩ t) = t \ s := by ext i; simp
  rw [hs'] at hs
  rw [ht'] at ht
  linarith

/-- The manuscript's item ordering gives the optimal core-plus-planted action. -/
theorem planted_core_optimal_of_item_order {d m : ℕ} (hm : 1 ≤ m) (hmd : m ≤ d)
    (i : Fin d) (hi : i ∈ confidenceCandidates d m hmd)
    {z Delta : ℝ} (hz : z ∈ Icc (-1 : ℝ) 1) (hDelta : 0 ≤ Delta)
    (hsmall : (m : ℝ) * Delta ≤ 1 / 2 ^ 13) (a : MSetAction d m) :
    actionLoss (coreComparator hm hmd i hi) (plantedItemLoss hmd z Delta 1 i) ≤
      actionLoss a (plantedItemLoss hmd z Delta 1 i) := by
  rw [actionLoss_eq_finset_sum, actionLoss_eq_finset_sum]
  apply sum_le_sum_of_equal_card_exchange _ _ _ ((coreComparator hm hmd i hi).2.trans a.2.symm)
  intro c hc j hj hjs
  have hjcore : j ∉ confidenceCore d m hmd := by
    intro hh
    exact hjs (Finset.mem_insert_of_mem hh)
  have hjV : j ∈ confidenceCandidates d m hmd := by simp [confidenceCandidates, hjcore]
  have hc' : c = i ∨ c ∈ confidenceCore d m hmd := by
    simpa only [coreComparator_val, Finset.mem_insert] using hc
  rcases hc' with rfl | hc
  · exact planted_candidate_minimal hmd hz hDelta hi hjV
  · exact (planted_core_lt_candidate hm hmd hz hDelta hsmall hi hc hjV).le

theorem bestComparator_eq_of_roundwise_min {d m : ℕ} (L : LossProcess d m)
    (a : MSetAction d m) (hmin : ∀ t h (b : MSetAction d m), actionLoss a (L.itemLoss t h) ≤
      actionLoss b (L.itemLoss t h)) :
    ∀ t (h : History d m t), bestComparatorCumulativeLoss L t h =
      comparatorCumulativeLoss L t h a := by
  have hcum : ∀ t (h : History d m t) (b : MSetAction d m), comparatorCumulativeLoss L t h a ≤
      comparatorCumulativeLoss L t h b := by
    intro t
    induction t with
    | zero => intro h b; rfl
    | succ t ih =>
        intro h b
        exact add_le_add (ih h.1 b) (hmin t h.1 b)
  intro t h
  unfold bestComparatorCumulativeLoss
  apply le_antisymm
  · exact csInf_le (Set.finite_range _).bddBelow ⟨a, rfl⟩
  · have hne : (Set.range (comparatorCumulativeLoss L t h)).Nonempty :=
      ⟨comparatorCumulativeLoss L t h a, a, rfl⟩
    apply le_csInf hne
    rintro y ⟨b, rfl⟩
    exact hcum t h b

def missedShapeSum {d m T : ℕ} (Z : Table T) (i : Fin d) :
    (t : ℕ) → History d m t → ℝ
  | 0, _ => 0
  | t + 1, h => missedShapeSum Z i t h.1 + shape (tableNoise Z t) * missedIndicator i h.2.1

def score {d m T : ℕ} (hmd : m ≤ d) (Z : Table T) (Delta : ℝ) (i : Fin d)
    (t : ℕ) (h : History d m t) : ℝ :=
  cumulativePenalty hmd t h + Delta * missedShapeSum Z i t h

theorem missedShapeSum_mem_Icc {d m T : ℕ} (Z : Table T) (i : Fin d) :
    ∀ t (h : History d m t), missedShapeSum Z i t h ∈ Icc (0 : ℝ) t := by
  intro t
  induction t with
  | zero => intro h; simp [missedShapeSum]
  | succ t ih =>
      intro h
      have hp := ih h.1
      have hg := shape_mem_Icc (tableNoise_mem_Icc Z t)
      have hi := missedIndicator_mem_Icc i h.2.1
      have hprod := mul_nonneg hg.1 hi.1
      have hprodle := mul_le_one₀ hg.2 hi.1 hi.2
      simp only [missedShapeSum, mem_Icc, Nat.cast_add, Nat.cast_one]
      constructor <;> linarith [hp.1, hp.2]

/-- The reference regret is exactly its excess-candidate penalty. -/
theorem reference_pathRegret_eq_penalty {d m T : ℕ} (hm : 1 ≤ m) (hmd : m ≤ d)
    (Z : Table T) (t : ℕ) (h : History d m t) :
    pathRegret ((referenceTableLossProcess hm hmd T).at Z) t h = cumulativePenalty hmd t h := by
  have hne : (confidenceCandidates d m hmd).Nonempty := by
    apply Finset.card_pos.mp
    rw [card_confidenceCandidates hm hmd]
    omega
  obtain ⟨i, hi⟩ := hne
  let L := (referenceTableLossProcess hm hmd T).at Z
  have hzero (z : ℝ) : plantedItemLoss hmd z 0 1 i = referenceItemLoss hmd z := by
    funext j
    simp [plantedItemLoss]
  have hmin := bestComparator_eq_of_roundwise_min L (coreComparator hm hmd i hi)
    (fun t _ a => by
      simpa only [L, referenceTableLossProcess, ParametricLossProcess.at, hzero] using
        planted_core_optimal_of_item_order hm hmd i hi (tableNoise_mem_Icc Z t)
          (show (0 : ℝ) ≤ 0 by rfl) (by norm_num) a)
  change realizedCumulativeLoss L t h - bestComparatorCumulativeLoss L t h = _
  rw [hmin]
  induction t with
  | zero => simp [realizedCumulativeLoss, comparatorCumulativeLoss, cumulativePenalty_zero]
  | succ t ih =>
      have hstep := planted_played_sub_comparator hm hmd i hi (tableNoise Z t) 0 h.2.1
      simp only [hzero, zero_mul, add_zero] at hstep
      change (realizedCumulativeLoss L t h.1 + actionLoss h.2.1 (referenceItemLoss hmd (tableNoise Z t))) -
        (comparatorCumulativeLoss L t h.1 (coreComparator hm hmd i hi) +
          actionLoss (coreComparator hm hmd i hi) (referenceItemLoss hmd (tableNoise Z t))) = _
      rw [cumulativePenalty_succ]
      linarith [ih h.1]

/-- Exact equality with external regret: the fixed core comparator is
simultaneously optimal at every round of the planted oblivious sequence. -/
theorem planted_pathRegret_eq_score {d m T : ℕ} (hm : 1 ≤ m) (hmd : m ≤ d)
    (Delta : ℝ) (hDelta : 0 ≤ Delta) (hsmall : (m : ℝ) * Delta ≤ 1 / 2 ^ 13)
    (i : Fin d) (hi : i ∈ confidenceCandidates d m hmd) (Z : Table T) :
    ∀ t (h : History d m t),
      pathRegret ((plantedTableLossProcess hm hmd Delta hDelta hsmall i T).at Z) t h =
        score hmd Z Delta i t h := by
  let L := (plantedTableLossProcess hm hmd Delta hDelta hsmall i T).at Z
  have hmin := bestComparator_eq_of_roundwise_min L (coreComparator hm hmd i hi)
    (fun t _ a => planted_core_optimal_of_item_order hm hmd i hi
      (tableNoise_mem_Icc Z t) hDelta hsmall a)
  have hdiff : ∀ t (h : History d m t), realizedCumulativeLoss L t h -
      comparatorCumulativeLoss L t h (coreComparator hm hmd i hi) =
        pathRegret ((referenceTableLossProcess hm hmd T).at Z) t h + Delta * missedShapeSum Z i t h := by
    intro t
    simp only [reference_pathRegret_eq_penalty hm hmd]
    induction t with
    | zero => intro h; simp [realizedCumulativeLoss, comparatorCumulativeLoss, score,
        cumulativePenalty, History.actionSum, missedShapeSum]
    | succ t ih =>
        intro h
        have hstep := planted_played_sub_comparator hm hmd i hi (tableNoise Z t) Delta h.2.1
        change (realizedCumulativeLoss L t h.1 +
          actionLoss h.2.1 (plantedItemLoss hmd (tableNoise Z t) Delta 1 i)) -
          (comparatorCumulativeLoss L t h.1 (coreComparator hm hmd i hi) +
          actionLoss (coreComparator hm hmd i hi) (plantedItemLoss hmd (tableNoise Z t) Delta 1 i)) = _
        simp only [score, cumulativePenalty_succ, missedShapeSum] at ih ⊢
        linarith [ih h.1]
  intro t h
  change realizedCumulativeLoss L t h - bestComparatorCumulativeLoss L t h = _
  rw [hmin]
  rw [hdiff, reference_pathRegret_eq_penalty hm hmd]
  rfl

theorem penalty_le_planted_regret {d m T : ℕ} (hm : 1 ≤ m) (hmd : m ≤ d)
    (Delta : ℝ) (hDelta : 0 ≤ Delta) (hsmall : (m : ℝ) * Delta ≤ 1 / 2 ^ 13)
    (i : Fin d) (hi : i ∈ confidenceCandidates d m hmd) (Z : Table T)
    (t : ℕ) (h : History d m t) : cumulativePenalty hmd t h ≤
      pathRegret ((plantedTableLossProcess hm hmd Delta hDelta hsmall i T).at Z) t h := by
  rw [planted_pathRegret_eq_score hm hmd Delta hDelta hsmall i hi Z]
  exact le_add_of_nonneg_right (mul_nonneg hDelta (missedShapeSum_mem_Icc Z i t h).1)

theorem total_candidate_pulls_eq {d m : ℕ} (hm : 1 ≤ m) (hmd : m ≤ d) :
    ∀ t (h : History d m t),
      History.actionSum (fun a => (candidateCount hmd a : ℝ)) t h =
        (t : ℝ) + 8 * m * cumulativePenalty hmd t h := by
  have hm0 : (m : ℝ) ≠ 0 := by exact_mod_cast Nat.ne_of_gt hm
  intro t
  induction t with
  | zero => intro h; simp [History.actionSum, cumulativePenalty]
  | succ t ih =>
      intro h
      rw [History.actionSum_succ, cumulativePenalty_succ, ih h.1]
      unfold candidatePenalty
      push_cast
      field_simp
      ring

end

end MsetsPaper.Lower.ConfidenceOblivious
