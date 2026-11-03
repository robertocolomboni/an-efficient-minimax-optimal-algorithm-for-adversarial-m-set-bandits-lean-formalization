import MsetsPaper.Lower.DenseCommonNoise

/-!
# Paired comparator and pathwise regret for the new dense construction

Each pair contributes its better signed coordinate to one fixed m-set. This
file proves the literal common-term cancellation against that comparator under
the original protocol's definition of regret. It makes no probabilistic claim.
-/

namespace MsetsPaper.Lower.DenseCommonNoise

open MsetsLower MsetsLower.Feedback MsetsLower.Lower MeasureTheory Set
open scoped BigOperators

noncomputable section

def pairIndex {d m : ℕ} (h2m : 2 * m ≤ d) (j : Fin m) (right : Bool) : Fin d :=
  ⟨2 * j.val + if right then 1 else 0, by cases right <;> simp <;> omega⟩

def comparatorIndex {d m : ℕ} (h2m : 2 * m ≤ d) (U : Fin d → ℝ)
    (j : Fin m) : Fin d :=
  if U (pairIndex h2m j false) ≤ U (pairIndex h2m j true)
    then pairIndex h2m j true else pairIndex h2m j false

theorem comparatorIndex_in_pair {d m : ℕ} (h2m : 2 * m ≤ d)
    (U : Fin d → ℝ) (j : Fin m) :
    2 * j.val ≤ (comparatorIndex h2m U j).val ∧
      (comparatorIndex h2m U j).val < 2 * j.val + 2 := by
  unfold comparatorIndex
  split <;> simp [pairIndex]

theorem comparatorIndex_injective {d m : ℕ} (h2m : 2 * m ≤ d)
    (U : Fin d → ℝ) : Function.Injective (comparatorIndex h2m U) := by
  intro j k hjk
  have hj := comparatorIndex_in_pair h2m U j
  have hk := comparatorIndex_in_pair h2m U k
  have heq := congrArg Fin.val hjk
  apply Fin.ext
  omega

/-- One better item per pair, with ties resolved by choosing the right item. -/
def pairedComparator {d m : ℕ} (h2m : 2 * m ≤ d) (U : Fin d → ℝ) : MSetAction d m :=
  ⟨Finset.univ.image (comparatorIndex h2m U), by
    rw [Finset.card_image_of_injective _ (comparatorIndex_injective h2m U)]
    simp⟩

theorem comparatorIndex_value {d m : ℕ} (h2m : 2 * m ≤ d)
    (U : Fin d → ℝ) (j : Fin m) :
    U (comparatorIndex h2m U j) =
      max (U (pairIndex h2m j false)) (U (pairIndex h2m j true)) := by
  unfold comparatorIndex
  split
  · exact (max_eq_right ‹_›).symm
  · exact (max_eq_left (le_of_not_ge ‹_›)).symm

def pairedSignScore {d m : ℕ} (h2m : 2 * m ≤ d) (U : Fin d → ℝ) : ℝ :=
  ∑ j : Fin m, max (U (pairIndex h2m j false)) (U (pairIndex h2m j true))

theorem actionLoss_pairedComparator {d m : ℕ} (h2m : 2 * m ≤ d)
    (U : Fin d → ℝ) :
    actionLoss (pairedComparator h2m U) U = pairedSignScore h2m U := by
  rw [actionLoss_eq_finset_sum]
  change (∑ i ∈ Finset.univ.image (comparatorIndex h2m U), U i) = _
  rw [Finset.sum_image]
  · exact Finset.sum_congr rfl fun j _ => comparatorIndex_value h2m U j
  · intro j _ k _ hjk
    exact comparatorIndex_injective h2m U hjk

/-- Since all score coordinates have the same nonnegative noise factor,
choosing the better sign chooses the better score in every pair. -/
theorem paired_score_eq_sum_max {d m : ℕ} (h2m : 2 * m ≤ d)
    (U : Fin d → ℝ) {G : ℝ} (hG : 0 ≤ G) :
    pairedSignScore h2m U * G =
      ∑ j : Fin m, max (U (pairIndex h2m j false) * G)
        (U (pairIndex h2m j true) * G) := by
  simp only [pairedSignScore, Finset.sum_mul, max_mul_of_nonneg _ _ hG]

def commonLossSum {m T : ℕ} (xi : Table m T) (t : ℕ) : ℝ :=
  ∑ r ∈ Finset.range t, (1 + tableNoise xi r) / 2

def shapeSum {m T : ℕ} (xi : Table m T) (t : ℕ) : ℝ :=
  ∑ r ∈ Finset.range t, shape (tableNoise xi r)

def learnerScore {d m T : ℕ} (xi : Table m T) :
    (t : ℕ) → History d m t → ℝ
  | 0, _ => 0
  | t + 1, h => learnerScore xi t h.1 +
      shape (tableNoise xi t) * actionLoss h.2.1 (signVector xi.1)

def deficit {d m T : ℕ} (h2m : 2 * m ≤ d) (xi : Table m T)
    (t : ℕ) (h : History d m t) : ℝ :=
  pairedSignScore h2m (signVector xi.1) * shapeSum xi t - learnerScore xi t h

theorem actionLoss_eq_common_sub_score {d m : ℕ} (hm : 0 < m)
    (eta z : ℝ) (U : Fin d → ℝ) (a : MSetAction d m) :
    actionLoss a (itemLoss m eta z U) =
      (1 + z) / 2 - eta / m * (shape z * actionLoss a U) := by
  rw [actionLoss_feedback_identity hm]
  unfold feedbackMap feedbackParameter
  ring

theorem realizedCumulativeLoss_eq_common_sub_score {d m : ℕ} (hm : 0 < m)
    (eta : ℝ) (heta : 0 ≤ eta) (hetaSmall : eta ≤ 1 / 16)
    (T : ℕ) (xi : Table m T) : ∀ t (h : History d m t),
    realizedCumulativeLoss ((tableLossProcess hm eta heta hetaSmall T).at xi) t h =
      commonLossSum xi t - eta / m * learnerScore xi t h := by
  intro t
  induction t with
  | zero => intro h; simp [realizedCumulativeLoss, commonLossSum, learnerScore]
  | succ t ih =>
      intro h
      rw [realizedCumulativeLoss, ih]
      change commonLossSum xi t - eta / m * learnerScore xi t h.1 +
        actionLoss h.2.1 (itemLoss m eta (tableNoise xi t) (signVector xi.1)) = _
      rw [actionLoss_eq_common_sub_score hm]
      simp only [commonLossSum, Finset.sum_range_succ, learnerScore]
      ring

theorem comparatorCumulativeLoss_eq_common_sub_score {d m : ℕ} (hm : 0 < m)
    (eta : ℝ) (heta : 0 ≤ eta) (hetaSmall : eta ≤ 1 / 16)
    (T : ℕ) (xi : Table m T) (a : MSetAction d m) : ∀ t (h : History d m t),
    comparatorCumulativeLoss ((tableLossProcess hm eta heta hetaSmall T).at xi) t h a =
      commonLossSum xi t - eta / m * (actionLoss a (signVector xi.1) * shapeSum xi t) := by
  intro t
  induction t with
  | zero => intro h; simp [comparatorCumulativeLoss, commonLossSum, shapeSum]
  | succ t ih =>
      intro h
      rw [comparatorCumulativeLoss, ih]
      change commonLossSum xi t - eta / m *
        (actionLoss a (signVector xi.1) * shapeSum xi t) +
        actionLoss a (itemLoss m eta (tableNoise xi t) (signVector xi.1)) = _
      rw [actionLoss_eq_common_sub_score hm]
      simp only [commonLossSum, shapeSum, Finset.sum_range_succ]
      ring

/-- Literal inequality `R_T ≥ (eta/m) Γ` under the original protocol's
pathwise regret. This is valid on every history, not just almost surely. -/
theorem scaled_deficit_le_pathRegret {d m : ℕ} (hm : 0 < m) (h2m : 2 * m ≤ d)
    (eta : ℝ) (heta : 0 ≤ eta) (hetaSmall : eta ≤ 1 / 16)
    (T : ℕ) (xi : Table m T) (t : ℕ) (h : History d m t) :
    eta / m * deficit h2m xi t h ≤
      pathRegret ((tableLossProcess hm eta heta hetaSmall T).at xi) t h := by
  have hbest : bestComparatorCumulativeLoss
      ((tableLossProcess hm eta heta hetaSmall T).at xi) t h ≤
      comparatorCumulativeLoss ((tableLossProcess hm eta heta hetaSmall T).at xi)
        t h (pairedComparator h2m (signVector xi.1)) :=
    csInf_le (Set.finite_range _).bddBelow ⟨pairedComparator h2m (signVector xi.1), rfl⟩
  rw [comparatorCumulativeLoss_eq_common_sub_score,
    actionLoss_pairedComparator] at hbest
  rw [pathRegret, realizedCumulativeLoss_eq_common_sub_score]
  unfold deficit
  linarith

theorem shapeSum_mem_Icc {m T : ℕ} (xi : Table m T) (t : ℕ) :
    shapeSum xi t ∈ Icc (0 : ℝ) t := by
  have hg : ∀ r, shape (tableNoise xi r) ∈ Icc (0 : ℝ) 1 :=
    fun r => shape_mem_Icc (tableNoise_mem_Icc xi r)
  constructor
  · exact Finset.sum_nonneg fun r _ => (hg r).1
  · calc
      shapeSum xi t ≤ ∑ _r ∈ Finset.range t, (1 : ℝ) :=
        Finset.sum_le_sum fun r _ => (hg r).2
      _ = (t : ℝ) := by simp

theorem abs_learnerScore_le {d m T : ℕ} (xi : Table m T) :
    ∀ t (h : History d m t), |learnerScore xi t h| ≤ (m : ℝ) * t := by
  intro t
  induction t with
  | zero => intro h; simp [learnerScore]
  | succ t ih =>
      intro h
      have hg := shape_mem_Icc (tableNoise_mem_Icc xi t)
      have hsign := abs_action_sign_sum_le h.2.1 (signVector xi.1) (abs_signVector_le xi.1)
      have hterm : |shape (tableNoise xi t) * actionLoss h.2.1 (signVector xi.1)| ≤
          (m : ℝ) := by
        rw [abs_mul, abs_of_nonneg hg.1]
        exact (mul_le_mul_of_nonneg_left hsign hg.1).trans
          (by simpa using mul_le_mul_of_nonneg_right hg.2 (show (0 : ℝ) ≤ m by positivity))
      rw [learnerScore]
      calc
        _ ≤ |learnerScore xi t h.1| +
            |shape (tableNoise xi t) * actionLoss h.2.1 (signVector xi.1)| := abs_add_le _ _
        _ ≤ (m : ℝ) * t + m := add_le_add (ih h.1) hterm
        _ = (m : ℝ) * (t + 1 : ℕ) := by push_cast; ring

/-- Both-sided boundedness gives integrability once the joint law is installed;
in particular the upper bound is the manuscript's exact `2*m*T`. -/
theorem abs_deficit_le {d m T : ℕ} (h2m : 2 * m ≤ d) (xi : Table m T)
    (t : ℕ) (h : History d m t) : |deficit h2m xi t h| ≤ 2 * (m : ℝ) * t := by
  have hG := shapeSum_mem_Icc xi t
  have hsign : |pairedSignScore h2m (signVector xi.1)| ≤ (m : ℝ) := by
    rw [← actionLoss_pairedComparator]
    exact abs_action_sign_sum_le _ _ (abs_signVector_le xi.1)
  have hc : |pairedSignScore h2m (signVector xi.1) * shapeSum xi t| ≤ (m : ℝ) * t := by
    rw [abs_mul, abs_of_nonneg hG.1]
    exact mul_le_mul hsign hG.2 hG.1 (Nat.cast_nonneg m)
  unfold deficit
  exact (abs_sub _ _).trans (by linarith [abs_learnerScore_le xi t h])

end

end MsetsPaper.Lower.DenseCommonNoise
