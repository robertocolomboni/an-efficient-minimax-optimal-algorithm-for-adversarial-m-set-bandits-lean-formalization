import MsetsLower.Core.ParametricRun
import MsetsLower.Feedback.Inverse
import MsetsLower.Lower.ParametricRegret

/-!
# The dense construction: common continuous noise

This is the construction of `prop:lower-action-count-dense` in `paper/main.tex`.
Its signs occupy the first
`2*m` coordinates, all other signs are zero, and every coordinate uses the same
continuous noise at each round. The table fixes the losses in advance.

This module establishes deterministic formulas and admissibility. The random
sign/noise law and its information estimates are separate obligations.
-/

namespace MsetsPaper.Lower.DenseCommonNoise

open MsetsLower MsetsLower.Feedback MsetsLower.Lower MeasureTheory Set
open scoped BigOperators

noncomputable section

/-- Independent fair bits will encode the first `2m` Rademacher signs. -/
abbrev Signs (m : ℕ) := Fin (2 * m) → Bool

def signValue (b : Bool) : ℝ := if b then 1 else -1

@[simp] theorem abs_signValue (b : Bool) : |signValue b| = 1 := by
  cases b <;> norm_num [signValue]

/-- The manuscript's sign vector, with zeros outside the first `2m` items. -/
def signVector {d m : ℕ} (U : Signs m) (i : Fin d) : ℝ :=
  if hi : i.val < 2 * m then signValue (U ⟨i.val, hi⟩) else 0

theorem abs_signVector_le {d m : ℕ} (U : Signs m) (i : Fin d) :
    |signVector U i| ≤ 1 := by
  unfold signVector
  split <;> simp

theorem signVector_eq_zero_outside {d m : ℕ} (U : Signs m) (i : Fin d)
    (hi : 2 * m ≤ i.val) : signVector U i = 0 := by
  simp [signVector, not_lt.mpr hi]

/-- Literal item loss from equation `eq:lower-dense-item-loss`. -/
def itemLoss {d : ℕ} (m : ℕ) (eta z : ℝ) (U : Fin d → ℝ) (i : Fin d) : ℝ :=
  (1 + z) / (2 * m) - eta / m * shape z * U i

/-- A single item's loss is exactly an affine translate of `F_{-eta U_i}`. -/
theorem itemLoss_feedback_identity {d m : ℕ} (hm : 0 < m)
    (eta z : ℝ) (U : Fin d → ℝ) (i : Fin d) :
    (m : ℝ) * itemLoss m eta z U i = 1 / 2 + feedbackMap (-eta * U i) z := by
  have hm0 : (m : ℝ) ≠ 0 := by exact_mod_cast Nat.ne_of_gt hm
  unfold itemLoss feedbackMap
  field_simp
  ring

/-- The feedback lemma yields the exact item-level normalization `[0,1/m]`. -/
theorem itemLoss_mem_Icc {d m : ℕ} (hm : 0 < m)
    {eta z : ℝ} (heta : 0 ≤ eta) (hetaSmall : eta ≤ 1 / 16)
    (hz : z ∈ Icc (-1 : ℝ) 1) (U : Fin d → ℝ)
    (hU : ∀ i, |U i| ≤ 1) (i : Fin d) :
    itemLoss m eta z U i ∈ Icc (0 : ℝ) (1 / m) := by
  have hmR : (0 : ℝ) < m := by exact_mod_cast hm
  have hu : |-eta * U i| ≤ 1 / 16 := by
    rw [abs_mul, abs_neg, abs_of_nonneg heta]
    exact (mul_le_mul_of_nonneg_left (hU i) heta).trans (by simpa using hetaSmall)
  have hf := (feedbackMap_bijOn hu).mapsTo hz
  have hid := itemLoss_feedback_identity hm eta z U i
  constructor
  · exact (mul_nonneg_iff_of_pos_left hmR).1 (by linarith [hf.1])
  · apply (le_div_iff₀ hmR).2
    nlinarith [hf.2]

/-- Any action sees a sign sum in `[-m,m]`, including coordinates with sign zero. -/
theorem abs_action_sign_sum_le {d m : ℕ} (a : MSetAction d m)
    (U : Fin d → ℝ) (hU : ∀ i, |U i| ≤ 1) : |actionLoss a U| ≤ (m : ℝ) := by
  rw [actionLoss_eq_finset_sum]
  calc
    |∑ i ∈ a.val, U i| ≤ ∑ i ∈ a.val, |U i| := Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ _i ∈ a.val, (1 : ℝ) := Finset.sum_le_sum fun i _ => hU i
    _ = (m : ℝ) := by simp [a.property]

def feedbackParameter {d m : ℕ} (eta : ℝ) (U : Fin d → ℝ)
    (a : MSetAction d m) : ℝ := -(eta / m) * actionLoss a U

theorem abs_feedbackParameter_le {d m : ℕ} (hm : 0 < m)
    {eta : ℝ} (heta : 0 ≤ eta) (U : Fin d → ℝ)
    (hU : ∀ i, |U i| ≤ 1) (a : MSetAction d m) :
    |feedbackParameter eta U a| ≤ eta := by
  have hmR : (0 : ℝ) < m := by exact_mod_cast hm
  unfold feedbackParameter
  rw [abs_mul, abs_neg, abs_of_nonneg (div_nonneg heta hmR.le)]
  calc
    eta / m * |actionLoss a U| ≤ eta / m * m :=
      mul_le_mul_of_nonneg_left (abs_action_sign_sum_le a U hU) (div_nonneg heta hmR.le)
    _ = eta := div_mul_cancel₀ eta (ne_of_gt hmR)

/-- The action feedback is exactly `1/2 + F_u(z)`, not merely equal in law. -/
theorem actionLoss_feedback_identity {d m : ℕ} (hm : 0 < m)
    (eta z : ℝ) (U : Fin d → ℝ) (a : MSetAction d m) :
    actionLoss a (itemLoss m eta z U) =
      1 / 2 + feedbackMap (feedbackParameter eta U a) z := by
  have hm0 : (m : ℝ) ≠ 0 := by exact_mod_cast Nat.ne_of_gt hm
  simp only [actionLoss_eq_finset_sum, itemLoss, Finset.sum_sub_distrib,
    ← Finset.mul_sum, Finset.sum_const, a.property, nsmul_eq_mul]
  unfold feedbackMap feedbackParameter
  rw [actionLoss_eq_finset_sum]
  field_simp
  ring

theorem actionLoss_mem_Icc {d m : ℕ} (hm : 0 < m)
    {eta z : ℝ} (heta : 0 ≤ eta) (hetaSmall : eta ≤ 1 / 16)
    (hz : z ∈ Icc (-1 : ℝ) 1) (U : Fin d → ℝ)
    (hU : ∀ i, |U i| ≤ 1) (a : MSetAction d m) :
    actionLoss a (itemLoss m eta z U) ∈ Icc (0 : ℝ) 1 := by
  have hu := (abs_feedbackParameter_le hm heta U hU a).trans hetaSmall
  have hf := (feedbackMap_bijOn hu).mapsTo hz
  rw [actionLoss_feedback_identity hm]
  constructor <;> linarith [hf.1, hf.2]

/-- Noise values are restricted by their type, so every fixed table is admissible. -/
abbrev Noise := {z : ℝ // z ∈ Icc (-1 : ℝ) 1}

abbrev Table (m T : ℕ) := Signs m × (Fin T → Noise)

/-- The finite table is extended by zero noise after its horizon. -/
def tableNoise {m T : ℕ} (xi : Table m T) (t : ℕ) : ℝ :=
  if ht : t < T then (xi.2 ⟨t, ht⟩).val else 0

theorem tableNoise_mem_Icc {m T : ℕ} (xi : Table m T) (t : ℕ) :
    tableNoise xi t ∈ Icc (-1 : ℝ) 1 := by
  unfold tableNoise
  split
  · exact (xi.2 _).property
  · norm_num

theorem measurable_tableNoise {m T : ℕ} (t : ℕ) :
    Measurable (fun xi : Table m T => tableNoise xi t) := by
  unfold tableNoise
  split
  · exact measurable_subtype_coe.comp ((measurable_pi_apply _).comp measurable_snd)
  · exact measurable_const

/-- A genuine measurable family of deterministic, oblivious loss processes
with the manuscript's new common-noise formula. -/
def tableLossProcess {d m : ℕ} (hm : 0 < m)
    (eta : ℝ) (heta : 0 ≤ eta) (hetaSmall : eta ≤ 1 / 16) (T : ℕ) :
    ParametricLossProcess (Table m T) d m where
  itemLoss t xi _ := itemLoss m eta (tableNoise xi t) (signVector xi.1)
  measurable_itemLoss t := by
    apply measurable_pi_lambda
    intro i
    have hz : Measurable (fun x : Table m T × History d m t => tableNoise x.1 t) :=
      (measurable_tableNoise t).comp measurable_fst
    have hU : Measurable (fun x : Table m T × History d m t => signVector x.1.1 i) :=
      (measurable_of_finite (fun U : Signs m => signVector U i)).comp
        (measurable_fst.comp measurable_fst)
    unfold itemLoss shape
    fun_prop
  action_nonneg xi t _ a :=
    (actionLoss_mem_Icc hm heta hetaSmall (tableNoise_mem_Icc xi t)
      (signVector xi.1) (abs_signVector_le xi.1) a).1
  action_le_one xi t _ a :=
    (actionLoss_mem_Icc hm heta hetaSmall (tableNoise_mem_Icc xi t)
      (signVector xi.1) (abs_signVector_le xi.1) a).2

/-- Fixing the table gives losses independent of every observed history. -/
theorem tableLossProcess_oblivious {d m : ℕ} (hm : 0 < m)
    (eta : ℝ) (heta : 0 ≤ eta) (hetaSmall : eta ≤ 1 / 16)
    (T : ℕ) (xi : Table m T) (t : ℕ) (h h' : History d m t) :
    ((tableLossProcess hm eta heta hetaSmall T).at xi).itemLoss t h =
      ((tableLossProcess hm eta heta hetaSmall T).at xi).itemLoss t h' := rfl

theorem tableLossProcess_item_mem_Icc {d m : ℕ} (hm : 0 < m)
    (eta : ℝ) (heta : 0 ≤ eta) (hetaSmall : eta ≤ 1 / 16)
    (T : ℕ) (xi : Table m T) (t : ℕ) (h : History d m t) (i : Fin d) :
    ((tableLossProcess hm eta heta hetaSmall T).at xi).itemLoss t h i ∈
      Icc (0 : ℝ) (1 / m) :=
  itemLoss_mem_Icc hm heta hetaSmall (tableNoise_mem_Icc xi t)
    (signVector xi.1) (abs_signVector_le xi.1) i

end

end MsetsPaper.Lower.DenseCommonNoise
