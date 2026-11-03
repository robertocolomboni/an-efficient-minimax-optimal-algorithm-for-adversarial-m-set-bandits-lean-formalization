import MsetsPaper.Lower.ConfidenceOblivious
import MsetsLower.Lower.Confidence.Fixing

/-! # One observable event under both confidence environments

The only old fixing-module ingredients used here are the generic definition
of protocol-compatible histories and its almost-sure validity for `runLaw`.
No old confidence lower bound or adaptive loss process is invoked.
-/

namespace MsetsPaper.Lower.ConfidenceOblivious

open MsetsLower MsetsLower.Feedback MsetsLower.Lower MsetsLower.Lower.Confidence
open MeasureTheory ProbabilityTheory Set
open scoped ENNReal ProbabilityTheory BigOperators

noncomputable section

def recoveredNoise {d m : ℕ} (hmd : m ≤ d) (a : MSetAction d m) (y : ℝ) : ℝ :=
  8 * (y - 1 / 4 - (candidateCount hmd a : ℝ) / (8 * m))

@[fun_prop] theorem measurable_recoveredNoise {d m : ℕ} (hmd : m ≤ d) :
    Measurable (fun ay : MSetAction d m × ℝ => recoveredNoise hmd ay.1 ay.2) := by
  unfold recoveredNoise
  exact measurable_const.mul <|
    (measurable_snd.sub_const _).sub <|
      ((measurable_of_finite (fun a : MSetAction d m => (candidateCount hmd a : ℝ))).comp
        measurable_fst).div_const _

theorem recoveredNoise_reference {d m : ℕ} (hm : 1 ≤ m) (hmd : m ≤ d)
    (a : MSetAction d m) (z : ℝ) :
    recoveredNoise hmd a (actionLoss a (referenceItemLoss hmd z)) = z := by
  rw [actionLoss_referenceItemLoss hm hmd]
  unfold recoveredNoise
  ring

theorem recoveredNoise_planted_missed {d m : ℕ} (hm : 1 ≤ m) (hmd : m ≤ d)
    (a : MSetAction d m) (z Delta : ℝ) (i : Fin d) (hi : i ∉ a.val) :
    recoveredNoise hmd a (actionLoss a (plantedItemLoss hmd z Delta 1 i)) = z := by
  rw [actionLoss_plantedItemLoss hm hmd]
  simp only [if_neg hi, mul_zero, sub_zero]
  unfold recoveredNoise
  ring

/-- On selected rounds the score contribution vanishes, so recovery of the
latent noise is neither asserted nor needed in the planted environment. -/
theorem recovered_shape_missed_planted {d m : ℕ} (hm : 1 ≤ m) (hmd : m ≤ d)
    (a : MSetAction d m) (z Delta : ℝ) (i : Fin d) :
    shape (recoveredNoise hmd a (actionLoss a (plantedItemLoss hmd z Delta 1 i))) *
        missedIndicator i a = shape z * missedIndicator i a := by
  classical
  by_cases hi : i ∈ a.val
  · simp [missedIndicator, hi]
  · rw [recoveredNoise_planted_missed hm hmd a z Delta i hi]

def observableMissedShapeSum {d m : ℕ} (hmd : m ≤ d) (i : Fin d) :
    (t : ℕ) → History d m t → ℝ
  | 0, _ => 0
  | t + 1, h => observableMissedShapeSum hmd i t h.1 +
      shape (recoveredNoise hmd h.2.1 h.2.2) * missedIndicator i h.2.1

theorem measurable_observableMissedShapeSum {d m : ℕ} (hmd : m ≤ d) (i : Fin d) :
    ∀ t, Measurable (observableMissedShapeSum hmd i t) := by
  intro t
  induction t with
  | zero => exact measurable_const
  | succ t ih =>
      exact (ih.comp measurable_fst).add <|
        ((measurable_shape.comp (measurable_recoveredNoise hmd)).comp measurable_snd).mul
          ((measurable_of_finite (missedIndicator i)).comp measurable_snd.fst)

def observableScore {d m : ℕ} (hmd : m ≤ d) (Delta : ℝ) (i : Fin d)
    (t : ℕ) (h : History d m t) : ℝ :=
  cumulativePenalty hmd t h + Delta * observableMissedShapeSum hmd i t h

theorem measurable_observableScore {d m : ℕ} (hmd : m ≤ d) (Delta : ℝ) (i : Fin d)
    (t : ℕ) : Measurable (observableScore hmd Delta i t) :=
  (measurable_cumulativePenalty hmd t).add
    ((measurable_observableMissedShapeSum hmd i t).const_mul Delta)

def scoreEvent {d m : ℕ} (hmd : m ≤ d) (Delta : ℝ) (i : Fin d) (T : ℕ) :
    Set (History d m T) := {h | Delta * T / 8 ≤ observableScore hmd Delta i T h}

theorem measurableSet_scoreEvent {d m : ℕ} (hmd : m ≤ d) (Delta : ℝ) (i : Fin d) (T : ℕ) :
    MeasurableSet (scoreEvent hmd Delta i T) :=
  measurableSet_le measurable_const (measurable_observableScore hmd Delta i T)

theorem observableMissed_eq_reference {d m T : ℕ} (hm : 1 ≤ m) (hmd : m ≤ d)
    (Z : Table T) (i : Fin d) : ∀ t (h : History d m t),
    ProtocolHistoryCompatible ((referenceTableLossProcess hm hmd T).at Z) t h →
      observableMissedShapeSum hmd i t h = missedShapeSum Z i t h := by
  intro t
  induction t with
  | zero => intro h _; rfl
  | succ t ih =>
      intro h hh
      change ProtocolHistoryCompatible _ t h.1 ∧
        h.2.2 = actionLoss h.2.1 (referenceItemLoss hmd (tableNoise Z t)) at hh
      simp only [observableMissedShapeSum, missedShapeSum]
      rw [ih h.1 hh.1, hh.2, recoveredNoise_reference hm hmd]

theorem observableMissed_eq_planted {d m T : ℕ} (hm : 1 ≤ m) (hmd : m ≤ d)
    (Delta : ℝ) (hDelta : 0 ≤ Delta) (hsmall : (m : ℝ) * Delta ≤ 1 / 2 ^ 13)
    (Z : Table T) (i : Fin d) : ∀ t (h : History d m t),
    ProtocolHistoryCompatible ((plantedTableLossProcess hm hmd Delta hDelta hsmall i T).at Z) t h →
      observableMissedShapeSum hmd i t h = missedShapeSum Z i t h := by
  intro t
  induction t with
  | zero => intro h _; rfl
  | succ t ih =>
      intro h hh
      change ProtocolHistoryCompatible _ t h.1 ∧
        h.2.2 = actionLoss h.2.1 (plantedItemLoss hmd (tableNoise Z t) Delta 1 i) at hh
      simp only [observableMissedShapeSum, missedShapeSum]
      rw [ih h.1 hh.1, hh.2, recovered_shape_missed_planted hm hmd]

theorem observableScore_eq_reference_ae {d m T : ℕ}
    (P : Policy d m) (hm : 1 ≤ m) (hmd : m ≤ d)
    (Delta : ℝ) (Z : Table T) (i : Fin d) (t : ℕ) :
    ∀ᵐ h ∂runLaw P ((referenceTableLossProcess hm hmd T).at Z) t,
      observableScore hmd Delta i t h = score hmd Z Delta i t h := by
  filter_upwards [ae_runLaw_protocolHistoryCompatible P
    ((referenceTableLossProcess hm hmd T).at Z) t] with h hh
  unfold observableScore score
  rw [observableMissed_eq_reference hm hmd Z i t h hh]

theorem observableScore_eq_planted_regret_ae {d m T : ℕ}
    (P : Policy d m) (hm : 1 ≤ m) (hmd : m ≤ d)
    (Delta : ℝ) (hDelta : 0 ≤ Delta) (hsmall : (m : ℝ) * Delta ≤ 1 / 2 ^ 13)
    (Z : Table T) (i : Fin d) (hi : i ∈ confidenceCandidates d m hmd) (t : ℕ) :
    ∀ᵐ h ∂runLaw P ((plantedTableLossProcess hm hmd Delta hDelta hsmall i T).at Z) t,
      observableScore hmd Delta i t h =
        pathRegret ((plantedTableLossProcess hm hmd Delta hDelta hsmall i T).at Z) t h := by
  filter_upwards [ae_runLaw_protocolHistoryCompatible P
    ((plantedTableLossProcess hm hmd Delta hDelta hsmall i T).at Z) t] with h hh
  rw [planted_pathRegret_eq_score hm hmd Delta hDelta hsmall i hi Z]
  unfold observableScore score
  rw [observableMissed_eq_planted hm hmd Delta hDelta hsmall Z i t h hh]

/-- The single history-measurable event is the true regret-tail event under
the planted run, with the same functional definition as under the reference. -/
theorem planted_scoreEvent_eq_regret_probability {d m T : ℕ}
    (P : Policy d m) (hm : 1 ≤ m) (hmd : m ≤ d)
    (Delta : ℝ) (hDelta : 0 ≤ Delta) (hsmall : (m : ℝ) * Delta ≤ 1 / 2 ^ 13)
    (Z : Table T) (i : Fin d) (hi : i ∈ confidenceCandidates d m hmd) :
    (runLaw P ((plantedTableLossProcess hm hmd Delta hDelta hsmall i T).at Z) T).real
      (scoreEvent hmd Delta i T) =
    (runLaw P ((plantedTableLossProcess hm hmd Delta hDelta hsmall i T).at Z) T).real
      {h | Delta * T / 8 ≤
        pathRegret ((plantedTableLossProcess hm hmd Delta hDelta hsmall i T).at Z) T h} := by
  apply congrArg ENNReal.toReal
  apply measure_congr
  filter_upwards [observableScore_eq_planted_regret_ae P hm hmd Delta hDelta hsmall Z i hi T]
    with h hh
  apply propext
  change (Delta * T / 8 ≤ observableScore hmd Delta i T h) ↔ _
  rw [hh]

end

end MsetsPaper.Lower.ConfidenceOblivious
