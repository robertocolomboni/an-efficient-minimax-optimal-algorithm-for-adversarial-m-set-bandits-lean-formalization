import MsetsLower.Lower.Statement

/-!
# The ordinary-bandit specialization

An exact one-set is canonically a single arm.  This module records that
identification at the loss level and turns the explicit m-set conclusion at
`m=1` into the literal coordinatewise `[0,1]` loss-vector conclusion of the
ordinary-bandit corollary.
-/

namespace MsetsLower.Lower

open MsetsLower Set

noncomputable section

/-- The one-set action corresponding to an arm. -/
def singletonAction {K : Nat} (i : Fin K) : MSetAction K 1 :=
  ⟨{i}, by simp⟩

@[simp] theorem actionLoss_singletonAction {K : Nat} (i : Fin K)
    (loss : Fin K → Real) :
    actionLoss (singletonAction i) loss = loss i := by
  rw [actionLoss_eq_finset_sum]
  simp [singletonAction]

/-- Literal fixed-parameter conclusion for an ordinary `K`-armed policy.
`Policy K 1` uses singleton subsets as actions, canonically identified with
arms by `singletonAction`. -/
def OrdinaryBanditConclusion (K T : Nat) (hK : 1 ≤ K)
    (delta : Real) : Prop :=
  ∀ P : Policy K 1,
    ∃ L : LossProcess K 1,
      (∀ t (h : History K 1 t) i,
        L.itemLoss t h i ∈ Icc (0 : Real) 1) ∧
      ENNReal.ofReal delta ≤
        regretTailProbability hK P L T
          (finalLowerConstant * Real.sqrt ((K : Real) * (T : Real) *
            (Real.log (K : Real) + confidenceLog delta)))

/-- Specializing the explicit exact-set theorem to `m=1` gives the ordinary
bandit statement, including coordinatewise normalization of the loss vector. -/
theorem ordinaryBanditConclusion_of_explicit
    {K T : Nat} (hK : 2 ≤ K) {delta : Real}
    (h : ExplicitLowerConclusion K 1 T (by omega) delta) :
    OrdinaryBanditConclusion K T (by omega) delta := by
  intro P
  obtain ⟨L, htail⟩ := h P
  refine ⟨L, ?_, ?_⟩
  · intro t history i
    have haction := L.action_mem_Icc t history (singletonAction i)
    simpa using haction
  · have hchoose : Nat.choose K 1 = K := Nat.choose_one_right K
    simpa [lowerComplexity, hchoose] using htail

#print axioms actionLoss_singletonAction
#print axioms ordinaryBanditConclusion_of_explicit

end

end MsetsLower.Lower
