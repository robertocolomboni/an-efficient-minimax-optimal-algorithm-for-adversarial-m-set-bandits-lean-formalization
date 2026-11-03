import MsetsPaper.Lower.MainNewRoute
import MsetsLower.Lower.OrdinaryBandit

/-! # Exact one-set / ordinary-arm identification

The imported ordinary-bandit module contributes only the singleton encoding
and its loss identity here, not any old lower-bound endpoint.
-/

namespace MsetsPaper.Lower.NewRoute

open MsetsLower MsetsLower.Lower MeasureTheory Set

noncomputable section

theorem singletonAction_injective (K : ℕ) :
    Function.Injective (@singletonAction K) := by
  intro i j hij
  have hfin : ({i} : Finset (Fin K)) = {j} := congrArg Subtype.val hij
  simpa using hfin

theorem singletonAction_surjective (K : ℕ) :
    Function.Surjective (@singletonAction K) := by
  intro a
  obtain ⟨i, hi⟩ := Finset.card_eq_one.mp a.property
  refine ⟨i, Subtype.ext ?_⟩
  exact hi.symm

/-- Thus `Policy K 1` uses exactly the ordinary K arms, with no extra action. -/
def ordinaryArmEquiv (K : ℕ) : Fin K ≃ MSetAction K 1 :=
  Equiv.ofBijective singletonAction
    ⟨singletonAction_injective K, singletonAction_surjective K⟩

@[simp] theorem ordinaryArmEquiv_loss {K : ℕ} (i : Fin K) (ell : Fin K → ℝ) :
    actionLoss (ordinaryArmEquiv K i) ell = ell i :=
  actionLoss_singletonAction i ell

/-- Action-level normalization becomes coordinatewise normalization at m=1. -/
theorem ordinary_item_range {K : ℕ} (L : LossProcess K 1)
    (t : ℕ) (h : History K 1 t) (i : Fin K) :
    L.itemLoss t h i ∈ Icc (0 : ℝ) 1 := by
  simpa using L.action_mem_Icc t h (singletonAction i)

/-- The fully explicit ordinary-bandit specialization of the NEW T3. -/
theorem ordinary_bandits_lower_bound_explicit {K T : ℕ} (hK : 2 ≤ K)
    {delta : ℝ} (hdelta : 0 < delta) (hsmall : delta ≤ (2 : ℝ) ^ (-36 : ℤ))
    (hT : Nat.ceil (64 * (K : ℝ) ^ 2 + 4 * (K : ℝ) * Real.log (1 / delta)) ≤ T) :
    ∀ P : Policy K 1, ∃ L : LossProcess K 1,
      (∀ t (h : History K 1 t) i, L.itemLoss t h i ∈ Icc (0 : ℝ) 1) ∧
      delta ≤ (runLaw P L T).real
        {h | (2 : ℝ) ^ (-43 : ℤ) * Real.sqrt ((K : ℝ) * T *
          (Real.log (K : ℝ) + Real.log (1 / delta))) ≤ pathRegret L T h} := by
  intro P
  have ht : horizon K 1 delta ≤ T := by simpa only [horizon_one hK] using hT
  obtain ⟨L, _hact, htail⟩ := NewRoute.lower_bound_explicit
    hK (by omega : 1 ≤ 1) (by omega : 1 ≤ K - 1) hdelta hsmall ht P
  refine ⟨L, ordinary_item_range L, ?_⟩
  simpa only [Nat.choose_one_right] using htail

def QualitativeOrdinaryBanditLowerBound : Prop :=
  ∃ (c delta0 : ℝ) (tau : ℕ → ℝ → ℕ),
    0 < c ∧ delta0 ∈ Ioo (0 : ℝ) 1 ∧
    (∀ K delta, 2 ≤ K → 0 < delta → delta ≤ delta0 →
      (tau K delta : ℝ) ≤ thresholdPolynomial K delta) ∧
    (∀ K delta T, 2 ≤ K → 0 < delta → delta ≤ delta0 → tau K delta ≤ T →
      ∀ P : Policy K 1, ∃ L : LossProcess K 1,
        (∀ t (h : History K 1 t) i, L.itemLoss t h i ∈ Icc (0 : ℝ) 1) ∧
        delta ≤ (runLaw P L T).real
          {h | c * Real.sqrt ((K : ℝ) * T *
            (Real.log (K : ℝ) + Real.log (1 / delta))) ≤ pathRegret L T h})

/-- C1 follows T2 exactly as in its English proof: use m=1 and tau(K,1,delta). -/
theorem ordinary_bandits_lower_bound : QualitativeOrdinaryBanditLowerBound := by
  obtain ⟨c, delta0, tau, hc, hdelta0, hpoly, hmain⟩ := NewRoute.lower_bound
  refine ⟨c, delta0, fun K delta ↦ tau K 1 delta, hc, hdelta0, ?_, ?_⟩
  · intro K delta hK hdelta hsmall
    exact hpoly K 1 delta (by omega) hdelta hsmall
  · intro K delta T hK hdelta hsmall hT P
    obtain ⟨L, _hact, htail⟩ := hmain K 1 delta T hK (by omega) (by omega)
      hdelta hsmall hT P
    refine ⟨L, ordinary_item_range L, ?_⟩
    simpa only [Nat.choose_one_right] using htail

end

end MsetsPaper.Lower.NewRoute
