import MsetsPaper.Probability.CanonicalFiniteTree

/-! Nodewise drift implies a Mathlib supermartingale on terminal paths.
The expectation conclusion below is obtained from that supermartingale's
set-integral inequality and is intended for the actual tail proof. -/

noncomputable section
open MeasureTheory ProbabilityTheory Set
open scoped BigOperators ENNReal

namespace MsetsPaper.Probability.CanonicalFiniteTree

variable {α : Type} [Fintype α]
local instance (t : ℕ) : MeasurableSpace (ActionTree α t) := ⊤
local instance (t : ℕ) : MeasurableSingletonClass (ActionTree α t) :=
  ⟨fun _ => trivial⟩

open Classical in
theorem restricted_expectation_le (P : BranchingLaw α)
    (M : (t : ℕ) → ActionTree α t → ℝ) (T : ℕ)
    (hstep : ∀ t < T, ∀ h, (∑ a, P.next t h a * M (t + 1) (h, a)) ≤ M t h)
    {i j : ℕ} (hij : i ≤ j) (hjT : j ≤ T) (s : Set (ActionTree α i)) :
    P.expectation j (fun h => if treePrefix hij h ∈ s then M j h else 0) ≤
      P.expectation i (fun h => if h ∈ s then M i h else 0) := by
  classical
  revert hjT
  induction j, hij using Nat.le_induction with
  | base => intro _; simp
  | succ j hij ih =>
    intro hjT
    rw [P.expectation_succ]
    apply (P.expectation_mono j _ _ ?_).trans (ih (Nat.le_of_succ_le hjT))
    intro h
    simp only [prefix_succ hij]
    by_cases hh : treePrefix hij h ∈ s
    · simp only [hh, ite_true]
      exact hstep j (lt_of_lt_of_le (Nat.lt_succ_self j) hjT) h
    · simp only [hh, ite_false, mul_zero, Finset.sum_const_zero]
      exact le_rfl

open Classical in
theorem setIntegral_prefix (P : BranchingLaw α) {i j T : ℕ}
    (hij : i ≤ j) (hjT : j ≤ T) (f : ActionTree α j → ℝ)
    (s : Set (ActionTree α i)) :
    (∫ x in treePrefix (hij.trans hjT) ⁻¹' s, f (treePrefix hjT x) ∂pathMeasure P T) =
      P.expectation j (fun h => if treePrefix hij h ∈ s then f h else 0) := by
  classical
  rw [← integral_indicator (show MeasurableSet (treePrefix (hij.trans hjT) ⁻¹' s) by trivial),
    integral_pathMeasure]
  change P.expectation T (fun x =>
    if treePrefix (hij.trans hjT) x ∈ s then f (treePrefix hjT x) else 0) = _
  have h := expectation_prefix P hjT (fun h => if treePrefix hij h ∈ s then f h else 0)
  simp_rw [prefix_trans] at h
  exact h

theorem supermartingale_of_step (P : BranchingLaw α)
    (M : (t : ℕ) → ActionTree α t → ℝ) (T : ℕ)
    (hstep : ∀ t < T, ∀ h, (∑ a, P.next t h a * M (t + 1) (h, a)) ≤ M t h) :
    Supermartingale (process T M) (prefixFiltration T) (pathMeasure P T) := by
  classical
  have hset (i j : Fin (T + 1)) (hij : i ≤ j) (s : Set (ActionTree α T))
      (hs : MeasurableSet[prefixFiltration T i] s) :
      (∫ x in s, process T M j x ∂pathMeasure P T) ≤
        ∫ x in s, process T M i x ∂pathMeasure P T := by
    obtain ⟨s', _hs', rfl⟩ := hs
    change (∫ x in treePrefix (Nat.le_of_lt_succ i.isLt) ⁻¹' s',
      M j.val (treePrefix (Nat.le_of_lt_succ j.isLt) x) ∂pathMeasure P T) ≤
      ∫ x in treePrefix (Nat.le_of_lt_succ i.isLt) ⁻¹' s',
        M i.val (treePrefix (Nat.le_of_lt_succ i.isLt) x) ∂pathMeasure P T
    rw [setIntegral_prefix P (show i.val ≤ j.val from hij) (Nat.le_of_lt_succ j.isLt),
      setIntegral_prefix P (le_refl i.val) (Nat.le_of_lt_succ i.isLt)]
    simp_rw [prefix_self]
    exact restricted_expectation_le P M T hstep
      (show i.val ≤ j.val from hij) (Nat.le_of_lt_succ j.isLt) s'
  have hsub : Submartingale (fun i x => -process T M i x)
      (prefixFiltration T) (pathMeasure P T) := by
    apply submartingale_of_setIntegral_le (process_stronglyAdapted T M).neg
      (fun i => (integrable_pathMeasure P T (process T M i)).neg)
    intro i j hij s hs
    change (∫ x in s, -process T M i x ∂pathMeasure P T) ≤
      ∫ x in s, -process T M j x ∂pathMeasure P T
    rw [integral_neg, integral_neg]
    exact neg_le_neg (hset i j hij s hs)
  convert hsub.neg using 1
  funext i x
  exact (neg_neg _).symm

/-- The actual finite-sum expectation bound is now a consequence of
Mathlib.Supermartingale.setIntegral_le on the canonical terminal space. -/
theorem expectation_le_initial (P : BranchingLaw α)
    (M : (t : ℕ) → ActionTree α t → ℝ) (T : ℕ)
    (hstep : ∀ t < T, ∀ h, (∑ a, P.next t h a * M (t + 1) (h, a)) ≤ M t h) :
    P.expectation T (M T) ≤ M 0 () := by
  have h := (supermartingale_of_step P M T hstep).setIntegral_le
    (i := (0 : Fin (T + 1))) (j := Fin.last T) (Fin.zero_le _)
    (s := Set.univ) MeasurableSet.univ
  rw [setIntegral_univ, setIntegral_univ, integral_process, integral_process] at h
  have hzero : P.expectation 0 (M 0) = M 0 () := by
    change (∑ x : Unit, (1 : ℝ) * M 0 x) = M 0 ()
    rw [Fintype.sum_unique, one_mul]
  simpa only [Fin.val_last, Fin.val_zero, hzero] using h

end MsetsPaper.Probability.CanonicalFiniteTree
