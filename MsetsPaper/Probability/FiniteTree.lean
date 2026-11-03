import Mathlib.Algebra.BigOperators.Field
import Mathlib.Data.Fintype.Prod
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Algebra.BigOperators.Group.Finset.Sigma
import Mathlib.Data.Real.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-!
# Exact finite conditional experiments

A depth-t node records the t actions already sampled. `next t h` is the
actual conditional law at that node, allowed to depend on the entire prefix.
The finite tower property is proved by summing the recursively defined path
probabilities, rather than postulated as a martingale certificate.

This representation is not yet the bridge to the manuscript's observable
history kernels. That equivalence and each algorithmic instance are separate
obligations; the generic results here do not assert the upper theorem.
-/

namespace MsetsPaper.Probability

open scoped BigOperators

def ActionTree (α : Type) : ℕ → Type
  | 0 => Unit
  | t + 1 => ActionTree α t × α

instance {α : Type} [Fintype α] : (t : ℕ) → Fintype (ActionTree α t)
  | 0 => inferInstanceAs (Fintype Unit)
  | t + 1 => by
    letI : Fintype (ActionTree α t) := instFintypeActionTree t
    exact inferInstanceAs (Fintype (ActionTree α t × α))

structure BranchingLaw (α : Type) [Fintype α] where
  next : (t : ℕ) → ActionTree α t → α → ℝ
  nonneg : ∀ t h a, 0 ≤ next t h a
  sum_one : ∀ t h, ∑ a, next t h a = 1

variable {α : Type} [Fintype α]

namespace BranchingLaw

noncomputable def mass (P : BranchingLaw α) : (t : ℕ) → ActionTree α t → ℝ
  | 0, _ => 1
  | t + 1, (h, a) => P.mass t h * P.next t h a

@[simp] theorem mass_zero (P : BranchingLaw α) (h : ActionTree α 0) : P.mass 0 h = 1 := rfl

@[simp] theorem mass_succ (P : BranchingLaw α) (t : ℕ) (h : ActionTree α t) (a : α) :
    P.mass (t + 1) (h, a) = P.mass t h * P.next t h a := rfl

theorem mass_nonneg (P : BranchingLaw α) : ∀ t h, 0 ≤ P.mass t h := by
  intro t
  induction t with
  | zero => intro h; exact zero_le_one
  | succ t ih =>
    rintro ⟨h, a⟩
    exact mul_nonneg (ih h) (P.nonneg t h a)

theorem mass_sum_one (P : BranchingLaw α) : ∀ t, ∑ h, P.mass t h = 1 := by
  intro t
  induction t with
  | zero =>
    change (∑ _h : Unit, (1 : ℝ)) = 1
    simp
  | succ t ih =>
    change (∑ h : ActionTree α t × α, P.mass t h.1 * P.next t h.1 h.2) = 1
    rw [Fintype.sum_prod_type]
    simp only [← Finset.mul_sum, P.sum_one, mul_one, ih]

noncomputable def expectation (P : BranchingLaw α) (t : ℕ) (f : ActionTree α t → ℝ) : ℝ :=
  ∑ h, P.mass t h * f h

noncomputable def probability (P : BranchingLaw α) (t : ℕ) (E : Set (ActionTree α t)) : ℝ := by
  classical
  exact P.expectation t (fun h ↦ if h ∈ E then 1 else 0)

theorem expectation_const (P : BranchingLaw α) (t : ℕ) (c : ℝ) :
    P.expectation t (fun _ ↦ c) = c := by
  rw [expectation, ← Finset.sum_mul, P.mass_sum_one, one_mul]

theorem expectation_add (P : BranchingLaw α) (t : ℕ) (f g : ActionTree α t → ℝ) :
    P.expectation t (fun h ↦ f h + g h) = P.expectation t f + P.expectation t g := by
  simp only [expectation, mul_add, Finset.sum_add_distrib]

theorem expectation_const_mul (P : BranchingLaw α) (t : ℕ)
    (f : ActionTree α t → ℝ) (c : ℝ) :
    P.expectation t (fun h ↦ c * f h) = c * P.expectation t f := by
  unfold expectation
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro h _
  ring

theorem expectation_nonneg (P : BranchingLaw α) (t : ℕ) (f : ActionTree α t → ℝ)
    (hf : ∀ h, 0 ≤ f h) : 0 ≤ P.expectation t f := by
  exact Finset.sum_nonneg (fun h _ ↦ mul_nonneg (P.mass_nonneg t h) (hf h))

theorem expectation_mono (P : BranchingLaw α) (t : ℕ) (f g : ActionTree α t → ℝ)
    (hfg : ∀ h, f h ≤ g h) : P.expectation t f ≤ P.expectation t g := by
  exact Finset.sum_le_sum (fun h _ ↦ mul_le_mul_of_nonneg_left (hfg h) (P.mass_nonneg t h))

/-- The exact tower property: average over the fresh draw, then the prefix. -/
theorem expectation_succ (P : BranchingLaw α) (t : ℕ)
    (f : ActionTree α (t + 1) → ℝ) :
    P.expectation (t + 1) f =
      P.expectation t (fun h ↦ ∑ a, P.next t h a * f (h, a)) := by
  change (∑ h : ActionTree α t × α, (P.mass t h.1 * P.next t h.1 h.2) * f h) = _
  rw [Fintype.sum_prod_type]
  simp only [expectation, Finset.mul_sum, mul_assoc]

theorem probability_mem_Icc (P : BranchingLaw α) (t : ℕ) (E : Set (ActionTree α t)) :
    P.probability t E ∈ Set.Icc (0 : ℝ) 1 := by
  classical
  refine ⟨P.expectation_nonneg t _ (fun h ↦ by split_ifs <;> norm_num), ?_⟩
  calc
    P.probability t E ≤ P.expectation t (fun _ ↦ 1) :=
      P.expectation_mono t _ _ (fun h ↦ by split_ifs <;> norm_num)
    _ = 1 := P.expectation_const t 1

theorem probability_mono (P : BranchingLaw α) (t : ℕ)
    (E F : Set (ActionTree α t)) (hEF : E ⊆ F) :
    P.probability t E ≤ P.probability t F := by
  classical
  apply P.expectation_mono
  intro h
  by_cases hh : h ∈ E
  · simp only [hh, hEF hh, ite_true, le_refl]
  · simp only [hh, ite_false]
    split_ifs <;> norm_num

theorem probability_add_compl (P : BranchingLaw α) (t : ℕ)
    (E : Set (ActionTree α t)) : P.probability t E + P.probability t Eᶜ = 1 := by
  classical
  unfold probability
  rw [← P.expectation_add]
  calc
    _ = P.expectation t (fun _ ↦ 1) := by
      unfold expectation
      apply Finset.sum_congr rfl
      intro h _
      by_cases hh : h ∈ E <;> simp [hh]
    _ = 1 := P.expectation_const t 1

theorem probability_le_of_compl_bound (P : BranchingLaw α) (t : ℕ)
    (E : Set (ActionTree α t)) {rho : ℝ} (hbad : P.probability t Eᶜ ≤ rho) :
    1 - rho ≤ P.probability t E := by
  linarith [P.probability_add_compl t E]

theorem probability_union_le (P : BranchingLaw α) (t : ℕ)
    (E F : Set (ActionTree α t)) :
    P.probability t (E ∪ F) ≤ P.probability t E + P.probability t F := by
  classical
  unfold probability
  rw [← P.expectation_add]
  apply P.expectation_mono
  intro h
  by_cases hE : h ∈ E <;> by_cases hF : h ∈ F <;> simp [hE, hF]

theorem probability_exists_le_sum {β : Type*} [Fintype β]
    (P : BranchingLaw α) (t : ℕ) (E : β → Set (ActionTree α t)) :
    P.probability t {h | ∃ b, h ∈ E b} ≤ ∑ b, P.probability t (E b) := by
  classical
  unfold probability expectation
  rw [Finset.sum_comm]
  apply Finset.sum_le_sum
  intro h _
  rw [← Finset.mul_sum]
  apply mul_le_mul_of_nonneg_left _ (P.mass_nonneg t h)
  by_cases hh : ∃ b, h ∈ E b
  · obtain ⟨b, hb⟩ := hh
    simp only [Set.mem_setOf_eq, show (∃ b, h ∈ E b) from ⟨b, hb⟩, ite_true]
    have hsum := Finset.single_le_sum (s := (Finset.univ : Finset β))
      (f := fun b ↦ if h ∈ E b then (1 : ℝ) else 0)
      (fun b _ ↦ by split_ifs <;> norm_num) (Finset.mem_univ b)
    simpa only [hb, ite_true] using hsum
  · simp only [Set.mem_setOf_eq, hh, ite_false]
    exact Finset.sum_nonneg (fun b _ ↦ by split_ifs <;> norm_num)

theorem probability_forall_ge_of_each {β : Type*} [Fintype β]
    (P : BranchingLaw α) (t : ℕ) (E : β → Set (ActionTree α t))
    (rho : β → ℝ) (hE : ∀ b, 1 - rho b ≤ P.probability t (E b)) :
    1 - ∑ b, rho b ≤ P.probability t {h | ∀ b, h ∈ E b} := by
  classical
  apply P.probability_le_of_compl_bound
  have hcompl : ({h | ∀ b, h ∈ E b} : Set (ActionTree α t))ᶜ =
      {h | ∃ b, h ∈ (E b)ᶜ} := by ext h; simp
  rw [hcompl]
  refine (P.probability_exists_le_sum t (fun b ↦ (E b)ᶜ)).trans ?_
  apply Finset.sum_le_sum
  intro b _
  linarith [P.probability_add_compl t (E b), hE b]

theorem probability_inter_ge (P : BranchingLaw α) (t : ℕ)
    (E F : Set (ActionTree α t)) {rho sigma : ℝ}
    (hE : 1 - rho ≤ P.probability t E) (hF : 1 - sigma ≤ P.probability t F) :
    1 - (rho + sigma) ≤ P.probability t (E ∩ F) := by
  apply P.probability_le_of_compl_bound
  rw [Set.compl_inter]
  have h := P.probability_union_le t Eᶜ Fᶜ
  linarith [P.probability_add_compl t E, P.probability_add_compl t F]

/-- Finite Markov inequality with no unproved integrability or measurability input. -/
theorem probability_ge_le_expectation_div (P : BranchingLaw α) (t : ℕ)
    (f : ActionTree α t → ℝ) (hf : ∀ h, 0 ≤ f h) {b : ℝ} (hb : 0 < b) :
    P.probability t {h | b ≤ f h} ≤ P.expectation t f / b := by
  classical
  apply (le_div_iff₀ hb).mpr
  calc
    P.probability t {h | b ≤ f h} * b =
        P.expectation t (fun h ↦ (if b ≤ f h then 1 else 0) * b) := by
      simp only [probability, expectation, Set.mem_setOf_eq, Finset.sum_mul, mul_assoc]
    _ ≤ P.expectation t f := by
      apply P.expectation_mono
      intro h
      split_ifs with hh
      · simpa using hh
      · simpa using hf h

/-- The finite-horizon expectation inequality for a nodewise supermartingale.
The one-step inequality is an upstream obligation, not the final tail claim. -/
theorem expectation_le_initial_of_step (P : BranchingLaw α)
    (M : (t : ℕ) → ActionTree α t → ℝ)
    (hstep : ∀ t h, (∑ a, P.next t h a * M (t + 1) (h, a)) ≤ M t h) :
    ∀ t, P.expectation t (M t) ≤ M 0 () := by
  intro t
  induction t with
  | zero =>
    change (∑ h : Unit, (1 : ℝ) * M 0 h) ≤ M 0 ()
    rw [Fintype.sum_unique, one_mul]
  | succ t ih =>
    rw [P.expectation_succ]
    exact (P.expectation_mono t _ _ (hstep t)).trans ih

/-- Finite-horizon form: no inequality is required after the terminal round. -/
theorem expectation_le_initial_of_step_upto (P : BranchingLaw α)
    (M : (t : ℕ) → ActionTree α t → ℝ) (T : ℕ) :
    (∀ t < T, ∀ h, (∑ a, P.next t h a * M (t + 1) (h, a)) ≤ M t h) →
      P.expectation T (M T) ≤ M 0 () := by
  induction T with
  | zero =>
    intro _
    change (∑ h : Unit, (1 : ℝ) * M 0 h) ≤ M 0 ()
    rw [Fintype.sum_unique, one_mul]
  | succ T ih =>
    intro hstep
    rw [P.expectation_succ]
    refine (P.expectation_mono T _ _ (hstep T (Nat.lt_succ_self T))).trans ?_
    exact ih (fun t ht h ↦ hstep t (Nat.lt_trans ht (Nat.lt_succ_self T)) h)

end BranchingLaw

end MsetsPaper.Probability
