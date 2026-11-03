import MsetsPaper.Probability.ExecutionMeasure
import Mathlib.Probability.Martingale.Basic

/-! Canonical finite-horizon probability space for a branching law.
The sample is the terminal action path. Time i reveals precisely its treePrefix,
and nodewise one-step inequalities give a genuine Mathlib supermartingale. -/

noncomputable section
open MeasureTheory ProbabilityTheory Set
open scoped BigOperators ENNReal

namespace MsetsPaper.Probability.CanonicalFiniteTree

variable {α : Type} [Fintype α]

local instance (t : ℕ) : MeasurableSpace (ActionTree α t) := ⊤
local instance (t : ℕ) : MeasurableSingletonClass (ActionTree α t) :=
  ⟨fun _ => trivial⟩

def treePrefix {s t : ℕ} (h : s ≤ t) : ActionTree α t → ActionTree α s :=
  Nat.leRecOn (C := fun k => ActionTree α k → ActionTree α s) h
    (fun f x => f x.1) id

@[simp] theorem prefix_self (t : ℕ) (x : ActionTree α t) : treePrefix (le_refl t) x = x := by
  simp [treePrefix, Nat.leRecOn_self]

theorem prefix_succ {s t : ℕ} (h : s ≤ t) (x : ActionTree α t) (a : α) :
    treePrefix (Nat.le.step h) (x, a) = treePrefix h x := by
  simp only [treePrefix, Nat.leRecOn_succ h]

theorem prefix_trans {r s t : ℕ} (hrs : r ≤ s) (hst : s ≤ t)
    (x : ActionTree α t) : treePrefix hrs (treePrefix hst x) = treePrefix (hrs.trans hst) x := by
  induction t, hst using Nat.le_induction with
  | base => simp
  | succ t hst ih =>
    rcases x with ⟨x, a⟩
    rw [prefix_succ hst, prefix_succ (hrs.trans hst)]
    exact ih x

theorem expectation_prefix (P : BranchingLaw α) {s t : ℕ} (h : s ≤ t)
    (f : ActionTree α s → ℝ) :
    P.expectation t (fun x => f (treePrefix h x)) = P.expectation s f := by
  induction t, h using Nat.le_induction with
  | base => simp
  | succ t h ih =>
    rw [P.expectation_succ]
    simp only [prefix_succ h, ← Finset.sum_mul, P.sum_one, one_mul]
    exact ih

def pathMeasure (P : BranchingLaw α) (T : ℕ) : Measure (ActionTree α T) :=
  finiteAtomicMeasure (P.mass T) id

instance pathMeasure_isProbabilityMeasure (P : BranchingLaw α) (T : ℕ) :
    IsProbabilityMeasure (pathMeasure P T) :=
  finiteAtomicMeasure_isProbabilityMeasure _ (P.mass_nonneg T) id (P.mass_sum_one T)

theorem integral_pathMeasure (P : BranchingLaw α) (T : ℕ)
    (f : ActionTree α T → ℝ) :
    (∫ x, f x ∂pathMeasure P T) = P.expectation T f :=
  integral_finiteAtomicMeasure _ (P.mass_nonneg T) id f

theorem integrable_pathMeasure (P : BranchingLaw α) (T : ℕ)
    (f : ActionTree α T → ℝ) : Integrable f (pathMeasure P T) :=
  integrable_finiteAtomicMeasure _ id f

def prefixFiltration (T : ℕ) : Filtration (Fin (T + 1)) (⊤ : MeasurableSpace (ActionTree α T)) where
  seq i := MeasurableSpace.comap (treePrefix (Nat.le_of_lt_succ i.isLt)) ⊤
  mono' i j hij := by
    apply MeasurableSpace.comap_le_comap_of_eq_comp (treePrefix (show i.val ≤ j.val from hij))
      (measurable_of_finite _)
    funext x
    exact (prefix_trans (show i.val ≤ j.val from hij) (Nat.le_of_lt_succ j.isLt) x).symm
  le' _ := le_top

def process (T : ℕ) (M : (t : ℕ) → ActionTree α t → ℝ)
    (i : Fin (T + 1)) (x : ActionTree α T) : ℝ :=
  M i.val (treePrefix (Nat.le_of_lt_succ i.isLt) x)

theorem process_stronglyAdapted (T : ℕ) (M : (t : ℕ) → ActionTree α t → ℝ) :
    StronglyAdapted (prefixFiltration T) (process T M) := by
  intro i
  exact ((measurable_of_finite (M i.val)).comp
    (comap_measurable (treePrefix (Nat.le_of_lt_succ i.isLt)))).stronglyMeasurable

theorem integral_process (P : BranchingLaw α) (T : ℕ)
    (M : (t : ℕ) → ActionTree α t → ℝ) (i : Fin (T + 1)) :
    (∫ x, process T M i x ∂pathMeasure P T) = P.expectation i.val (M i.val) := by
  rw [integral_pathMeasure]
  exact expectation_prefix P (Nat.le_of_lt_succ i.isLt) (M i.val)

end MsetsPaper.Probability.CanonicalFiniteTree
