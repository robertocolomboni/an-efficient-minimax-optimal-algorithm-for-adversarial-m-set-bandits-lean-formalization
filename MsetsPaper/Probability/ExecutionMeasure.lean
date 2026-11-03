import MsetsPaper.Probability.FiniteTree
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Measure.GiryMonad
import Mathlib.MeasureTheory.Function.SpecialFunctions.Basic
import Mathlib.Tactic

/-!
# Exact measure-theoretic interpretation of finite atomic experiments

These identities connect the explicit finite sums to genuine measures,
integrals, and event probabilities.  They do not assume an execution-law
equivalence or any concentration conclusion.
-/

noncomputable section

open scoped BigOperators ENNReal
open MeasureTheory

namespace MsetsPaper.Probability

variable {α β : Type*} [Fintype α] [MeasurableSpace β]

def finiteAtomicMeasure (w : α → ℝ) (f : α → β) : Measure β :=
  ∑ a, ENNReal.ofReal (w a) • Measure.dirac (f a)

open Classical in
theorem finiteAtomicMeasure_apply (w : α → ℝ) (f : α → β)
    (s : Set β) (hs : MeasurableSet s) :
    finiteAtomicMeasure w f s =
      ∑ a, ENNReal.ofReal (w a) * (if f a ∈ s then 1 else 0) := by
  classical
  simp only [finiteAtomicMeasure, Measure.finsetSum_apply, Measure.smul_apply,
    smul_eq_mul, Measure.dirac_apply' _ hs, Set.indicator_apply, Pi.one_apply]

open Classical in
theorem finiteAtomicMeasure_apply_eq_ofReal (w : α → ℝ) (hw : ∀ a, 0 ≤ w a)
    (f : α → β) (s : Set β) (hs : MeasurableSet s) :
    finiteAtomicMeasure w f s =
      ENNReal.ofReal (∑ a, w a * (if f a ∈ s then 1 else 0)) := by
  classical
  rw [finiteAtomicMeasure_apply w f s hs,
    ENNReal.ofReal_sum_of_nonneg (fun a _ => mul_nonneg (hw a) (by positivity))]
  apply Finset.sum_congr rfl
  intro a _
  by_cases ha : f a ∈ s <;> simp [ha]

open Classical in
theorem finiteAtomicMeasure_real_apply (w : α → ℝ) (hw : ∀ a, 0 ≤ w a)
    (f : α → β) (s : Set β) (hs : MeasurableSet s) :
    (finiteAtomicMeasure w f).real s = ∑ a, w a * (if f a ∈ s then 1 else 0) := by
  classical
  rw [Measure.real_def, finiteAtomicMeasure_apply_eq_ofReal w hw f s hs,
    ENNReal.toReal_ofReal]
  exact Finset.sum_nonneg (fun a _ => mul_nonneg (hw a) (by positivity))

theorem finiteAtomicMeasure_univ (w : α → ℝ) (hw : ∀ a, 0 ≤ w a)
    (f : α → β) (hsum : ∑ a, w a = 1) : finiteAtomicMeasure w f Set.univ = 1 := by
  rw [finiteAtomicMeasure_apply_eq_ofReal w hw f Set.univ MeasurableSet.univ]
  simp only [Set.mem_univ, ite_true, mul_one, hsum, ENNReal.ofReal_one]

theorem finiteAtomicMeasure_isProbabilityMeasure (w : α → ℝ) (hw : ∀ a, 0 ≤ w a)
    (f : α → β) (hsum : ∑ a, w a = 1) : IsProbabilityMeasure (finiteAtomicMeasure w f) :=
  ⟨finiteAtomicMeasure_univ w hw f hsum⟩

open Classical in
/-- Finite atomic measures evaluate every subset by its atoms.  Measurable
singletons suffice; global measurability of the subset is unnecessary. -/
theorem finiteAtomicMeasure_real_apply_of_singletons [MeasurableSingletonClass β]
    (w : α → ℝ) (hw : ∀ a, 0 ≤ w a) (f : α → β) (s : Set β) :
    (finiteAtomicMeasure w f).real s = ∑ a, w a * (if f a ∈ s then 1 else 0) := by
  classical
  have heq : finiteAtomicMeasure w f s =
      ENNReal.ofReal (∑ a, w a * (if f a ∈ s then 1 else 0)) := by
    rw [ENNReal.ofReal_sum_of_nonneg (fun a _ => mul_nonneg (hw a) (by positivity))]
    simp only [finiteAtomicMeasure, Measure.finsetSum_apply, Measure.smul_apply,
      smul_eq_mul, Measure.dirac_apply, Set.indicator_apply, Pi.one_apply]
    apply Finset.sum_congr rfl
    intro a _
    by_cases ha : f a ∈ s <;> simp [ha]
  rw [Measure.real_def, heq, ENNReal.toReal_ofReal]
  exact Finset.sum_nonneg (fun a _ => mul_nonneg (hw a) (by positivity))

theorem ae_finiteAtomicMeasure_of_forall [MeasurableSingletonClass β]
    (w : α → ℝ) (f : α → β) (p : β → Prop) (hp : ∀ a, p (f a)) :
    ∀ᵐ x ∂finiteAtomicMeasure w f, p x := by
  rw [finiteAtomicMeasure, ae_finsetSum_measure_iff]
  intro a _
  exact Measure.ae_smul_measure (by simpa using hp a) _

theorem lintegral_finiteAtomicMeasure [MeasurableSingletonClass β]
    (w : α → ℝ) (f : α → β) (g : β → ℝ≥0∞) :
    ∫⁻ x, g x ∂finiteAtomicMeasure w f = ∑ a, ENNReal.ofReal (w a) * g (f a) := by
  simp only [finiteAtomicMeasure, lintegral_finsetSum_measure,
    lintegral_smul_measure, lintegral_dirac, smul_eq_mul]

theorem integrable_finiteAtomicMeasure [MeasurableSingletonClass β]
    (w : α → ℝ) (f : α → β) (g : β → ℝ) : Integrable g (finiteAtomicMeasure w f) := by
  apply integrable_finsetSum_measure.mpr
  intro a _
  exact (integrable_dirac (by simp)).smul_measure ENNReal.ofReal_ne_top

theorem integral_finiteAtomicMeasure [MeasurableSingletonClass β]
    (w : α → ℝ) (hw : ∀ a, 0 ≤ w a) (f : α → β) (g : β → ℝ) :
    ∫ x, g x ∂finiteAtomicMeasure w f = ∑ a, w a * g (f a) := by
  rw [finiteAtomicMeasure, integral_finsetSum_measure]
  · simp only [integral_smul_measure, integral_dirac, ENNReal.toReal_ofReal (hw _), smul_eq_mul]
  · intro a _
    exact (integrable_dirac (by simp)).smul_measure ENNReal.ofReal_ne_top

theorem measurable_finiteAtomicMeasure {Ω : Type*} [MeasurableSpace Ω]
    (w : Ω → α → ℝ) (hw : ∀ a, Measurable (fun x => w x a)) (f : α → β) :
    Measurable (fun x => finiteAtomicMeasure (w x) f) := by
  classical
  apply Finset.measurable_sum
  intro a _
  exact ((hw a).ennreal_ofReal).smul_measure (Measure.dirac (f a))

end MsetsPaper.Probability
