import MsetsPaper.Upper.FiniteKL
import MsetsPaper.Probability.ExecutionMeasure
import Mathlib.InformationTheory.KullbackLeibler.Basic

/-! The paper's extended-valued KL and the finite sums used by its upper
proofs agree for strictly positive reference laws. Zero comparator masses
are allowed. The excluded support-mismatch case has genuine value infinity.
-/

noncomputable section
open scoped BigOperators ENNReal
open MeasureTheory InformationTheory

namespace MsetsPaper.Probability

variable {α : Type*} [Fintype α] [MeasurableSpace α] [MeasurableSingletonClass α]

theorem finiteAtomicMeasure_id_singleton (p : α → ℝ) (a : α) :
    finiteAtomicMeasure p id {a} = ENNReal.ofReal (p a) := by
  classical
  simp [finiteAtomicMeasure_apply, eq_comm]

theorem finiteAtomicMeasure_withDensity_ratio_of_support (q p : α → ℝ)
    (hp : ∀ x, 0 ≤ p x) (hqp : ∀ x, p x = 0 → q x = 0) :
    (finiteAtomicMeasure p id).withDensity (fun x => ENNReal.ofReal (q x / p x)) =
      finiteAtomicMeasure q id := by
  classical
  unfold finiteAtomicMeasure
  rw [← Measure.sum_fintype, withDensity_sum, Measure.sum_fintype]
  apply Finset.sum_congr rfl
  intro x _
  rw [withDensity_smul_measure, dirac_withDensity, smul_smul]
  congr 1
  rw [← ENNReal.ofReal_mul (hp x)]
  congr 1
  simp only [id_eq]
  by_cases hpx : p x = 0
  · simp [hpx, hqp x hpx]
  · field_simp [hpx]

theorem finiteAtomicMeasure_withDensity_ratio (q p : α → ℝ)
    (_hq : ∀ x, 0 ≤ q x) (hp : ∀ x, 0 < p x) :
    (finiteAtomicMeasure p id).withDensity (fun x => ENNReal.ofReal (q x / p x)) =
      finiteAtomicMeasure q id :=
  finiteAtomicMeasure_withDensity_ratio_of_support q p (fun x => (hp x).le)
    (fun x hx => False.elim ((hp x).ne' hx))

theorem finiteAtomicMeasure_absolutelyContinuous (q p : α → ℝ)
    (hq : ∀ x, 0 ≤ q x) (hp : ∀ x, 0 < p x) :
    finiteAtomicMeasure q id ≪ finiteAtomicMeasure p id := by
  rw [← finiteAtomicMeasure_withDensity_ratio q p hq hp]
  exact withDensity_absolutelyContinuous _ _

theorem klDiv_finiteAtomicMeasure_eq_ofReal_of_support (q p : α → ℝ)
    (hq : ∀ x, 0 ≤ q x) (hqsum : ∑ x, q x = 1)
    (hp : ∀ x, 0 ≤ p x) (hpsum : ∑ x, p x = 1)
    (hqp : ∀ x, p x = 0 → q x = 0) :
    klDiv (finiteAtomicMeasure q id) (finiteAtomicMeasure p id) =
      ENNReal.ofReal (MsetsPaper.Upper.finiteKL q p) := by
  let := finiteAtomicMeasure_isProbabilityMeasure q hq id hqsum
  let := finiteAtomicMeasure_isProbabilityMeasure p hp id hpsum
  have hwd := finiteAtomicMeasure_withDensity_ratio_of_support q p hp hqp
  have hac : finiteAtomicMeasure q id ≪ finiteAtomicMeasure p id := by
    rw [← hwd]
    exact withDensity_absolutelyContinuous _ _
  have hRN : (finiteAtomicMeasure q id).rnDeriv (finiteAtomicMeasure p id)
      =ᵐ[finiteAtomicMeasure p id] fun x => ENNReal.ofReal (q x / p x) := by
    conv_lhs => rw [← hwd]
    exact Measure.rnDeriv_withDensity _ (measurable_of_countable _)
  have hlog : llr (finiteAtomicMeasure q id) (finiteAtomicMeasure p id) =ᵐ[finiteAtomicMeasure q id]
      fun x => Real.log (q x / p x) := by
    filter_upwards [hac.ae_le hRN] with x hx
    simp only [llr, hx, ENNReal.toReal_ofReal (div_nonneg (hq x) (hp x))]
  rw [klDiv_of_ac_of_integrable hac (integrable_finiteAtomicMeasure q id _)]
  rw [integral_congr_ae hlog, integral_finiteAtomicMeasure q hq id]
  simp [MsetsPaper.Upper.finiteKL]

theorem klDiv_finiteAtomicMeasure_eq_ofReal_finiteKL (q p : α → ℝ)
    (hq : ∀ x, 0 ≤ q x) (hqsum : ∑ x, q x = 1)
    (hp : ∀ x, 0 < p x) (hpsum : ∑ x, p x = 1) :
    klDiv (finiteAtomicMeasure q id) (finiteAtomicMeasure p id) =
      ENNReal.ofReal (MsetsPaper.Upper.finiteKL q p) :=
  klDiv_finiteAtomicMeasure_eq_ofReal_of_support q p hq hqsum
    (fun x => (hp x).le) hpsum (fun x hx => False.elim ((hp x).ne' hx))

theorem klDiv_finiteAtomicMeasure_toReal (q p : α → ℝ)
    (hq : ∀ x, 0 ≤ q x) (hqsum : ∑ x, q x = 1)
    (hp : ∀ x, 0 < p x) (hpsum : ∑ x, p x = 1) :
    (klDiv (finiteAtomicMeasure q id) (finiteAtomicMeasure p id)).toReal =
      MsetsPaper.Upper.finiteKL q p := by
  rw [klDiv_finiteAtomicMeasure_eq_ofReal_finiteKL q p hq hqsum hp hpsum,
    ENNReal.toReal_ofReal (MsetsPaper.Upper.finiteKL_nonneg q p hq hqsum hp hpsum)]

theorem klDiv_finiteAtomicMeasure_eq_top_of_support_mismatch (q p : α → ℝ)
    (a : α) (hqa : 0 < q a) (hpa : p a = 0) :
    klDiv (finiteAtomicMeasure q id) (finiteAtomicMeasure p id) = ∞ := by
  apply klDiv_of_not_ac
  intro hac
  have hz : finiteAtomicMeasure p id {a} = 0 := by
    rw [finiteAtomicMeasure_id_singleton, hpa, ENNReal.ofReal_zero]
  have hzero := hac hz
  rw [finiteAtomicMeasure_id_singleton] at hzero
  exact (ENNReal.ofReal_pos.mpr hqa).ne' hzero

open Classical in
/-- The complete finite probability-law convention, including common zero
atoms and genuine support mismatch. -/
theorem klDiv_finiteAtomicMeasure_formula (q p : α → ℝ)
    (hq : ∀ x, 0 ≤ q x) (hqsum : ∑ x, q x = 1)
    (hp : ∀ x, 0 ≤ p x) (hpsum : ∑ x, p x = 1) :
    klDiv (finiteAtomicMeasure q id) (finiteAtomicMeasure p id) =
      if ∀ x, p x = 0 → q x = 0 then ENNReal.ofReal (MsetsPaper.Upper.finiteKL q p)
      else ∞ := by
  split_ifs with hsupport
  · exact klDiv_finiteAtomicMeasure_eq_ofReal_of_support q p hq hqsum hp hpsum hsupport
  · push_neg at hsupport
    obtain ⟨a, hpa, hqa⟩ := hsupport
    exact klDiv_finiteAtomicMeasure_eq_top_of_support_mismatch q p a
      (lt_of_le_of_ne (hq a) (Ne.symm hqa)) hpa

end MsetsPaper.Probability
