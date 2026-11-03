import CoefficientOne.Sampling.Model
import Mathlib.Probability.ProbabilityMassFunction.Integrals
import Mathlib.Data.ENNReal.BigOperators

/-!
# Finite masses and the probability measure of Appendix E.2

The measure in the sampling argument is built from the very same real masses
that occur in the existing finite-sum covariance theorem.
-/

open scoped BigOperators
open EffectiveResistance MeasureTheory

namespace CoefficientOne.Sampling

noncomputable section

variable {α : Type*} [Fintype α]

/-- Convert a normalized nonnegative real mass function to a PMF. -/
def lawPMF (p : FiniteLaw α) : PMF α :=
  PMF.ofFintype (fun a => ENNReal.ofReal (p.val a)) (by
    rw [← ENNReal.ofReal_sum_of_nonneg (fun a _ => law_nonneg p a), law_sum]
    simp)

@[simp] theorem lawPMF_apply (p : FiniteLaw α) (a : α) :
    lawPMF p a = ENNReal.ofReal (p.val a) := rfl

@[simp] theorem lawPMF_apply_toReal (p : FiniteLaw α) (a : α) :
    (lawPMF p a).toReal = p.val a := by
  exact ENNReal.toReal_ofReal (law_nonneg p a)

section Measure
variable [MeasurableSpace α] [MeasurableSingletonClass α]

/-- The concrete probability measure associated to a finite law. -/
def lawMeasure (p : FiniteLaw α) : Measure α := (lawPMF p).toMeasure

instance lawMeasure_isProbabilityMeasure (p : FiniteLaw α) :
    IsProbabilityMeasure (lawMeasure p) := by
  unfold lawMeasure
  infer_instance

@[simp] theorem lawMeasure_singleton (p : FiniteLaw α) (a : α) :
    lawMeasure p {a} = ENNReal.ofReal (p.val a) := by
  exact (lawPMF p).toMeasure_apply_singleton a (measurableSet_singleton a)

theorem integral_lawMeasure (p : FiniteLaw α) (f : α → ℝ) :
    ∫ a, f a ∂lawMeasure p = lawExpectation p f := by
  rw [lawMeasure, PMF.integral_eq_sum]
  simp only [lawPMF_apply_toReal, smul_eq_mul, lawExpectation]

end Measure

variable {ι : Type*} [Fintype ι] [DecidableEq ι] {k : ℕ}

/-- The existing external-field probability masses as a finite law. -/
def externalFieldLaw (w : ι → ℝ) (hw : ∀ i, 0 < w i)
    (hk : k ≤ Fintype.card ι) : FiniteLaw (RankSubset ι k) :=
  ⟨subsetProbability w k,
    ⟨fun S => (subsetProbability_pos w hw hk S).le, sum_subsetProbability w hw hk⟩⟩

@[simp] theorem externalFieldLaw_apply (w : ι → ℝ) (hw : ∀ i, 0 < w i)
    (hk : k ≤ Fintype.card ι) (S : RankSubset ι k) :
    (externalFieldLaw w hw hk).val S = subsetProbability w k S := rfl

@[simp] theorem externalFieldLaw_expectation (w : ι → ℝ) (hw : ∀ i, 0 < w i)
    (hk : k ≤ Fintype.card ι) (f : RankSubset ι k → ℝ) :
    lawExpectation (externalFieldLaw w hw hk) f = expectation w k f := rfl

@[simp] theorem externalFieldLaw_mean (w : ι → ℝ) (hw : ∀ i, 0 < w i)
    (hk : k ≤ Fintype.card ι) :
    lawMean (externalFieldLaw w hw hk) = inclusionMean w k := rfl

@[simp] theorem externalFieldLaw_covariance (w : ι → ℝ) (hw : ∀ i, 0 < w i)
    (hk : k ≤ Fintype.card ι) :
    lawCovariance (externalFieldLaw w hw hk) = covarianceMatrix w k := rfl

/-- The integral expectation is exactly the finite-sum expectation in the
already proved spectral theorem. -/
theorem integral_externalFieldLaw (w : ι → ℝ) (hw : ∀ i, 0 < w i)
    (hk : k ≤ Fintype.card ι) (f : RankSubset ι k → ℝ) :
    ∫ S, f S ∂lawMeasure (externalFieldLaw w hw hk) = expectation w k f := by
  exact integral_lawMeasure _ _

theorem integral_centered_indicators_externalField (w : ι → ℝ)
    (hw : ∀ i, 0 < w i) (hk : k ≤ Fintype.card ι) (i j : ι) :
    (∫ S : RankSubset ι k,
      (indicator i S.val - inclusionMean w k i) *
        (indicator j S.val - inclusionMean w k j)
      ∂lawMeasure (externalFieldLaw w hw hk)) = covarianceMatrix w k i j := by
  exact integral_externalFieldLaw _ _ _ _

end
end CoefficientOne.Sampling
