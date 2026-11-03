import MsetsLower.Prelude
import Mathlib.MeasureTheory.Integral.Bochner.SumMeasure
import Mathlib.MeasureTheory.Order.Lattice
import Mathlib.MeasureTheory.VectorMeasure.Decomposition.Jordan

/-!
# A maximum under changed laws

This file formalizes `lem:changed-law-maximum`.  Total variation is defined
by the Jordan total variation of the difference of two finite measures.  For
probability measures this is the usual convention

`TV(μ,ν) = (1/2) |μ-ν|(Ω)`.
-/

namespace MsetsLower.Probability

open MeasureTheory
open scoped BigOperators ENNReal

noncomputable section

/-- Total-variation distance, with the probability-theory normalization. -/
def totalVariationDistance {Ω : Type*} [MeasurableSpace Ω]
    (μ ν : Measure Ω) [IsFiniteMeasure μ] [IsFiniteMeasure ν] : Real :=
  (1 / 2 : Real) *
    (μ.toSignedMeasure - ν.toSignedMeasure).totalVariation.real Set.univ

theorem totalVariationDistance_nonneg {Ω : Type*} [MeasurableSpace Ω]
    (μ ν : Measure Ω) [IsFiniteMeasure μ] [IsFiniteMeasure ν] :
    0 ≤ totalVariationDistance μ ν := by
  unfold totalVariationDistance
  positivity

/-- The standard dual estimate for total variation, proved internally from
the Jordan decomposition rather than imported as an external fact. -/
theorem abs_integral_sub_integral_le_two_mul_totalVariationDistance
    {Ω : Type*} [MeasurableSpace Ω]
    (μ ν : Measure Ω) [IsFiniteMeasure μ] [IsFiniteMeasure ν]
    {f : Ω → Real} {M : Real}
    (hf : Measurable f)
    (hbound : ∀ ω, |f ω| ≤ M) :
    |(∫ ω, f ω ∂μ) - ∫ ω, f ω ∂ν| ≤
      2 * M * totalVariationDistance μ ν := by
  let s : SignedMeasure Ω := μ.toSignedMeasure - ν.toSignedMeasure
  let j : JordanDecomposition Ω := s.toJordanDecomposition
  have hfμ : Integrable f μ :=
    Integrable.of_bound hf.aestronglyMeasurable M
      (ae_of_all μ fun ω ↦ by simpa [Real.norm_eq_abs] using hbound ω)
  have hfν : Integrable f ν :=
    Integrable.of_bound hf.aestronglyMeasurable M
      (ae_of_all ν fun ω ↦ by simpa [Real.norm_eq_abs] using hbound ω)
  have hfpos : Integrable f j.posPart :=
    Integrable.of_bound hf.aestronglyMeasurable M
      (ae_of_all j.posPart fun ω ↦ by
        simpa [Real.norm_eq_abs] using hbound ω)
  have hfneg : Integrable f j.negPart :=
    Integrable.of_bound hf.aestronglyMeasurable M
      (ae_of_all j.negPart fun ω ↦ by
        simpa [Real.norm_eq_abs] using hbound ω)
  have hj : j.posPart.toSignedMeasure - j.negPart.toSignedMeasure = s := by
    simpa [j, JordanDecomposition.toSignedMeasure] using
      (SignedMeasure.toSignedMeasure_toJordanDecomposition s)
  have hsigned :
      (μ + j.negPart).toSignedMeasure = (ν + j.posPart).toSignedMeasure := by
    simp only [Measure.toSignedMeasure_add]
    rw [show μ.toSignedMeasure = s + ν.toSignedMeasure by
      dsimp [s]
      abel]
    rw [← hj]
    abel
  have hmeasure : μ + j.negPart = ν + j.posPart :=
    Measure.toSignedMeasure_eq_toSignedMeasure_iff.mp hsigned
  have hdiff :
      (∫ ω, f ω ∂μ) - ∫ ω, f ω ∂ν =
        (∫ ω, f ω ∂j.posPart) - ∫ ω, f ω ∂j.negPart := by
    have hint : ∫ ω, f ω ∂(μ + j.negPart) =
        ∫ ω, f ω ∂(ν + j.posPart) := by rw [hmeasure]
    rw [integral_add_measure hfμ hfneg,
      integral_add_measure hfν hfpos] at hint
    linarith
  have hpos : |(∫ ω, f ω ∂j.posPart)| ≤ M * j.posPart.real Set.univ := by
    simpa [Real.norm_eq_abs] using
      (norm_integral_le_of_norm_le_const
        (μ := j.posPart) (f := f) (C := M)
        (ae_of_all j.posPart fun ω ↦ by
          simpa [Real.norm_eq_abs] using hbound ω))
  have hneg : |(∫ ω, f ω ∂j.negPart)| ≤ M * j.negPart.real Set.univ := by
    simpa [Real.norm_eq_abs] using
      (norm_integral_le_of_norm_le_const
        (μ := j.negPart) (f := f) (C := M)
        (ae_of_all j.negPart fun ω ↦ by
          simpa [Real.norm_eq_abs] using hbound ω))
  calc
    |(∫ ω, f ω ∂μ) - ∫ ω, f ω ∂ν| =
        |(∫ ω, f ω ∂j.posPart) - ∫ ω, f ω ∂j.negPart| := by rw [hdiff]
    _ ≤ |(∫ ω, f ω ∂j.posPart)| + |(∫ ω, f ω ∂j.negPart)| :=
      abs_sub _ _
    _ ≤ M * j.posPart.real Set.univ + M * j.negPart.real Set.univ :=
      add_le_add hpos hneg
    _ = M * s.totalVariation.real Set.univ := by
      simp only [SignedMeasure.totalVariation, j, s, Measure.real, Measure.add_apply]
      rw [ENNReal.toReal_add (measure_ne_top _ _) (measure_ne_top _ _)]
      ring
    _ = 2 * M * totalVariationDistance μ ν := by
      simp only [totalVariationDistance, s]
      ring

/-- Uniform mixture of a nonempty finite family of measures. -/
def averageMeasure {Ω ι : Type*} [MeasurableSpace Ω] [Fintype ι]
    (Q : ι → Measure Ω) : Measure Ω :=
  ((Fintype.card ι : ENNReal)⁻¹) • ∑ i, Q i

instance averageMeasure.instIsFiniteMeasure
    {Ω ι : Type*} [MeasurableSpace Ω] [Fintype ι] [Nonempty ι]
    (Q : ι → Measure Ω) [∀ i, IsFiniteMeasure (Q i)] :
    IsFiniteMeasure (averageMeasure Q) := by
  constructor
  unfold averageMeasure
  rw [Measure.smul_apply]
  simp only [smul_eq_mul]
  rw [show (∑ i, Q i) Set.univ = ∑ i, Q i Set.univ by
    exact Measure.finsetSum_apply Finset.univ Q Set.univ]
  have hcardPos : (0 : ENNReal) < Fintype.card ι := by
    exact_mod_cast Fintype.card_pos
  exact ENNReal.mul_lt_top (ENNReal.inv_lt_top.2 hcardPos)
    (ENNReal.sum_lt_top.mpr fun i _ ↦ measure_lt_top (Q i) Set.univ)

instance averageMeasure.instIsProbabilityMeasure
    {Ω ι : Type*} [MeasurableSpace Ω] [Fintype ι] [Nonempty ι]
    (Q : ι → Measure Ω) [∀ i, IsProbabilityMeasure (Q i)] :
    IsProbabilityMeasure (averageMeasure Q) := by
  constructor
  simp [averageMeasure]
  have hcard : (Fintype.card ι : ENNReal) ≠ 0 := by
    exact_mod_cast Fintype.card_ne_zero
  exact ENNReal.inv_mul_cancel hcard (by finiteness)

theorem integral_averageMeasure
    {Ω ι : Type*} [MeasurableSpace Ω] [Fintype ι]
    (Q : ι → Measure Ω) {f : Ω → Real}
    (hf : ∀ i, Integrable f (Q i)) :
    ∫ ω, f ω ∂averageMeasure Q =
      (Fintype.card ι : Real)⁻¹ * ∑ i, ∫ ω, f ω ∂Q i := by
  unfold averageMeasure
  rw [integral_smul_measure]
  rw [integral_finsetSum_measure (fun i _ ↦ hf i)]
  simp only [ENNReal.toReal_inv, ENNReal.toReal_natCast, smul_eq_mul]

/-- Pointwise maximum of a nonempty finite score family. -/
def finiteMax {Ω ι : Type*} [Fintype ι] [Nonempty ι]
    (S : ι → Ω → Real) (ω : Ω) : Real :=
  Finset.univ.sup' Finset.univ_nonempty (fun i ↦ S i ω)

theorem measurable_finiteMax
    {Ω ι : Type*} [MeasurableSpace Ω] [Fintype ι] [Nonempty ι]
    {S : ι → Ω → Real} (hS : ∀ i, Measurable (S i)) :
    Measurable (finiteMax S) := by
  have heq : finiteMax S =
      Finset.univ.sup' Finset.univ_nonempty S := by
    funext ω
    rw [Finset.sup'_apply]
    rfl
  rw [heq]
  exact Finset.measurable_sup' Finset.univ_nonempty
    (fun i _ ↦ hS i)

theorem le_finiteMax
    {Ω ι : Type*} [Fintype ι] [Nonempty ι]
    (S : ι → Ω → Real) (i : ι) (ω : Ω) :
    S i ω ≤ finiteMax S ω := by
  exact Finset.le_sup' (fun j ↦ S j ω) (Finset.mem_univ i)

theorem finiteMax_le
    {Ω ι : Type*} [Fintype ι] [Nonempty ι]
    {S : ι → Ω → Real} {C : Real}
    (hS : ∀ i ω, S i ω ≤ C) (ω : Ω) :
    finiteMax S ω ≤ C := by
  exact Finset.sup'_le Finset.univ_nonempty _
    (fun i _ ↦ hS i ω)

/-- `lem:changed-law-maximum` with its literal uniform mixture and the
probability-theory normalization of total variation. -/
theorem changed_law_maximum
    {Ω ι : Type*} [MeasurableSpace Ω] [Fintype ι] [Nonempty ι]
    (P : Measure Ω) (Q : ι → Measure Ω)
    [IsProbabilityMeasure P] [∀ i, IsProbabilityMeasure (Q i)]
    (S : ι → Ω → Real) {M : Real}
    (hSmeas : ∀ i, Measurable (S i))
    (hSrange : ∀ i ω, S i ω ∈ Set.Icc (-M) M) :
    ∫ ω, finiteMax S ω ∂P ≥
      (Fintype.card ι : Real)⁻¹ * ∑ i, ∫ ω, S i ω ∂Q i -
        2 * M * totalVariationDistance (averageMeasure Q) P := by
  have hmaxMeas : Measurable (finiteMax S) :=
    measurable_finiteMax hSmeas
  have hmaxUpper : ∀ ω, finiteMax S ω ≤ M :=
    finiteMax_le (fun i ω ↦ (hSrange i ω).2)
  let i₀ : ι := Classical.choice inferInstance
  have hmaxLower : ∀ ω, -M ≤ finiteMax S ω := fun ω ↦
    (hSrange i₀ ω).1.trans (le_finiteMax S i₀ ω)
  have hmaxAbs : ∀ ω, |finiteMax S ω| ≤ M := by
    intro ω
    exact (abs_le).2 ⟨hmaxLower ω, hmaxUpper ω⟩
  have hSint : ∀ i, Integrable (S i) (Q i) := fun i ↦
    Integrable.of_bound (hSmeas i).aestronglyMeasurable M
      (ae_of_all (Q i) fun ω ↦ by
        simpa [Real.norm_eq_abs] using (abs_le.2 (hSrange i ω)))
  have hmaxIntQ : ∀ i, Integrable (finiteMax S) (Q i) := fun i ↦
    Integrable.of_bound hmaxMeas.aestronglyMeasurable M
      (ae_of_all (Q i) fun ω ↦ by
        simpa [Real.norm_eq_abs] using hmaxAbs ω)
  have havgLower :
      (Fintype.card ι : Real)⁻¹ * ∑ i, ∫ ω, S i ω ∂Q i ≤
        ∫ ω, finiteMax S ω ∂averageMeasure Q := by
    rw [integral_averageMeasure Q hmaxIntQ]
    exact mul_le_mul_of_nonneg_left
      (Finset.sum_le_sum fun i _ ↦
        integral_mono_ae (hSint i) (hmaxIntQ i)
          (ae_of_all (Q i) fun ω ↦ le_finiteMax S i ω))
      (by positivity)
  have htv :=
    abs_integral_sub_integral_le_two_mul_totalVariationDistance
      (averageMeasure Q) P hmaxMeas hmaxAbs
  have hchange :
      ∫ ω, finiteMax S ω ∂averageMeasure Q -
          2 * M * totalVariationDistance (averageMeasure Q) P ≤
        ∫ ω, finiteMax S ω ∂P := by
    rw [abs_le] at htv
    linarith [htv.1, htv.2]
  linarith

/-- Support-safe form of `changed_law_maximum`.  In sequential experiments
the observable score bounds usually hold only on the full-measure protocol
support.  Clipping every score to `[-M,M]`, applying the pointwise theorem,
and then removing the clipping almost everywhere gives the same conclusion.
The cross-indexed `hSrangeQ` premise is needed because the maximum contains
all scores under every changed law. -/
theorem changed_law_maximum_of_ae_range
    {Ω ι : Type*} [MeasurableSpace Ω] [Fintype ι] [Nonempty ι]
    (P : Measure Ω) (Q : ι → Measure Ω)
    [IsProbabilityMeasure P] [∀ i, IsProbabilityMeasure (Q i)]
    (S : ι → Ω → Real) {M : Real} (hM : 0 ≤ M)
    (hSmeas : ∀ i, Measurable (S i))
    (hSrangeP : ∀ i, ∀ᵐ ω ∂P, S i ω ∈ Set.Icc (-M) M)
    (hSrangeQ : ∀ i j, ∀ᵐ ω ∂Q j, S i ω ∈ Set.Icc (-M) M) :
    ∫ ω, finiteMax S ω ∂P ≥
      (Fintype.card ι : Real)⁻¹ * ∑ i, ∫ ω, S i ω ∂Q i -
        2 * M * totalVariationDistance (averageMeasure Q) P := by
  let Sclip : ι → Ω → Real := fun i ω => max (-M) (min M (S i ω))
  have hclipMeas : ∀ i, Measurable (Sclip i) := by
    intro i
    exact measurable_const.max (measurable_const.min (hSmeas i))
  have hclipRange : ∀ i ω, Sclip i ω ∈ Set.Icc (-M) M := by
    intro i ω
    constructor
    · exact le_max_left _ _
    · exact max_le (by linarith) (min_le_left _ _)
  have hclipEq {i : ι} {ω : Ω} (h : S i ω ∈ Set.Icc (-M) M) :
      Sclip i ω = S i ω := by
    dsimp [Sclip]
    rw [min_eq_right h.2, max_eq_right h.1]
  have hPall : ∀ᵐ ω ∂P, ∀ i, Sclip i ω = S i ω := by
    rw [MeasureTheory.ae_all_iff]
    intro i
    filter_upwards [hSrangeP i] with ω hω
    exact hclipEq hω
  have hmaxEqP : finiteMax Sclip =ᵐ[P] finiteMax S := by
    filter_upwards [hPall] with ω hω
    unfold finiteMax
    apply Finset.sup'_congr Finset.univ_nonempty rfl
    intro i _hi
    exact hω i
  have hQi : ∀ i, (∫ ω, Sclip i ω ∂Q i) = ∫ ω, S i ω ∂Q i := by
    intro i
    apply MeasureTheory.integral_congr_ae
    filter_upwards [hSrangeQ i i] with ω hω
    exact hclipEq hω
  have hmain := changed_law_maximum P Q Sclip hclipMeas hclipRange
  rw [MeasureTheory.integral_congr_ae hmaxEqP] at hmain
  simp_rw [hQi] at hmain
  exact hmain

#print axioms changed_law_maximum_of_ae_range

end

end MsetsLower.Probability
