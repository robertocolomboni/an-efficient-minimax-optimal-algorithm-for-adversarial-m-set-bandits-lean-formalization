import MsetsLower.Lower.Sparse.JointLikelihood
import MsetsLower.Lower.Dense.Assouad
import Mathlib.MeasureTheory.Integral.MeanInequalities

/-!
# Sparse likelihood mixtures and total variation

This file formalizes the analytic chi-square/total-variation step used in
`eq:lower-mixture-tv`.  It is independent of the later fixing argument: its
input is an explicit density, and its output uses the project's normalized
Jordan total variation.
-/

namespace MsetsLower.Lower.Sparse

open MsetsLower Probability MeasureTheory Set
open scoped BigOperators ENNReal ProbabilityTheory

noncomputable section

/-- Pearson chi-square of an explicit real probability density. -/
def densityChiSquare
    {Omega : Type*} [MeasurableSpace Omega]
    (P : Measure Omega) (L : Omega -> Real) : Real :=
  ∫ x, (L x - 1) ^ 2 ∂P

/-- Real representative of an `ENNReal` Radon--Nikodym density. -/
def ennrealDensityReal
    {Omega : Type*} (Lambda : Omega -> ENNReal) (x : Omega) : Real :=
  (Lambda x).toReal

theorem measurable_ennrealDensityReal
    {Omega : Type*} [MeasurableSpace Omega]
    {Lambda : Omega -> ENNReal} (hLambda : Measurable Lambda) :
    Measurable (ennrealDensityReal Lambda) :=
  hLambda.ennreal_toReal

theorem ennrealDensityReal_nonneg
    {Omega : Type*} (Lambda : Omega -> ENNReal) (x : Omega) :
    0 <= ennrealDensityReal Lambda x :=
  ENNReal.toReal_nonneg

/-- Replacing a finite `ENNReal` density by its real representative does not
change the measure. -/
theorem withDensity_ofReal_ennrealDensityReal_eq
    {Omega : Type*} [MeasurableSpace Omega]
    (P : Measure Omega) (Lambda : Omega -> ENNReal)
    (hfinite : ∀ᵐ x ∂P, Lambda x < ∞) :
    P.withDensity (fun x => ENNReal.ofReal (ennrealDensityReal Lambda x)) =
      P.withDensity Lambda := by
  apply withDensity_congr_ae
  filter_upwards [hfinite] with x hx
  exact ENNReal.ofReal_toReal hx.ne

/-- A probability density is integrable and has real integral one. -/
theorem ennrealDensityReal_integrable_and_integral_eq_one
    {Omega : Type*} [MeasurableSpace Omega]
    (P : Measure Omega) (Lambda : Omega -> ENNReal)
    (hLambda : Measurable Lambda)
    (hfinite : ∀ᵐ x ∂P, Lambda x < ∞)
    (hQ : IsProbabilityMeasure (P.withDensity Lambda)) :
    Integrable (ennrealDensityReal Lambda) P ∧
      ∫ x, ennrealDensityReal Lambda x ∂P = 1 := by
  let Q := P.withDensity Lambda
  letI : IsProbabilityMeasure Q := hQ
  have hlin : (∫⁻ x, Lambda x ∂P) = 1 := by
    calc
      (∫⁻ x, Lambda x ∂P) = Q Set.univ := by
        rw [show Q = P.withDensity Lambda by rfl,
          withDensity_apply _ MeasurableSet.univ, Measure.restrict_univ]
      _ = 1 := measure_univ
  constructor
  · apply integrable_toReal_of_lintegral_ne_top hLambda.aemeasurable
    rw [hlin]
    exact ENNReal.one_ne_top
  · unfold ennrealDensityReal
    rw [integral_toReal hLambda.aemeasurable hfinite, hlin]
    simp

/-- Conversion of a finite joint `ENNReal` moment to the real product moment
used by the manuscript's chi-square expansion. -/
theorem ennrealDensityReal_pair_integrable_and_integral_eq
    {Omega : Type*} [MeasurableSpace Omega]
    (P : Measure Omega) (Lambda Gamma : Omega -> ENNReal)
    (hLambda : Measurable Lambda) (hGamma : Measurable Gamma)
    (hLambdaFinite : ∀ᵐ x ∂P, Lambda x < ∞)
    (hGammaFinite : ∀ᵐ x ∂P, Gamma x < ∞)
    (hmomentFinite : (∫⁻ x, Lambda x * Gamma x ∂P) ≠ ∞) :
    Integrable (fun x =>
        ennrealDensityReal Lambda x * ennrealDensityReal Gamma x) P ∧
      (∫ x, ennrealDensityReal Lambda x * ennrealDensityReal Gamma x ∂P) =
        (∫⁻ x, Lambda x * Gamma x ∂P).toReal := by
  have hprodMeas : Measurable (fun x => Lambda x * Gamma x) :=
    hLambda.mul hGamma
  have hprodFinite : ∀ᵐ x ∂P, Lambda x * Gamma x < ∞ := by
    filter_upwards [hLambdaFinite, hGammaFinite] with x hx hy
    exact ENNReal.mul_lt_top hx hy
  have hint := integrable_toReal_of_lintegral_ne_top
    hprodMeas.aemeasurable hmomentFinite
  have heq : (fun x =>
      ennrealDensityReal Lambda x * ennrealDensityReal Gamma x) =
      (fun x => (Lambda x * Gamma x).toReal) := by
    funext x
    exact (ENNReal.toReal_mul).symm
  constructor
  · simpa [heq] using hint
  · rw [heq]
    exact integral_toReal hprodMeas.aemeasurable hprodFinite

theorem ennrealDensityReal_pair_integral_le
    {Omega : Type*} [MeasurableSpace Omega]
    (P : Measure Omega) (Lambda Gamma : Omega -> ENNReal)
    (hLambda : Measurable Lambda) (hGamma : Measurable Gamma)
    (hLambdaFinite : ∀ᵐ x ∂P, Lambda x < ∞)
    (hGammaFinite : ∀ᵐ x ∂P, Gamma x < ∞)
    {C : Real} (hC0 : 0 <= C)
    (hmoment : (∫⁻ x, Lambda x * Gamma x ∂P) <= ENNReal.ofReal C) :
    Integrable (fun x =>
        ennrealDensityReal Lambda x * ennrealDensityReal Gamma x) P ∧
      (∫ x, ennrealDensityReal Lambda x * ennrealDensityReal Gamma x ∂P) <= C := by
  have hmomentFinite : (∫⁻ x, Lambda x * Gamma x ∂P) ≠ ∞ := by
    exact ne_top_of_le_ne_top ENNReal.ofReal_ne_top hmoment
  obtain ⟨hint, heq⟩ :=
    ennrealDensityReal_pair_integrable_and_integral_eq P Lambda Gamma
      hLambda hGamma hLambdaFinite hGammaFinite hmomentFinite
  refine ⟨hint, ?_⟩
  rw [heq]
  have hreal := ENNReal.toReal_mono ENNReal.ofReal_ne_top hmoment
  simpa [ENNReal.toReal_ofReal hC0] using hreal

/-- The standard inequality
`TV(P.withDensity L,P) <= (1/2) sqrt (int (L-1)^2 dP)`, proved for the
project's Jordan-normalized total variation.  The proof uses the event that
attains total variation and Cauchy--Schwarz; no information inequality is
inserted in place of the manuscript's chi-square argument. -/
theorem totalVariationDistance_withDensity_le_half_sqrt_chiSquare
    {Omega : Type*} [MeasurableSpace Omega]
    (P : Measure Omega) [IsProbabilityMeasure P]
    (L : Omega -> Real) (hL : Measurable L)
    (hL0 : forall x, 0 <= L x)
    (hQ : IsProbabilityMeasure
      (P.withDensity (fun x => ENNReal.ofReal (L x))))
    (hchiInt : Integrable (fun x => (L x - 1) ^ 2) P) :
    totalVariationDistance
        (P.withDensity (fun x => ENNReal.ofReal (L x))) P <=
      (1 : Real) / 2 * Real.sqrt (densityChiSquare P L) := by
  let Q := P.withDensity (fun x => ENNReal.ofReal (L x))
  letI : IsProbabilityMeasure Q := hQ
  have hden : Measurable (fun x => ENNReal.ofReal (L x)) :=
    hL.ennreal_ofReal
  have hdenTop : ∀ᵐ x ∂P,
      ENNReal.ofReal (L x) < ∞ :=
    ae_of_all P fun x => ENNReal.ofReal_lt_top
  have hlintegral_ne_top :
      (∫⁻ x, ENNReal.ofReal (L x) ∂P) ≠ ∞ := by
    have hmass : (∫⁻ x, ENNReal.ofReal (L x) ∂P) = Q Set.univ := by
      rw [show Q = P.withDensity (fun x => ENNReal.ofReal (L x)) by rfl,
        withDensity_apply _ MeasurableSet.univ, Measure.restrict_univ]
    rw [hmass]
    exact measure_ne_top Q Set.univ
  have hLint : Integrable L P := by
    have hto : Integrable
        (fun x => (ENNReal.ofReal (L x)).toReal) P :=
      integrable_toReal_of_lintegral_ne_top hden.aemeasurable
        hlintegral_ne_top
    convert hto using 1
    funext x
    rw [ENNReal.toReal_ofReal (hL0 x)]
  have hfInt : Integrable (fun x => L x - 1) P :=
    hLint.sub (integrable_const 1)
  have hfAbsInt : Integrable (fun x => |L x - 1|) P := hfInt.abs
  have hdensitySet : forall (s : Set Omega), MeasurableSet s ->
      Q.real s = ∫ x in s, L x ∂P := by
    intro s hs
    have hd := setIntegral_withDensity_eq_setIntegral_toReal_smul
      (μ := P) hden
      (ae_restrict_of_ae hdenTop) (fun _ : Omega => (1 : Real)) hs
    simpa [Q, hL0, measureReal_def] using hd
  obtain ⟨B, hB, hTV⟩ :=
    MsetsLower.Lower.Dense.exists_event_totalVariationDistance_eq Q P
  let f : Omega -> Real := fun x => L x - 1
  have hTVInt : totalVariationDistance Q P = ∫ x in B, f x ∂P := by
    rw [hTV, hdensitySet B hB]
    change (∫ x in B, L x ∂P) - P.real B = ∫ x in B, L x - 1 ∂P
    rw [integral_sub hLint.integrableOn (integrable_const 1)]
    simp
  have hmean : ∫ x, f x ∂P = 0 := by
    change (∫ x, L x - 1 ∂P) = 0
    rw [integral_sub hLint (integrable_const 1)]
    have hmass := hdensitySet Set.univ MeasurableSet.univ
    have hmass' : ∫ x, L x ∂P = 1 := by
      rw [← setIntegral_univ, ← hmass]
      simp
    rw [hmass']
    simp
  have hcompInt : ∫ x in Bᶜ, f x ∂P =
      -totalVariationDistance Q P := by
    have hsplit := integral_add_compl hB hfInt
    rw [hmean, ← hTVInt] at hsplit
    linarith
  have htv0 : 0 <= totalVariationDistance Q P :=
    totalVariationDistance_nonneg Q P
  have hBbound : totalVariationDistance Q P <=
      ∫ x in B, |f x| ∂P := by
    calc
      totalVariationDistance Q P = |totalVariationDistance Q P| :=
        (abs_of_nonneg htv0).symm
      _ = |∫ x in B, f x ∂P| := by rw [← hTVInt]
      _ <= ∫ x in B, |f x| ∂P := abs_integral_le_integral_abs
  have hBcBound : totalVariationDistance Q P <=
      ∫ x in Bᶜ, |f x| ∂P := by
    calc
      totalVariationDistance Q P = |-totalVariationDistance Q P| := by
        rw [abs_neg, abs_of_nonneg htv0]
      _ = |∫ x in Bᶜ, f x ∂P| := by rw [hcompInt]
      _ <= ∫ x in Bᶜ, |f x| ∂P := abs_integral_le_integral_abs
  have hL1 : 2 * totalVariationDistance Q P <=
      ∫ x, |f x| ∂P := by
    calc
      2 * totalVariationDistance Q P =
          totalVariationDistance Q P + totalVariationDistance Q P := by ring
      _ <= (∫ x in B, |f x| ∂P) +
          ∫ x in Bᶜ, |f x| ∂P := add_le_add hBbound hBcBound
      _ = ∫ x, |f x| ∂P := integral_add_compl hB hfAbsInt
  let A : Omega -> ENNReal := fun x => ENNReal.ofReal |f x|
  let chi : ENNReal := ∫⁻ x, ENNReal.ofReal (f x ^ 2) ∂P
  have hA : AEMeasurable A P := by
    have hf : Measurable f := hL.sub measurable_const
    simpa only [A, Real.norm_eq_abs] using (hf.norm.ennreal_ofReal.aemeasurable (μ := P))
  have hholder : (2 : Real).HolderConjugate 2 :=
    Real.holderConjugate_iff.mpr ⟨by norm_num, by norm_num⟩
  have hcs0 := ENNReal.lintegral_mul_le_Lp_mul_Lq P hholder hA
    (aemeasurable_const : AEMeasurable (fun _ : Omega => (1 : ENNReal)) P)
  have hcs : (∫⁻ x, A x ∂P) <= chi ^ ((1 : Real) / 2) := by
    simpa [A, chi, ENNReal.rpow_two, ← ENNReal.ofReal_pow,
      abs_nonneg, sq_abs] using hcs0
  have hL1enn : ENNReal.ofReal (2 * totalVariationDistance Q P) <=
      chi ^ ((1 : Real) / 2) := by
    calc
      ENNReal.ofReal (2 * totalVariationDistance Q P) <=
          ENNReal.ofReal (∫ x, |f x| ∂P) :=
        ENNReal.ofReal_le_ofReal hL1
      _ = ∫⁻ x, ENNReal.ofReal |f x| ∂P :=
        ofReal_integral_eq_lintegral_ofReal hfAbsInt
          (ae_of_all P fun x => abs_nonneg (f x))
      _ = ∫⁻ x, A x ∂P := rfl
      _ <= chi ^ ((1 : Real) / 2) := hcs
  have hchiTop : chi ≠ ∞ := by
    unfold chi
    rw [← ofReal_integral_eq_lintegral_ofReal hchiInt
      (ae_of_all P fun x => sq_nonneg (f x))]
    exact ENNReal.ofReal_ne_top
  have hsqrtTop : chi ^ ((1 : Real) / 2) ≠ ∞ :=
    ENNReal.rpow_ne_top_of_nonneg (by norm_num) hchiTop
  have hreal := ENNReal.toReal_mono hsqrtTop hL1enn
  have hchiReal : chi.toReal = densityChiSquare P L := by
    unfold chi densityChiSquare f
    rw [← ofReal_integral_eq_lintegral_ofReal hchiInt
      (ae_of_all P fun x => sq_nonneg (L x - 1))]
    rw [ENNReal.toReal_ofReal]
    exact integral_nonneg_of_ae
      (ae_of_all P fun x => sq_nonneg (L x - 1))
  rw [ENNReal.toReal_ofReal (mul_nonneg (by norm_num) htv0),
    ← ENNReal.toReal_rpow, hchiReal, ← Real.sqrt_eq_rpow] at hreal
  nlinarith [Real.sqrt_nonneg (densityChiSquare P L)]

/-- The real density of the uniform mixture of a finite family of densities. -/
def uniformMixtureDensity
    {Omega ι : Type*} [Fintype ι]
    (L : ι -> Omega -> Real) (x : Omega) : Real :=
  (Fintype.card ι : Real)⁻¹ * ∑ i, L i x

theorem measurable_uniformMixtureDensity
    {Omega ι : Type*} [MeasurableSpace Omega] [Fintype ι]
    (L : ι -> Omega -> Real) (hL : forall i, Measurable (L i)) :
    Measurable (uniformMixtureDensity L) := by
  exact measurable_const.mul (Finset.measurable_sum _ fun i _ => hL i)

theorem uniformMixtureDensity_nonneg
    {Omega ι : Type*} [Fintype ι] [Nonempty ι]
    (L : ι -> Omega -> Real) (hL0 : forall i x, 0 <= L i x) (x : Omega) :
    0 <= uniformMixtureDensity L x := by
  unfold uniformMixtureDensity
  exact mul_nonneg (inv_nonneg.mpr (Nat.cast_nonneg _))
    (Finset.sum_nonneg fun i _ => hL0 i x)

theorem integrable_uniformMixtureDensity
    {Omega ι : Type*} [MeasurableSpace Omega] [Fintype ι]
    (P : Measure Omega) (L : ι -> Omega -> Real)
    (hLint : forall i, Integrable (L i) P) :
    Integrable (uniformMixtureDensity L) P := by
  unfold uniformMixtureDensity
  exact (integrable_finsetSum _ fun i _ => hLint i).const_mul _

/-- If every component is normalized, so is its uniform real density. -/
theorem integral_uniformMixtureDensity
    {Omega ι : Type*} [MeasurableSpace Omega] [Fintype ι] [Nonempty ι]
    (P : Measure Omega) (L : ι -> Omega -> Real)
    (hLint : forall i, Integrable (L i) P)
    (hLmass : forall i, ∫ x, L i x ∂P = 1) :
    ∫ x, uniformMixtureDensity L x ∂P = 1 := by
  unfold uniformMixtureDensity
  rw [integral_const_mul]
  rw [integral_finsetSum _ fun i _ => hLint i]
  simp [hLmass]

theorem ofReal_uniformMixtureDensity
    {Omega ι : Type*} [Fintype ι] [Nonempty ι]
    (L : ι -> Omega -> Real) (hL0 : forall i x, 0 <= L i x) (x : Omega) :
    ENNReal.ofReal (uniformMixtureDensity L x) =
      (Fintype.card ι : ENNReal)⁻¹ * ∑ i, ENNReal.ofReal (L i x) := by
  have hcard : 0 < (Fintype.card ι : Real) := by
    exact_mod_cast Fintype.card_pos
  unfold uniformMixtureDensity
  rw [ENNReal.ofReal_mul (inv_nonneg.mpr hcard.le),
    ENNReal.ofReal_inv_of_pos hcard, ENNReal.ofReal_natCast,
    ENNReal.ofReal_sum_of_nonneg (fun i _ => hL0 i x)]

/-- The manuscript's definition `Q_g = r^{-1} sum_j Q_j` agrees exactly
with the measure having the averaged likelihood as density. -/
theorem averageMeasure_withDensity_eq_withDensity_uniformMixtureDensity
    {Omega ι : Type*} [MeasurableSpace Omega] [Fintype ι] [Nonempty ι]
    (P : Measure Omega) (L : ι -> Omega -> Real)
    (hL : forall i, Measurable (L i))
    (hL0 : forall i x, 0 <= L i x) :
    averageMeasure (fun i =>
        P.withDensity (fun x => ENNReal.ofReal (L i x))) =
      P.withDensity (fun x =>
        ENNReal.ofReal (uniformMixtureDensity L x)) := by
  classical
  ext s hs
  unfold averageMeasure
  rw [Measure.smul_apply]
  rw [Measure.finsetSum_apply Finset.univ _ s]
  simp_rw [withDensity_apply _ hs]
  simp_rw [ofReal_uniformMixtureDensity L hL0]
  rw [lintegral_const_mul]
  · rw [lintegral_finsetSum _ fun i _ => (hL i).ennreal_ofReal]
    simp only [smul_eq_mul]
  · exact Finset.measurable_sum _ fun i _ => (hL i).ennreal_ofReal

/-- For a normalized density, Pearson chi-square is its second moment minus
one. -/
theorem densityChiSquare_eq_integral_sq_sub_one
    {Omega : Type*} [MeasurableSpace Omega]
    (P : Measure Omega) [IsProbabilityMeasure P]
    (L : Omega -> Real) (hLint : Integrable L P)
    (hLsqInt : Integrable (fun x => L x ^ 2) P)
    (hLmass : ∫ x, L x ∂P = 1) :
    densityChiSquare P L = (∫ x, L x ^ 2 ∂P) - 1 := by
  have htwoInt : Integrable (fun x => 2 * L x) P := hLint.const_mul 2
  unfold densityChiSquare
  calc
    (∫ x, (L x - 1) ^ 2 ∂P) =
        ∫ x, (L x ^ 2 - 2 * L x) + 1 ∂P := by
      apply integral_congr_ae
      filter_upwards [] with x
      ring
    _ = (∫ x, L x ^ 2 - 2 * L x ∂P) + ∫ _x : Omega, 1 ∂P :=
      integral_add (hLsqInt.sub htwoInt) (integrable_const 1)
    _ = ((∫ x, L x ^ 2 ∂P) - ∫ x, 2 * L x ∂P) + 1 := by
      rw [integral_sub hLsqInt htwoInt]
      simp
    _ = (∫ x, L x ^ 2 ∂P) - 1 := by
      rw [integral_const_mul, hLmass]
      ring

/-- The second moment of a uniform mixture expands into all ordered pairs of
component likelihoods. -/
theorem integral_uniformMixtureDensity_sq
    {Omega ι : Type*} [MeasurableSpace Omega] [Fintype ι]
    (P : Measure Omega) (L : ι -> Omega -> Real)
    (hpairInt : forall i j, Integrable (fun x => L i x * L j x) P) :
    (∫ x, uniformMixtureDensity L x ^ 2 ∂P) =
      (Fintype.card ι : Real)⁻¹ ^ 2 *
        ∑ i, ∑ j, ∫ x, L i x * L j x ∂P := by
  classical
  have hpoint : forall x,
      uniformMixtureDensity L x ^ 2 =
        (Fintype.card ι : Real)⁻¹ ^ 2 *
          ∑ i, ∑ j, L i x * L j x := by
    intro x
    unfold uniformMixtureDensity
    rw [mul_pow]
    congr 1
    rw [pow_two, Finset.sum_mul]
    apply Finset.sum_congr rfl
    intro i hi
    rw [Finset.mul_sum]
  calc
    (∫ x, uniformMixtureDensity L x ^ 2 ∂P) =
        ∫ x, (Fintype.card ι : Real)⁻¹ ^ 2 *
          (∑ i, ∑ j, L i x * L j x) ∂P := by
      exact integral_congr_ae (ae_of_all P hpoint)
    _ = (Fintype.card ι : Real)⁻¹ ^ 2 *
        ∫ x, (∑ i, ∑ j, L i x * L j x) ∂P :=
      by rw [integral_const_mul]
    _ = (Fintype.card ι : Real)⁻¹ ^ 2 *
        ∑ i, ∑ j, ∫ x, L i x * L j x ∂P := by
      congr 1
      rw [integral_finsetSum _ fun i _ =>
        integrable_finsetSum _ fun j _ => hpairInt i j]
      apply Finset.sum_congr rfl
      intro i hi
      rw [integral_finsetSum _ fun j _ => hpairInt i j]

theorem integrable_densityChiSquare_integrand_uniformMixtureDensity
    {Omega ι : Type*} [MeasurableSpace Omega] [Fintype ι]
    (P : Measure Omega) [IsFiniteMeasure P] (L : ι -> Omega -> Real)
    (hLint : forall i, Integrable (L i) P)
    (hpairInt : forall i j, Integrable (fun x => L i x * L j x) P) :
    Integrable (fun x => (uniformMixtureDensity L x - 1) ^ 2) P := by
  classical
  let r : Real := Fintype.card ι
  have hdoubleInt : Integrable
      (fun x => r⁻¹ ^ 2 * ∑ i, ∑ j, L i x * L j x) P :=
    (integrable_finsetSum _ fun i _ =>
      integrable_finsetSum _ fun j _ => hpairInt i j).const_mul _
  have hpoint : forall x,
      uniformMixtureDensity L x ^ 2 =
        r⁻¹ ^ 2 * ∑ i, ∑ j, L i x * L j x := by
    intro x
    unfold uniformMixtureDensity
    change (r⁻¹ * ∑ i, L i x) ^ 2 = _
    rw [mul_pow]
    congr 1
    rw [pow_two, Finset.sum_mul]
    apply Finset.sum_congr rfl
    intro i hi
    rw [Finset.mul_sum]
  have hsqInt : Integrable
      (fun x => uniformMixtureDensity L x ^ 2) P :=
    hdoubleInt.congr (ae_of_all P fun x => (hpoint x).symm)
  have hmixInt := integrable_uniformMixtureDensity P L hLint
  have hpolyInt : Integrable (fun x =>
      (uniformMixtureDensity L x ^ 2 -
        2 * uniformMixtureDensity L x) + 1) P :=
    (hsqInt.sub (hmixInt.const_mul 2)).add (integrable_const 1)
  apply hpolyInt.congr
  filter_upwards [] with x
  ring

/-- The direct expansion displayed in the manuscript:
`chi^2(Q_g || P) = r^-2 sum_{j,l} (E[L_j L_l] - 1)`. -/
theorem densityChiSquare_uniformMixtureDensity_eq_pair_sum
    {Omega ι : Type*} [MeasurableSpace Omega] [Fintype ι] [Nonempty ι]
    (P : Measure Omega) [IsProbabilityMeasure P]
    (L : ι -> Omega -> Real)
    (hLint : forall i, Integrable (L i) P)
    (hLmass : forall i, ∫ x, L i x ∂P = 1)
    (hpairInt : forall i j, Integrable (fun x => L i x * L j x) P) :
    densityChiSquare P (uniformMixtureDensity L) =
      (Fintype.card ι : Real)⁻¹ ^ 2 *
        ∑ i, ∑ j, ((∫ x, L i x * L j x ∂P) - 1) := by
  classical
  let r : Real := Fintype.card ι
  have hr : r ≠ 0 := by
    dsimp [r]
    exact_mod_cast Fintype.card_ne_zero
  have hdoubleInt : Integrable
      (fun x => r⁻¹ ^ 2 * ∑ i, ∑ j, L i x * L j x) P :=
    (integrable_finsetSum _ fun i _ =>
      integrable_finsetSum _ fun j _ => hpairInt i j).const_mul _
  have hpoint : forall x,
      uniformMixtureDensity L x ^ 2 =
        r⁻¹ ^ 2 * ∑ i, ∑ j, L i x * L j x := by
    intro x
    unfold uniformMixtureDensity
    change (r⁻¹ * ∑ i, L i x) ^ 2 = _
    rw [mul_pow]
    congr 1
    rw [pow_two, Finset.sum_mul]
    apply Finset.sum_congr rfl
    intro i hi
    rw [Finset.mul_sum]
  have hmixSqInt : Integrable
      (fun x => uniformMixtureDensity L x ^ 2) P :=
    hdoubleInt.congr (ae_of_all P fun x => (hpoint x).symm)
  have hmixInt := integrable_uniformMixtureDensity P L hLint
  rw [densityChiSquare_eq_integral_sq_sub_one P
    (uniformMixtureDensity L) hmixInt hmixSqInt
    (integral_uniformMixtureDensity P L hLint hLmass)]
  rw [integral_uniformMixtureDensity_sq P L hpairInt]
  change r⁻¹ ^ 2 * (∑ i, ∑ j, ∫ x, L i x * L j x ∂P) - 1 =
    r⁻¹ ^ 2 * ∑ i, ∑ j, ((∫ x, L i x * L j x ∂P) - 1)
  have hsum :
      (∑ i, ∑ j, ((∫ x, L i x * L j x ∂P) - 1)) =
        (∑ i, ∑ j, ∫ x, L i x * L j x ∂P) - r ^ 2 := by
    dsimp [r]
    simp only [Finset.sum_sub_distrib, Finset.sum_const,
      Finset.card_univ, nsmul_eq_mul, mul_one]
    ring
  rw [hsum]
  field_simp [hr]

/-- Uniform density attached directly to a nonempty finset of coordinates. -/
def finsetUniformMixtureDensity
    {Omega ι : Type*} [DecidableEq ι]
    (G : Finset ι) (L : ι -> Omega -> Real) (x : Omega) : Real :=
  (G.card : Real)⁻¹ * ∑ i ∈ G, L i x

theorem uniformMixtureDensity_subtype_eq_finsetUniformMixtureDensity
    {Omega ι : Type*} [DecidableEq ι]
    (G : Finset ι) (L : ι -> Omega -> Real) :
    uniformMixtureDensity (fun i : ↥G => L i.1) =
      finsetUniformMixtureDensity G L := by
  classical
  funext x
  unfold uniformMixtureDensity finsetUniformMixtureDensity
  rw [Fintype.card_coe]
  congr 1
  have hsum := Finset.sum_attach G (fun i => L i x)
  rw [Finset.attach_eq_univ] at hsum
  exact hsum

theorem measurable_finsetUniformMixtureDensity
    {Omega ι : Type*} [MeasurableSpace Omega] [DecidableEq ι]
    (G : Finset ι) (L : ι -> Omega -> Real)
    (hL : forall i, i ∈ G -> Measurable (L i)) :
    Measurable (finsetUniformMixtureDensity G L) := by
  unfold finsetUniformMixtureDensity
  exact measurable_const.mul
    (Finset.measurable_sum G fun i hi => hL i hi)

theorem finsetUniformMixtureDensity_nonneg
    {Omega ι : Type*} [DecidableEq ι]
    (G : Finset ι) (L : ι -> Omega -> Real)
    (hL0 : forall i, i ∈ G -> forall x, 0 <= L i x) (x : Omega) :
    0 <= finsetUniformMixtureDensity G L x := by
  unfold finsetUniformMixtureDensity
  exact mul_nonneg (inv_nonneg.mpr (Nat.cast_nonneg _))
    (Finset.sum_nonneg fun i hi => hL0 i hi x)

theorem averageMeasure_finset_withDensity_eq_withDensity
    {Omega ι : Type*} [MeasurableSpace Omega] [DecidableEq ι]
    (P : Measure Omega) (G : Finset ι) (hG : G.Nonempty)
    (L : ι -> Omega -> Real)
    (hL : forall i, i ∈ G -> Measurable (L i))
    (hL0 : forall i, i ∈ G -> forall x, 0 <= L i x) :
    averageMeasure (fun i : ↥G =>
        P.withDensity (fun x => ENNReal.ofReal (L i.1 x))) =
      P.withDensity (fun x =>
        ENNReal.ofReal (finsetUniformMixtureDensity G L x)) := by
  letI : Nonempty (↥G) := Finset.nonempty_coe_sort.mpr hG
  rw [← uniformMixtureDensity_subtype_eq_finsetUniformMixtureDensity G L]
  exact averageMeasure_withDensity_eq_withDensity_uniformMixtureDensity
    P (fun i : ↥G => L i.1) (fun i => hL i.1 i.2)
      (fun i x => hL0 i.1 i.2 x)

theorem probability_withDensity_finsetUniformMixtureDensity
    {Omega ι : Type*} [MeasurableSpace Omega] [DecidableEq ι]
    (P : Measure Omega) (G : Finset ι) (hG : G.Nonempty)
    (L : ι -> Omega -> Real)
    (hL : forall i, i ∈ G -> Measurable (L i))
    (hL0 : forall i, i ∈ G -> forall x, 0 <= L i x)
    (hQ : forall i, i ∈ G -> IsProbabilityMeasure
      (P.withDensity (fun x => ENNReal.ofReal (L i x)))) :
    IsProbabilityMeasure (P.withDensity (fun x =>
      ENNReal.ofReal (finsetUniformMixtureDensity G L x))) := by
  letI : Nonempty (↥G) := Finset.nonempty_coe_sort.mpr hG
  letI (i : ↥G) : IsProbabilityMeasure
      (P.withDensity (fun x => ENNReal.ofReal (L i.1 x))) := hQ i.1 i.2
  have havg : IsProbabilityMeasure (averageMeasure (fun i : ↥G =>
      P.withDensity (fun x => ENNReal.ofReal (L i.1 x)))) := inferInstance
  rw [averageMeasure_finset_withDensity_eq_withDensity
    P G hG L hL hL0] at havg
  exact havg

theorem integrable_densityChiSquare_integrand_finsetUniformMixtureDensity
    {Omega ι : Type*} [MeasurableSpace Omega] [DecidableEq ι]
    (P : Measure Omega) [IsFiniteMeasure P]
    (G : Finset ι) (_hG : G.Nonempty)
    (L : ι -> Omega -> Real)
    (hLint : forall i, i ∈ G -> Integrable (L i) P)
    (hpairInt : forall i, i ∈ G -> forall j, j ∈ G ->
      Integrable (fun x => L i x * L j x) P) :
    Integrable (fun x => (finsetUniformMixtureDensity G L x - 1) ^ 2) P := by
  letI : Nonempty (↥G) := Finset.nonempty_coe_sort.mpr _hG
  rw [← uniformMixtureDensity_subtype_eq_finsetUniformMixtureDensity G L]
  exact integrable_densityChiSquare_integrand_uniformMixtureDensity
    P (fun i : ↥G => L i.1) (fun i => hLint i.1 i.2)
      (fun i j => hpairInt i.1 i.2 j.1 j.2)

theorem densityChiSquare_finsetUniformMixtureDensity_eq_pair_sum
    {Omega ι : Type*} [MeasurableSpace Omega] [DecidableEq ι]
    (P : Measure Omega) [IsProbabilityMeasure P]
    (G : Finset ι) (hG : G.Nonempty) (L : ι -> Omega -> Real)
    (hLint : forall i, i ∈ G -> Integrable (L i) P)
    (hLmass : forall i, i ∈ G -> ∫ x, L i x ∂P = 1)
    (hpairInt : forall i, i ∈ G -> forall j, j ∈ G ->
      Integrable (fun x => L i x * L j x) P) :
    densityChiSquare P (finsetUniformMixtureDensity G L) =
      (G.card : Real)⁻¹ ^ 2 *
        ∑ i ∈ G, ∑ j ∈ G,
          ((∫ x, L i x * L j x ∂P) - 1) := by
  classical
  letI : Nonempty (↥G) := Finset.nonempty_coe_sort.mpr hG
  let L' : (↥G) -> Omega -> Real := fun i => L i.1
  have hbase := densityChiSquare_uniformMixtureDensity_eq_pair_sum
    P L' (fun i => hLint i.1 i.2) (fun i => hLmass i.1 i.2)
      (fun i j => hpairInt i.1 i.2 j.1 j.2)
  have hden : uniformMixtureDensity L' =
      finsetUniformMixtureDensity G L := by
    funext x
    unfold uniformMixtureDensity finsetUniformMixtureDensity
    rw [Fintype.card_coe]
    congr 1
    have hsum := Finset.sum_attach G (fun i => L i x)
    rw [Finset.attach_eq_univ] at hsum
    exact hsum
  have hpairs :
      (∑ i : ↥G, ∑ j : ↥G,
          ((∫ x, L i.1 x * L j.1 x ∂P) - 1)) =
        ∑ i ∈ G, ∑ j ∈ G,
          ((∫ x, L i x * L j x ∂P) - 1) := by
    calc
      (∑ i : ↥G, ∑ j : ↥G,
          ((∫ x, L i.1 x * L j.1 x ∂P) - 1)) =
        ∑ i ∈ G.attach, ∑ j ∈ G.attach,
          ((∫ x, L i.1 x * L j.1 x ∂P) - 1) := by
            simp only [Finset.attach_eq_univ]
      _ = ∑ i ∈ G.attach, ∑ j ∈ G,
          ((∫ x, L i.1 x * L j x ∂P) - 1) := by
            apply Finset.sum_congr rfl
            intro i hi
            exact Finset.sum_attach G (fun j =>
              ((∫ x, L i.1 x * L j x ∂P) - 1))
      _ = ∑ i ∈ G, ∑ j ∈ G,
          ((∫ x, L i x * L j x ∂P) - 1) :=
            Finset.sum_attach G (fun i =>
              ∑ j ∈ G, ((∫ x, L i x * L j x ∂P) - 1))
  rw [hden, Fintype.card_coe, hpairs] at hbase
  exact hbase

/-- Aggregation of diagonal and off-diagonal likelihood moments over
equal-sized groups.  This is the algebraic content between the three
displayed formulas preceding `eq:lower-mixture-tv`. -/
theorem average_densityChiSquare_finset_groups_le
    {Omega ι γ : Type*} [MeasurableSpace Omega] [DecidableEq ι]
    [Fintype γ] [Nonempty γ]
    (P : Measure Omega) [IsProbabilityMeasure P]
    (G : γ -> Finset ι) (r : Nat) (hr : 1 <= r)
    (hcard : forall g, (G g).card = r)
    (L : ι -> Omega -> Real)
    (hLint : forall g i, i ∈ G g -> Integrable (L i) P)
    (hLmass : forall g i, i ∈ G g -> ∫ x, L i x ∂P = 1)
    (hpairInt : forall g i, i ∈ G g -> forall j, j ∈ G g ->
      Integrable (fun x => L i x * L j x) P)
    (D K M : Real) (hK0 : 0 <= K)
    (W : ι × ι -> Real)
    (hdiag : forall g i, i ∈ G g ->
      (∫ x, L i x * L i x ∂P) <= D)
    (hcross : forall g p, p ∈ (G g).offDiag ->
      (∫ x, L p.1 x * L p.2 x ∂P) - 1 <= K * W p)
    (hWsum : (∑ g, ∑ p ∈ (G g).offDiag, W p) <= M) :
    (∑ g, densityChiSquare P (finsetUniformMixtureDensity (G g) L)) /
        (Fintype.card γ : Real) <=
      (D - 1) / (r : Real) +
        K * M / ((Fintype.card γ : Real) * (r : Real) ^ 2) := by
  classical
  let c : Real := Fintype.card γ
  let rr : Real := r
  have hcpos : 0 < c := by
    dsimp [c]
    exact_mod_cast Fintype.card_pos
  have hrrpos : 0 < rr := by
    dsimp [rr]
    exact_mod_cast hr
  have hGnonempty : forall g, (G g).Nonempty := by
    intro g
    rw [Finset.nonempty_iff_ne_empty]
    intro hzero
    have : (G g).card = 0 := by simp [hzero]
    rw [hcard g] at this
    omega
  let E : ι × ι -> Real := fun p =>
    (∫ x, L p.1 x * L p.2 x ∂P) - 1
  have hsplit : forall g,
      (∑ i ∈ G g, ∑ j ∈ G g, E (i, j)) =
        (∑ i ∈ G g, E (i, i)) +
          ∑ p ∈ (G g).offDiag, E p := by
    intro g
    rw [← Finset.sum_product']
    rw [← Finset.diag_union_offDiag]
    rw [Finset.sum_union (Finset.disjoint_diag_offDiag _)]
    rw [Finset.sum_diag]
  have hdiagSum : forall g,
      (∑ i ∈ G g, E (i, i)) <= (r : Real) * (D - 1) := by
    intro g
    calc
      (∑ i ∈ G g, E (i, i)) <= ∑ _i ∈ G g, (D - 1) := by
        apply Finset.sum_le_sum
        intro i hi
        dsimp [E]
        linarith [hdiag g i hi]
      _ = (r : Real) * (D - 1) := by
        simp [hcard g]
        ring
  have hcrossSum : forall g,
      (∑ p ∈ (G g).offDiag, E p) <=
        K * ∑ p ∈ (G g).offDiag, W p := by
    intro g
    calc
      (∑ p ∈ (G g).offDiag, E p) <=
          ∑ p ∈ (G g).offDiag, K * W p := by
        apply Finset.sum_le_sum
        intro p hp
        exact hcross g p hp
      _ = K * ∑ p ∈ (G g).offDiag, W p := by
        rw [Finset.mul_sum]
  have hgroup : forall g,
      densityChiSquare P (finsetUniformMixtureDensity (G g) L) <=
        (r : Real)⁻¹ ^ 2 * ((r : Real) * (D - 1) +
          K * ∑ p ∈ (G g).offDiag, W p) := by
    intro g
    rw [densityChiSquare_finsetUniformMixtureDensity_eq_pair_sum
      P (G g) (hGnonempty g) L (hLint g) (hLmass g) (hpairInt g)]
    rw [hcard g]
    apply mul_le_mul_of_nonneg_left _ (sq_nonneg _)
    rw [hsplit g]
    exact add_le_add (hdiagSum g) (hcrossSum g)
  have hsumGroup :
      (∑ g, densityChiSquare P (finsetUniformMixtureDensity (G g) L)) <=
        c * (rr⁻¹ ^ 2 * (rr * (D - 1))) +
          rr⁻¹ ^ 2 * K * M := by
    calc
      (∑ g, densityChiSquare P (finsetUniformMixtureDensity (G g) L)) <=
          ∑ g, rr⁻¹ ^ 2 * (rr * (D - 1) +
            K * ∑ p ∈ (G g).offDiag, W p) := by
        apply Finset.sum_le_sum
        intro g hg
        simpa [rr] using hgroup g
      _ = c * (rr⁻¹ ^ 2 * (rr * (D - 1))) +
          rr⁻¹ ^ 2 * K *
            (∑ g, ∑ p ∈ (G g).offDiag, W p) := by
        simp only [mul_add, ← mul_assoc, Finset.sum_add_distrib,
          Finset.sum_const, nsmul_eq_mul]
        rw [Finset.mul_sum]
        dsimp [c]
      _ <= c * (rr⁻¹ ^ 2 * (rr * (D - 1))) +
          rr⁻¹ ^ 2 * K * M := by
        exact add_le_add le_rfl (mul_le_mul_of_nonneg_left hWsum
          (mul_nonneg (sq_nonneg _) hK0))
  change (∑ g, densityChiSquare P
      (finsetUniformMixtureDensity (G g) L)) / c <=
    (D - 1) / rr + K * M / (c * rr ^ 2)
  have hdiv := div_le_div_of_nonneg_right hsumGroup hcpos.le
  calc
    (∑ g, densityChiSquare P
        (finsetUniformMixtureDensity (G g) L)) / c <=
      (c * (rr⁻¹ ^ 2 * (rr * (D - 1))) +
        rr⁻¹ ^ 2 * K * M) / c := hdiv
    _ = (D - 1) / rr + K * M / (c * rr ^ 2) := by
      field_simp [hcpos.ne', hrrpos.ne']

/-- Direct integration of `eq:lower-good-partition` with the likelihood
moment expansion.  It returns the actual manuscript partition and the
corresponding average chi-square estimate. -/
theorem exists_sparse_good_partition_average_densityChiSquare_le
    {Omega : Type*} [MeasurableSpace Omega]
    {n n' k r q c0 t : Nat}
    (hk : 1 <= k) (hr : 1 <= r) (hn' : 2 <= n') (hn'n : n' <= n)
    (hprod : n' = k * r)
    (P : Measure Omega) [IsProbabilityMeasure P]
    (mu : Measure (History n k t)) [IsProbabilityMeasure mu]
    (L : Fin n' -> Omega -> Real)
    (hLint : forall j, Integrable (L j) P)
    (hLmass : forall j, ∫ x, L j x ∂P = 1)
    (hpairInt : forall j l, Integrable (fun x => L j x * L l x) P)
    (D K : Real) (hK0 : 0 <= K)
    (hdiag : forall j, (∫ x, L j x * L j x ∂P) <= D)
    (hcross : forall j l, j ≠ l ->
      (∫ x, L j x * L l x ∂P) - 1 <=
        K * sparseExpectedN mu hn'n q c0 j l) :
    ∃ sigma : Equiv.Perm (Fin n'),
      (forall g : Fin k,
        (sparsePartitionGroup hprod sigma g).card = r) ∧
      (∑ g : Fin k, densityChiSquare P
          (finsetUniformMixtureDensity
            (sparsePartitionGroup hprod sigma g) L)) / (k : Real) <=
        (D - 1) / (r : Real) +
          K * ((t : Real) / (k : Real)) /
            ((k : Real) * (r : Real) ^ 2) := by
  obtain ⟨sigma, hcards, hgood⟩ :=
    lower_good_partition hk hn' hn'n hprod mu
  refine ⟨sigma, hcards, ?_⟩
  letI : Nonempty (Fin k) := ⟨⟨0, by omega⟩⟩
  let W : Fin n' × Fin n' -> Real := fun p =>
    sparseExpectedN mu hn'n q c0 p.1 p.2
  have hagg := average_densityChiSquare_finset_groups_le
    P (fun g : Fin k => sparsePartitionGroup hprod sigma g) r hr hcards L
      (fun _g i _hi => hLint i)
      (fun _g i _hi => hLmass i)
      (fun _g i _hi j _hj => hpairInt i j)
      D K ((t : Real) / (k : Real)) hK0 W
      (fun _g i _hi => hdiag i)
      (fun _g p hp => by
        exact hcross p.1 p.2 (Finset.mem_offDiag.mp hp).2.2)
      hgood
  simpa [W] using hagg

/-- Full RN-density version of the preceding theorem.  This is the form
intended for the full hidden-table likelihoods: normalization and all real
integrability premises are derived here from the actual probability laws and
finite `ENNReal` moment bounds. -/
theorem exists_sparse_good_partition_average_densityChiSquare_le_of_ennreal
    {Omega : Type*} [MeasurableSpace Omega]
    {n n' k r q c0 t : Nat}
    (hk : 1 <= k) (hr : 1 <= r) (hn' : 2 <= n') (hn'n : n' <= n)
    (hprod : n' = k * r)
    (P : Measure Omega) [IsProbabilityMeasure P]
    (mu : Measure (History n k t)) [IsProbabilityMeasure mu]
    (Lambda : Fin n' -> Omega -> ENNReal)
    (hLambda : forall j, Measurable (Lambda j))
    (hLambdaFinite : forall j, ∀ᵐ x ∂P, Lambda j x < ∞)
    (hQ : forall j, IsProbabilityMeasure (P.withDensity (Lambda j)))
    (D K : Real) (hD0 : 0 <= D) (hK0 : 0 <= K)
    (hdiag : forall j,
      (∫⁻ x, Lambda j x * Lambda j x ∂P) <= ENNReal.ofReal D)
    (hcross : forall j l, j ≠ l ->
      (∫⁻ x, Lambda j x * Lambda l x ∂P) <=
        ENNReal.ofReal
          (1 + K * sparseExpectedN mu hn'n q c0 j l)) :
    ∃ sigma : Equiv.Perm (Fin n'),
      (forall g : Fin k,
        (sparsePartitionGroup hprod sigma g).card = r) ∧
      (∑ g : Fin k, densityChiSquare P
          (finsetUniformMixtureDensity
            (sparsePartitionGroup hprod sigma g)
            (fun j => ennrealDensityReal (Lambda j)))) / (k : Real) <=
        (D - 1) / (r : Real) +
          K * ((t : Real) / (k : Real)) /
            ((k : Real) * (r : Real) ^ 2) := by
  let L : Fin n' -> Omega -> Real := fun j =>
    ennrealDensityReal (Lambda j)
  have hnorm : forall j,
      Integrable (L j) P ∧ ∫ x, L j x ∂P = 1 := by
    intro j
    exact ennrealDensityReal_integrable_and_integral_eq_one
      P (Lambda j) (hLambda j) (hLambdaFinite j) (hQ j)
  have hmomentFinite : forall j l,
      (∫⁻ x, Lambda j x * Lambda l x ∂P) ≠ ∞ := by
    intro j l
    by_cases hjl : j = l
    · subst l
      exact ne_top_of_le_ne_top ENNReal.ofReal_ne_top (hdiag j)
    · exact ne_top_of_le_ne_top ENNReal.ofReal_ne_top (hcross j l hjl)
  have hpairReal : forall j l,
      Integrable (fun x => L j x * L l x) P ∧
        (∫ x, L j x * L l x ∂P) =
          (∫⁻ x, Lambda j x * Lambda l x ∂P).toReal := by
    intro j l
    exact ennrealDensityReal_pair_integrable_and_integral_eq
      P (Lambda j) (Lambda l) (hLambda j) (hLambda l)
        (hLambdaFinite j) (hLambdaFinite l) (hmomentFinite j l)
  have hdiagReal : forall j, (∫ x, L j x * L j x ∂P) <= D := by
    intro j
    have hreal := ENNReal.toReal_mono ENNReal.ofReal_ne_top (hdiag j)
    rw [(hpairReal j j).2]
    simpa [ENNReal.toReal_ofReal hD0] using hreal
  have hcrossReal : forall j l, j ≠ l ->
      (∫ x, L j x * L l x ∂P) - 1 <=
        K * sparseExpectedN mu hn'n q c0 j l := by
    intro j l hjl
    have hW0 : 0 <= sparseExpectedN mu hn'n q c0 j l :=
      sparseExpectedN_nonneg mu hn'n j l
    have hC0 : 0 <= 1 + K * sparseExpectedN mu hn'n q c0 j l :=
      add_nonneg (by norm_num) (mul_nonneg hK0 hW0)
    have hreal := ENNReal.toReal_mono ENNReal.ofReal_ne_top
      (hcross j l hjl)
    rw [(hpairReal j l).2]
    rw [ENNReal.toReal_ofReal hC0] at hreal
    linarith
  exact exists_sparse_good_partition_average_densityChiSquare_le
    hk hr hn' hn'n hprod P mu L
      (fun j => (hnorm j).1) (fun j => (hnorm j).2)
      (fun j l => (hpairReal j l).1) D K hK0 hdiagReal hcrossReal

/-- Jensen/Cauchy--Schwarz step in `eq:lower-mixture-tv`, for an arbitrary
finite family of explicit probability densities. -/
theorem average_totalVariationDistance_le_half_sqrt_average_chiSquare
    {Omega ι : Type*} [MeasurableSpace Omega] [Fintype ι] [Nonempty ι]
    (P : Measure Omega) [IsProbabilityMeasure P]
    (L : ι -> Omega -> Real)
    (hL : forall i, Measurable (L i))
    (hL0 : forall i x, 0 <= L i x)
    (hQ : forall i, IsProbabilityMeasure
      (P.withDensity (fun x => ENNReal.ofReal (L i x))))
    (hchiInt : forall i, Integrable (fun x => (L i x - 1) ^ 2) P) :
    (∑ i, totalVariationDistance
        (P.withDensity (fun x => ENNReal.ofReal (L i x))) P) /
          (Fintype.card ι : Real) <=
      (1 : Real) / 2 * Real.sqrt
        ((∑ i, densityChiSquare P (L i)) /
          (Fintype.card ι : Real)) := by
  classical
  let r : Real := Fintype.card ι
  have hrpos : 0 < r := by
    dsimp [r]
    exact_mod_cast Fintype.card_pos
  have hchi0 : forall i, 0 <= densityChiSquare P (L i) := by
    intro i
    exact integral_nonneg fun x => sq_nonneg (L i x - 1)
  have hterm : forall i,
      totalVariationDistance
          (P.withDensity (fun x => ENNReal.ofReal (L i x))) P <=
        (1 : Real) / 2 * Real.sqrt (densityChiSquare P (L i)) := by
    intro i
    exact totalVariationDistance_withDensity_le_half_sqrt_chiSquare
      P (L i) (hL i) (hL0 i) (hQ i) (hchiInt i)
  have hsumTV :
      (∑ i, totalVariationDistance
          (P.withDensity (fun x => ENNReal.ofReal (L i x))) P) <=
        (1 : Real) / 2 * ∑ i, Real.sqrt (densityChiSquare P (L i)) := by
    calc
      (∑ i, totalVariationDistance
          (P.withDensity (fun x => ENNReal.ofReal (L i x))) P) <=
          ∑ i, (1 : Real) / 2 *
            Real.sqrt (densityChiSquare P (L i)) :=
        Finset.sum_le_sum fun i _ => hterm i
      _ = (1 : Real) / 2 *
          ∑ i, Real.sqrt (densityChiSquare P (L i)) := by
        rw [Finset.mul_sum]
  have hcs : (∑ i, Real.sqrt (densityChiSquare P (L i))) <=
      Real.sqrt (∑ i, densityChiSquare P (L i)) * Real.sqrt r := by
    have h := Real.sum_sqrt_mul_sqrt_le
      (Finset.univ : Finset ι) hchi0 (fun _ => (zero_le_one : (0 : Real) <= 1))
    simpa [r] using h
  have hsqrtrpos : 0 < Real.sqrt r := Real.sqrt_pos.2 hrpos
  have hnormalize :
      r⁻¹ * (Real.sqrt (∑ i, densityChiSquare P (L i)) * Real.sqrt r) =
        Real.sqrt (r⁻¹ * ∑ i, densityChiSquare P (L i)) := by
    rw [Real.sqrt_mul (inv_nonneg.mpr hrpos.le), Real.sqrt_inv]
    have hsqrtrsq : Real.sqrt r ^ 2 = r := Real.sq_sqrt hrpos.le
    field_simp [hrpos.ne', hsqrtrpos.ne']
    rw [hsqrtrsq]
    ring
  change (∑ i, totalVariationDistance
      (P.withDensity (fun x => ENNReal.ofReal (L i x))) P) * r⁻¹ <=
    (1 : Real) / 2 * Real.sqrt
      ((∑ i, densityChiSquare P (L i)) * r⁻¹)
  rw [mul_comm (∑ i, totalVariationDistance
      (P.withDensity (fun x => ENNReal.ofReal (L i x))) P) r⁻¹,
    mul_comm (∑ i, densityChiSquare P (L i)) r⁻¹]
  calc
    r⁻¹ * (∑ i, totalVariationDistance
        (P.withDensity (fun x => ENNReal.ofReal (L i x))) P) <=
      r⁻¹ * ((1 : Real) / 2 *
        ∑ i, Real.sqrt (densityChiSquare P (L i))) :=
      mul_le_mul_of_nonneg_left hsumTV (inv_nonneg.mpr hrpos.le)
    _ <= r⁻¹ * ((1 : Real) / 2 *
        (Real.sqrt (∑ i, densityChiSquare P (L i)) * Real.sqrt r)) :=
      mul_le_mul_of_nonneg_left
        (mul_le_mul_of_nonneg_left hcs (by norm_num))
        (inv_nonneg.mpr hrpos.le)
    _ = (1 : Real) / 2 * Real.sqrt
        (r⁻¹ * ∑ i, densityChiSquare P (L i)) := by
      rw [← hnormalize]
      ring

theorem half_sqrt_two_zpow_neg_thirty :
    (1 : Real) / 2 * Real.sqrt ((2 : Real) ^ (-30 : Int)) =
      (2 : Real) ^ (-16 : Int) := by
  rw [show (2 : Real) ^ (-30 : Int) = ((32768 : Real) ^ 2)⁻¹ by
    norm_num [zpow_neg]]
  rw [Real.sqrt_inv, Real.sqrt_sq_eq_abs]
  norm_num [zpow_neg]

/-- Equation `eq:lower-mixture-tv`: once the likelihood calculation gives
the manuscript's average chi-square bound `2^-30`, the average total
variation is at most `2^-16`. -/
theorem lower_mixture_tv_of_average_chiSquare_le
    {Omega ι : Type*} [MeasurableSpace Omega] [Fintype ι] [Nonempty ι]
    (P : Measure Omega) [IsProbabilityMeasure P]
    (L : ι -> Omega -> Real)
    (hL : forall i, Measurable (L i))
    (hL0 : forall i x, 0 <= L i x)
    (hQ : forall i, IsProbabilityMeasure
      (P.withDensity (fun x => ENNReal.ofReal (L i x))))
    (hchiInt : forall i, Integrable (fun x => (L i x - 1) ^ 2) P)
    (hchiAverage :
      (∑ i, densityChiSquare P (L i)) / (Fintype.card ι : Real) <=
        (2 : Real) ^ (-30 : Int)) :
    (∑ i, totalVariationDistance
        (P.withDensity (fun x => ENNReal.ofReal (L i x))) P) /
          (Fintype.card ι : Real) <=
      (2 : Real) ^ (-16 : Int) := by
  have hJensen :=
    average_totalVariationDistance_le_half_sqrt_average_chiSquare
      P L hL hL0 hQ hchiInt
  calc
    (∑ i, totalVariationDistance
        (P.withDensity (fun x => ENNReal.ofReal (L i x))) P) /
          (Fintype.card ι : Real) <=
      (1 : Real) / 2 * Real.sqrt
        ((∑ i, densityChiSquare P (L i)) /
          (Fintype.card ι : Real)) := hJensen
    _ <= (1 : Real) / 2 * Real.sqrt ((2 : Real) ^ (-30 : Int)) :=
      mul_le_mul_of_nonneg_left (Real.sqrt_le_sqrt hchiAverage) (by norm_num)
    _ = (2 : Real) ^ (-16 : Int) := half_sqrt_two_zpow_neg_thirty

/-- Finset-group form of `eq:lower-mixture-tv`.  By
`averageMeasure_finset_withDensity_eq_withDensity`, each measure displayed
on the left is literally the uniform mixture of the component changed laws. -/
theorem lower_mixture_tv_finset_groups_of_average_chiSquare_le
    {Omega ι γ : Type*} [MeasurableSpace Omega] [DecidableEq ι]
    [Fintype γ] [Nonempty γ]
    (P : Measure Omega) [IsProbabilityMeasure P]
    (G : γ -> Finset ι) (hG : forall g, (G g).Nonempty)
    (L : ι -> Omega -> Real)
    (hL : forall i, Measurable (L i))
    (hL0 : forall i x, 0 <= L i x)
    (hLint : forall i, Integrable (L i) P)
    (hpairInt : forall i j, Integrable (fun x => L i x * L j x) P)
    (hQg : forall g, IsProbabilityMeasure
      (P.withDensity (fun x => ENNReal.ofReal
        (finsetUniformMixtureDensity (G g) L x))))
    (hchiAverage :
      (∑ g, densityChiSquare P
          (finsetUniformMixtureDensity (G g) L)) /
          (Fintype.card γ : Real) <= (2 : Real) ^ (-30 : Int)) :
    (∑ g, totalVariationDistance
        (P.withDensity (fun x => ENNReal.ofReal
          (finsetUniformMixtureDensity (G g) L x))) P) /
          (Fintype.card γ : Real) <= (2 : Real) ^ (-16 : Int) := by
  let Lg : γ -> Omega -> Real := fun g =>
    finsetUniformMixtureDensity (G g) L
  have hLg : forall g, Measurable (Lg g) := by
    intro g
    exact measurable_finsetUniformMixtureDensity (G g) L
      (fun i _hi => hL i)
  have hLg0 : forall g x, 0 <= Lg g x := by
    intro g x
    exact finsetUniformMixtureDensity_nonneg (G g) L
      (fun i _hi x => hL0 i x) x
  have hQg' : forall g, IsProbabilityMeasure
      (P.withDensity (fun x => ENNReal.ofReal (Lg g x))) := by
    intro g
    simpa [Lg] using hQg g
  have hchiInt : forall g,
      Integrable (fun x => (Lg g x - 1) ^ 2) P := by
    intro g
    exact integrable_densityChiSquare_integrand_finsetUniformMixtureDensity
      P (G g) (hG g) L (fun i _hi => hLint i)
        (fun i _hi j _hj => hpairInt i j)
  have htv := lower_mixture_tv_of_average_chiSquare_le
    P Lg hLg hLg0 hQg' hchiInt (by simpa [Lg] using hchiAverage)
  simpa [Lg] using htv

#print axioms totalVariationDistance_withDensity_le_half_sqrt_chiSquare
#print axioms withDensity_ofReal_ennrealDensityReal_eq
#print axioms ennrealDensityReal_pair_integral_le
#print axioms averageMeasure_withDensity_eq_withDensity_uniformMixtureDensity
#print axioms densityChiSquare_uniformMixtureDensity_eq_pair_sum
#print axioms average_densityChiSquare_finset_groups_le
#print axioms exists_sparse_good_partition_average_densityChiSquare_le_of_ennreal
#print axioms average_totalVariationDistance_le_half_sqrt_average_chiSquare
#print axioms lower_mixture_tv_of_average_chiSquare_le
#print axioms lower_mixture_tv_finset_groups_of_average_chiSquare_le

end

end MsetsLower.Lower.Sparse
