import MsetsLower.Lower.Dense.PairedConstruction
import MsetsLower.Information.SequentialKL
import Mathlib.Probability.Distributions.Bernoulli

/-!
# One-step information bound for the dense paired construction

This file formalizes equation `eq:lower-dense-one-step-kl` from the
manuscript.  The binary divergence is expanded into its two finite atoms;
the proof does not assume a Bernoulli KL estimate as a hypothesis.
-/

namespace MsetsLower.Lower.Dense

open MsetsLower
open MeasureTheory ProbabilityTheory InformationTheory
open scoped BigOperators ENNReal NNReal

noncomputable section

/-- The binary relative entropy used by the manuscript, written as the
literal sum over the two Bernoulli atoms. -/
def bernoulliKL (a b : Real) : Real :=
  a * Real.log (a / b) + (1 - a) * Real.log ((1 - a) / (1 - b))

/-- The two-atom mass function of a Bernoulli law. -/
def bernoulliMass (a : Real) : Bool → Real
  | true => a
  | false => 1 - a

/-- Relative entropy of two finite mass functions, expanded atom by atom. -/
def finiteLawKL {ι : Type*} [Fintype ι] (p q : ι → Real) : Real :=
  ∑ i, p i * Real.log (p i / q i)

/-- `bernoulliKL` is literally the finite-law KL between the corresponding
two-atom Bernoulli mass functions. -/
theorem finiteLawKL_bernoulliMass (a b : Real) :
    finiteLawKL (bernoulliMass a) (bernoulliMass b) = bernoulliKL a b := by
  rw [finiteLawKL, Fintype.sum_bool]
  simp [bernoulliMass, bernoulliKL]

/-- Counting-measure density of the finite Bernoulli law. -/
def bernoulliDensity (a : Real) (x : Bool) : ℝ≥0∞ :=
  ENNReal.ofReal (bernoulliMass a x)

/-- Pointwise likelihood ratio of two Bernoulli densities. -/
def bernoulliDensityRatio (a b : Real) (x : Bool) : ℝ≥0∞ :=
  bernoulliDensity a x / bernoulliDensity b x

/-- A genuine measure realization of the two-atom Bernoulli law. -/
def bernoulliLaw (a : Real) : Measure Bool :=
  Measure.count.withDensity (bernoulliDensity a)

theorem measurable_bernoulliDensity (a : Real) :
    Measurable (bernoulliDensity a) := measurable_of_finite _

theorem measurable_bernoulliDensityRatio (a b : Real) :
    Measurable (bernoulliDensityRatio a b) := by
  exact (measurable_bernoulliDensity a).div (measurable_bernoulliDensity b)

theorem bernoulliMass_pos {a : Real} (ha0 : 0 < a) (ha1 : a < 1)
    (x : Bool) : 0 < bernoulliMass a x := by
  cases x <;> simp [bernoulliMass] <;> linarith

theorem bernoulliDensity_ne_zero {a : Real} (ha0 : 0 < a) (ha1 : a < 1)
    (x : Bool) : bernoulliDensity a x ≠ 0 := by
  exact ne_of_gt (ENNReal.ofReal_pos.mpr (bernoulliMass_pos ha0 ha1 x))

theorem bernoulliDensity_ne_top (a : Real) (x : Bool) :
    bernoulliDensity a x ≠ ∞ := by
  simp [bernoulliDensity]

/-- The measure has total mass one whenever `a` is a probability. -/
theorem bernoulliLaw_apply_univ {a : Real} (ha0 : 0 ≤ a) (ha1 : a ≤ 1) :
    bernoulliLaw a Set.univ = 1 := by
  rw [bernoulliLaw, withDensity_apply _ MeasurableSet.univ,
    Measure.restrict_univ, lintegral_fintype]
  rw [Fintype.sum_bool]
  simp only [Measure.count_singleton, mul_one, bernoulliDensity, bernoulliMass]
  rw [← ENNReal.ofReal_add ha0 (sub_nonneg.mpr ha1)]
  norm_num

/-- Reweighting the `b`-Bernoulli law by the pointwise likelihood ratio
gives the `a`-Bernoulli law. -/
theorem bernoulliLaw_withDensity_ratio {a b : Real}
    (hb0 : 0 < b) (hb1 : b < 1) :
    bernoulliLaw a = (bernoulliLaw b).withDensity
      (bernoulliDensityRatio a b) := by
  have hprod :
      bernoulliDensity b * bernoulliDensityRatio a b =
        bernoulliDensity a := by
    funext x
    change bernoulliDensity b x *
      bernoulliDensityRatio a b x = bernoulliDensity a x
    exact ENNReal.mul_div_cancel
      (bernoulliDensity_ne_zero hb0 hb1 x) (bernoulliDensity_ne_top b x)
  rw [bernoulliLaw, bernoulliLaw]
  calc
    Measure.count.withDensity (bernoulliDensity a) =
        Measure.count.withDensity
          (bernoulliDensity b * bernoulliDensityRatio a b) := by rw [hprod]
    _ = (Measure.count.withDensity (bernoulliDensity b)).withDensity
        (bernoulliDensityRatio a b) :=
      withDensity_mul Measure.count (measurable_bernoulliDensity b)
        (measurable_bernoulliDensityRatio a b)

/-- Interior Bernoulli laws are mutually absolutely continuous. -/
theorem bernoulliLaw_absolutelyContinuous {a b : Real}
    (hb0 : 0 < b) (hb1 : b < 1) : bernoulliLaw a ≪ bernoulliLaw b := by
  rw [bernoulliLaw_withDensity_ratio hb0 hb1]
  exact MeasureTheory.withDensity_absolutelyContinuous _ _

/-- Radon--Nikodym derivative of two interior Bernoulli laws. -/
theorem rnDeriv_bernoulliLaw {a b : Real} (hb0 : 0 < b) (hb1 : b < 1) :
    (bernoulliLaw a).rnDeriv (bernoulliLaw b) =ᵐ[bernoulliLaw b]
      bernoulliDensityRatio a b := by
  letI : SigmaFinite (bernoulliLaw b) := by
    rw [bernoulliLaw]
    exact SigmaFinite.withDensity_of_ne_top'
      (fun x => bernoulliDensity_ne_top b x)
  have hratio :
      ((bernoulliLaw b).withDensity (bernoulliDensityRatio a b)).rnDeriv
          (bernoulliLaw b) =ᵐ[bernoulliLaw b] bernoulliDensityRatio a b :=
    Measure.rnDeriv_withDensity (bernoulliLaw b)
      (measurable_bernoulliDensityRatio a b)
  nth_rw 1 [bernoulliLaw_withDensity_ratio (a := a) (b := b) hb0 hb1]
  exact hratio

/-- Mathlib's measure-theoretic KL of the genuine two-atom measures equals
the finite Bernoulli formula used above. -/
theorem toReal_klDiv_bernoulliLaw_eq {a b : Real}
    (ha0 : 0 < a) (ha1 : a < 1) (hb0 : 0 < b) (hb1 : b < 1) :
    (klDiv (bernoulliLaw a) (bernoulliLaw b)).toReal = bernoulliKL a b := by
  letI : IsFiniteMeasure (bernoulliLaw a) :=
    ⟨by rw [bernoulliLaw_apply_univ ha0.le ha1.le]; norm_num⟩
  letI : IsFiniteMeasure (bernoulliLaw b) :=
    ⟨by rw [bernoulliLaw_apply_univ hb0.le hb1.le]; norm_num⟩
  have hac : bernoulliLaw a ≪ bernoulliLaw b :=
    bernoulliLaw_absolutelyContinuous hb0 hb1
  rw [InformationTheory.toReal_klDiv_eq_integral_klFun hac]
  have hrn := rnDeriv_bernoulliLaw (a := a) (b := b) hb0 hb1
  calc
    (∫ x, klFun (((bernoulliLaw a).rnDeriv (bernoulliLaw b) x).toReal)
        ∂bernoulliLaw b) =
        ∫ x, klFun ((bernoulliDensityRatio a b x).toReal)
          ∂bernoulliLaw b := by
      apply integral_congr_ae
      filter_upwards [hrn] with x hx
      rw [hx]
    _ = bernoulliKL a b := by
      have hdtop : ∀ᵐ x ∂(Measure.count : Measure Bool),
          bernoulliDensity b x < ∞ :=
        ae_of_all _ fun x => lt_top_iff_ne_top.mpr (bernoulliDensity_ne_top b x)
      rw [bernoulliLaw,
        integral_withDensity_eq_integral_toReal_smul
          (measurable_bernoulliDensity b) hdtop]
      rw [MeasureTheory.integral_count, Fintype.sum_bool]
      simp only [smul_eq_mul, bernoulliDensityRatio, bernoulliDensity,
        bernoulliMass]
      rw [ENNReal.toReal_ofReal hb0.le,
        ENNReal.toReal_ofReal (sub_nonneg.mpr hb1.le),
        ENNReal.toReal_div, ENNReal.toReal_div,
        ENNReal.toReal_ofReal ha0.le, ENNReal.toReal_ofReal hb0.le,
        ENNReal.toReal_ofReal (sub_nonneg.mpr ha1.le),
        ENNReal.toReal_ofReal (sub_nonneg.mpr hb1.le)]
      rw [klFun_apply, klFun_apply]
      rw [bernoulliKL]
      field_simp [ne_of_gt hb0, ne_of_gt (sub_pos.mpr hb1)]
      ring

/-- ENNReal-valued version of the exact Bernoulli KL formula. -/
theorem klDiv_bernoulliLaw_eq_ofReal {a b : Real}
    (ha0 : 0 < a) (ha1 : a < 1) (hb0 : 0 < b) (hb1 : b < 1) :
    klDiv (bernoulliLaw a) (bernoulliLaw b) = ENNReal.ofReal (bernoulliKL a b) := by
  letI : IsFiniteMeasure (bernoulliLaw a) :=
    ⟨by rw [bernoulliLaw_apply_univ ha0.le ha1.le]; norm_num⟩
  letI : IsFiniteMeasure (bernoulliLaw b) :=
    ⟨by rw [bernoulliLaw_apply_univ hb0.le hb1.le]; norm_num⟩
  have hac : bernoulliLaw a ≪ bernoulliLaw b :=
    bernoulliLaw_absolutelyContinuous hb0 hb1
  have hint : Integrable
      (llr (bernoulliLaw a) (bernoulliLaw b)) (bernoulliLaw a) := by
    rw [← integrableOn_univ]
    exact IntegrableOn.of_finite Set.finite_univ
  have hne : klDiv (bernoulliLaw a) (bernoulliLaw b) ≠ ∞ :=
    InformationTheory.klDiv_ne_top hac hint
  calc
    klDiv (bernoulliLaw a) (bernoulliLaw b) =
        ENNReal.ofReal (klDiv (bernoulliLaw a) (bernoulliLaw b)).toReal :=
      (ENNReal.ofReal_toReal hne).symm
    _ = ENNReal.ofReal (bernoulliKL a b) := by
      rw [toReal_klDiv_bernoulliLaw_eq ha0 ha1 hb0 hb1]

/-- The elementary estimate `kl(a,b) ≤ (a-b)²/(b(1-b))`, proved directly
from `log x ≤ x-1` on the two atoms. -/
theorem bernoulliKL_le_chiSquare {a b : Real}
    (ha0 : 0 < a) (ha1 : a < 1) (hb0 : 0 < b) (hb1 : b < 1) :
    bernoulliKL a b ≤ (a - b) ^ 2 / (b * (1 - b)) := by
  have hab0 : 0 < a / b := div_pos ha0 hb0
  have hcab0 : 0 < (1 - a) / (1 - b) :=
    div_pos (sub_pos.mpr ha1) (sub_pos.mpr hb1)
  have hfirst := mul_le_mul_of_nonneg_left
    (Real.log_le_sub_one_of_pos hab0) ha0.le
  have hsecond := mul_le_mul_of_nonneg_left
    (Real.log_le_sub_one_of_pos hcab0) (sub_nonneg.mpr ha1.le)
  rw [bernoulliKL]
  calc
    a * Real.log (a / b) + (1 - a) * Real.log ((1 - a) / (1 - b)) ≤
        a * (a / b - 1) + (1 - a) * ((1 - a) / (1 - b) - 1) :=
      add_le_add hfirst hsecond
    _ = (a - b) ^ 2 / (b * (1 - b)) := by
      field_simp [ne_of_gt hb0, ne_of_gt (sub_pos.mpr hb1)]
      ring

/-- Flip one coordinate of a paired hypothesis. -/
def PairSign.flip : PairSign → PairSign
  | PairSign.neg => PairSign.pos
  | PairSign.pos => PairSign.neg

@[simp] theorem PairSign.value_flip (s : PairSign) :
    PairSign.value s.flip = -PairSign.value s := by
  cases s <;> norm_num [PairSign.flip, PairSign.value]

/-- The adjacent hypothesis `θ^(g)` of the manuscript. -/
def flipHypothesis {k : Nat} (θ : Fin k → PairSign) (g : Fin k) :
    Fin k → PairSign :=
  Function.update θ g (θ g).flip

@[simp] theorem flipHypothesis_same {k : Nat} (θ : Fin k → PairSign)
    (g : Fin k) : flipHypothesis θ g g = (θ g).flip := by
  simp [flipHypothesis]

theorem flipHypothesis_other {k : Nat} (θ : Fin k → PairSign)
    {g i : Fin k} (hi : i ≠ g) : flipHypothesis θ g i = θ i := by
  simp [flipHypothesis, hi]

/-- Flipping coordinate `g` changes the signed sum only in that coordinate. -/
theorem sum_value_flipHypothesis {n k : Nat} (hD : 2 * k ≤ n)
    (θ : Fin k → PairSign) (A : MSetAction n k) (g : Fin k) :
    (∑ i : Fin k, PairSign.value (flipHypothesis θ g i) * pairedZ hD A i) =
      (∑ i : Fin k, PairSign.value (θ i) * pairedZ hD A i) -
        2 * PairSign.value (θ g) * pairedZ hD A g := by
  classical
  calc
    (∑ i : Fin k, PairSign.value (flipHypothesis θ g i) * pairedZ hD A i) =
        ∑ i : Fin k,
          (PairSign.value (θ i) * pairedZ hD A i +
            if i = g then -2 * PairSign.value (θ g) * pairedZ hD A g else 0) := by
      apply Finset.sum_congr rfl
      intro i _
      by_cases hi : i = g
      · subst i
        simp [flipHypothesis]
        ring
      · simp [flipHypothesis_other θ hi, hi]
    _ = (∑ i : Fin k, PairSign.value (θ i) * pairedZ hD A i) -
        2 * PairSign.value (θ g) * pairedZ hD A g := by
      rw [Finset.sum_add_distrib]
      simp
      ring

/-- Exact change of the Bernoulli feedback parameter under one coordinate
flip.  Its absolute value is `ε/k` precisely when the pair is split, and is
zero otherwise. -/
theorem pairedBernoulliParameter_sub_flip {n k : Nat} (hk : 1 ≤ k)
    (hD : 2 * k ≤ n) (θ : Fin k → PairSign) (ε : Real)
    (A : MSetAction n k) (g : Fin k) :
    pairedBernoulliParameter hD θ ε A -
        pairedBernoulliParameter hD (flipHypothesis θ g) ε A =
      -(ε / (k : Real)) *
        (PairSign.value (θ g) * pairedZ hD A g) := by
  rw [lower_dense_bernoulli_parameter hk hD θ ε A,
    lower_dense_bernoulli_parameter hk hD (flipHypothesis θ g) ε A,
    sum_value_flipHypothesis hD θ A g]
  have hk0 : (k : Real) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt hk)
  field_simp
  ring

/-- Every atom of `p_θ` lies between `(1-ε)/(2k)` and
`(1+ε)/(2k)`. -/
theorem pairedProbability_mem_interval {k : Nat} (hk : 1 ≤ k)
    (θ : Fin k → PairSign) {ε : Real} (hε0 : 0 ≤ ε)
    (j : PairItem k) :
    pairedProbability θ ε j ∈
      Set.Icc ((1 - ε) / (2 * (k : Real)))
        ((1 + ε) / (2 * (k : Real))) := by
  have hkR : 0 < (k : Real) := by exact_mod_cast hk
  have hden : 0 < (2 : Real) * k := mul_pos (by norm_num) hkR
  rcases j with ⟨g, b⟩
  cases b <;> cases hθ : θ g <;>
    simp only [pairedProbability_left, pairedProbability_right, hθ,
      PairSign.value_neg, PairSign.value_pos] <;>
    constructor <;> apply (div_le_div_iff_of_pos_right hden).2 <;> nlinarith

/-- The feedback parameter is bounded by the number `h=|S|` of selected
paired coordinates, using the atomwise bounds above. -/
theorem pairedBernoulliParameter_between_card_multiples {n k : Nat}
    (hk : 1 ≤ k) (hD : 2 * k ≤ n) (θ : Fin k → PairSign)
    {ε : Real} (hε0 : 0 ≤ ε) (A : MSetAction n k) :
    ((1 - ε) / (2 * (k : Real))) * (pairedSectionCard hD A : Real) ≤
        pairedBernoulliParameter hD θ ε A ∧
      pairedBernoulliParameter hD θ ε A ≤
        ((1 + ε) / (2 * (k : Real))) * (pairedSectionCard hD A : Real) := by
  have hcard := pairedSectionCard_eq_indicator_sum hD A
  rw [pairedBernoulliParameter, hcard]
  constructor
  · rw [Finset.mul_sum]
    exact Finset.sum_le_sum fun j _ =>
      mul_le_mul_of_nonneg_right
        (pairedProbability_mem_interval hk θ hε0 j).1
        (pairedSelected_mem_Icc hD A j).1
  · rw [Finset.mul_sum]
    exact Finset.sum_le_sum fun j _ =>
      mul_le_mul_of_nonneg_right
        (pairedProbability_mem_interval hk θ hε0 j).2
        (pairedSelected_mem_Icc hD A j).1

/-- The two denominator estimates quoted immediately before
`eq:lower-dense-one-step-kl`, specialized to `D=2k`. -/
theorem pairedBernoulliParameter_denominator_bounds {n k : Nat}
    (hk : 1 ≤ k) (hD : 2 * k ≤ n) (θ : Fin k → PairSign)
    {ε : Real} (hε0 : 0 ≤ ε) (hε16 : ε ≤ (1 : Real) / 16)
    (A : MSetAction n k) :
    3 * (pairedSectionCard hD A : Real) / (8 * (k : Real)) ≤
        pairedBernoulliParameter hD θ ε A ∧
      (3 : Real) / 8 ≤ 1 - pairedBernoulliParameter hD θ ε A := by
  have hraw := pairedBernoulliParameter_between_card_multiples
    hk hD θ hε0 A
  have hkR : 0 < (k : Real) := by exact_mod_cast hk
  have hh_nat := pairedSectionCard_le hD A
  have hh0 : 0 ≤ (pairedSectionCard hD A : Real) := Nat.cast_nonneg _
  have hh_le : (pairedSectionCard hD A : Real) ≤ k := by exact_mod_cast hh_nat
  constructor
  · calc
      3 * (pairedSectionCard hD A : Real) / (8 * (k : Real)) ≤
          ((1 - ε) / (2 * (k : Real))) *
            (pairedSectionCard hD A : Real) := by
        have hcoef : (3 : Real) / (8 * k) ≤ (1 - ε) / (2 * k) := by
          have hk0 : (k : Real) ≠ 0 := ne_of_gt hkR
          field_simp [hk0]
          nlinarith
        calc
          3 * (pairedSectionCard hD A : Real) / (8 * (k : Real)) =
              ((3 : Real) / (8 * k)) * pairedSectionCard hD A := by ring
          _ ≤ ((1 - ε) / (2 * (k : Real))) *
              (pairedSectionCard hD A : Real) :=
            mul_le_mul_of_nonneg_right hcoef hh0
      _ ≤ pairedBernoulliParameter hD θ ε A := hraw.1
  · calc
      (3 : Real) / 8 ≤ 1 -
          ((1 + ε) / (2 * (k : Real))) *
            (pairedSectionCard hD A : Real) := by
        have hcoef : 0 ≤ (1 + ε) / (2 * (k : Real)) := by positivity
        have hmul := mul_le_mul_of_nonneg_left hh_le hcoef
        have hupper :
            ((1 + ε) / (2 * (k : Real))) *
                (pairedSectionCard hD A : Real) ≤ (1 + ε) / 2 := by
          calc
            ((1 + ε) / (2 * (k : Real))) *
                (pairedSectionCard hD A : Real) ≤
                ((1 + ε) / (2 * (k : Real))) * (k : Real) := hmul
            _ = (1 + ε) / 2 := by field_simp
        nlinarith
      _ ≤ 1 - pairedBernoulliParameter hD θ ε A := by linarith [hraw.2]

/-- A split pair contributes one unit to `z_g²`; an unsplit pair contributes
zero.  In either case it is bounded by the number of selected members. -/
theorem pairedZ_sq_le_selected_pair {n k : Nat} (hD : 2 * k ≤ n)
    (A : MSetAction n k) (g : Fin k) :
    pairedZ hD A g ^ 2 ≤
      pairedSelected hD A (g, false) + pairedSelected hD A (g, true) := by
  by_cases hl : pairCoordinate hD (g, false) ∈ A.1
  · by_cases hr : pairCoordinate hD (g, true) ∈ A.1
    · simp [pairedZ, pairedSelected, pairCoordinate_mem_pairedSection_iff, hl, hr]
    · simp [pairedZ, pairedSelected, pairCoordinate_mem_pairedSection_iff, hl, hr]
  · by_cases hr : pairCoordinate hD (g, true) ∈ A.1
    · simp [pairedZ, pairedSelected, pairCoordinate_mem_pairedSection_iff, hl, hr]
    · simp [pairedZ, pairedSelected, pairCoordinate_mem_pairedSection_iff, hl, hr]

/-- Hence the number of split pairs is at most `h=|S|`, in the exact
weighted form used by the KL summation. -/
theorem sum_pairedZ_sq_le_sectionCard {n k : Nat} (hD : 2 * k ≤ n)
    (A : MSetAction n k) :
    (∑ g : Fin k, pairedZ hD A g ^ 2) ≤ (pairedSectionCard hD A : Real) := by
  rw [pairedSectionCard_eq_indicator_sum hD A, Fintype.sum_prod_type]
  simp_rw [Fintype.sum_bool]
  exact Finset.sum_le_sum fun g _ => by
    simpa [add_comm] using pairedZ_sq_le_selected_pair hD A g

/-- Squared parameter displacement, including the exact split-pair factor
`z_g(S)²`. -/
theorem pairedBernoulliParameter_sub_flip_sq {n k : Nat} (hk : 1 ≤ k)
    (hD : 2 * k ≤ n) (θ : Fin k → PairSign) (ε : Real)
    (A : MSetAction n k) (g : Fin k) :
    (pairedBernoulliParameter hD θ ε A -
        pairedBernoulliParameter hD (flipHypothesis θ g) ε A) ^ 2 =
      ε ^ 2 / (k : Real) ^ 2 * pairedZ hD A g ^ 2 := by
  rw [pairedBernoulliParameter_sub_flip hk hD θ ε A g]
  rw [mul_pow, mul_pow, PairSign.value_sq]
  ring

/-- If `S` contains no paired coordinate, its Bernoulli feedback parameter
is zero under every hypothesis. -/
theorem pairedBernoulliParameter_eq_zero_of_card_eq_zero {n k : Nat}
    (hk : 1 ≤ k) (hD : 2 * k ≤ n) (θ : Fin k → PairSign)
    {ε : Real} (hε0 : 0 ≤ ε) (hε1 : ε ≤ 1) (A : MSetAction n k)
    (hh : pairedSectionCard hD A = 0) :
    pairedBernoulliParameter hD θ ε A = 0 := by
  have hraw := pairedBernoulliParameter_between_card_multiples
    hk hD θ hε0 A
  have hnonneg := (pairedBernoulliParameter_mem_Icc
    hk hD θ hε0 hε1 A).1
  rw [hh, Nat.cast_zero, mul_zero] at hraw
  exact le_antisymm (by simpa using hraw.2) hnonneg

/-- Per-coordinate information estimate.  The factor `z_g(S)²` is exactly
the split-pair indicator: no information is charged when pair `g` is not
split by the chosen action. -/
theorem bernoulliKL_parameter_flip_le_split {n k : Nat} (hk : 1 ≤ k)
    (hD : 2 * k ≤ n) (θ : Fin k → PairSign) {ε : Real}
    (hε0 : 0 ≤ ε) (hε16 : ε ≤ (1 : Real) / 16)
    (A : MSetAction n k) (hh : 0 < pairedSectionCard hD A) (g : Fin k) :
    bernoulliKL (pairedBernoulliParameter hD θ ε A)
        (pairedBernoulliParameter hD (flipHypothesis θ g) ε A) ≤
      (64 * ε ^ 2) /
          (9 * (pairedSectionCard hD A : Real) * (k : Real)) *
        pairedZ hD A g ^ 2 := by
  let a := pairedBernoulliParameter hD θ ε A
  let b := pairedBernoulliParameter hD (flipHypothesis θ g) ε A
  have ha_bounds := pairedBernoulliParameter_denominator_bounds
    hk hD θ hε0 hε16 A
  have hb_bounds := pairedBernoulliParameter_denominator_bounds
    hk hD (flipHypothesis θ g) hε0 hε16 A
  have hkR : 0 < (k : Real) := by exact_mod_cast hk
  have hhR : 0 < (pairedSectionCard hD A : Real) := by exact_mod_cast hh
  have ha0 : 0 < a := by
    dsimp [a]
    have hlower : 0 < 3 * (pairedSectionCard hD A : Real) /
        (8 * (k : Real)) := by positivity
    exact hlower.trans_le ha_bounds.1
  have hb0 : 0 < b := by
    dsimp [b]
    have hlower : 0 < 3 * (pairedSectionCard hD A : Real) /
        (8 * (k : Real)) := by positivity
    exact hlower.trans_le hb_bounds.1
  have ha1 : a < 1 := by
    dsimp [a]
    linarith [ha_bounds.2]
  have hb1 : b < 1 := by
    dsimp [b]
    linarith [hb_bounds.2]
  have hden_lower :
      9 * (pairedSectionCard hD A : Real) / (64 * (k : Real)) ≤
        b * (1 - b) := by
    have hmul := mul_le_mul hb_bounds.1 hb_bounds.2
      (by norm_num : (0 : Real) ≤ 3 / 8) hb0.le
    dsimp [b] at hmul ⊢
    calc
      9 * (pairedSectionCard hD A : Real) / (64 * (k : Real)) =
          (3 * (pairedSectionCard hD A : Real) / (8 * (k : Real))) *
            (3 / 8 : Real) := by field_simp; ring
      _ ≤ pairedBernoulliParameter hD (flipHypothesis θ g) ε A *
          (1 - pairedBernoulliParameter hD (flipHypothesis θ g) ε A) := hmul
  have hden_pos :
      0 < 9 * (pairedSectionCard hD A : Real) / (64 * (k : Real)) := by
    positivity
  calc
    bernoulliKL a b ≤ (a - b) ^ 2 / (b * (1 - b)) :=
      bernoulliKL_le_chiSquare ha0 ha1 hb0 hb1
    _ ≤ (a - b) ^ 2 /
        (9 * (pairedSectionCard hD A : Real) / (64 * (k : Real))) :=
      div_le_div_of_nonneg_left (sq_nonneg _) hden_pos hden_lower
    _ = (64 * ε ^ 2) /
          (9 * (pairedSectionCard hD A : Real) * (k : Real)) *
        pairedZ hD A g ^ 2 := by
      dsimp [a, b]
      rw [pairedBernoulliParameter_sub_flip_sq hk hD θ ε A g]
      have hk0 : (k : Real) ≠ 0 := ne_of_gt hkR
      have hh0 : (pairedSectionCard hD A : Real) ≠ 0 := ne_of_gt hhR
      field_simp [hk0, hh0]

/-- Equation `eq:lower-dense-one-step-kl`, with `D=2k`.  The proof follows
the manuscript literally: one binary divergence per adjacent hypothesis,
each split pair costs at most `128 ε²/(9hD)`, and the number of split pairs
is at most `h`. -/
theorem lower_dense_one_step_kl {n k : Nat} (hk : 1 ≤ k)
    (hD : 2 * k ≤ n) (θ : Fin k → PairSign) {ε : Real}
    (hε0 : 0 ≤ ε) (hε16 : ε ≤ (1 : Real) / 16)
    (A : MSetAction n k) :
    (∑ g : Fin k,
      bernoulliKL (pairedBernoulliParameter hD θ ε A)
        (pairedBernoulliParameter hD (flipHypothesis θ g) ε A)) ≤
      16 * ε ^ 2 / (2 * (k : Real)) := by
  have hε1 : ε ≤ 1 := hε16.trans (by norm_num)
  by_cases hh0 : pairedSectionCard hD A = 0
  · have ha := pairedBernoulliParameter_eq_zero_of_card_eq_zero
      hk hD θ hε0 hε1 A hh0
    have hb (g : Fin k) := pairedBernoulliParameter_eq_zero_of_card_eq_zero
      hk hD (flipHypothesis θ g) hε0 hε1 A hh0
    simp_rw [ha]
    simp_rw [hb]
    simp [bernoulliKL]
    positivity
  · have hh : 0 < pairedSectionCard hD A := Nat.pos_of_ne_zero hh0
    have hkR : 0 < (k : Real) := by exact_mod_cast hk
    have hhR : 0 < (pairedSectionCard hD A : Real) := by exact_mod_cast hh
    have hcoefficient :
        0 ≤ (64 * ε ^ 2) /
          (9 * (pairedSectionCard hD A : Real) * (k : Real)) := by positivity
    calc
      (∑ g : Fin k,
          bernoulliKL (pairedBernoulliParameter hD θ ε A)
            (pairedBernoulliParameter hD (flipHypothesis θ g) ε A)) ≤
          ∑ g : Fin k,
            (64 * ε ^ 2) /
                (9 * (pairedSectionCard hD A : Real) * (k : Real)) *
              pairedZ hD A g ^ 2 :=
        Finset.sum_le_sum fun g _ =>
          bernoulliKL_parameter_flip_le_split
            hk hD θ hε0 hε16 A hh g
      _ = (64 * ε ^ 2) /
            (9 * (pairedSectionCard hD A : Real) * (k : Real)) *
          ∑ g : Fin k, pairedZ hD A g ^ 2 := by rw [Finset.mul_sum]
      _ ≤ (64 * ε ^ 2) /
            (9 * (pairedSectionCard hD A : Real) * (k : Real)) *
          (pairedSectionCard hD A : Real) :=
        mul_le_mul_of_nonneg_left (sum_pairedZ_sq_le_sectionCard hD A)
          hcoefficient
      _ = 64 * ε ^ 2 / (9 * (k : Real)) := by
        have hhne : (pairedSectionCard hD A : Real) ≠ 0 := ne_of_gt hhR
        field_simp [hhne]
      _ ≤ 16 * ε ^ 2 / (2 * (k : Real)) := by
        have hk0 : (k : Real) ≠ 0 := ne_of_gt hkR
        have hsq : 0 ≤ ε ^ 2 := sq_nonneg ε
        field_simp [hk0]
        nlinarith

/-- The same one-step bound stated explicitly as KL divergence between the
two finite Bernoulli laws. -/
theorem lower_dense_one_step_finite_law_kl {n k : Nat} (hk : 1 ≤ k)
    (hD : 2 * k ≤ n) (θ : Fin k → PairSign) {ε : Real}
    (hε0 : 0 ≤ ε) (hε16 : ε ≤ (1 : Real) / 16)
    (A : MSetAction n k) :
    (∑ g : Fin k,
      finiteLawKL
        (bernoulliMass (pairedBernoulliParameter hD θ ε A))
        (bernoulliMass
          (pairedBernoulliParameter hD (flipHypothesis θ g) ε A))) ≤
      16 * ε ^ 2 / (2 * (k : Real)) := by
  simpa only [finiteLawKL_bernoulliMass] using
    lower_dense_one_step_kl hk hD θ hε0 hε16 A

/-- `eq:lower-dense-one-step-kl` stated with Mathlib's measure-theoretic
`klDiv` between the genuine Bernoulli measures. -/
theorem lower_dense_one_step_measure_kl {n k : Nat} (hk : 1 ≤ k)
    (hD : 2 * k ≤ n) (θ : Fin k → PairSign) {ε : Real}
    (hε0 : 0 ≤ ε) (hε16 : ε ≤ (1 : Real) / 16)
    (A : MSetAction n k) :
    (∑ g : Fin k,
      (klDiv
        (bernoulliLaw (pairedBernoulliParameter hD θ ε A))
        (bernoulliLaw
          (pairedBernoulliParameter hD (flipHypothesis θ g) ε A))).toReal) ≤
      16 * ε ^ 2 / (2 * (k : Real)) := by
  have hε1 : ε ≤ 1 := hε16.trans (by norm_num)
  by_cases hh0 : pairedSectionCard hD A = 0
  · have ha := pairedBernoulliParameter_eq_zero_of_card_eq_zero
      hk hD θ hε0 hε1 A hh0
    have hb (g : Fin k) := pairedBernoulliParameter_eq_zero_of_card_eq_zero
      hk hD (flipHypothesis θ g) hε0 hε1 A hh0
    letI : SigmaFinite (bernoulliLaw 0) := by
      rw [bernoulliLaw]
      exact SigmaFinite.withDensity_of_ne_top'
        (fun x => bernoulliDensity_ne_top 0 x)
    simp_rw [ha]
    simp_rw [hb]
    simp [klDiv_self]
    positivity
  · have hh : 0 < pairedSectionCard hD A := Nat.pos_of_ne_zero hh0
    have hhR : 0 < (pairedSectionCard hD A : Real) := by exact_mod_cast hh
    have hkR : 0 < (k : Real) := by exact_mod_cast hk
    have ha_bounds := pairedBernoulliParameter_denominator_bounds
      hk hD θ hε0 hε16 A
    have ha0 : 0 < pairedBernoulliParameter hD θ ε A := by
      have : 0 < 3 * (pairedSectionCard hD A : Real) /
          (8 * (k : Real)) := by positivity
      exact this.trans_le ha_bounds.1
    have ha1 : pairedBernoulliParameter hD θ ε A < 1 := by
      linarith [ha_bounds.2]
    calc
      (∑ g : Fin k,
        (klDiv
          (bernoulliLaw (pairedBernoulliParameter hD θ ε A))
          (bernoulliLaw
            (pairedBernoulliParameter hD (flipHypothesis θ g) ε A))).toReal) =
          ∑ g : Fin k,
            bernoulliKL (pairedBernoulliParameter hD θ ε A)
              (pairedBernoulliParameter hD (flipHypothesis θ g) ε A) := by
        apply Finset.sum_congr rfl
        intro g _
        have hb_bounds := pairedBernoulliParameter_denominator_bounds
          hk hD (flipHypothesis θ g) hε0 hε16 A
        have hb0 :
            0 < pairedBernoulliParameter hD (flipHypothesis θ g) ε A := by
          have : 0 < 3 * (pairedSectionCard hD A : Real) /
              (8 * (k : Real)) := by positivity
          exact this.trans_le hb_bounds.1
        have hb1 :
            pairedBernoulliParameter hD (flipHypothesis θ g) ε A < 1 := by
          linarith [hb_bounds.2]
        exact toReal_klDiv_bernoulliLaw_eq ha0 ha1 hb0 hb1
      _ ≤ 16 * ε ^ 2 / (2 * (k : Real)) :=
        lower_dense_one_step_kl hk hD θ hε0 hε16 A

/-- ENNReal-valued form of `eq:lower-dense-one-step-kl`, ready for direct
use inside Mathlib's sequential KL chain rule. -/
theorem lower_dense_one_step_measure_kl_ennreal {n k : Nat} (hk : 1 ≤ k)
    (hD : 2 * k ≤ n) (θ : Fin k → PairSign) {ε : Real}
    (hε0 : 0 ≤ ε) (hε16 : ε ≤ (1 : Real) / 16)
    (A : MSetAction n k) :
    (∑ g : Fin k,
      klDiv
        (bernoulliLaw (pairedBernoulliParameter hD θ ε A))
        (bernoulliLaw
          (pairedBernoulliParameter hD (flipHypothesis θ g) ε A))) ≤
      ENNReal.ofReal (16 * ε ^ 2 / (2 * (k : Real))) := by
  have hε1 : ε ≤ 1 := hε16.trans (by norm_num)
  by_cases hh0 : pairedSectionCard hD A = 0
  · have ha := pairedBernoulliParameter_eq_zero_of_card_eq_zero
      hk hD θ hε0 hε1 A hh0
    have hb (g : Fin k) := pairedBernoulliParameter_eq_zero_of_card_eq_zero
      hk hD (flipHypothesis θ g) hε0 hε1 A hh0
    letI : SigmaFinite (bernoulliLaw 0) := by
      rw [bernoulliLaw]
      exact SigmaFinite.withDensity_of_ne_top'
        (fun x => bernoulliDensity_ne_top 0 x)
    simp_rw [ha]
    simp_rw [hb]
    simp [klDiv_self]
  · have hh : 0 < pairedSectionCard hD A := Nat.pos_of_ne_zero hh0
    have hhR : 0 < (pairedSectionCard hD A : Real) := by exact_mod_cast hh
    have hkR : 0 < (k : Real) := by exact_mod_cast hk
    have ha_bounds := pairedBernoulliParameter_denominator_bounds
      hk hD θ hε0 hε16 A
    have ha0 : 0 < pairedBernoulliParameter hD θ ε A := by
      have : 0 < 3 * (pairedSectionCard hD A : Real) /
          (8 * (k : Real)) := by positivity
      exact this.trans_le ha_bounds.1
    have ha1 : pairedBernoulliParameter hD θ ε A < 1 := by
      linarith [ha_bounds.2]
    have hb0 (g : Fin k) :
        0 < pairedBernoulliParameter hD (flipHypothesis θ g) ε A := by
      have hb_bounds := pairedBernoulliParameter_denominator_bounds
        hk hD (flipHypothesis θ g) hε0 hε16 A
      have : 0 < 3 * (pairedSectionCard hD A : Real) /
          (8 * (k : Real)) := by positivity
      exact this.trans_le hb_bounds.1
    have hb1 (g : Fin k) :
        pairedBernoulliParameter hD (flipHypothesis θ g) ε A < 1 := by
      have hb_bounds := pairedBernoulliParameter_denominator_bounds
        hk hD (flipHypothesis θ g) hε0 hε16 A
      linarith [hb_bounds.2]
    have hkl0 (g : Fin k) :
        0 ≤ bernoulliKL (pairedBernoulliParameter hD θ ε A)
          (pairedBernoulliParameter hD (flipHypothesis θ g) ε A) := by
      rw [← toReal_klDiv_bernoulliLaw_eq ha0 ha1 (hb0 g) (hb1 g)]
      exact ENNReal.toReal_nonneg
    calc
      (∑ g : Fin k,
        klDiv
          (bernoulliLaw (pairedBernoulliParameter hD θ ε A))
          (bernoulliLaw
            (pairedBernoulliParameter hD (flipHypothesis θ g) ε A))) =
          ∑ g : Fin k,
            ENNReal.ofReal
              (bernoulliKL (pairedBernoulliParameter hD θ ε A)
                (pairedBernoulliParameter hD (flipHypothesis θ g) ε A)) := by
        apply Finset.sum_congr rfl
        intro g _
        exact klDiv_bernoulliLaw_eq_ofReal ha0 ha1 (hb0 g) (hb1 g)
      _ = ENNReal.ofReal
          (∑ g : Fin k,
            bernoulliKL (pairedBernoulliParameter hD θ ε A)
              (pairedBernoulliParameter hD (flipHypothesis θ g) ε A)) := by
        symm
        exact ENNReal.ofReal_sum_of_nonneg fun g _ => hkl0 g
      _ ≤ ENNReal.ofReal (16 * ε ^ 2 / (2 * (k : Real))) :=
        ENNReal.ofReal_le_ofReal
          (lower_dense_one_step_kl hk hD θ hε0 hε16 A)

/-- Pointwise accumulation of the conditional Bernoulli information over
`T` rounds.  The action may be arbitrary at every round, so this is exactly
the uniform local budget that the sequential KL chain rule consumes after
conditioning on a past history. -/
theorem paired_conditional_kl_sum {n k T : Nat} (hk : 1 ≤ k)
    (hD : 2 * k ≤ n) (θ : Fin k → PairSign) {ε : Real}
    (hε0 : 0 ≤ ε) (hε16 : ε ≤ (1 : Real) / 16)
    (A : Fin T → MSetAction n k) :
    (∑ t : Fin T, ∑ g : Fin k,
      finiteLawKL
        (bernoulliMass (pairedBernoulliParameter hD θ ε (A t)))
        (bernoulliMass
          (pairedBernoulliParameter hD (flipHypothesis θ g) ε (A t)))) ≤
      16 * ε ^ 2 * (T : Real) / (2 * (k : Real)) := by
  calc
    (∑ t : Fin T, ∑ g : Fin k,
        finiteLawKL
          (bernoulliMass (pairedBernoulliParameter hD θ ε (A t)))
          (bernoulliMass
            (pairedBernoulliParameter hD (flipHypothesis θ g) ε (A t)))) ≤
        ∑ _t : Fin T, 16 * ε ^ 2 / (2 * (k : Real)) :=
      Finset.sum_le_sum fun t _ =>
        lower_dense_one_step_finite_law_kl hk hD θ hε0 hε16 (A t)
    _ = 16 * ε ^ 2 * (T : Real) / (2 * (k : Real)) := by
      simp
      ring

/-- The preceding accumulated budget with the manuscript's order of
summation: adjacent coordinates outside, rounds inside. -/
theorem paired_sequential_kl_budget {n k T : Nat} (hk : 1 ≤ k)
    (hD : 2 * k ≤ n) (θ : Fin k → PairSign) {ε : Real}
    (hε0 : 0 ≤ ε) (hε16 : ε ≤ (1 : Real) / 16)
    (A : Fin T → MSetAction n k) :
    (∑ g : Fin k, ∑ t : Fin T,
      finiteLawKL
        (bernoulliMass (pairedBernoulliParameter hD θ ε (A t)))
        (bernoulliMass
          (pairedBernoulliParameter hD (flipHypothesis θ g) ε (A t)))) ≤
      16 * ε ^ 2 * (T : Real) / (2 * (k : Real)) := by
  rw [Finset.sum_comm]
  exact paired_conditional_kl_sum hk hD θ hε0 hε16 A

/-- T-round conditional budget with every summand expressed as Mathlib's
measure-theoretic KL.  This is the numeric right-hand side of
`eq:paired-sequential-kl`; composing it with the protocol chain rule only
requires identifying each conditional observation kernel with the displayed
Bernoulli law. -/
theorem paired_sequential_measure_kl_budget {n k T : Nat} (hk : 1 ≤ k)
    (hD : 2 * k ≤ n) (θ : Fin k → PairSign) {ε : Real}
    (hε0 : 0 ≤ ε) (hε16 : ε ≤ (1 : Real) / 16)
    (A : Fin T → MSetAction n k) :
    (∑ g : Fin k, ∑ t : Fin T,
      (klDiv
        (bernoulliLaw (pairedBernoulliParameter hD θ ε (A t)))
        (bernoulliLaw
          (pairedBernoulliParameter hD (flipHypothesis θ g) ε (A t)))).toReal) ≤
      16 * ε ^ 2 * (T : Real) / (2 * (k : Real)) := by
  rw [Finset.sum_comm]
  calc
    (∑ t : Fin T, ∑ g : Fin k,
      (klDiv
        (bernoulliLaw (pairedBernoulliParameter hD θ ε (A t)))
        (bernoulliLaw
          (pairedBernoulliParameter hD (flipHypothesis θ g) ε (A t)))).toReal) ≤
        ∑ _t : Fin T, 16 * ε ^ 2 / (2 * (k : Real)) :=
      Finset.sum_le_sum fun t _ =>
        lower_dense_one_step_measure_kl hk hD θ hε0 hε16 (A t)
    _ = 16 * ε ^ 2 * (T : Real) / (2 * (k : Real)) := by
      simp
      ring

/-- ENNReal accumulation of the same conditional budget, in precisely the
codomain used by `runLaw_klDiv_le_sum`. -/
theorem paired_sequential_measure_kl_budget_ennreal {n k T : Nat}
    (hk : 1 ≤ k) (hD : 2 * k ≤ n) (θ : Fin k → PairSign) {ε : Real}
    (hε0 : 0 ≤ ε) (hε16 : ε ≤ (1 : Real) / 16)
    (A : Fin T → MSetAction n k) :
    (∑ g : Fin k, ∑ t : Fin T,
      klDiv
        (bernoulliLaw (pairedBernoulliParameter hD θ ε (A t)))
        (bernoulliLaw
          (pairedBernoulliParameter hD (flipHypothesis θ g) ε (A t)))) ≤
      T * ENNReal.ofReal (16 * ε ^ 2 / (2 * (k : Real))) := by
  rw [Finset.sum_comm]
  calc
    (∑ t : Fin T, ∑ g : Fin k,
      klDiv
        (bernoulliLaw (pairedBernoulliParameter hD θ ε (A t)))
        (bernoulliLaw
          (pairedBernoulliParameter hD (flipHypothesis θ g) ε (A t)))) ≤
        ∑ _t : Fin T,
          ENNReal.ofReal (16 * ε ^ 2 / (2 * (k : Real))) :=
      Finset.sum_le_sum fun t _ =>
        lower_dense_one_step_measure_kl_ennreal
          hk hD θ hε0 hε16 (A t)
    _ = T * ENNReal.ofReal (16 * ε ^ 2 / (2 * (k : Real))) := by simp

#print axioms bernoulliKL_le_chiSquare
#print axioms pairedBernoulliParameter_sub_flip
#print axioms pairedBernoulliParameter_denominator_bounds
#print axioms sum_pairedZ_sq_le_sectionCard
#print axioms lower_dense_one_step_kl
#print axioms lower_dense_one_step_finite_law_kl
#print axioms toReal_klDiv_bernoulliLaw_eq
#print axioms klDiv_bernoulliLaw_eq_ofReal
#print axioms lower_dense_one_step_measure_kl
#print axioms lower_dense_one_step_measure_kl_ennreal
#print axioms paired_sequential_kl_budget
#print axioms paired_sequential_measure_kl_budget
#print axioms paired_sequential_measure_kl_budget_ennreal

end

end MsetsLower.Lower.Dense
