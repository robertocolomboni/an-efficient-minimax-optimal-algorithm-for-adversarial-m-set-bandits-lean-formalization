import CoefficientOne.Sampling.FiniteLawMeasure
import EffectiveResistance.FiniteProbability

/-! # Regression and total variance after revealing one bit

The conditional laws are constructed from the actual finite masses on the two
fibres. Their expectations, rather than assumed conditional-mean identities,
are used throughout.
-/

open scoped BigOperators
open EffectiveResistance Matrix

namespace CoefficientOne.Sampling
noncomputable section

variable {α : Type*} [Fintype α]

def lawVariance (p : FiniteLaw α) (Y : α → ℝ) : ℝ :=
  lawExpectation p (fun a => (Y a - lawExpectation p Y) ^ 2)

def binaryMass (p : FiniteLaw α) (X : α → Bool) (b : Bool) : ℝ :=
  lawExpectation p (fun a => if X a = b then 1 else 0)

def binaryNumerator (p : FiniteLaw α) (X : α → Bool) (Y : α → ℝ) (b : Bool) : ℝ :=
  lawExpectation p (fun a => if X a = b then Y a else 0)

theorem binaryMass_nonneg (p : FiniteLaw α) (X : α → Bool) (b : Bool) :
    0 ≤ binaryMass p X b := by
  apply Finset.sum_nonneg
  intro a _
  exact mul_nonneg (law_nonneg p a) (by dsimp; split_ifs <;> norm_num)

def binaryConditionalLaw (p : FiniteLaw α) (X : α → Bool) (b : Bool)
    (hb : 0 < binaryMass p X b) : FiniteLaw α :=
  ⟨fun a => if X a = b then p.val a / binaryMass p X b else 0, by
    constructor
    · intro a
      dsimp
      split_ifs
      · exact div_nonneg (law_nonneg p a) hb.le
      · exact le_rfl
    · have hnum : (∑ a, if X a = b then p.val a else 0) = binaryMass p X b := by
        simp [binaryMass, lawExpectation, mul_ite]
      have heq : (∑ a, if X a = b then p.val a / binaryMass p X b else 0) =
          (∑ a, if X a = b then p.val a else 0) / binaryMass p X b := by
        rw [Finset.sum_div]
        apply Finset.sum_congr rfl
        intro a _
        split_ifs <;> simp
      rw [heq, hnum, div_self hb.ne']⟩

theorem binaryConditionalLaw_expectation (p : FiniteLaw α) (X : α → Bool)
    (Y : α → ℝ) (b : Bool) (hb : 0 < binaryMass p X b) :
    lawExpectation (binaryConditionalLaw p X b hb) Y =
      binaryNumerator p X Y b / binaryMass p X b := by
  unfold binaryNumerator
  simp only [lawExpectation, binaryConditionalLaw, Subtype.coe_mk]
  rw [Finset.sum_div]
  apply Finset.sum_congr rfl
  intro a _
  split_ifs <;> ring

theorem binaryNumerator_add (p : FiniteLaw α) (X : α → Bool) (Y : α → ℝ) :
    binaryNumerator p X Y false + binaryNumerator p X Y true = lawExpectation p Y := by
  unfold binaryNumerator lawExpectation
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro a _
  cases hX : X a <;> simp [hX]

theorem binaryMass_add (p : FiniteLaw α) (X : α → Bool) :
    binaryMass p X false + binaryMass p X true = 1 := by
  have h := binaryNumerator_add p X (fun _ => 1)
  simpa only [binaryNumerator, binaryMass, lawExpectation_const] using h

def binaryConditionalMean (p : FiniteLaw α) (X : α → Bool) (Y : α → ℝ) (a : α) : ℝ :=
  binaryNumerator p X Y (X a) / binaryMass p X (X a)

/-- The finite conditional-mean identity on each fibre. -/
theorem binaryConditionalMean_fibre (p : FiniteLaw α) (X : α → Bool) (Y : α → ℝ)
    (hb : ∀ b, 0 < binaryMass p X b) (b : Bool) :
    binaryNumerator p X (binaryConditionalMean p X Y) b = binaryNumerator p X Y b := by
  unfold binaryNumerator lawExpectation
  have heq : (∑ a, p.val a * (if X a = b then binaryConditionalMean p X Y a else 0)) =
      (∑ a, p.val a * (if X a = b then 1 else 0)) *
        (binaryNumerator p X Y b / binaryMass p X b) := by
    rw [Finset.sum_mul]
    apply Finset.sum_congr rfl
    intro a _
    by_cases hx : X a = b
    · simp [hx, binaryConditionalMean]
    · simp [hx]
  rw [heq]
  change binaryMass p X b * (binaryNumerator p X Y b / binaryMass p X b) =
    binaryNumerator p X Y b
  field_simp [(hb b).ne']

theorem lawVariance_expansion (p : FiniteLaw α) (Y : α → ℝ) :
    lawVariance p Y = lawExpectation p (fun a => (Y a) ^ 2) - (lawExpectation p Y) ^ 2 := by
  exact finiteVariance_expansion (law_sum p) Y

theorem binaryConditionalMean_expectation (p : FiniteLaw α) (X : α → Bool) (Y : α → ℝ)
    (hb : ∀ b, 0 < binaryMass p X b) :
    lawExpectation p (binaryConditionalMean p X Y) = lawExpectation p Y := by
  rw [← binaryNumerator_add p X (binaryConditionalMean p X Y),
    binaryConditionalMean_fibre p X Y hb false, binaryConditionalMean_fibre p X Y hb true,
    binaryNumerator_add]

theorem binaryExpectation_function (p : FiniteLaw α) (X : α → Bool) (f : Bool → ℝ) :
    lawExpectation p (fun a => f (X a)) =
      binaryMass p X false * f false + binaryMass p X true * f true := by
  unfold lawExpectation binaryMass
  simp only [lawExpectation, Finset.sum_mul, ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro a _
  cases X a <;> simp

/-- Total variance for the actual pair of conditional laws. -/
theorem binary_total_variance (p : FiniteLaw α) (X : α → Bool) (Y : α → ℝ)
    (hb : ∀ b, 0 < binaryMass p X b) :
    lawVariance p Y =
      binaryMass p X false * lawVariance (binaryConditionalLaw p X false (hb false)) Y +
      binaryMass p X true * lawVariance (binaryConditionalLaw p X true (hb true)) Y +
      lawVariance p (binaryConditionalMean p X Y) := by
  simp only [lawVariance_expansion, binaryConditionalLaw_expectation,
    binaryConditionalMean_expectation p X Y hb]
  have hs : lawExpectation p (fun a => (binaryConditionalMean p X Y a) ^ 2) =
      binaryMass p X false * (binaryNumerator p X Y false / binaryMass p X false) ^ 2 +
      binaryMass p X true * (binaryNumerator p X Y true / binaryMass p X true) ^ 2 :=
    binaryExpectation_function p X (fun b => (binaryNumerator p X Y b / binaryMass p X b) ^ 2)
  rw [hs, ← binaryNumerator_add p X (fun a => (Y a) ^ 2)]
  field_simp [(hb false).ne', (hb true).ne']
  <;> ring

def binaryValue (X : α → Bool) (a : α) : ℝ := if X a then 1 else 0

theorem binaryValue_expectation (p : FiniteLaw α) (X : α → Bool) :
    lawExpectation p (binaryValue X) = binaryMass p X true := by
  rfl

def binaryCovariance (p : FiniteLaw α) (X : α → Bool) (Y : α → ℝ) : ℝ :=
  lawExpectation p (fun a => (Y a - lawExpectation p Y) *
    (binaryValue X a - binaryMass p X true))

theorem binaryCovariance_expansion (p : FiniteLaw α) (X : α → Bool) (Y : α → ℝ) :
    binaryCovariance p X Y = binaryNumerator p X Y true -
      lawExpectation p Y * binaryMass p X true := by
  have he := finiteCovariance_expansion (law_sum p) Y (binaryValue X)
  change binaryCovariance p X Y = _
  have hv : finiteExpectation p.val (binaryValue X) = binaryMass p X true :=
    binaryValue_expectation p X
  have hp : finiteExpectation p.val (fun a => Y a * binaryValue X a) =
      binaryNumerator p X Y true := by
    unfold finiteExpectation binaryNumerator lawExpectation
    apply Finset.sum_congr rfl
    intro a _
    cases X a <;> simp [binaryValue]
  rw [hv, hp] at he
  exact he

theorem binaryVariance (p : FiniteLaw α) (X : α → Bool) :
    lawVariance p (binaryValue X) = binaryMass p X true * (1 - binaryMass p X true) := by
  rw [lawVariance_expansion, binaryValue_expectation]
  have hs : (fun a => (binaryValue X a) ^ 2) = binaryValue X := by
    ext a
    cases X a <;> simp [binaryValue]
  rw [hs, binaryValue_expectation]
  ring

/-- Binary regression, pointwise as the explicitly constructed conditional mean. -/
theorem binary_regression (p : FiniteLaw α) (X : α → Bool) (Y : α → ℝ)
    (hb : ∀ b, 0 < binaryMass p X b) (a : α) :
    binaryConditionalMean p X Y a = lawExpectation p Y +
      binaryCovariance p X Y / lawVariance p (binaryValue X) *
        (binaryValue X a - lawExpectation p (binaryValue X)) := by
  have hsum := binaryMass_add p X
  have hnum := binaryNumerator_add p X Y
  have hq : 1 - binaryMass p X true ≠ 0 := by linarith [hb false]
  rw [binaryCovariance_expansion, binaryVariance, binaryValue_expectation]
  unfold binaryConditionalMean binaryValue
  cases hxa : X a
  · simp only [Bool.false_eq_true, ↓reduceIte]
    have h0 : binaryMass p X false = 1 - binaryMass p X true := by linarith
    have hn0 : binaryNumerator p X Y false = lawExpectation p Y - binaryNumerator p X Y true := by
      linarith
    rw [h0, hn0]
    field_simp [(hb true).ne', hq]
    <;> ring
  · simp only [↓reduceIte]
    field_simp [(hb true).ne', hq]
    <;> ring

theorem lawExpectation_affine (p : FiniteLaw α) (Y : α → ℝ) (a b : ℝ) :
    lawExpectation p (fun x => a + b * Y x) = a + b * lawExpectation p Y := by
  unfold lawExpectation
  simp_rw [mul_add, Finset.sum_add_distrib]
  rw [← Finset.sum_mul, law_sum, one_mul, Finset.mul_sum]
  congr 1
  apply Finset.sum_congr rfl
  intro x _
  ring

theorem lawVariance_affine (p : FiniteLaw α) (Y : α → ℝ) (a b : ℝ) :
    lawVariance p (fun x => a + b * Y x) = b ^ 2 * lawVariance p Y := by
  unfold lawVariance
  rw [lawExpectation_affine]
  unfold lawExpectation
  conv_rhs => rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro x _
  ring

theorem binaryVariance_pos (p : FiniteLaw α) (X : α → Bool)
    (hb : ∀ b, 0 < binaryMass p X b) : 0 < lawVariance p (binaryValue X) := by
  rw [binaryVariance]
  apply mul_pos (hb true)
  linarith [binaryMass_add p X, hb false]

theorem binaryConditionalMean_variance (p : FiniteLaw α) (X : α → Bool) (Y : α → ℝ)
    (hb : ∀ b, 0 < binaryMass p X b) :
    lawVariance p (binaryConditionalMean p X Y) =
      (binaryCovariance p X Y) ^ 2 / lawVariance p (binaryValue X) := by
  have heq : binaryConditionalMean p X Y = fun a =>
      (lawExpectation p Y - binaryCovariance p X Y / lawVariance p (binaryValue X) *
        lawExpectation p (binaryValue X)) +
      (binaryCovariance p X Y / lawVariance p (binaryValue X)) * binaryValue X a := by
    ext a
    rw [binary_regression p X Y hb a]
    ring
  rw [heq, lawVariance_affine]
  field_simp [(binaryVariance_pos p X hb).ne']

/-- Exact variance drop after revealing the bit, with both conditional laws
constructed from p, rather than supplied as arbitrary measures. -/
theorem binary_variance_drop (p : FiniteLaw α) (X : α → Bool) (Y : α → ℝ)
    (hb : ∀ b, 0 < binaryMass p X b) :
    lawVariance p Y -
      (binaryMass p X false * lawVariance (binaryConditionalLaw p X false (hb false)) Y +
       binaryMass p X true * lawVariance (binaryConditionalLaw p X true (hb true)) Y) =
      (binaryCovariance p X Y) ^ 2 / lawVariance p (binaryValue X) := by
  have h := binary_total_variance p X Y hb
  rw [binaryConditionalMean_variance p X Y hb] at h
  linarith

section Indicators
variable {ι : Type*} [Fintype ι] [DecidableEq ι] {k : ℕ}

def rankIndicatorBit (i : ι) (S : RankSubset ι k) : Bool := decide (i ∈ S.val)

@[simp] theorem binaryValue_rankIndicatorBit (i : ι) (S : RankSubset ι k) :
    binaryValue (rankIndicatorBit i) S = indicator i S.val := by
  simp [binaryValue, rankIndicatorBit, indicator]

theorem binaryMass_indicator_true (p : FiniteLaw (RankSubset ι k)) (i : ι) :
    binaryMass p (rankIndicatorBit i) true = lawMean p i := by
  rw [← binaryValue_expectation]
  simp only [lawExpectation, binaryValue_rankIndicatorBit, lawMean]

def lawLinearStatistic (a : ι → ℝ) (S : RankSubset ι k) : ℝ :=
  ∑ i, a i * indicator i S.val

theorem lawLinearStatistic_expectation (p : FiniteLaw (RankSubset ι k)) (a : ι → ℝ) :
    lawExpectation p (lawLinearStatistic a) = ∑ i, a i * lawMean p i := by
  simp only [lawExpectation, lawLinearStatistic, lawMean, Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro S _
  ring

theorem binaryCovariance_linearStatistic (p : FiniteLaw (RankSubset ι k))
    (a : ι → ℝ) (i : ι) :
    binaryCovariance p (rankIndicatorBit i) (lawLinearStatistic a) =
      (lawCovariance p *ᵥ a) i := by
  unfold binaryCovariance
  rw [binaryMass_indicator_true, lawLinearStatistic_expectation]
  have hc (S : RankSubset ι k) : lawLinearStatistic a S - ∑ j, a j * lawMean p j =
      ∑ j, a j * (indicator j S.val - lawMean p j) := by
    simp only [lawLinearStatistic, mul_sub, Finset.sum_sub_distrib]
  simp only [lawExpectation, binaryValue_rankIndicatorBit, hc, Finset.sum_mul, Finset.mul_sum]
  rw [Finset.sum_comm]
  change (∑ j, ∑ S, p.val S * (a j * (indicator j S.val - lawMean p j) *
    (indicator i S.val - lawMean p i))) = _
  simp only [Matrix.mulVec, dotProduct, lawCovariance, lawExpectation, Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro j _
  apply Finset.sum_congr rfl
  intro S _
  ring

theorem binaryVariance_indicator (p : FiniteLaw (RankSubset ι k)) (i : ι) :
    lawVariance p (binaryValue (rankIndicatorBit i)) = lawCovariance p i i := by
  unfold lawVariance
  rw [binaryValue_expectation, binaryMass_indicator_true]
  simp only [lawExpectation, binaryValue_rankIndicatorBit, lawCovariance, pow_two]

theorem binaryMass_indicator_pos (p : FiniteLaw (RankSubset ι k)) (i : ι)
    (hv : 0 < lawCovariance p i i) (b : Bool) : 0 < binaryMass p (rankIndicatorBit i) b := by
  have hm := binaryMass_add p (rankIndicatorBit i)
  have h0 := binaryMass_nonneg p (rankIndicatorBit i) false
  have h1 := binaryMass_nonneg p (rankIndicatorBit i) true
  have he := binaryVariance p (rankIndicatorBit i)
  rw [binaryVariance_indicator] at he
  cases b <;> nlinarith

theorem binary_indicator_variance_drop (p : FiniteLaw (RankSubset ι k))
    (a : ι → ℝ) (i : ι) (hv : 0 < lawCovariance p i i) :
    lawVariance p (lawLinearStatistic a) -
      (binaryMass p (rankIndicatorBit i) false *
        lawVariance (binaryConditionalLaw p (rankIndicatorBit i) false
          (binaryMass_indicator_pos p i hv false)) (lawLinearStatistic a) +
       binaryMass p (rankIndicatorBit i) true *
        lawVariance (binaryConditionalLaw p (rankIndicatorBit i) true
          (binaryMass_indicator_pos p i hv true)) (lawLinearStatistic a)) =
      ((lawCovariance p *ᵥ a) i) ^ 2 / lawCovariance p i i := by
  simpa only [binaryCovariance_linearStatistic, binaryVariance_indicator] using
    binary_variance_drop p (rankIndicatorBit i) (lawLinearStatistic a)
      (binaryMass_indicator_pos p i hv)

theorem lawVariance_linearStatistic (p : FiniteLaw (RankSubset ι k)) (a : ι → ℝ) :
    lawVariance p (lawLinearStatistic a) = quadraticForm (lawCovariance p) a := by
  have hc (S : RankSubset ι k) : lawLinearStatistic a S - lawExpectation p (lawLinearStatistic a) =
      ∑ i, a i * (indicator i S.val - lawMean p i) := by
    rw [lawLinearStatistic_expectation]
    simp only [lawLinearStatistic, mul_sub, Finset.sum_sub_distrib]
  have hcomm (f : ι → ι → RankSubset ι k → ℝ) :
      (∑ i, ∑ j, ∑ S, f i j S) = ∑ S, ∑ i, ∑ j, f i j S := by
    calc
      _ = ∑ i, ∑ S, ∑ j, f i j S := by
        apply Finset.sum_congr rfl
        intro i _
        rw [Finset.sum_comm]
      _ = _ := by rw [Finset.sum_comm]
  symm
  calc
    quadraticForm (lawCovariance p) a = ∑ i, ∑ j, ∑ S,
        p.val S * (a i * (indicator i S.val - lawMean p i)) *
          (a j * (indicator j S.val - lawMean p j)) := by
      simp only [quadraticForm, Matrix.mulVec, dotProduct, lawCovariance, lawExpectation,
        Finset.mul_sum, Finset.sum_mul]
      apply Finset.sum_congr rfl
      intro i _
      apply Finset.sum_congr rfl
      intro j _
      apply Finset.sum_congr rfl
      intro S _
      ring
    _ = ∑ S, ∑ i, ∑ j, p.val S * (a i * (indicator i S.val - lawMean p i)) *
        (a j * (indicator j S.val - lawMean p j)) := hcomm _
    _ = lawVariance p (lawLinearStatistic a) := by
      unfold lawVariance
      change _ = ∑ S, p.val S *
        (lawLinearStatistic a S - lawExpectation p (lawLinearStatistic a)) ^ 2
      simp only [hc]
      apply Finset.sum_congr rfl
      intro S _
      simp only [pow_two, Finset.mul_sum, Finset.sum_mul]
      apply Finset.sum_congr rfl
      intro i _
      apply Finset.sum_congr rfl
      intro j _
      ring

end Indicators

end
end CoefficientOne.Sampling
