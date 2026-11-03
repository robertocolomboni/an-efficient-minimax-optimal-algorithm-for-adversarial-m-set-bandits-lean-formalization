import EffectiveResistance.ThreeSliceCurvature

/-!
# Weighted regression over three consecutive ranks

The loss is written as a mixture of three external-field laws.  Conditional
variance gives the covariance mixture, while a three-point weighted
Cauchy--Schwarz inequality controls the three conditional means.
-/

open scoped BigOperators

namespace EffectiveResistance

noncomputable section

/-- Weighted Cauchy--Schwarz for the second difference of three scalars. -/
theorem weighted_three_point_second_difference
    {pminus pzero pplus rminus rzero rplus : ℝ}
    (hminus : 0 < pminus) (hzero : 0 < pzero) (hplus : 0 < pplus) :
    (rminus - 2 * rzero + rplus) ^ 2 ≤
      (1 / pminus + 4 / pzero + 1 / pplus) *
        (pminus * rminus ^ 2 + pzero * rzero ^ 2 +
          pplus * rplus ^ 2) := by
  let zminus : ℝ := 1 / pminus
  let zzero : ℝ := -2 / pzero
  let zplus : ℝ := 1 / pplus
  have h12 : 0 ≤ pminus * pzero *
      (rminus * zzero - rzero * zminus) ^ 2 := by positivity
  have h13 : 0 ≤ pminus * pplus *
      (rminus * zplus - rplus * zminus) ^ 2 := by positivity
  have h23 : 0 ≤ pzero * pplus *
      (rzero * zplus - rplus * zzero) ^ 2 := by positivity
  have hid :
      (1 / pminus + 4 / pzero + 1 / pplus) *
          (pminus * rminus ^ 2 + pzero * rzero ^ 2 +
            pplus * rplus ^ 2) -
        (rminus - 2 * rzero + rplus) ^ 2 =
      pminus * pzero * (rminus * zzero - rzero * zminus) ^ 2 +
        pminus * pplus * (rminus * zplus - rplus * zminus) ^ 2 +
          pzero * pplus * (rzero * zplus - rplus * zzero) ^ 2 := by
    dsimp only [zminus, zzero, zplus]
    field_simp [ne_of_gt hminus, ne_of_gt hzero, ne_of_gt hplus]
    <;> ring
  rw [← sub_nonneg, hid]
  exact add_nonneg (add_nonneg h12 h13) h23

theorem weighted_three_point_second_difference_div
    {pminus pzero pplus rminus rzero rplus : ℝ}
    (hminus : 0 < pminus) (hzero : 0 < pzero) (hplus : 0 < pplus) :
    (rminus - 2 * rzero + rplus) ^ 2 /
        (1 / pminus + 4 / pzero + 1 / pplus) ≤
      pminus * rminus ^ 2 + pzero * rzero ^ 2 +
        pplus * rplus ^ 2 := by
  have hD : 0 < 1 / pminus + 4 / pzero + 1 / pplus := by positivity
  apply (div_le_iff₀ hD).2
  simpa [mul_comm] using
    (weighted_three_point_second_difference
      (rminus := rminus) (rzero := rzero) (rplus := rplus)
      hminus hzero hplus)

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

namespace PairTable

variable (P : PairTable)

/-- The centered linear-regression loss after conditioning on endpoint states
`11`, `10/01`, and `00`. -/
def threeSliceLoss (w : ι → ℝ) (q : ℕ) (α : ℝ) (a : ι → ℝ) : ℝ :=
  P.p11 * expectation w q
      (fun S => (0 - α - rankLinearStatistic a S.1) ^ 2) +
    P.s * expectation w (q + 1)
      (fun S => (1 - α - rankLinearStatistic a S.1) ^ 2) +
    P.p00 * expectation w (q + 2)
      (fun S => (0 - α - rankLinearStatistic a S.1) ^ 2)

/-- The same three-slice loss when the middle-slice response has amplitude
`r` instead of one. -/
def scaledThreeSliceLoss (w : ι → ℝ) (q : ℕ) (r α : ℝ)
    (a : ι → ℝ) : ℝ :=
  P.p11 * expectation w q
      (fun S => (0 - α - rankLinearStatistic a S.1) ^ 2) +
    P.s * expectation w (q + 1)
      (fun S => (r - α - rankLinearStatistic a S.1) ^ 2) +
    P.p00 * expectation w (q + 2)
      (fun S => (0 - α - rankLinearStatistic a S.1) ^ 2)

theorem rankLinearStatistic_div (a : ι → ℝ) (r : ℝ)
    (S : Finset ι) :
    rankLinearStatistic (fun i => a i / r) S =
      rankLinearStatistic a S / r := by
  unfold rankLinearStatistic
  rw [Finset.sum_div]
  apply Finset.sum_congr rfl
  intro i _
  ring

theorem scaledThreeSliceLoss_eq_scale
    (w : ι → ℝ) (q : ℕ) {r : ℝ} (hr : r ≠ 0)
    (α : ℝ) (a : ι → ℝ) :
    P.scaledThreeSliceLoss w q r α a =
      r ^ 2 * P.threeSliceLoss w q (α / r) (fun i => a i / r) := by
  have hscale (t : ℕ) (b : ℝ) :
      expectation w t
          (fun S => (r * b - α - rankLinearStatistic a S.1) ^ 2) =
        r ^ 2 * expectation w t
          (fun S => (b - α / r -
            rankLinearStatistic (fun i => a i / r) S.1) ^ 2) := by
    unfold expectation
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro S _
    change subsetProbability w t S *
        (r * b - α - rankLinearStatistic a S.1) ^ 2 =
      r ^ 2 * (subsetProbability w t S *
        (b - α / r -
          rankLinearStatistic (fun i => a i / r) S.1) ^ 2)
    rw [rankLinearStatistic_div]
    field_simp [hr]
  unfold scaledThreeSliceLoss threeSliceLoss
  have hminus := hscale q 0
  have hzero := hscale (q + 1) 1
  have hplus := hscale (q + 2) 0
  simp only [mul_zero, mul_one, zero_sub] at hminus hzero hplus ⊢
  rw [hminus, hzero, hplus]
  ring

theorem scaledThreeSliceLoss_nonnegative
    (w : ι → ℝ) (hw : ∀ i, 0 < w i) (q : ℕ)
    (hq : q + 2 ≤ Fintype.card ι) (r α : ℝ) (a : ι → ℝ) :
    0 ≤ P.scaledThreeSliceLoss w q r α a := by
  have hq0 : q ≤ Fintype.card ι := by omega
  have hq1 : q + 1 ≤ Fintype.card ι := by omega
  have hs : 0 ≤ P.s := by
    exact add_nonneg P.nonneg10 P.nonneg01
  unfold scaledThreeSliceLoss
  exact add_nonneg
    (add_nonneg
      (mul_nonneg P.nonneg11
        (expectation_nonnegative w hw hq0 fun S => sq_nonneg _))
      (mul_nonneg hs
        (expectation_nonnegative w hw hq1 fun S => sq_nonneg _)))
    (mul_nonneg P.nonneg00
      (expectation_nonnegative w hw hq fun S => sq_nonneg _))

theorem threeSliceLoss_decomposition
    (w : ι → ℝ) (hw : ∀ i, 0 < w i) (q : ℕ)
    (hq : q + 2 ≤ Fintype.card ι) (α : ℝ) (a : ι → ℝ) :
    P.threeSliceLoss w q α a = P.threeSliceQuadratic w q a +
      (P.p11 * (-α - ∑ i, a i * inclusionMean w q i) ^ 2 +
        P.s * (1 - α - ∑ i, a i * inclusionMean w (q + 1) i) ^ 2 +
        P.p00 * (-α - ∑ i, a i * inclusionMean w (q + 2) i) ^ 2) := by
  have hq0 : q ≤ Fintype.card ι := by omega
  have hq1 : q + 1 ≤ Fintype.card ι := by omega
  unfold threeSliceLoss
  rw [expectation_rankLinear_residual_decomposition w hw q hq0 a (0 - α),
    expectation_rankLinear_residual_decomposition w hw (q + 1) hq1 a (1 - α),
    expectation_rankLinear_residual_decomposition w hw (q + 2) hq a (0 - α)]
  unfold threeSliceQuadratic
  ring

theorem threeSlice_mean_loss_lower_bound
    (w : ι → ℝ) (q : ℕ)
    (h11 : 0 < P.p11) (h10 : 0 < P.p10) (h00 : 0 < P.p00)
    (α : ℝ) (a : ι → ℝ) :
    (2 + ∑ i, a i * rankCurvature w q i) ^ 2 /
        P.sliceDenominator ≤
      P.p11 * (-α - ∑ i, a i * inclusionMean w q i) ^ 2 +
        P.s * (1 - α - ∑ i, a i * inclusionMean w (q + 1) i) ^ 2 +
        P.p00 * (-α - ∑ i, a i * inclusionMean w (q + 2) i) ^ 2 := by
  have hs : 0 < P.s := P.s_pos h10
  let rminus : ℝ := -α - ∑ i, a i * inclusionMean w q i
  let rzero : ℝ := 1 - α - ∑ i, a i * inclusionMean w (q + 1) i
  let rplus : ℝ := -α - ∑ i, a i * inclusionMean w (q + 2) i
  have hsecond :
      (rminus - 2 * rzero + rplus) ^ 2 =
        (2 + ∑ i, a i * rankCurvature w q i) ^ 2 := by
    dsimp only [rminus, rzero, rplus]
    have hsum :
        (∑ i, a i * rankCurvature w q i) =
          (∑ i, a i * inclusionMean w q i) -
            2 * (∑ i, a i * inclusionMean w (q + 1) i) +
              ∑ i, a i * inclusionMean w (q + 2) i := by
      unfold rankCurvature
      calc
        (∑ i, a i *
            (inclusionMean w q i - 2 * inclusionMean w (q + 1) i +
              inclusionMean w (q + 2) i)) =
          ∑ i, ((a i * inclusionMean w q i -
              2 * (a i * inclusionMean w (q + 1) i)) +
                a i * inclusionMean w (q + 2) i) := by
            apply Finset.sum_congr rfl
            intro i _
            ring
        _ = (∑ i, (a i * inclusionMean w q i -
              2 * (a i * inclusionMean w (q + 1) i))) +
                ∑ i, a i * inclusionMean w (q + 2) i := by
            rw [Finset.sum_add_distrib]
        _ = _ := by
          rw [Finset.sum_sub_distrib, Finset.mul_sum]
    rw [hsum]
    ring
  have hbound := weighted_three_point_second_difference_div
    (rminus := rminus) (rzero := rzero) (rplus := rplus) h11 hs h00
  rw [hsecond] at hbound
  change (2 + ∑ i, a i * rankCurvature w q i) ^ 2 /
      P.sliceDenominator ≤
    P.p11 * rminus ^ 2 + P.s * rzero ^ 2 + P.p00 * rplus ^ 2
  simpa only [sliceDenominator] using hbound

/-- The unconditional three-slice regression lower bound for every intercept
and every linear background coefficient. -/
theorem externalField_threeSliceLoss_bound
    (w : ι → ℝ) (hw : ∀ i, 0 < w i) (q : ℕ)
    (hq : q + 2 ≤ Fintype.card ι)
    (h11 : 0 < P.p11) (h10 : 0 < P.p10) (h01 : 0 < P.p01)
    (h00 : 0 < P.p00) (hω : 0 ≤ P.ω)
    (htheta : adjacentTheta w q =
      P.p11 * P.p00 / (P.p10 * P.p01)) (α : ℝ) (a : ι → ℝ) :
    4 * P.p11 * P.p00 * P.s / (P.vi + P.vj) ≤
      P.threeSliceLoss w q α a := by
  have hobj := P.externalField_threeSlice_objective_bound
    w hw q hq h11 h10 h01 h00 hω htheta a
  have hmean := P.threeSlice_mean_loss_lower_bound
    w q h11 h10 h00 α a
  rw [P.threeSliceLoss_decomposition w hw q hq α a]
  linarith

/-- Homogeneous form of the three-slice bound.  It remains valid at `r = 0`
and therefore never requires division by the endpoint imbalance. -/
theorem externalField_scaledThreeSliceLoss_bound
    (w : ι → ℝ) (hw : ∀ i, 0 < w i) (q : ℕ)
    (hq : q + 2 ≤ Fintype.card ι)
    (h11 : 0 < P.p11) (h10 : 0 < P.p10) (h01 : 0 < P.p01)
    (h00 : 0 < P.p00) (hω : 0 ≤ P.ω)
    (htheta : adjacentTheta w q =
      P.p11 * P.p00 / (P.p10 * P.p01))
    (r α : ℝ) (a : ι → ℝ) :
    r ^ 2 * (4 * P.p11 * P.p00 * P.s / (P.vi + P.vj)) ≤
      P.scaledThreeSliceLoss w q r α a := by
  by_cases hr : r = 0
  · subst r
    simp only [zero_pow (by norm_num : (2 : ℕ) ≠ 0), zero_mul]
    exact P.scaledThreeSliceLoss_nonnegative w hw q hq 0 α a
  · have hbase := P.externalField_threeSliceLoss_bound
      w hw q hq h11 h10 h01 h00 hω htheta (α / r) (fun i => a i / r)
    have hscaled := mul_le_mul_of_nonneg_left hbase (sq_nonneg r)
    rw [P.scaledThreeSliceLoss_eq_scale w q hr α a]
    exact hscaled

end PairTable

end

end EffectiveResistance
