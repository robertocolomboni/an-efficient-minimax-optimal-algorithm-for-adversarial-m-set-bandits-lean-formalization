import CoefficientOne.Sampling.ResidualNetwork

/-! # Exact conditional variances after deleting a revealed coordinate -/

open scoped BigOperators
open EffectiveResistance Matrix
namespace CoefficientOne.Sampling
noncomputable section
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

def restrictedNumerator (w : ι → ℝ) (R : Finset ι) (r : ℕ) (f : Finset ι → ℝ) : ℝ :=
  ∑ S ∈ R.powersetCard r, subsetWeight w S * f S

theorem restrictedSum_eq_numerator (w : ι → ℝ) (R : Finset ι) (r : ℕ) (f : Finset ι → ℝ) :
    restrictedSum w R r f = restrictedNumerator w R r f / restrictedElementary w R r := by
  simp only [restrictedSum, restrictedMass, ite_mul, zero_mul, Finset.sum_ite_mem,
    Finset.univ_inter, restrictedNumerator, Finset.sum_div]
  apply Finset.sum_congr rfl
  intro S _
  ring

theorem restrictedNumerator_insert (w : ι → ℝ) (R : Finset ι) (i : ι)
    (hi : i ∉ R) (r : ℕ) (f : Finset ι → ℝ) :
    restrictedNumerator w (insert i R) (r + 1) f =
      restrictedNumerator w R (r + 1) f +
        w i * restrictedNumerator w R r (fun S => f (insert i S)) := by
  have hd : Disjoint (R.powersetCard (r + 1)) ((R.powersetCard r).image (insert i)) := by
    apply Finset.disjoint_left.mpr
    intro S hS hI
    obtain ⟨T, hT, rfl⟩ := Finset.mem_image.mp hI
    exact hi ((Finset.mem_powersetCard.mp hS).1 (Finset.mem_insert_self _ _))
  have hinj : ∀ S ∈ R.powersetCard r, ∀ T ∈ R.powersetCard r, insert i S = insert i T → S = T := by
    intro S hS T hT he
    have hSi : i ∉ S := fun h => hi ((Finset.mem_powersetCard.mp hS).1 h)
    have hTi : i ∉ T := fun h => hi ((Finset.mem_powersetCard.mp hT).1 h)
    have he' := congrArg (fun A : Finset ι => A.erase i) he
    simpa only [Finset.erase_insert hSi, Finset.erase_insert hTi] using he'
  unfold restrictedNumerator
  rw [Finset.powersetCard_succ_insert hi, Finset.sum_union hd, Finset.sum_image hinj]
  congr 1
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro S hS
  have hSi : i ∉ S := fun h => hi ((Finset.mem_powersetCard.mp hS).1 h)
  simp only [subsetWeight, Finset.prod_insert hSi]
  ring

theorem restrictedSum_delete (w : ι → ℝ) (hw : ∀ i, 0 < w i)
    (R : Finset ι) (r : ℕ) (hr0 : 0 < r) (hrtop : r < R.card)
    (i : ι) (hi : i ∈ R) (f : Finset ι → ℝ) :
    restrictedSum w R r f =
      sequentialThreshold w R r i * restrictedSum w (R.erase i) (r - 1) (fun S => f (insert i S)) +
      (1 - sequentialThreshold w R r i) * restrictedSum w (R.erase i) r f := by
  have he := restrictedNumerator_insert w (R.erase i) i (Finset.notMem_erase _ _) (r - 1) f
  rw [Finset.insert_erase hi, Nat.sub_add_cancel hr0] at he
  rw [restrictedSum_eq_numerator, he]
  rw [one_sub_sequentialThreshold w hw R r hr0 hrtop.le i hi]
  simp only [restrictedSum_eq_numerator, sequentialThreshold]
  have hp := (restrictedElementary_pos w hw (R.erase i) (r - 1)
    (by rw [Finset.card_erase_of_mem hi]; omega)).ne'
  have hq := (restrictedElementary_pos w hw (R.erase i) r
    (by rw [Finset.card_erase_of_mem hi]; omega)).ne'
  have hR := (restrictedElementary_pos w hw R r hrtop.le).ne'
  field_simp
  <;> ring

def subsetIndicatorBit (i : ι) (S : Finset ι) : Bool := decide (i ∈ S)

theorem restrictedSum_bit_true (w : ι → ℝ) (hw : ∀ i, 0 < w i)
    (R : Finset ι) (r : ℕ) (hr0 : 0 < r) (hrtop : r < R.card)
    (i : ι) (hi : i ∈ R) (f : Finset ι → ℝ) :
    restrictedSum w R r (fun S => if subsetIndicatorBit i S = true then f S else 0) =
      sequentialThreshold w R r i * restrictedSum w (R.erase i) (r - 1) (fun S => f (insert i S)) := by
  rw [restrictedSum_delete w hw R r hr0 hrtop i hi]
  have hno : restrictedSum w (R.erase i) r
      (fun S => if subsetIndicatorBit i S = true then f S else 0) = 0 := by
    calc
      _ = restrictedSum w (R.erase i) r (fun _ => 0) := by
        apply restrictedSum_congr
        intro S hS
        have hn : i ∉ S := fun h => Finset.notMem_erase i R ((Finset.mem_powersetCard.mp hS).1 h)
        simp [subsetIndicatorBit, hn]
      _ = 0 := by simp [restrictedSum]
  simp only [subsetIndicatorBit, Finset.mem_insert_self, decide_true, ↓reduceIte] at *
  rw [hno]
  ring

theorem restrictedSum_bit_false (w : ι → ℝ) (hw : ∀ i, 0 < w i)
    (R : Finset ι) (r : ℕ) (hr0 : 0 < r) (hrtop : r < R.card)
    (i : ι) (hi : i ∈ R) (f : Finset ι → ℝ) :
    restrictedSum w R r (fun S => if subsetIndicatorBit i S = false then f S else 0) =
      (1 - sequentialThreshold w R r i) * restrictedSum w (R.erase i) r f := by
  rw [restrictedSum_delete w hw R r hr0 hrtop i hi]
  have hno : restrictedSum w (R.erase i) r
      (fun S => if subsetIndicatorBit i S = false then f S else 0) = restrictedSum w (R.erase i) r f := by
    apply restrictedSum_congr
    intro S hS
    have hn : i ∉ S := fun h => Finset.notMem_erase i R ((Finset.mem_powersetCard.mp hS).1 h)
    simp [subsetIndicatorBit, hn]
  simp only [subsetIndicatorBit, Finset.mem_insert_self, decide_true, Bool.true_eq_false,
    ↓reduceIte] at *
  rw [hno]
  simp [restrictedSum]

theorem restrictedSum_const (w : ι → ℝ) (hw : ∀ i, 0 < w i)
    (R : Finset ι) (r : ℕ) (hr : r ≤ R.card) (c : ℝ) :
    restrictedSum w R r (fun _ => c) = c :=
  lawExpectation_const (restrictedLaw w hw R r hr) c

theorem residual_binaryMass (w : ι → ℝ) (hw : ∀ i, 0 < w i)
    (R : Finset ι) (r : ℕ) (hr0 : 0 < r) (hrtop : r < R.card)
    (i : ι) (hi : i ∈ R) (b : Bool) :
    binaryMass (restrictedLaw w hw R r hrtop.le) (subsetIndicatorBit i) b =
      if b then sequentialThreshold w R r i else 1 - sequentialThreshold w R r i := by
  cases b
  · change restrictedSum w R r (fun S => if subsetIndicatorBit i S = false then 1 else 0) = _
    rw [restrictedSum_bit_false w hw R r hr0 hrtop i hi]
    rw [restrictedSum_const w hw (R.erase i) r (by rw [Finset.card_erase_of_mem hi]; omega)]
    simp
  · change restrictedSum w R r (fun S => if subsetIndicatorBit i S = true then 1 else 0) = _
    rw [restrictedSum_bit_true w hw R r hr0 hrtop i hi]
    rw [restrictedSum_const w hw (R.erase i) (r - 1) (by rw [Finset.card_erase_of_mem hi]; omega)]
    simp

theorem residual_binaryMass_pos (w : ι → ℝ) (hw : ∀ i, 0 < w i)
    (R : Finset ι) (r : ℕ) (hr0 : 0 < r) (hrtop : r < R.card)
    (i : ι) (hi : i ∈ R) (b : Bool) :
    0 < binaryMass (restrictedLaw w hw R r hrtop.le) (subsetIndicatorBit i) b := by
  rw [residual_binaryMass w hw R r hr0 hrtop i hi b]
  cases b
  · exact sub_pos.mpr (sequentialThreshold_lt_one w hw R r hr0 hrtop i hi)
  · exact sequentialThreshold_pos w hw R r hr0 hrtop.le i hi

theorem residual_binaryConditional_expectation_true (w : ι → ℝ) (hw : ∀ i, 0 < w i)
    (R : Finset ι) (r : ℕ) (hr0 : 0 < r) (hrtop : r < R.card)
    (i : ι) (hi : i ∈ R) (f : Finset ι → ℝ) :
    lawExpectation (binaryConditionalLaw (restrictedLaw w hw R r hrtop.le)
      (subsetIndicatorBit i) true (residual_binaryMass_pos w hw R r hr0 hrtop i hi true)) f =
      restrictedSum w (R.erase i) (r - 1) (fun S => f (insert i S)) := by
  rw [binaryConditionalLaw_expectation]
  change restrictedSum w R r (fun S => if subsetIndicatorBit i S = true then f S else 0) /
    binaryMass (restrictedLaw w hw R r hrtop.le) (subsetIndicatorBit i) true = _
  rw [restrictedSum_bit_true w hw R r hr0 hrtop i hi,
    residual_binaryMass w hw R r hr0 hrtop i hi true]
  simp only [↓reduceIte]
  field_simp [(sequentialThreshold_pos w hw R r hr0 hrtop.le i hi).ne']

theorem residual_binaryConditional_expectation_false (w : ι → ℝ) (hw : ∀ i, 0 < w i)
    (R : Finset ι) (r : ℕ) (hr0 : 0 < r) (hrtop : r < R.card)
    (i : ι) (hi : i ∈ R) (f : Finset ι → ℝ) :
    lawExpectation (binaryConditionalLaw (restrictedLaw w hw R r hrtop.le)
      (subsetIndicatorBit i) false (residual_binaryMass_pos w hw R r hr0 hrtop i hi false)) f =
      restrictedSum w (R.erase i) r f := by
  rw [binaryConditionalLaw_expectation]
  change restrictedSum w R r (fun S => if subsetIndicatorBit i S = false then f S else 0) /
    binaryMass (restrictedLaw w hw R r hrtop.le) (subsetIndicatorBit i) false = _
  rw [restrictedSum_bit_false w hw R r hr0 hrtop i hi,
    residual_binaryMass w hw R r hr0 hrtop i hi false]
  simp only [Bool.false_eq_true, ↓reduceIte]
  field_simp [(sub_pos.mpr (sequentialThreshold_lt_one w hw R r hr0 hrtop i hi)).ne']

theorem residual_binaryConditional_variance_true (w : ι → ℝ) (hw : ∀ i, 0 < w i)
    (R : Finset ι) (r : ℕ) (hr0 : 0 < r) (hrtop : r < R.card)
    (i : ι) (hi : i ∈ R) (f : Finset ι → ℝ) :
    lawVariance (binaryConditionalLaw (restrictedLaw w hw R r hrtop.le)
      (subsetIndicatorBit i) true (residual_binaryMass_pos w hw R r hr0 hrtop i hi true)) f =
      lawVariance (restrictedLaw w hw (R.erase i) (r - 1)
        (by rw [Finset.card_erase_of_mem hi]; omega)) (fun S => f (insert i S)) := by
  unfold lawVariance
  rw [residual_binaryConditional_expectation_true w hw R r hr0 hrtop i hi,
    residual_binaryConditional_expectation_true w hw R r hr0 hrtop i hi]
  rfl

theorem residual_binaryConditional_variance_false (w : ι → ℝ) (hw : ∀ i, 0 < w i)
    (R : Finset ι) (r : ℕ) (hr0 : 0 < r) (hrtop : r < R.card)
    (i : ι) (hi : i ∈ R) (f : Finset ι → ℝ) :
    lawVariance (binaryConditionalLaw (restrictedLaw w hw R r hrtop.le)
      (subsetIndicatorBit i) false (residual_binaryMass_pos w hw R r hr0 hrtop i hi false)) f =
      lawVariance (restrictedLaw w hw (R.erase i) r
        (by rw [Finset.card_erase_of_mem hi]; omega)) f := by
  unfold lawVariance
  rw [residual_binaryConditional_expectation_false w hw R r hr0 hrtop i hi,
    residual_binaryConditional_expectation_false w hw R r hr0 hrtop i hi]
  rfl

theorem residual_variance_insert (w : ι → ℝ) (hw : ∀ i, 0 < w i)
    (R : Finset ι) (r : ℕ) (hr : r ≤ R.card) (i : ι) (hi : i ∉ R) (a : ι → ℝ) :
    lawVariance (restrictedLaw w hw R r hr) (fun S => subsetLinearStatistic a (insert i S)) =
      residualVariance w hw R r hr a := by
  have hval (S : Finset ι) (hS : S ∈ R.powersetCard r) :
      subsetLinearStatistic a (insert i S) = a i + 1 * subsetLinearStatistic a S := by
    have hni : i ∉ S := fun h => hi ((Finset.mem_powersetCard.mp hS).1 h)
    simp [subsetLinearStatistic, Finset.sum_insert hni]
  have hm : lawExpectation (restrictedLaw w hw R r hr) (fun S => subsetLinearStatistic a (insert i S)) =
      lawExpectation (restrictedLaw w hw R r hr) (fun S => a i + 1 * subsetLinearStatistic a S) :=
    restrictedSum_congr w R r _ _ hval
  calc
    _ = lawVariance (restrictedLaw w hw R r hr) (fun S => a i + 1 * subsetLinearStatistic a S) := by
      unfold lawVariance
      rw [hm]
      apply restrictedSum_congr
      intro S hS
      dsimp only
      rw [hval S hS]
    _ = residualVariance w hw R r hr a := by rw [lawVariance_affine]; simp [residualVariance]

@[simp] theorem binaryValue_subsetIndicatorBit (i : ι) (S : Finset ι) :
    binaryValue (subsetIndicatorBit i) S = indicator i S := by
  simp [binaryValue, subsetIndicatorBit, indicator]

theorem residual_binaryMass_true_eq_mean (w : ι → ℝ) (hw : ∀ i, 0 < w i)
    (R : Finset ι) (r : ℕ) (hr : r ≤ R.card) (i : ι) :
    binaryMass (restrictedLaw w hw R r hr) (subsetIndicatorBit i) true = residualMean w R r i := by
  simp [binaryMass, subsetIndicatorBit, residualMean, lawExpectation, restrictedLaw,
    restrictedSum, indicator]

theorem residual_statistic_expectation (w : ι → ℝ) (hw : ∀ i, 0 < w i)
    (R : Finset ι) (r : ℕ) (hr : r ≤ R.card) (a : ι → ℝ) :
    lawExpectation (restrictedLaw w hw R r hr) (subsetLinearStatistic a) =
      ∑ i, a i * residualMean w R r i := by
  simp only [subsetLinearStatistic_eq_indicator, lawExpectation, residualMean,
    restrictedSum, restrictedLaw, Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro S _
  ring

theorem residual_binaryCovariance_statistic (w : ι → ℝ) (hw : ∀ i, 0 < w i)
    (R : Finset ι) (r : ℕ) (hr : r ≤ R.card) (a : ι → ℝ) (i : ι) :
    binaryCovariance (restrictedLaw w hw R r hr) (subsetIndicatorBit i) (subsetLinearStatistic a) =
      (residualCovariance w R r *ᵥ a) i := by
  unfold binaryCovariance
  rw [residual_binaryMass_true_eq_mean, residual_statistic_expectation]
  have hc (S : Finset ι) : subsetLinearStatistic a S - ∑ j, a j * residualMean w R r j =
      ∑ j, a j * (indicator j S - residualMean w R r j) := by
    rw [subsetLinearStatistic_eq_indicator]
    simp only [mul_sub, Finset.sum_sub_distrib]
  simp only [lawExpectation, binaryValue_subsetIndicatorBit, hc, Finset.sum_mul, Finset.mul_sum]
  rw [Finset.sum_comm]
  change (∑ j, ∑ S, restrictedMass w R r S *
    (a j * (indicator j S - residualMean w R r j) * (indicator i S - residualMean w R r i))) =
      ∑ j, residualCovariance w R r i j * a j
  apply Finset.sum_congr rfl
  intro j _
  simp only [residualCovariance, restrictedSum, Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro S _
  ring

theorem residual_binaryVariance (w : ι → ℝ) (hw : ∀ i, 0 < w i)
    (R : Finset ι) (r : ℕ) (hr : r ≤ R.card) (i : ι) :
    lawVariance (restrictedLaw w hw R r hr) (binaryValue (subsetIndicatorBit i)) =
      residualCovariance w R r i i := by
  unfold lawVariance
  rw [binaryValue_expectation, residual_binaryMass_true_eq_mean]
  simp only [binaryValue_subsetIndicatorBit, lawExpectation, restrictedLaw,
    residualCovariance, restrictedSum, pow_two]

/-- The exact one-bit variance drop for the two actual deleted residual laws. -/
theorem residual_coordinate_variance_drop (w : ι → ℝ) (hw : ∀ i, 0 < w i)
    (R : Finset ι) (r : ℕ) (hr0 : 0 < r) (hrtop : r < R.card)
    (a : ι → ℝ) (i : ι) (hi : i ∈ R) :
    quadraticForm (residualCovariance w R r) a -
      (sequentialThreshold w R r i * quadraticForm (residualCovariance w (R.erase i) (r - 1)) a +
       (1 - sequentialThreshold w R r i) * quadraticForm (residualCovariance w (R.erase i) r) a) =
      ((residualCovariance w R r *ᵥ a) i) ^ 2 / residualCovariance w R r i i := by
  have h := binary_variance_drop (restrictedLaw w hw R r hrtop.le)
    (subsetIndicatorBit i) (subsetLinearStatistic a)
    (residual_binaryMass_pos w hw R r hr0 hrtop i hi)
  rw [residual_binaryConditional_variance_true w hw R r hr0 hrtop i hi,
    residual_binaryConditional_variance_false w hw R r hr0 hrtop i hi,
    residual_variance_insert w hw (R.erase i) (r - 1) _ i (Finset.notMem_erase _ _),
    residual_binaryMass w hw R r hr0 hrtop i hi true,
    residual_binaryMass w hw R r hr0 hrtop i hi false,
    residual_binaryCovariance_statistic, residual_binaryVariance] at h
  change residualVariance w hw R r hrtop.le a -
      ((1 - sequentialThreshold w R r i) * residualVariance w hw (R.erase i) r _ a +
       sequentialThreshold w R r i * residualVariance w hw (R.erase i) (r - 1) _ a) = _ at h
  simp only [residualVariance_eq_covariance] at h
  linarith

end
end CoefficientOne.Sampling
