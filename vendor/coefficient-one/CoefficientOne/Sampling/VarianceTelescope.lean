import CoefficientOne.Sampling.CutVariance
import CoefficientOne.Sampling.RankSubsetLaw

/-! # Finite telescoping of the actual conditional variances -/
open scoped BigOperators
open EffectiveResistance Matrix MeasureTheory
namespace CoefficientOne.Sampling
noncomputable section

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

theorem restrictedSum_univ (w : ι → ℝ) (hw : ∀ i, 0 < w i)
    (k : ℕ) (hk : k ≤ Fintype.card ι) (f : Finset ι → ℝ) :
    restrictedSum w Finset.univ k f = expectation w k (fun S => f S.val) := by
  have h := integral_restrictedLaw_univ w hw k hk f
  simpa only [integral_lawMeasure, lawExpectation, restrictedLaw, externalFieldLaw,
    restrictedSum, expectation] using h

theorem residualCovariance_univ (w : ι → ℝ) (hw : ∀ i, 0 < w i)
    (k : ℕ) (hk : k ≤ Fintype.card ι) :
    residualCovariance w Finset.univ k = covarianceMatrix w k := by
  have hm (i : ι) : residualMean w Finset.univ k i = inclusionMean w k i := by
    rw [residualMean, restrictedSum_univ w hw k hk]
    rfl
  ext i j
  rw [residualCovariance, restrictedSum_univ w hw k hk, hm i, hm j]
  rfl

theorem residualCovariance_quadratic_nonneg (w : ι → ℝ) (hw : ∀ i, 0 < w i)
    (R : Finset ι) (r : ℕ) (a : ι → ℝ) :
    0 ≤ quadraticForm (residualCovariance w R r) a := by
  rw [← residualNetwork_laplacian w hw R r, ← ConductanceNetwork.energy_eq_quadraticForm]
  exact (residualNetwork w hw R r).energy_nonnegative a

theorem samplerCovariance_initial {n : ℕ} (w : Fin n → ℝ) (hw : ∀ i, 0 < w i)
    (k : ℕ) (hk : k ≤ n) (ω : Seed n) : samplerCovariance w k 0 ω = covarianceMatrix w k := by
  simp only [samplerCovariance, historyRemaining, List.drop_zero, permutation_order_toFinset,
    historyQuota, historySelected, prefixSelected_zero, Finset.card_empty, Nat.sub_zero]
  exact residualCovariance_univ w hw k (by simpa using hk)

theorem samplerCovariance_last {n : ℕ} (w : Fin n → ℝ) (hw : ∀ i, 0 < w i)
    (k : ℕ) (hk : k ≤ n) (ω : Seed n) : samplerCovariance w k n ω = 0 := by
  have hR : historyRemaining n ω = ∅ := by simp [historyRemaining]
  have hq := historyQuota_le_remaining_card w k n hk ω
  rw [hR, Finset.card_empty] at hq
  apply samplerCovariance_terminal w hw k n ω
  exact Or.inl (Nat.eq_zero_of_le_zero hq)

theorem finite_drift_telescope (n : ℕ) (z q : ℕ → ℝ)
    (hstep : ∀ ℓ < n, q ℓ ≤ z ℓ - z (ℓ + 1)) (hlast : 0 ≤ z n) :
    ∑ ℓ ∈ Finset.range n, q ℓ ≤ z 0 := by
  have hsum : ∀ m ≤ n, ∑ ℓ ∈ Finset.range m, q ℓ ≤ z 0 - z m := by
    intro m hm
    induction m with
    | zero => simp
    | succ m ih =>
      rw [Finset.sum_range_succ]
      have hi := ih (by omega)
      have hs := hstep m (by omega)
      linarith
  have h := hsum n le_rfl
  linarith

/-- The manuscript's finite variance telescope, for every deterministic
linear statistic, along the real common-seed sampler. -/
theorem sampler_variance_telescope {n : ℕ} (w : Fin n → ℝ) (hw : ∀ i, 0 < w i)
    (k : ℕ) (hk : k ≤ n) (a : Fin n → ℝ) :
    (∫ ω, ∑ ℓ ∈ Finset.range n,
      quadraticForm (samplerCovariance w k ℓ ω) a / (historyRemaining ℓ ω).card ∂seedMeasure n) ≤
      quadraticForm (covarianceMatrix w k) a := by
  let Z := fun ℓ => ∫ ω, quadraticForm (samplerCovariance w k ℓ ω) a ∂seedMeasure n
  let Q := fun ℓ => ∫ ω, quadraticForm (samplerCovariance w k ℓ ω) a /
    (historyRemaining ℓ ω).card ∂seedMeasure n
  have hZ (ℓ : ℕ) : Integrable (fun ω => quadraticForm (samplerCovariance w k ℓ ω) a)
      (seedMeasure n) := integrable_historyStatistic w k ℓ
    (fun z => quadraticForm (residualCovariance w z.1 z.2) a)
  have hQ (ℓ : ℕ) : Integrable (fun ω => quadraticForm (samplerCovariance w k ℓ ω) a /
      (historyRemaining ℓ ω).card) (seedMeasure n) := integrable_historyStatistic w k ℓ
    (fun z => quadraticForm (residualCovariance w z.1 z.2) a / z.1.card)
  have hstep (ℓ : ℕ) (hℓ : ℓ < n) : Q ℓ ≤ Z ℓ - Z (ℓ + 1) := by
    have h := sampler_variance_drift w hw k ℓ hk hℓ a
    rw [integral_sub (hZ ℓ) (hQ ℓ)] at h
    dsimp only [Q, Z]
    linarith
  have hlast : 0 ≤ Z n := by
    apply integral_nonneg
    intro ω
    exact residualCovariance_quadratic_nonneg w hw _ _ a
  have h := finite_drift_telescope n Z Q hstep hlast
  have hzero : Z 0 = quadraticForm (covarianceMatrix w k) a := by
    simp only [Z, samplerCovariance_initial w hw k hk]
    simp
  rw [hzero] at h
  rw [integral_finsetSum _ (fun ℓ _ => hQ ℓ)]
  exact h

end
end CoefficientOne.Sampling
