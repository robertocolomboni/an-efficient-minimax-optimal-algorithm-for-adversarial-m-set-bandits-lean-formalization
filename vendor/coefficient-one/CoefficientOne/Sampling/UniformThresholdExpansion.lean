import CoefficientOne.Sampling.LocalThresholds

/-! # A single differential remainder for all finitely many residual states -/

open scoped BigOperators Topology
open EffectiveResistance Filter

namespace CoefficientOne.Sampling
noncomputable section
set_option maxHeartbeats 1000000

variable {α ι : Type*} [Fintype α] [Fintype ι]

def finiteDerivativeError (f : α → ℝ → ι → ℝ) (v : α → ι → ℝ) (t : ℝ) : ℝ :=
  ∑ s, ∑ i, |(f s t i - f s 0 i) / t - v s i|

theorem finiteDerivativeError_nonneg (f : α → ℝ → ι → ℝ) (v : α → ι → ℝ) (t : ℝ) :
    0 ≤ finiteDerivativeError f v t :=
  Finset.sum_nonneg fun _ _ => Finset.sum_nonneg fun _ _ => abs_nonneg _

theorem finiteDerivativeError_tendsto (f : α → ℝ → ι → ℝ) (v : α → ι → ℝ)
    (hf : ∀ s, HasDerivAt (f s) (v s) 0) :
    Tendsto (finiteDerivativeError f v) (𝓝[≠] 0) (𝓝 0) := by
  have hlim : Tendsto (finiteDerivativeError f v) (𝓝[≠] 0)
      (𝓝 (∑ _ : α, ∑ _ : ι, (0 : ℝ))) := by
    apply tendsto_finset_sum
    intro s _
    apply tendsto_finset_sum
    intro i _
    have hs := (hasDerivAt_pi.mp (hf s) i).tendsto_slope
    have hh := (hs.sub (tendsto_const_nhds (x := v s i))).abs
    simpa [slope, sub_zero, smul_eq_mul, div_eq_mul_inv, mul_comm] using hh
  simpa using hlim

theorem finiteDerivativeError_bound (f : α → ℝ → ι → ℝ) (v : α → ι → ℝ)
    (s : α) (t : ℝ) :
    l1Norm (fun i => f s t i - f s 0 i - t * v s i) ≤ |t| * finiteDerivativeError f v t := by
  classical
  by_cases ht : t = 0
  · subst t
    simp [l1Norm]
  have heq (i : ι) : f s t i - f s 0 i - t * v s i =
      t * ((f s t i - f s 0 i) / t - v s i) := by field_simp
  simp only [l1Norm, heq, abs_mul, ← Finset.mul_sum]
  apply mul_le_mul_of_nonneg_left _ (abs_nonneg t)
  change (∑ i, |(f s t i - f s 0 i) / t - v s i|) ≤
    ∑ a, ∑ i, |(f a t i - f a 0 i) / t - v a i|
  exact Finset.single_le_sum (fun a _ => Finset.sum_nonneg fun i _ =>
    abs_nonneg ((f a t i - f a 0 i) / t - v a i)) (Finset.mem_univ s)

theorem finiteDerivative_local_lipschitz (f : α → ℝ → ι → ℝ) (v : α → ι → ℝ)
    (hf : ∀ s, HasDerivAt (f s) (v s) 0) :
    ∃ L : ℝ, 0 < L ∧ ∀ᶠ t in 𝓝[≠] (0 : ℝ), ∀ s i,
      |f s t i - f s 0 i| ≤ L * |t| := by
  classical
  let D : ℝ := ∑ s, ∑ i, |v s i|
  have hD : 0 ≤ D := Finset.sum_nonneg fun s _ => Finset.sum_nonneg fun i _ => abs_nonneg _
  refine ⟨D + 1, by linarith, ?_⟩
  have he := (finiteDerivativeError_tendsto f v hf).eventually (Iio_mem_nhds (show (0 : ℝ) < 1 by norm_num))
  filter_upwards [he] with t ht
  intro s i
  have hvi : |v s i| ≤ D :=
    (Finset.single_le_sum (fun j _ => abs_nonneg (v s j)) (Finset.mem_univ i)).trans
      (Finset.single_le_sum (fun a _ => Finset.sum_nonneg fun j _ => abs_nonneg (v a j))
        (Finset.mem_univ s))
  have herr : |f s t i - f s 0 i - t * v s i| ≤
      l1Norm (fun j => f s t j - f s 0 j - t * v s j) := by
    change |f s t i - f s 0 i - t * v s i| ≤ ∑ j, |f s t j - f s 0 j - t * v s j|
    exact Finset.single_le_sum (fun j _ => abs_nonneg (f s t j - f s 0 j - t * v s j)) (Finset.mem_univ i)
  have heq : f s t i - f s 0 i = (f s t i - f s 0 i - t * v s i) + t * v s i := by ring
  calc
    |f s t i - f s 0 i| ≤ |f s t i - f s 0 i - t * v s i| + |t * v s i| := by
      conv_lhs => rw [heq]
      exact abs_add_le _ _
    _ ≤ |t| * finiteDerivativeError f v t + |t| * |v s i| := by
      rw [abs_mul]
      exact add_le_add (herr.trans (finiteDerivativeError_bound f v s t)) le_rfl
    _ ≤ (D + 1) * |t| := by
      have h1 := mul_le_mul_of_nonneg_left ht.le (abs_nonneg t)
      have h2 := mul_le_mul_of_nonneg_left hvi (abs_nonneg t)
      nlinarith

variable [DecidableEq ι]

abbrev AdmissibleResidualState (ι : Type*) [Fintype ι] :=
  (R : Finset ι) × Fin (R.card + 1)

def uniformThresholdError (θ : ℝ → ι → ℝ) (h : ι → ℝ) : ℝ → ℝ :=
  finiteDerivativeError
    (fun s : AdmissibleResidualState ι => fun t => residualThresholdVector (θ t) s.1 s.2.val)
    (fun s : AdmissibleResidualState ι =>
      (residualCovariance (fun i => Real.exp (θ 0 i)) s.1 s.2.val).mulVec h)

set_option maxHeartbeats 1000000 in
theorem uniformThresholdError_tendsto (θ : ℝ → ι → ℝ) (h : ι → ℝ)
    (hθ : HasDerivAt θ h 0) : Tendsto (uniformThresholdError θ h) (𝓝[≠] 0) (𝓝 0) :=
  finiteDerivativeError_tendsto _ _ (fun s => residualThresholdVector_hasDerivAt θ h hθ
    s.1 s.2.val (by omega))

theorem uniformThresholdError_expansion (θ : ℝ → ι → ℝ) (h : ι → ℝ)
    (R : Finset ι) (r : ℕ) (hr : r ≤ R.card) (t : ℝ) :
    l1Norm (fun i => residualThresholdVector (θ t) R r i - residualThresholdVector (θ 0) R r i -
      t * (residualCovariance (fun j => Real.exp (θ 0 j)) R r).mulVec h i) ≤
      |t| * uniformThresholdError θ h t :=
  finiteDerivativeError_bound
    (fun s : AdmissibleResidualState ι => fun t => residualThresholdVector (θ t) s.1 s.2.val)
    (fun s : AdmissibleResidualState ι =>
      (residualCovariance (fun i => Real.exp (θ 0 i)) s.1 s.2.val).mulVec h)
    (⟨R, ⟨r, by omega⟩⟩ : AdmissibleResidualState ι) t

theorem residualThresholds_uniform_lipschitz (θ : ℝ → ι → ℝ) (h : ι → ℝ)
    (hθ : HasDerivAt θ h 0) :
    ∃ L : ℝ, 0 < L ∧ ∀ᶠ t in 𝓝[≠] (0 : ℝ), ∀ (R : Finset ι) (r : ℕ),
      r ≤ R.card → ∀ i ∈ R,
        |quotaThreshold (fun j => Real.exp (θ t j)) R r i -
          quotaThreshold (fun j => Real.exp (θ 0 j)) R r i| ≤ L * |t| := by
  obtain ⟨L, hL, hbound⟩ := finiteDerivative_local_lipschitz
    (fun s : AdmissibleResidualState ι => fun t => residualThresholdVector (θ t) s.1 s.2.val)
    (fun s : AdmissibleResidualState ι =>
      (residualCovariance (fun i => Real.exp (θ 0 i)) s.1 s.2.val).mulVec h)
    (fun s => residualThresholdVector_hasDerivAt θ h hθ s.1 s.2.val (by omega))
  refine ⟨L, hL, ?_⟩
  filter_upwards [hbound] with t ht
  intro R r hr i hi
  simpa only [residualThresholdVector, if_pos hi] using ht (⟨R, ⟨r, by omega⟩⟩ : AdmissibleResidualState ι) i

end
end CoefficientOne.Sampling
