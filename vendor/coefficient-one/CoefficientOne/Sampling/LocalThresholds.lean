import CoefficientOne.Sampling.ParametrizationTheorem
import CoefficientOne.Sampling.ResidualNetwork
import CoefficientOne.Sampling.QuotaMonotonicity

/-!
# Differentiation of every conditional threshold

The threshold is first identified with the actual residual marginal, and its
derivative is then transported from the covariance on the remaining subtype.
-/

open scoped BigOperators Topology
open EffectiveResistance Filter

namespace CoefficientOne.Sampling
noncomputable section

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

theorem restricted_weighted_indicator_sum (w : ι → ℝ) (R : Finset ι) (r : ℕ)
    (hr : 0 < r) (i : ι) (hi : i ∈ R) :
    (∑ S ∈ R.powersetCard r, subsetWeight w S * indicator i S) =
      w i * restrictedElementary w (R.erase i) (r - 1) := by
  classical
  have hfilter := Finset.filter_powersetCard_subset {i} R r
    (Finset.singleton_subset_iff.mpr hi) (by simp only [Finset.card_singleton]; omega)
  simp only [Finset.singleton_subset_iff, Finset.card_singleton,
    Finset.sdiff_singleton_eq_erase] at hfilter
  simp only [indicator, mul_ite, mul_one, mul_zero, ← Finset.sum_filter]
  rw [hfilter, Finset.sum_image]
  · rw [restrictedElementary, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro T hT
    have hiT : i ∉ T := fun h => (Finset.notMem_erase i R) ((Finset.mem_powersetCard.mp hT).1 h)
    simp [Finset.union_singleton, subsetWeight, Finset.prod_insert hiT]
  · intro A hA B hB hab
    have hiA : i ∉ A := fun h => (Finset.notMem_erase i R) ((Finset.mem_powersetCard.mp hA).1 h)
    have hiB : i ∉ B := fun h => (Finset.notMem_erase i R) ((Finset.mem_powersetCard.mp hB).1 h)
    have hh := congrArg (fun S : Finset ι => S.erase i) hab
    simpa [Finset.union_singleton, hiA, hiB] using hh

theorem residualMean_eq_quotaThreshold (w : ι → ℝ) (hw : ∀ i, 0 < w i)
    (R : Finset ι) (r : ℕ) (hr : r ≤ R.card) (i : ι) (hi : i ∈ R) :
    residualMean w R r i = quotaThreshold w R r i := by
  by_cases hz : r = 0
  · subst r
    simp [residualMean, indicator]
  have hrpos : 0 < r := Nat.pos_of_ne_zero hz
  rw [quotaThreshold_eq_sequentialThreshold w hw R r hrpos hr i hi]
  unfold residualMean restrictedSum restrictedMass
  simp only [ite_mul, zero_mul, Finset.sum_ite_mem, Finset.univ_inter]
  simp_rw [div_mul_eq_mul_div]
  rw [← Finset.sum_div, restricted_weighted_indicator_sum w R r hrpos i hi]
  rfl

def residualThresholdVector (θ : ι → ℝ) (R : Finset ι) (r : ℕ) : ι → ℝ :=
  fun i => if i ∈ R then quotaThreshold (fun j => Real.exp (θ j)) R r i else 0

theorem residualThresholdVector_eq_residualMean (θ : ι → ℝ) (R : Finset ι) (r : ℕ)
    (hr : r ≤ R.card) : residualThresholdVector θ R r = residualMean (fun i => Real.exp (θ i)) R r := by
  funext i
  by_cases hi : i ∈ R
  · simp only [residualThresholdVector, if_pos hi]
    exact (residualMean_eq_quotaThreshold _ (fun j => Real.exp_pos (θ j)) R r hr i hi).symm
  · simp [residualThresholdVector, hi, residualMean_notMem _ R r i hi]

theorem residualThresholdVector_hasDerivAt (θ : ℝ → ι → ℝ) (h : ι → ℝ)
    (hθ : HasDerivAt θ h 0) (R : Finset ι) (r : ℕ) (hr : r ≤ R.card) :
    HasDerivAt (fun t => residualThresholdVector (θ t) R r)
      ((residualCovariance (fun i => Real.exp (θ 0 i)) R r).mulVec h) 0 := by
  apply hasDerivAt_pi.2
  intro i
  by_cases hi : i ∈ R
  · let ii : R := ⟨i, hi⟩
    have hrestrict : HasDerivAt (fun t : ℝ => fun j : R => θ t j.val)
        (fun j : R => h j.val) 0 := by
      apply hasDerivAt_pi.2
      intro j
      exact (hasFDerivAt_apply j.val (θ 0)).comp_hasDerivAt 0 hθ
    have hm := (exponentialMean_hasFDerivAt (ι := R) (by simpa using hr)
      (fun j : R => θ 0 j.val)).comp_hasDerivAt 0 hrestrict
    have hd := (hasFDerivAt_apply ii (exponentialMean r (fun j : R => θ 0 j.val))).comp_hasDerivAt 0 hm
    have hfun : (fun t => residualThresholdVector (θ t) R r i) =
        (fun t => exponentialMean r (fun j : R => θ t j.val) ii) := by
      funext t
      rw [residualThresholdVector_eq_residualMean _ R r hr]
      exact residualMean_subtype _ R r ii
    rw [hfun]
    convert hd using 1 <;> try rfl
    change _ = meanDerivative r (fun j : R => θ 0 j.val) (fun j : R => h j.val) ii
    rw [meanDerivative_apply (ι := R) (by simpa using hr)]
    exact residualCovariance_mulVec_subtype _ R r h ii
  · have hfun : (fun t => residualThresholdVector (θ t) R r i) = fun _ => (0 : ℝ) := by
      funext t
      simp [residualThresholdVector, hi]
    have hzero : (residualCovariance (fun j => Real.exp (θ 0 j)) R r).mulVec h i = 0 := by
      simp [Matrix.mulVec, dotProduct, residualCovariance_notMem_left _ R r i _ hi]
    rw [hfun, hzero]
    exact hasDerivAt_const 0 0

end
end CoefficientOne.Sampling
