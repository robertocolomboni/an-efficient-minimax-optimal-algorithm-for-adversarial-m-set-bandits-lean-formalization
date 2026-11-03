import CoefficientOne.Sampling.InteriorSampler

/-! # Interior marginal segments and the covariance velocity identity -/
open scoped BigOperators Topology
open Set Filter EffectiveResistance MeasureTheory Matrix
namespace CoefficientOne.Sampling
noncomputable section
variable {n k : ℕ} [NeZero n]

def interiorSegmentVector (x y : interiorHypersimplex (Fin n) k) (s : ℝ) : Fin n → ℝ :=
  x.val + s • (y.val - x.val)

@[simp] theorem interiorSegmentVector_zero (x y : interiorHypersimplex (Fin n) k) :
    interiorSegmentVector x y 0 = x.val := by simp [interiorSegmentVector]

@[simp] theorem interiorSegmentVector_one (x y : interiorHypersimplex (Fin n) k) :
    interiorSegmentVector x y 1 = y.val := by simp [interiorSegmentVector]

theorem interiorSegmentVector_sum (x y : interiorHypersimplex (Fin n) k) (s : ℝ) :
    ∑ i, interiorSegmentVector x y s i = (k : ℝ) := by
  simp only [interiorSegmentVector, Pi.add_apply, Pi.smul_apply, Pi.sub_apply, smul_eq_mul,
    Finset.sum_add_distrib]
  rw [← Finset.mul_sum, Finset.sum_sub_distrib, x.property.2, y.property.2]
  ring

theorem interiorSegmentVector_mem (x y : interiorHypersimplex (Fin n) k)
    (s : ℝ) (hs : s ∈ Icc (0 : ℝ) 1) :
    interiorSegmentVector x y s ∈ interiorHypersimplex (Fin n) k := by
  refine ⟨?_, interiorSegmentVector_sum x y s⟩
  intro i
  have hx := x.property.1 i
  have hy := y.property.1 i
  change 0 < x.val i + s * (y.val i - x.val i) ∧
    x.val i + s * (y.val i - x.val i) < 1
  by_cases h0 : s = 0
  · simpa [h0] using hx
  · have hsp : 0 < s := lt_of_le_of_ne hs.1 (Ne.symm h0)
    have hlow := mul_nonneg (sub_nonneg.mpr hs.2) hx.1.le
    have hlow' := mul_pos hsp hy.1
    have hupp := mul_nonneg (sub_nonneg.mpr hs.2) (sub_nonneg.mpr hx.2.le)
    have hupp' := mul_pos hsp (sub_pos.mpr hy.2)
    constructor <;> nlinarith

theorem hasDerivAt_interiorSegmentVector (x y : interiorHypersimplex (Fin n) k) (s : ℝ) :
    HasDerivAt (interiorSegmentVector x y) (y.val - x.val) s := by
  convert (hasDerivAt_const s x.val).add ((hasDerivAt_id s).smul_const (y.val - x.val)) using 1 <;>
    first | rfl | simp

theorem interiorSegmentVector_shift (x y : interiorHypersimplex (Fin n) k) (s t : ℝ) :
    interiorSegmentVector x y (s + t) = interiorSegmentVector x y s + t • (y.val - x.val) := by
  ext i
  simp only [interiorSegmentVector, Pi.add_apply, Pi.smul_apply, Pi.sub_apply, smul_eq_mul]
  ring

theorem hasDerivAt_interiorSegmentShift (x y : interiorHypersimplex (Fin n) k) (s : ℝ) :
    HasDerivAt (fun t => interiorSegmentVector x y (s + t)) (y.val - x.val) 0 := by
  have he : (fun t => interiorSegmentVector x y (s + t)) =
      fun t => interiorSegmentVector x y s + t • (y.val - x.val) :=
    funext (interiorSegmentVector_shift x y s)
  rw [he]
  convert (hasDerivAt_const (0 : ℝ) (interiorSegmentVector x y s)).add
    ((hasDerivAt_id (0 : ℝ)).smul_const (y.val - x.val)) using 1 <;>
    first | rfl | simp

theorem interiorSegmentShift_eventually (x y : interiorHypersimplex (Fin n) k)
    (s : ℝ) (hs : s ∈ Icc (0 : ℝ) 1) :
    ∀ᶠ t in 𝓝 (0 : ℝ), interiorSegmentVector x y (s + t) ∈ interiorHypersimplex (Fin n) k := by
  have hcont := (hasDerivAt_interiorSegmentShift x y s).continuousAt
  have hmem := (interiorSegmentVector_mem x y s hs).1
  have hi (i : Fin n) : ∀ᶠ t in 𝓝 (0 : ℝ), interiorSegmentVector x y (s + t) i ∈ Ioo (0 : ℝ) 1 := by
    have hc := (continuous_apply i).continuousAt.comp hcont
    exact hc.eventually (isOpen_Ioo.mem_nhds (by simpa using hmem i))
  filter_upwards [Filter.eventually_all.mpr hi] with t ht
  exact ⟨ht, interiorSegmentVector_sum x y (s + t)⟩

def interiorSegmentParameter (x y : interiorHypersimplex (Fin n) k) (s t : ℝ) : Fin n → ℝ :=
  (parameterOfMarginal k (interiorSegmentVector x y (s + t))).val

theorem interiorSegmentParameter_hasDerivAt (hkpos : 1 ≤ k) (hktop : k < n)
    (x y : interiorHypersimplex (Fin n) k) (s : ℝ) (hs : s ∈ Icc (0 : ℝ) 1) :
    HasDerivAt (interiorSegmentParameter x y s) (deriv (interiorSegmentParameter x y s) 0) 0 := by
  have hp := parameterOfMarginal_hasFDerivAt hkpos (by simpa using hktop)
    (interiorSegmentVector x y s) (interiorSegmentVector_mem x y s hs)
  have hstart : interiorSegmentVector x y (s + 0) = interiorSegmentVector x y s := by rw [add_zero]
  rw [← hstart] at hp
  have hc := hp.comp_hasDerivAt 0 (hasDerivAt_interiorSegmentShift x y s)
  have hp' := (parameterSpace (Fin n)).subtypeL.hasFDerivAt.comp_hasDerivAt 0 hc
  convert hp'.differentiableAt.hasDerivAt using 1 <;> rfl

theorem interiorSegment_covariance_velocity (hkpos : 1 ≤ k) (hktop : k < n)
    (x y : interiorHypersimplex (Fin n) k) (s : ℝ) (hs : s ∈ Icc (0 : ℝ) 1) :
    covarianceMatrix (marginalWeights k (interiorSegmentVector x y s)) k *ᵥ
      deriv (interiorSegmentParameter x y s) 0 = y.val - x.val := by
  have h := parameterOfMarginal_path_velocity hkpos (by simpa using hktop)
    (fun t => interiorSegmentVector x y (s + t)) (y.val - x.val)
    (hasDerivAt_interiorSegmentShift x y s) (interiorSegmentShift_eventually x y s hs)
  unfold marginalWeights interiorSegmentParameter
  simpa only [add_zero] using h.symm

end
end CoefficientOne.Sampling
