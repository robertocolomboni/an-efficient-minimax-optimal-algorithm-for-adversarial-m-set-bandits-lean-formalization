import CoefficientOne.Sampling.Model
import Mathlib

/-! # The relative interior of the hypersimplex -/

open scoped BigOperators Topology
open Filter

namespace CoefficientOne.Sampling
noncomputable section

variable {ι : Type*} [Fintype ι] {k : ℕ}

theorem sum_eq_of_mem_affineSpan_hypersimplex (x : ι → ℝ)
    (hx : x ∈ affineSpan ℝ (hypersimplex ι k)) : ∑ i, x i = (k : ℝ) := by
  refine affineSpan_induction (p := fun x : ι → ℝ => ∑ i, x i = (k : ℝ)) hx
    (fun _ hz => hz.2) ?_
  intro c u v w hu hv hw
  change ∑ i, (c • (u - v) + w) i = (k : ℝ)
  simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, Pi.sub_apply,
    Finset.sum_add_distrib, ← Finset.mul_sum, Finset.sum_sub_distrib, hu, hv, hw]
  ring

theorem interiorHypersimplex_subset_intrinsicInterior :
    interiorHypersimplex ι k ⊆ intrinsicInterior ℝ (hypersimplex ι k) := by
  classical
  intro x hx
  have hxs : x ∈ hypersimplex ι k := interiorHypersimplex_subset hx
  let X : affineSpan ℝ (hypersimplex ι k) := ⟨x, subset_affineSpan ℝ _ hxs⟩
  let O : Set (affineSpan ℝ (hypersimplex ι k)) :=
    {z | ∀ i, 0 < z.val i ∧ z.val i < 1}
  have hO : IsOpen O := by
    simp only [O, Set.setOf_forall]
    apply isOpen_iInter_of_finite
    intro i
    have hc : Continuous (fun z : affineSpan ℝ (hypersimplex ι k) => z.val i) :=
      (continuous_apply i).comp continuous_subtype_val
    exact (isOpen_lt continuous_const hc).inter (isOpen_lt hc continuous_const)
  apply mem_intrinsicInterior.mpr
  refine ⟨X, ?_, rfl⟩
  apply mem_interior_iff_mem_nhds.mpr
  apply Filter.mem_of_superset (hO.mem_nhds (show X ∈ O from hx.1))
  intro z hz
  exact ⟨fun i => ⟨(hz i).1.le, (hz i).2.le⟩,
    sum_eq_of_mem_affineSpan_hypersimplex z.val z.property⟩

theorem intrinsicInterior_hypersimplex_eq (hkpos : 1 ≤ k) (hktop : k < Fintype.card ι) :
    intrinsicInterior ℝ (hypersimplex ι k) = interiorHypersimplex ι k := by
  apply Set.Subset.antisymm ?_ interiorHypersimplex_subset_intrinsicInterior
  intro x hx
  have hxs := intrinsicInterior_subset (𝕜 := ℝ) hx
  obtain ⟨X, hX, hXe⟩ := mem_intrinsicInterior.mp hx
  have hn : (0 : ℝ) < Fintype.card ι := by exact_mod_cast (show 0 < Fintype.card ι by omega)
  let u : ι → ℝ := fun _ => (k : ℝ) / Fintype.card ι
  have hui : ∀ i, 0 < u i ∧ u i < 1 := by
    intro i
    exact ⟨div_pos (by exact_mod_cast (show 0 < k by omega)) hn,
      (div_lt_one hn).mpr (by exact_mod_cast hktop)⟩
  have hu : u ∈ hypersimplex ι k := by
    refine ⟨fun i => ⟨(hui i).1.le, (hui i).2.le⟩, ?_⟩
    simp only [u, Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
    field_simp
  have hxa : x ∈ affineSpan ℝ (hypersimplex ι k) := subset_affineSpan ℝ _ hxs
  have hua : u ∈ affineSpan ℝ (hypersimplex ι k) := subset_affineSpan ℝ _ hu
  let f : ℝ → affineSpan ℝ (hypersimplex ι k) := fun t =>
    ⟨t • (x - u) + x, (affineSpan ℝ (hypersimplex ι k)).smul_vsub_vadd_mem t hxa hua hxa⟩
  have hf : Continuous f := by
    apply Continuous.subtype_mk
    change Continuous (fun t : ℝ => t • (x - u) + x)
    fun_prop
  have hf0 : f 0 = X := by
    apply Subtype.ext
    simpa [f] using hXe.symm
  have hevent : ∀ᶠ t : ℝ in 𝓝 0, (f t).val ∈ hypersimplex ι k := by
    have hft := hf.tendsto 0
    rw [hf0] at hft
    exact hft.eventually (mem_interior_iff_mem_nhds.mp hX)
  have hsmall := hevent.filter_mono (show 𝓝[>] (0 : ℝ) ≤ 𝓝 0 from nhdsWithin_le_nhds)
  obtain ⟨t, htmem, htpos⟩ := (hsmall.and self_mem_nhdsWithin).exists
  refine ⟨?_, hxs.2⟩
  intro i
  have hi := htmem.1 i
  change 0 ≤ t * (x i - u i) + x i ∧ t * (x i - u i) + x i ≤ 1 at hi
  have hi0 := (hxs.1 i).1
  have hi1 := (hxs.1 i).2
  have hy := hui i
  constructor
  · by_contra hbad
    have hzero : x i = 0 := le_antisymm (le_of_not_gt hbad) hi0
    rw [hzero] at hi
    nlinarith
  · by_contra hbad
    have hone : x i = 1 := le_antisymm hi1 (le_of_not_gt hbad)
    rw [hone] at hi
    nlinarith

end
end CoefficientOne.Sampling
