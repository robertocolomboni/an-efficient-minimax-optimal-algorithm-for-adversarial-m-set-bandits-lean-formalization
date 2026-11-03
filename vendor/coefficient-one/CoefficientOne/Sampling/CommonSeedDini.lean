import CoefficientOne.Sampling.OutputMetric
import CoefficientOne.Sampling.DiniBound

/-! # From local common-seed distance estimates to a global segment bound

The distance function is not assumed differentiable. Its continuity is
derived from the local estimate before the scalar Dini theorem is applied.
-/

open Set Filter MeasureTheory
open scoped Topology
namespace CoefficientOne.Sampling
noncomputable section

variable {Ω ι : Type*} [MeasurableSpace Ω] [Fintype ι] [DecidableEq ι]
  (μ : Measure Ω) [IsFiniteMeasure μ]

def LocalSeedSlope (F : ℝ → Ω → Finset ι) (L s : ℝ) : Prop :=
  ∀ ε > 0, ∀ᶠ t in 𝓝[≠] (0 : ℝ),
    expectedOutputDistance μ (F s) (F (s + t)) / |t| ≤ L + ε

theorem localSeedSlope_distance (F : ℝ → Ω → Finset ι) (L s : ℝ)
    (hloc : LocalSeedSlope μ F L s) (ε : ℝ) (hε : 0 < ε) :
    ∀ᶠ z in 𝓝 s, expectedOutputDistance μ (F s) (F z) ≤ (L + ε) * |z - s| := by
  have ht := eventually_nhdsWithin_iff.mp (hloc ε hε)
  have hfull : ∀ᶠ t in 𝓝 (0 : ℝ),
      expectedOutputDistance μ (F s) (F (s + t)) ≤ (L + ε) * |t| := by
    filter_upwards [ht] with t ht
    by_cases hz : t = 0
    · subst t
      simp
    · exact (div_le_iff₀ (abs_pos.mpr hz)).mp (ht (by simpa using hz))
  have hshift : Tendsto (fun z : ℝ => z - s) (𝓝 s) (𝓝 (0 : ℝ)) := by
    simpa only [sub_self, id_eq] using
      (tendsto_id.sub_const s : Tendsto (fun z : ℝ => z - s) (𝓝 s) (𝓝 (s - s)))
  filter_upwards [hshift.eventually hfull] with z hz
  simpa only [add_sub_cancel] using hz

theorem expectedOutputDistance_abs_sub_le (F G H : Ω → Finset ι)
    (hF : Measurable F) (hG : Measurable G) (hH : Measurable H) :
    |expectedOutputDistance μ F G - expectedOutputDistance μ F H| ≤
      expectedOutputDistance μ G H := by
  have h1 := expectedOutputDistance_triangle μ hF hH hG
  have h2 := expectedOutputDistance_triangle μ hF hG hH
  rw [expectedOutputDistance_comm μ H G] at h1
  exact abs_le.mpr ⟨by linarith, by linarith⟩

theorem seedDistance_continuousAt_of_localSlope (F : ℝ → Ω → Finset ι)
    (hF : ∀ t, Measurable (F t)) (L s : ℝ) (hL : 0 ≤ L)
    (hloc : LocalSeedSlope μ F L s) :
    ContinuousAt (fun t => expectedOutputDistance μ (F 0) (F t)) s := by
  apply Metric.continuousAt_iff.mpr
  intro ε hε
  obtain ⟨δ, hδ, hδbound⟩ := Metric.eventually_nhds_iff.mp
    (localSeedSlope_distance μ F L s hloc 1 (by norm_num))
  have hLp : 0 < L + 1 := by linarith
  refine ⟨min δ (ε / (L + 1)), lt_min hδ (div_pos hε hLp), ?_⟩
  intro z hz
  have hzδ : dist z s < δ := (lt_min_iff.mp hz).1
  have hzε : |z - s| < ε / (L + 1) := by
    simpa only [Real.dist_eq] using (lt_min_iff.mp hz).2
  rw [Real.dist_eq]
  have habs := expectedOutputDistance_abs_sub_le μ (F 0) (F z) (F s) (hF 0) (hF z) (hF s)
  rw [expectedOutputDistance_comm μ (F z) (F s)] at habs
  apply lt_of_le_of_lt (habs.trans (hδbound hzδ))
  have hm := (lt_div_iff₀ hLp).mp hzε
  simpa only [mul_comm] using hm

theorem seedDistance_upperRightSlope (F : ℝ → Ω → Finset ι)
    (hF : ∀ t, Measurable (F t)) (L : ℝ)
    (hloc : ∀ s ∈ Icc (0 : ℝ) 1, LocalSeedSlope μ F L s) :
    HasUpperRightSlopeBound (fun t => expectedOutputDistance μ (F 0) (F t)) L 0 1 := by
  intro s hs r hr
  have hε : 0 < (r - L) / 2 := by linarith
  have hb := localSeedSlope_distance μ F L s (hloc s ⟨hs.1, hs.2.le⟩) _ hε
  filter_upwards [hb.filter_mono nhdsWithin_le_nhds, eventually_mem_nhdsWithin] with z hz hzs
  have hpos : 0 < z - s := sub_pos.mpr hzs
  have htri := expectedOutputDistance_triangle μ (hF 0) (hF s) (hF z)
  rw [abs_of_pos hpos] at hz
  rw [slope_def_field]
  apply (div_lt_iff₀ hpos).mpr
  have hm : (L + (r - L) / 2) * (z - s) < r * (z - s) := by
    exact mul_lt_mul_of_pos_right (by linarith) hpos
  linarith

/-- The Dini reduction for the exact common-seed expected distance. The
local slope is an explicit hypothesis here, to be discharged by the sampler
coupling theorem in the final interior application. -/
theorem commonSeed_dini_stretch (F : ℝ → Ω → Finset ι)
    (hF : ∀ t, Measurable (F t)) (L : ℝ) (hL : 0 ≤ L)
    (hloc : ∀ s ∈ Icc (0 : ℝ) 1, LocalSeedSlope μ F L s) :
    expectedOutputDistance μ (F 0) (F 1) ≤ L := by
  have hg : ContinuousOn (fun t => expectedOutputDistance μ (F 0) (F t)) (Icc (0 : ℝ) 1) :=
    fun s hs => (seedDistance_continuousAt_of_localSlope μ F hF L s hL (hloc s hs)).continuousWithinAt
  have h := dini_unit_interval_bound _ L hg (seedDistance_upperRightSlope μ F hF L hloc)
  simpa only [expectedOutputDistance_self, sub_zero] using h

end
end CoefficientOne.Sampling
