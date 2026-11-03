import CoefficientOne.Sampling.Parametrization

/-!
# Radial continuity of the maximum-entropy law

Compactness gives cluster points. Feasible mixtures approximate the boundary
maximizer, and continuity and uniqueness of entropy identify every cluster point.
-/

open scoped BigOperators Topology
open EffectiveResistance Filter

namespace CoefficientOne.Sampling
noncomputable section

variable {ι : Type*} [Fintype ι] [DecidableEq ι] {k : ℕ}

theorem maximumEntropyMass_tendsto_of_comparison {β : Type*} (l : Filter β)
    (xs : β → hypersimplex ι k) (x : hypersimplex ι k)
    (hxs : Tendsto (fun t => (xs t).val) l (𝓝 x.val))
    (q : β → RankSubset ι k → ℝ)
    (hq : ∀ᶠ t in l, q t ∈ marginalFiber (xs t).val)
    (hqt : Tendsto q l (𝓝 (maximumEntropyMass x))) :
    Tendsto (fun t => maximumEntropyMass (xs t)) l (𝓝 (maximumEntropyMass x)) := by
  apply (isCompact_stdSimplex ℝ (RankSubset ι k)).tendsto_nhds_of_unique_mapClusterPt
    (Eventually.of_forall fun t => (maximumEntropyMass_spec (xs t)).1.1)
  intro p hp hcluster
  obtain ⟨U, hUl, hUp⟩ := mapClusterPt_iff_ultrafilter.mp hcluster
  have hmeanp : massMeanLinear p = x.val := by
    have hpmean := ((massMeanLinear (ι := ι) (k := k)).continuous_of_finiteDimensional.tendsto p).comp hUp
    have hxmean : Tendsto (fun t => massMeanLinear (maximumEntropyMass (xs t))) U (𝓝 x.val) := by
      have heq : (fun t => massMeanLinear (maximumEntropyMass (xs t))) =
          (fun t => (xs t).val) := by
        funext t
        exact (maximumEntropyMass_spec (xs t)).1.2
      rw [heq]
      exact hxs.mono_left hUl
    exact tendsto_nhds_unique hpmean hxmean
  have hH : finiteEntropy (maximumEntropyMass x) ≤ finiteEntropy p := by
    apply le_of_tendsto_of_tendsto
      (finiteEntropy_continuous.continuousAt.tendsto.comp (hqt.mono_left hUl))
      (finiteEntropy_continuous.continuousAt.tendsto.comp hUp)
    filter_upwards [hq.filter_mono hUl] with t ht
    exact (maximumEntropyMass_spec (xs t)).2 ht
  have hpmax : IsMaxOn finiteEntropy (marginalFiber x.val) p := by
    intro r hr
    exact ((maximumEntropyMass_spec x).2 hr).trans hH
  exact (finiteEntropy_strictConcave_fiber x.val).eq_of_isMaxOn hpmax
    (maximumEntropyMass_spec x).2 ⟨hp, hmeanp⟩ (maximumEntropyMass_spec x).1

def marginalSegment (x y : hypersimplex ι k) (t : unitInterval) : hypersimplex ι k :=
  ⟨(1 - (t : ℝ)) • x.val + (t : ℝ) • y.val, by
    refine ⟨fun i => ⟨?_, ?_⟩, ?_⟩
    · exact add_nonneg (mul_nonneg (sub_nonneg.mpr t.property.2) (x.property.1 i).1)
        (mul_nonneg t.property.1 (y.property.1 i).1)
    · change (1 - (t : ℝ)) * x.val i + (t : ℝ) * y.val i ≤ 1
      have h1 := mul_le_mul_of_nonneg_left (x.property.1 i).2 (sub_nonneg.mpr t.property.2)
      have h2 := mul_le_mul_of_nonneg_left (y.property.1 i).2 t.property.1
      linarith
    · simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, Finset.sum_add_distrib,
        ← Finset.mul_sum, x.property.2, y.property.2]
      ring⟩

@[simp] theorem marginalSegment_zero (x y : hypersimplex ι k) : marginalSegment x y 0 = x := by
  apply Subtype.ext
  simp [marginalSegment]

theorem maximumEntropyMass_segment_tendsto_zero (x y : hypersimplex ι k) :
    Tendsto (fun t : unitInterval => maximumEntropyMass (marginalSegment x y t))
      (𝓝 0) (𝓝 (maximumEntropyMass x)) := by
  let q : unitInterval → RankSubset ι k → ℝ := fun t =>
    (1 - (t : ℝ)) • maximumEntropyMass x + (t : ℝ) • maximumEntropyMass y
  apply maximumEntropyMass_tendsto_of_comparison (𝓝 (0 : unitInterval))
    (marginalSegment x y) x ?_ q ?_ ?_
  · have hc : Continuous (fun t : unitInterval => (marginalSegment x y t).val) := by
      change Continuous (fun t : unitInterval => (1 - (t : ℝ)) • x.val + (t : ℝ) • y.val)
      fun_prop
    simpa only [marginalSegment_zero] using hc.tendsto 0
  · apply Eventually.of_forall
    intro t
    refine ⟨(convex_stdSimplex ℝ (RankSubset ι k))
      (maximumEntropyMass_spec x).1.1 (maximumEntropyMass_spec y).1.1
      (sub_nonneg.mpr t.property.2) t.property.1 (by ring), ?_⟩
    change massMeanLinear ((1 - (t : ℝ)) • maximumEntropyMass x +
      (t : ℝ) • maximumEntropyMass y) = _
    simp only [map_add, map_smul, (maximumEntropyMass_spec x).1.2,
      (maximumEntropyMass_spec y).1.2]
    rfl
  · have hc : Continuous q := by dsimp [q]; fun_prop
    simpa [q] using hc.tendsto 0

/-- The finite-space total variation distance, in real mass coordinates. -/
def finiteTotalVariation {α : Type*} [Fintype α] (p q : α → ℝ) : ℝ :=
  (1 / 2 : ℝ) * ∑ a, |p a - q a|

theorem finiteTotalVariation_continuous_right {α : Type*} [Fintype α] (q : α → ℝ) :
    Continuous (fun p : α → ℝ => finiteTotalVariation p q) := by
  unfold finiteTotalVariation
  fun_prop

@[simp] theorem finiteTotalVariation_self {α : Type*} [Fintype α] (p : α → ℝ) :
    finiteTotalVariation p p = 0 := by simp [finiteTotalVariation]

theorem maximumEntropyLaw_segment_totalVariation (x y : hypersimplex ι k) :
    Tendsto (fun t : unitInterval => finiteTotalVariation
      (maximumEntropyLaw (marginalSegment x y t)).val (maximumEntropyLaw x).val)
      (𝓝 0) (𝓝 0) := by
  have hh := (finiteTotalVariation_continuous_right (maximumEntropyMass x)).continuousAt.tendsto.comp
    (maximumEntropyMass_segment_tendsto_zero x y)
  simpa only [finiteTotalVariation_self, maximumEntropyLaw, Function.comp_def] using hh

def uniformMarginal (k : ℕ) (hk : k ≤ Fintype.card ι) : hypersimplex ι k :=
  ⟨fun _ => (k : ℝ) / Fintype.card ι, by
    refine ⟨fun i => ⟨div_nonneg (Nat.cast_nonneg k) (Nat.cast_nonneg _), ?_⟩, ?_⟩
    · haveI : Nonempty ι := ⟨i⟩
      apply (div_le_one (Nat.cast_pos.mpr Fintype.card_pos)).mpr
      exact_mod_cast hk
    · by_cases hn : Fintype.card ι = 0
      · have hk0 : k = 0 := by omega
        simp [hk0]
      · have hn' : (Fintype.card ι : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr hn
        simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
        field_simp⟩

theorem uniformMarginal_mem_interior (hkpos : 1 ≤ k) (hktop : k < Fintype.card ι) :
    (uniformMarginal k hktop.le).val ∈ interiorHypersimplex ι k := by
  refine ⟨?_, (uniformMarginal k hktop.le).property.2⟩
  intro i
  have hn : (0 : ℝ) < Fintype.card ι := by exact_mod_cast (show 0 < Fintype.card ι by omega)
  exact ⟨div_pos (by exact_mod_cast (show 0 < k by omega)) hn,
    (div_lt_one hn).mpr (by exact_mod_cast hktop)⟩

def radialMarginal (x : hypersimplex ι k) (t : unitInterval) : hypersimplex ι k :=
  marginalSegment x (uniformMarginal k (rank_le_card_of_mem_hypersimplex x)) t

theorem radialMarginal_mem_interior (hkpos : 1 ≤ k) (hktop : k < Fintype.card ι)
    (x : hypersimplex ι k) (t : unitInterval) (ht : 0 < (t : ℝ)) :
    (radialMarginal x t).val ∈ interiorHypersimplex ι k := by
  refine ⟨?_, (radialMarginal x t).property.2⟩
  intro i
  have hy := (uniformMarginal_mem_interior (ι := ι) hkpos hktop).1 i
  have hx := x.property.1 i
  change 0 < (1 - (t : ℝ)) * x.val i + (t : ℝ) * ((k : ℝ) / Fintype.card ι) ∧
    (1 - (t : ℝ)) * x.val i + (t : ℝ) * ((k : ℝ) / Fintype.card ι) < 1
  change 0 < (k : ℝ) / Fintype.card ι ∧ (k : ℝ) / Fintype.card ι < 1 at hy
  have ht1 : 0 ≤ 1 - (t : ℝ) := sub_nonneg.mpr t.property.2
  constructor
  · exact add_pos_of_nonneg_of_pos (mul_nonneg ht1 hx.1) (mul_pos ht hy.1)
  · have hp := mul_pos ht (sub_pos.mpr hy.2)
    have hn := mul_nonneg ht1 (sub_nonneg.mpr hx.2)
    nlinarith

theorem maximumEntropyMass_radial_tendsto_zero (x : hypersimplex ι k) :
    Tendsto (fun t : unitInterval => maximumEntropyMass (radialMarginal x t))
      (𝓝 0) (𝓝 (maximumEntropyMass x)) :=
  maximumEntropyMass_segment_tendsto_zero x _

theorem maximumEntropyLaw_radial_totalVariation (x : hypersimplex ι k) :
    Tendsto (fun t : unitInterval => finiteTotalVariation
      (maximumEntropyLaw (radialMarginal x t)).val (maximumEntropyLaw x).val)
      (𝓝 0) (𝓝 0) := maximumEntropyLaw_segment_totalVariation x _

end
end CoefficientOne.Sampling
