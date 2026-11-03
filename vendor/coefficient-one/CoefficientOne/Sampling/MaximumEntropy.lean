import CoefficientOne.Sampling.HypersimplexFeasibility
import Mathlib.Analysis.SpecialFunctions.Log.NegMulLog

/-!
# The actual maximum-entropy law

Entropy is maximized on the compact fiber of real probability masses.
Existence and uniqueness are proved, not included as assumptions in a model.
-/

open scoped BigOperators Topology
open EffectiveResistance
open Filter

namespace CoefficientOne.Sampling

noncomputable section

variable {α : Type*} [Fintype α]

def finiteEntropy (p : α → ℝ) : ℝ := ∑ a, Real.negMulLog (p a)

theorem finiteEntropy_continuous : Continuous (finiteEntropy (α := α)) := by
  apply continuous_finset_sum
  intro a _
  exact Real.continuous_negMulLog.comp (continuous_apply a)

theorem finiteEntropy_strictConcave :
    StrictConcaveOn ℝ (stdSimplex ℝ α) finiteEntropy := by
  classical
  refine ⟨convex_stdSimplex ℝ α, ?_⟩
  intro p hp q hq hpq a b ha hb hab
  obtain ⟨i, hi⟩ : ∃ i, p i ≠ q i := Function.ne_iff.mp hpq
  have hle (j : α) :
      a * Real.negMulLog (p j) + b * Real.negMulLog (q j) ≤
        Real.negMulLog (a * p j + b * q j) :=
    Real.concaveOn_negMulLog.2 (hp.1 j) (hq.1 j) ha.le hb.le hab
  have hlt : a * Real.negMulLog (p i) + b * Real.negMulLog (q i) <
      Real.negMulLog (a * p i + b * q i) :=
    Real.strictConcaveOn_negMulLog.2 (hp.1 i) (hq.1 i) hi ha hb hab
  have hh := Finset.sum_lt_sum (fun j (_ : j ∈ (Finset.univ : Finset α)) => hle j)
    ⟨i, Finset.mem_univ i, hlt⟩
  simpa [finiteEntropy, Finset.sum_add_distrib, Finset.mul_sum] using hh

variable {ι : Type*} [Fintype ι] [DecidableEq ι] {k : ℕ}

theorem finiteEntropy_strictConcave_fiber (x : ι → ℝ) :
    StrictConcaveOn ℝ (marginalFiber (k := k) x) finiteEntropy :=
  ⟨marginalFiber_convex x, fun _ hp _ hq hpq _ _ ha hb hab =>
    finiteEntropy_strictConcave.2 hp.1 hq.1 hpq ha hb hab⟩

/-- Existence and uniqueness of the entropy maximizer on every marginal fiber. -/
theorem existsUnique_entropy_maximizer (x : ι → ℝ) (hx : x ∈ hypersimplex ι k) :
    ∃! p : RankSubset ι k → ℝ,
      p ∈ marginalFiber x ∧ IsMaxOn finiteEntropy (marginalFiber x) p := by
  obtain ⟨p, hp, hmax⟩ := (marginalFiber_isCompact x).exists_isMaxOn
    (marginalFiber_nonempty_of_mem_hypersimplex x hx) finiteEntropy_continuous.continuousOn
  refine ⟨p, ⟨hp, hmax⟩, ?_⟩
  intro q hq
  exact (finiteEntropy_strictConcave_fiber x).eq_of_isMaxOn hq.2 hmax hq.1 hp

def maximumEntropyMass (x : hypersimplex ι k) : RankSubset ι k → ℝ :=
  Classical.choose (existsUnique_entropy_maximizer x.val x.property)

theorem maximumEntropyMass_spec (x : hypersimplex ι k) :
    maximumEntropyMass x ∈ marginalFiber x.val ∧
      IsMaxOn finiteEntropy (marginalFiber x.val) (maximumEntropyMass x) :=
  (Classical.choose_spec (existsUnique_entropy_maximizer x.val x.property)).1

def maximumEntropyLaw (x : hypersimplex ι k) : FiniteLaw (RankSubset ι k) :=
  ⟨maximumEntropyMass x, (maximumEntropyMass_spec x).1.1⟩

theorem maximumEntropyLaw_mean (x : hypersimplex ι k) :
    lawMean (maximumEntropyLaw x) = x.val :=
  (maximumEntropyMass_spec x).1.2

theorem maximumEntropyLaw_maximal (x : hypersimplex ι k)
    (p : FiniteLaw (RankSubset ι k)) (hp : lawMean p = x.val) :
    finiteEntropy p.val ≤ finiteEntropy (maximumEntropyLaw x).val :=
  (maximumEntropyMass_spec x).2 ⟨p.property, hp⟩

theorem maximumEntropyLaw_unique (x : hypersimplex ι k)
    (p : FiniteLaw (RankSubset ι k)) (hp : lawMean p = x.val)
    (hmax : ∀ q : FiniteLaw (RankSubset ι k), lawMean q = x.val →
      finiteEntropy q.val ≤ finiteEntropy p.val) : p = maximumEntropyLaw x := by
  apply Subtype.ext
  apply (finiteEntropy_strictConcave_fiber x.val).eq_of_isMaxOn
      (y := (maximumEntropyLaw x).val)
  · intro q hq
    exact hmax ⟨q, hq.1⟩ hq.2
  · exact (maximumEntropyMass_spec x).2
  · exact ⟨p.property, hp⟩
  · exact (maximumEntropyMass_spec x).1

/-- A common positive perturbation size below all distances to the boundary. -/
theorem exists_uniform_interior_margin (x : ι → ℝ)
    (hx : ∀ i, 0 < x i ∧ x i < 1) :
    ∃ e : ℝ, 0 < e ∧ e < 1 ∧ ∀ i, e < x i ∧ e < 1 - x i := by
  classical
  let s : Finset ℝ := insert 1 ((Finset.univ.image x) ∪
    (Finset.univ.image (fun i => 1 - x i)))
  have hs : s.Nonempty := Finset.insert_nonempty _ _
  have hpos : ∀ z ∈ s, 0 < z := by
    intro z hz
    simp only [s, Finset.mem_insert, Finset.mem_union, Finset.mem_image,
      Finset.mem_univ, true_and] at hz
    rcases hz with rfl | ⟨i, rfl⟩ | ⟨i, rfl⟩
    · norm_num
    · exact (hx i).1
    · linarith [(hx i).2]
  have hmpos := hpos _ (Finset.min'_mem s hs)
  have hm1 : s.min' hs ≤ 1 := Finset.min'_le _ _ (by simp [s])
  refine ⟨s.min' hs / 2, by positivity, by linarith, ?_⟩
  intro i
  have hmi : s.min' hs ≤ x i := Finset.min'_le _ _ (by simp [s])
  have hmj : s.min' hs ≤ 1 - x i := Finset.min'_le _ _ (by simp [s])
  constructor <;> linarith

/-- Each atom receives positive mass in some law in an interior fiber. -/
theorem interior_fiber_positive_at_atom (x : ι → ℝ)
    (hx : x ∈ interiorHypersimplex ι k) (S : RankSubset ι k) :
    ∃ p ∈ marginalFiber x, 0 < p S := by
  classical
  obtain ⟨e, he, he1, hex⟩ := exists_uniform_interior_margin x hx.1
  let y : ι → ℝ := fun i => (x i - e * indicator i S.val) / (1 - e)
  have hden : 0 < 1 - e := sub_pos.mpr he1
  have hy : y ∈ hypersimplex ι k := by
    constructor
    · intro i
      have hi := hx.1 i
      have hei := hex i
      dsimp [y]
      by_cases hS : i ∈ S.val
      · simp only [indicator, if_pos hS, mul_one]
        exact ⟨div_nonneg (by linarith) hden.le,
          (div_le_one hden).mpr (by linarith)⟩
      · simp only [indicator, if_neg hS, mul_zero, sub_zero]
        exact ⟨div_nonneg hi.1.le hden.le,
          (div_le_one hden).mpr (by linarith)⟩
    · simp only [y, ← Finset.sum_div, Finset.sum_sub_distrib, ← Finset.mul_sum,
        sum_indicator, hx.2]
      field_simp
  obtain ⟨q, hq⟩ := marginalFiber_nonempty_of_mem_hypersimplex y hy
  let p : RankSubset ι k → ℝ := (1 - e) • q + e • Pi.single S 1
  have hp : p ∈ stdSimplex ℝ (RankSubset ι k) :=
    (convex_stdSimplex ℝ (RankSubset ι k)) hq.1 (single_mem_stdSimplex ℝ S)
      hden.le he.le (by ring)
  refine ⟨p, ⟨hp, ?_⟩, ?_⟩
  · ext i
    have hatom : massMeanLinear (ι := ι) (k := k) (Pi.single S 1) i =
        indicator i S.val := by simp [massMeanLinear, Pi.single_apply]
    simp only [p, map_add, map_smul, Pi.add_apply, Pi.smul_apply, smul_eq_mul,
      hq.2, hatom, y]
    field_simp
    ring
  · have hqnonneg : 0 ≤ q S := hq.1.1 S
    dsimp [p]
    simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, Pi.single_eq_same, mul_one]
    positivity

/-- Averaging the preceding atomwise laws gives a law with full support. -/
theorem interior_fiber_exists_fullSupport (x : ι → ℝ)
    (hx : x ∈ interiorHypersimplex ι k) :
    ∃ p ∈ marginalFiber (k := k) x, ∀ S, 0 < p S := by
  classical
  have hnonempty : Nonempty (RankSubset ι k) := by
    obtain ⟨p, hp⟩ := marginalFiber_nonempty_of_mem_hypersimplex x
      (interiorHypersimplex_subset hx)
    by_contra hn
    haveI : IsEmpty (RankSubset ι k) := not_nonempty_iff.mp hn
    have := hp.1.2
    simp at this
  letI := hnonempty
  choose p hp hpos using interior_fiber_positive_at_atom x hx
  let c : ℝ := (Fintype.card (RankSubset ι k) : ℝ)⁻¹
  have hc : 0 < c := inv_pos.mpr (by exact_mod_cast Fintype.card_pos)
  have hsumc : ∑ _ : RankSubset ι k, c = 1 := by
    simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, c]
    exact mul_inv_cancel₀ (by exact_mod_cast ne_of_gt (Fintype.card_pos (α := RankSubset ι k)))
  let q : RankSubset ι k → ℝ := fun S => ∑ T, c * p T S
  have hq : q ∈ stdSimplex ℝ (RankSubset ι k) := by
    constructor
    · intro S
      exact Finset.sum_nonneg fun T _ => mul_nonneg hc.le ((hp T).1.1 S)
    · simp only [q]
      rw [Finset.sum_comm]
      calc
        _ = ∑ _T : RankSubset ι k, c := by
          apply Finset.sum_congr rfl
          intro T _
          rw [← Finset.mul_sum, (hp T).1.2, mul_one]
        _ = 1 := hsumc
  refine ⟨q, ⟨hq, ?_⟩, ?_⟩
  · ext i
    simp only [massMeanLinear_apply, q, Finset.sum_mul]
    rw [Finset.sum_comm]
    calc
      _ = ∑ T, c * massMeanLinear (p T) i := by
        apply Finset.sum_congr rfl
        intro T _
        simp [massMeanLinear, Finset.mul_sum, mul_assoc]
      _ = ∑ _T : RankSubset ι k, c * x i := by simp_rw [fun T => (hp T).2]
      _ = x i := by rw [← Finset.sum_mul, hsumc, one_mul]
  · intro S
    apply Finset.sum_pos'
    · intro T _; exact mul_nonneg hc.le ((hp T).1.1 S)
    · exact ⟨S, Finset.mem_univ _, mul_pos hc (hpos S)⟩

/-- At a missing atom, mixing gains an additional `-t log t` contribution.
Concavity bounds the contributions of all other atoms from below. -/
theorem finiteEntropy_mix_gain (p q : α → ℝ)
    (hp : ∀ a, 0 ≤ p a) (hq : ∀ a, 0 ≤ q a) (a₀ : α) (hp₀ : p a₀ = 0)
    (t : ℝ) (ht : 0 ≤ t) (ht1 : t ≤ 1) :
    (1 - t) * finiteEntropy p + t * finiteEntropy q + q a₀ * Real.negMulLog t ≤
      finiteEntropy ((1 - t) • p + t • q) := by
  classical
  have hterm (a : α) :
      (1 - t) * Real.negMulLog (p a) + t * Real.negMulLog (q a) +
        (if a = a₀ then q a₀ * Real.negMulLog t else 0) ≤
      Real.negMulLog ((1 - t) * p a + t * q a) := by
    by_cases h : a = a₀
    · subst a
      simp only [hp₀, Real.negMulLog_zero, mul_zero, zero_add, if_true,
        Real.negMulLog_mul]
      ring_nf
      exact le_rfl
    · simp only [if_neg h, add_zero]
      exact Real.concaveOn_negMulLog.2 (hp a) (hq a) (by linarith) ht (by ring)
  have hh := Finset.sum_le_sum (fun a (_ : a ∈ (Finset.univ : Finset α)) => hterm a)
  simpa [finiteEntropy, Finset.sum_add_distrib, Finset.mul_sum] using hh

theorem finiteEntropy_mix_slope_lower (p q : α → ℝ)
    (hp : ∀ a, 0 ≤ p a) (hq : ∀ a, 0 ≤ q a) (a₀ : α) (hp₀ : p a₀ = 0)
    (t : ℝ) (ht : 0 < t) (ht1 : t ≤ 1) :
    finiteEntropy q - finiteEntropy p - q a₀ * Real.log t ≤
      (finiteEntropy ((1 - t) • p + t • q) - finiteEntropy p) / t := by
  have hh := finiteEntropy_mix_gain p q hp hq a₀ hp₀ t ht.le ht1
  rw [Real.negMulLog_def] at hh
  apply (le_div_iff₀ ht).mpr
  nlinarith

/-- The entropy directional quotient really diverges at a missing atom. -/
theorem finiteEntropy_mix_slope_tendsto_atTop (p q : α → ℝ)
    (hp : ∀ a, 0 ≤ p a) (hq : ∀ a, 0 ≤ q a) (a₀ : α)
    (hp₀ : p a₀ = 0) (hq₀ : 0 < q a₀) :
    Tendsto (fun t : ℝ =>
      (finiteEntropy ((1 - t) • p + t • q) - finiteEntropy p) / t)
      (𝓝[>] 0) atTop := by
  apply tendsto_atTop.2
  intro b
  have hlog : ∀ᶠ t : ℝ in 𝓝[>] 0,
      Real.log t ≤ (finiteEntropy q - finiteEntropy p - b) / q a₀ :=
    Real.tendsto_log_nhdsGT_zero.eventually (eventually_le_atBot _)
  have hpos : ∀ᶠ t : ℝ in 𝓝[>] 0, 0 < t := self_mem_nhdsWithin
  have hsmall : ∀ᶠ t : ℝ in 𝓝[>] 0, t < 1 := by
    have h : ∀ᶠ t : ℝ in 𝓝 0, t < 1 := Iio_mem_nhds (by norm_num)
    exact h.filter_mono nhdsWithin_le_nhds
  filter_upwards [hlog, hpos, hsmall] with t hlog ht ht1
  have hmul := (le_div_iff₀ hq₀).mp hlog
  have hlow := finiteEntropy_mix_slope_lower p q hp hq a₀ hp₀ t ht ht1.le
  nlinarith

/-- The entropy maximizer has positive mass at every atom for interior inputs. -/
theorem maximumEntropyLaw_fullSupport (x : hypersimplex ι k)
    (hx : ∀ i, 0 < x.val i ∧ x.val i < 1) (S : RankSubset ι k) :
    0 < (maximumEntropyLaw x).val S := by
  classical
  obtain ⟨q, hq, hqpos⟩ := interior_fiber_exists_fullSupport x.val ⟨hx, x.property.2⟩
  let p := (maximumEntropyLaw x).val
  have hp : p ∈ marginalFiber x.val := (maximumEntropyMass_spec x).1
  by_contra hn
  have hpS : p S = 0 := le_antisymm (le_of_not_gt hn) (hp.1.1 S)
  have hlim := finiteEntropy_mix_slope_tendsto_atTop p q hp.1.1 hq.1.1 S hpS (hqpos S)
  have hlarge : ∀ᶠ t : ℝ in 𝓝[>] 0,
      1 < (finiteEntropy ((1 - t) • p + t • q) - finiteEntropy p) / t :=
    hlim.eventually (eventually_gt_atTop 1)
  have hpos : ∀ᶠ t : ℝ in 𝓝[>] 0, 0 < t := self_mem_nhdsWithin
  have hsmall : ∀ᶠ t : ℝ in 𝓝[>] 0, t < 1 := by
    have h : ∀ᶠ t : ℝ in 𝓝 0, t < 1 := Iio_mem_nhds (by norm_num)
    exact h.filter_mono nhdsWithin_le_nhds
  obtain ⟨t, ht, ht1, hlarge⟩ := (hpos.and (hsmall.and hlarge)).exists
  have hmix : (1 - t) • p + t • q ∈ marginalFiber x.val :=
    (marginalFiber_convex x.val) hp hq (by linarith) ht.le (by ring)
  have hmax := (maximumEntropyMass_spec x).2 hmix
  have hnonpos : (finiteEntropy ((1 - t) • p + t • q) - finiteEntropy p) / t ≤ 0 :=
    div_nonpos_of_nonpos_of_nonneg (sub_nonpos.mpr hmax) ht.le
  linarith

end
end CoefficientOne.Sampling
