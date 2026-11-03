import Mathlib.Analysis.LocallyConvex.Separation
import Mathlib.Analysis.Convex.Function
import Mathlib.Topology.Order.Compact
import Mathlib.Tactic

/-! # Finite convex Slater duality from geometric separation

The argument separates the open upper image of the perturbed objective and
constraints. Strict feasibility forces a nonzero objective coefficient; its
normalization gives nonnegative multipliers and an attained dual certificate.
No property of the m-set projection objective is assumed in this module.
-/

namespace MsetsPaper.Upper.FiniteSlater

open Set Filter
open scoped BigOperators Topology

noncomputable section

variable {E I : Type*} [AddCommGroup E] [Module ℝ E] [Fintype I] [DecidableEq I]

def upperImage (C : Set E) (F : E → I → ℝ) : Set (I → ℝ) :=
  {u | ∃ x ∈ C, ∀ i, F x i < u i}

theorem upperImage_convex (C : Set E) (F : E → I → ℝ)
    (hC : Convex ℝ C) (hF : ∀ i, ConvexOn ℝ C (fun x => F x i)) :
    Convex ℝ (upperImage C F) := by
  rintro u ⟨x, hx, hu⟩ v ⟨y, hy, hv⟩ a b ha hb hab
  refine ⟨a • x + b • y, hC hx hy ha hb hab, ?_⟩
  intro i
  have hc := (hF i).2 hx hy ha hb hab
  change F (a • x + b • y) i ≤ a * F x i + b * F y i at hc
  change F (a • x + b • y) i < a * u i + b * v i
  have hux : 0 < u i - F x i := sub_pos.mpr (hu i)
  have hvy : 0 < v i - F y i := sub_pos.mpr (hv i)
  have hapos : 0 < a ∨ 0 < b := by rcases eq_or_lt_of_le ha with heq | hlt; right; linarith; exact Or.inl hlt
  rcases hapos with hapos | hbpos
  · nlinarith [mul_pos hapos hux, mul_nonneg hb hvy.le]
  · nlinarith [mul_nonneg ha hux.le, mul_pos hbpos hvy]

theorem upperImage_isOpen (C : Set E) (F : E → I → ℝ) : IsOpen (upperImage C F) := by
  apply isOpen_iff_mem_nhds.mpr
  rintro u ⟨x, hx, hu⟩
  have hi (i : I) : ∀ᶠ v in 𝓝 u, F x i < v i :=
    (isOpen_lt continuous_const (continuous_apply i)).mem_nhds (hu i)
  filter_upwards [eventually_all.mpr hi] with v hv
  exact ⟨x, hx, hv⟩

theorem linear_apply_eq_sum (l : StrongDual ℝ (I → ℝ)) (u : I → ℝ) :
    l u = ∑ i, u i * l (Pi.single i 1) := by
  have hu : u = ∑ i, u i • Pi.single i (1 : ℝ) := by
    ext j
    simp [Pi.single_apply]
  nth_rw 1 [hu]
  rw [map_sum]
  simp only [map_smul, smul_eq_mul]

theorem linear_single (l : StrongDual ℝ (I → ℝ)) (i : I) (t : ℝ) :
    l (Pi.single i t) = t * l (Pi.single i 1) := by
  have heq : Pi.single i t = t • Pi.single i (1 : ℝ) := by ext j; by_cases h : j = i <;> simp [h]
  rw [heq, map_smul, smul_eq_mul]

/-- Separation supplies nonnegative coefficients on every upward direction. -/
theorem separator_coeff_nonneg (C : Set E) (F : E → I → ℝ)
    (x₀ : E) (hx₀ : x₀ ∈ C) (l : StrongDual ℝ (I → ℝ))
    (hl : ∀ u ∈ upperImage C F, 0 < l u) (i : I) :
    0 ≤ l (Pi.single i 1) := by
  let u : I → ℝ := fun j => F x₀ j + 1
  have hu : u ∈ upperImage C F := ⟨x₀, hx₀, fun _ => by dsimp [u]; linarith⟩
  have hpos := hl u hu
  by_contra hn
  have hn' : l (Pi.single i 1) < 0 := lt_of_not_ge hn
  let t : ℝ := -l u / l (Pi.single i 1) + 1
  have ht : 0 ≤ t := by
    have : 0 < -l u / l (Pi.single i 1) := div_pos_of_neg_of_neg (by linarith) hn'
    dsimp [t]
    linarith
  have hv : u + t • Pi.single i (1 : ℝ) ∈ upperImage C F := by
    refine ⟨x₀, hx₀, ?_⟩
    intro j
    by_cases hj : j = i
    · subst j; simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, Pi.single_eq_same, mul_one]
      dsimp [u]; linarith
    · simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, Pi.single_eq_of_ne hj, mul_zero, add_zero]
      dsimp [u]
      linarith
  have hp := hl _ hv
  rw [map_add, map_smul, smul_eq_mul] at hp
  have heq : t * l (Pi.single i 1) = -l u + l (Pi.single i 1) := by
    dsimp [t]
    field_simp [ne_of_lt hn'] <;> ring
  linarith

theorem separator_boundary_nonneg (C : Set E) (F : E → I → ℝ)
    (l : StrongDual ℝ (I → ℝ)) (hl : ∀ u ∈ upperImage C F, 0 < l u)
    (x : E) (hx : x ∈ C) : 0 ≤ l (F x) := by
  have hcont : Continuous (fun t : ℝ => l (fun i => F x i + t)) := by fun_prop
  have hlim : Tendsto (fun t : ℝ => l (fun i => F x i + t)) (𝓝[>] 0) (𝓝 (l (F x))) := by
    simpa using (hcont.tendsto 0).mono_left nhdsWithin_le_nhds
  apply ge_of_tendsto hlim
  filter_upwards [self_mem_nhdsWithin] with t ht
  exact (hl _ ⟨x, hx, fun i => by change F x i < F x i + t; exact lt_add_of_pos_right _ ht⟩).le

/-- General finite convex Slater theorem at an attained primal minimum.
The conclusion is an attained Lagrangian certificate, including slackness. -/
theorem multipliers_of_minimum (C : Set E) (hC : Convex ℝ C)
    (f : E → ℝ) (hf : ConvexOn ℝ C f)
    (g : I → E → ℝ) (hg : ∀ i, ConvexOn ℝ C (g i))
    (xstar : E) (hxstar : xstar ∈ C) (hfeasible : ∀ i, g i xstar ≤ 0)
    (hmin : ∀ x ∈ C, (∀ i, g i x ≤ 0) → f xstar ≤ f x)
    (x₀ : E) (hx₀ : x₀ ∈ C) (hstrict : ∀ i, g i x₀ < 0) :
    ∃ lam : I → ℝ, (∀ i, 0 ≤ lam i) ∧
      (∀ x ∈ C, f xstar ≤ f x + ∑ i, lam i * g i x) ∧
      (∑ i, lam i * g i xstar) = 0 := by
  let F : E → Option I → ℝ := fun x j =>
    match j with
    | none => f x - f xstar
    | some i => g i x
  have hF : ∀ j, ConvexOn ℝ C (fun x => F x j) := by
    intro j
    cases j with
    | none => exact hf.sub (concaveOn_const (f xstar) hC)
    | some i => exact hg i
  have hnot : (0 : Option I → ℝ) ∉ upperImage C F := by
    rintro ⟨x, hx, hlt⟩
    have hcost := hlt none
    have hcons (i : I) : g i x ≤ 0 := (hlt (some i)).le
    have := hmin x hx hcons
    change f x - f xstar < 0 at hcost
    linarith
  obtain ⟨l, hl⟩ := geometric_hahn_banach_point_open
    (upperImage_convex C F hC hF) (upperImage_isOpen C F) hnot
  simp only [map_zero] at hl
  have hc (j : Option I) : 0 ≤ l (Pi.single j 1) :=
    separator_coeff_nonneg C F x₀ hx₀ l hl j
  let t : ℝ := max (F x₀ none) 0 + 1
  have ht : 0 < t := by dsimp [t]; linarith [le_max_right (F x₀ none) 0]
  have hu : Pi.single none t ∈ upperImage C F := by
    refine ⟨x₀, hx₀, ?_⟩
    intro j
    cases j with
    | none => simp only [Pi.single_eq_same]; dsimp [t]; linarith [le_max_left (F x₀ none) 0]
    | some i => simpa only [F, Pi.single_eq_of_ne (Option.some_ne_none i)] using hstrict i
  have hobj : 0 < l (Pi.single (none : Option I) 1) := by
    have hp := hl _ hu
    rw [linear_single] at hp
    rcases mul_pos_iff.mp hp with hp | hp
    · exact hp.2
    · exact (not_lt_of_ge ht.le hp.1).elim
  let lam : I → ℝ := fun i => l (Pi.single (some i) 1) / l (Pi.single none 1)
  have hlam (i : I) : 0 ≤ lam i := div_nonneg (hc (some i)) hobj.le
  have hlag (x : E) (hx : x ∈ C) : f xstar ≤ f x + ∑ i, lam i * g i x := by
    have hb := separator_boundary_nonneg C F l hl x hx
    rw [linear_apply_eq_sum, Fintype.sum_option] at hb
    simp only [F] at hb
    have heq : (∑ i, g i x * l (Pi.single (some i) 1)) =
        l (Pi.single none 1) * ∑ i, lam i * g i x := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro i _
      dsimp [lam]
      field_simp [ne_of_gt hobj] <;> ring
    rw [heq] at hb
    nlinarith
  refine ⟨lam, hlam, hlag, ?_⟩
  apply le_antisymm
  · exact Finset.sum_nonpos fun i _ => mul_nonpos_of_nonneg_of_nonpos (hlam i) (hfeasible i)
  · have := hlag xstar hxstar
    linarith

/-- Compactness and continuity supply primal attainment; Slater supplies
the multipliers. Convex constraints are allowed, including affine ones. -/
theorem multipliers_on_compact [TopologicalSpace E]
    (C : Set E) (hC : Convex ℝ C) (hcompact : IsCompact C)
    (f : E → ℝ) (hf : ConvexOn ℝ C f) (hfcont : ContinuousOn f C)
    (g : I → E → ℝ) (hg : ∀ i, ConvexOn ℝ C (g i))
    (hgcont : ∀ i, Continuous (g i))
    (x₀ : E) (hx₀ : x₀ ∈ C) (hstrict : ∀ i, g i x₀ < 0) :
    ∃ xstar ∈ C, (∀ i, g i xstar ≤ 0) ∧ ∃ lam : I → ℝ,
      (∀ i, 0 ≤ lam i) ∧
      (∀ x ∈ C, f xstar ≤ f x + ∑ i, lam i * g i x) ∧
      (∑ i, lam i * g i xstar) = 0 := by
  let S := C ∩ ⋂ i, {x | g i x ≤ 0}
  have hS : IsCompact S := hcompact.inter_right
    (isClosed_iInter fun i => isClosed_le (hgcont i) continuous_const)
  have hne : S.Nonempty := ⟨x₀, hx₀, by simp only [mem_iInter, mem_setOf_eq]; exact fun i => (hstrict i).le⟩
  obtain ⟨xstar, hxstar, hmin⟩ := hS.exists_isMinOn hne (hfcont.mono inter_subset_left)
  have hfeasible : ∀ i, g i xstar ≤ 0 := by
    simpa only [mem_iInter, mem_setOf_eq] using hxstar.2
  have hminimal (x : E) (hx : x ∈ C) (hgx : ∀ i, g i x ≤ 0) : f xstar ≤ f x :=
    hmin ⟨hx, by simpa only [mem_iInter, mem_setOf_eq] using hgx⟩
  exact ⟨xstar, hxstar.1, hfeasible,
    multipliers_of_minimum C hC f hf g hg xstar hxstar.1 hfeasible hminimal x₀ hx₀ hstrict⟩

end
end MsetsPaper.Upper.FiniteSlater
