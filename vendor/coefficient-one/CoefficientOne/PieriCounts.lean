import Mathlib

/-!
# Integer counts in the scalar Schur coefficient proof

The mathematical objects here are actual finite sets, rather than assumed
coefficient formulas. `convolutionCount` counts pairs `(x,y)` with prescribed
sum. `intervalCount` counts an intersection of two closed integer intervals.

The central count is reduced by the bijection `(x,y) ↦ x` to one integer
interval. The second-sector cancellation uses the reflection `x ↦ β - x`.
The remaining arithmetic proofs use the exact `Int.card_Icc` formula, with
`Int.toNat` retaining all empty-interval boundary cases.
-/

noncomputable section

namespace CoefficientOne

open Finset

/-- Number of integers in `[a,b] ∩ [c,d]`; reversed endpoints give an empty set. -/
def intervalCount (a b c d : ℤ) : ℕ :=
  ((Finset.Icc a b) ∩ Finset.Icc c d).card

/-- The bounded pairs defining the convolution `N_{b,e}(u)` in the paper. -/
def convolutionPairs (b e u : ℤ) : Finset (ℤ × ℤ) :=
  ((Finset.Icc 0 b).product (Finset.Icc 0 e)).filter
    (fun p => p.1 + p.2 = u)

def convolutionCount (b e u : ℤ) : ℕ :=
  (convolutionPairs b e u).card

/-- Intersecting closed intervals takes the larger lower and smaller upper bound. -/
theorem interval_inter_eq (a b c d : ℤ) :
    (Finset.Icc a b) ∩ Finset.Icc c d =
      Finset.Icc (max a c) (min b d) := by
  ext x
  simp only [Finset.mem_inter, Finset.mem_Icc, max_le_iff, le_min_iff]
  omega

/-- Exact count, including empty intervals. -/
theorem intervalCount_formula (a b c d : ℤ) :
    intervalCount a b c d = (min b d + 1 - max a c).toNat := by
  unfold intervalCount
  rw [interval_inter_eq, Int.card_Icc]

/-- Translating all four endpoints does not change the count. -/
theorem intervalCount_shift (a b c d t : ℤ) :
    intervalCount a b c d =
      intervalCount (a - t) (b - t) (c - t) (d - t) := by
  unfold intervalCount
  refine Finset.card_bij (fun x _ => x - t) ?_ ?_ ?_
  · intro x hx
    simp only [Finset.mem_inter, Finset.mem_Icc] at hx ⊢
    omega
  · intro x hx y hy hxy
    omega
  · intro y hy
    refine ⟨y + t, ?_, ?_⟩
    · simp only [Finset.mem_inter, Finset.mem_Icc] at hy ⊢
      omega
    · omega

/-- A pair with sum `u` is uniquely determined by its first coordinate. -/
theorem convolutionCount_eq_card (b e u : ℤ) :
    convolutionCount b e u =
      (Finset.Icc (max 0 (u - e)) (min b u)).card := by
  unfold convolutionCount convolutionPairs
  refine Finset.card_bij (fun p _ => p.1) ?_ ?_ ?_
  · intro p hp
    simp only [Finset.mem_filter] at hp
    have hpBounds := Finset.mem_product.mp hp.1
    simp only [Finset.mem_Icc] at hpBounds
    simp only [Finset.mem_Icc, max_le_iff, le_min_iff]
    omega
  · intro p hp q hq hpq
    simp only [Finset.mem_filter] at hp hq
    apply Prod.ext
    · exact hpq
    · omega
  · intro x hx
    simp only [Finset.mem_Icc, max_le_iff, le_min_iff] at hx
    refine ⟨(x, u - x), ?_, rfl⟩
    simp only [Finset.mem_filter]
    refine ⟨Finset.mem_product.mpr ?_, ?_⟩
    · simp only [Finset.mem_Icc]
      omega
    · omega

theorem convolutionCount_formula (b e u : ℤ) :
    convolutionCount b e u =
      (min b u + 1 - max 0 (u - e)).toNat := by
  rw [convolutionCount_eq_card, Int.card_Icc]

/--
The central increment of `N_{b,e}` is one precisely when the two bounds agree.
The equation `2*u = b+e` expresses centrality without integer division and
automatically enforces the parity condition. This includes `b=e=0`.
-/
theorem convolution_central_increment (b e u : ℤ)
    (hb : 0 ≤ b) (he : 0 ≤ e) (hcenter : 2 * u = b + e) :
    (convolutionCount b e u : ℤ) - (convolutionCount b e (u - 1) : ℤ) =
      if b = e then 1 else 0 := by
  rw [convolutionCount_formula, convolutionCount_formula]
  simp only [min_def, max_def]
  split_ifs <;> omega

/-- The initial two-strip product coefficient in the first sector. -/
theorem initialProduct_count (k α β γ δ ε : ℤ)
    (hβ : 0 ≤ β) (hε : 0 ≤ ε)
    (hsector : α + β + γ = k)
    (hdegree : ε = β + 2 * γ + 2 - 2 * δ) :
    (convolutionCount β ε (k + 1 - α - δ) : ℤ) -
        (convolutionCount β ε (k - α - δ) : ℤ) =
      if δ = γ + 1 then 1 else 0 := by
  have hcenter : 2 * (k + 1 - α - δ) = β + ε := by omega
  have hshift : k - α - δ = (k + 1 - α - δ) - 1 := by omega
  rw [hshift, convolution_central_increment β ε (k + 1 - α - δ) hβ hε hcenter]
  have hequiv : β = ε ↔ δ = γ + 1 := by omega
  simp only [hequiv]

/--
The first-sector difference `Q-P` after translating by `γ`.
This slightly stronger form does not need `β-2*u ≥ 0`: the exact interval
formula also covers the case in which both counts vanish.
-/
theorem firstSector_shifted_difference (β u : ℤ) (hβ : 0 ≤ β) :
    (intervalCount 0 β (u - 1) (β - u - 1) : ℤ) -
        (intervalCount 0 β u (β - u) : ℤ) =
      if u = 0 then -1 else 0 := by
  rw [intervalCount_formula, intervalCount_formula]
  simp only [min_def, max_def]
  split_ifs <;> omega

/-- The surviving first-sector count when the target has no two-box rows. -/
theorem firstSector_zero_twos (β γ ε : ℤ)
    (hβ : 0 ≤ β) (hγ : 0 ≤ γ)
    (hdegree : ε = β + 2 * γ + 2) :
    (intervalCount γ (β + γ) (-2) (ε - 2) : ℤ) = β + 1 := by
  rw [intervalCount_formula]
  simp only [min_def, max_def]
  split_ifs <;> omega

/-- The two source-index intervals in the first sector, before translation. -/
theorem firstSector_difference (β γ δ ε : ℤ) (hβ : 0 ≤ β)
    (hdegree : ε = β + 2 * γ + 2 - 2 * δ) :
    (intervalCount γ (β + γ) (δ - 2) (δ + ε - 2) : ℤ) -
        (intervalCount γ (β + γ) (δ - 1) (δ + ε - 1) : ℤ) =
      if δ = γ + 1 then -1 else 0 := by
  have hQ : intervalCount γ (β + γ) (δ - 2) (δ + ε - 2) =
      intervalCount 0 β ((δ - γ - 1) - 1) (β - (δ - γ - 1) - 1) := by
    calc
      _ = intervalCount (γ - γ) (β + γ - γ)
          (δ - 2 - γ) (δ + ε - 2 - γ) := intervalCount_shift _ _ _ _ γ
      _ = _ := by congr 1 <;> omega
  have hP : intervalCount γ (β + γ) (δ - 1) (δ + ε - 1) =
      intervalCount 0 β (δ - γ - 1) (β - (δ - γ - 1)) := by
    calc
      _ = intervalCount (γ - γ) (β + γ - γ)
          (δ - 1 - γ) (δ + ε - 1 - γ) := intervalCount_shift _ _ _ _ γ
      _ = _ := by congr 1 <;> omega
  rw [hQ, hP, firstSector_shifted_difference β (δ - γ - 1) hβ]
  have hequiv : δ - γ - 1 = 0 ↔ δ = γ + 1 := by omega
  simp only [hequiv]

/--
The complete first-sector coefficient, including the missing `P` contribution
when `δ=0`. The initial product cancels the exceptional negative difference.
-/
theorem firstSector_coefficient (β γ δ ε : ℤ)
    (hβ : 0 ≤ β) (hγ : 0 ≤ γ) (hδ : 0 ≤ δ)
    (hdegree : ε = β + 2 * γ + 2 - 2 * δ) :
    (if δ = γ + 1 then (1 : ℤ) else 0) +
        (intervalCount γ (β + γ) (δ - 2) (δ + ε - 2) : ℤ) -
        (if δ = 0 then 0 else
          (intervalCount γ (β + γ) (δ - 1) (δ + ε - 1) : ℤ)) =
      if δ = 0 then β + 1 else 0 := by
  by_cases hzero : δ = 0
  · subst δ
    have hno : ¬ (0 : ℤ) = γ + 1 := by omega
    have hdegree' : ε = β + 2 * γ + 2 := by omega
    have hQ := firstSector_zero_twos β γ ε hβ hγ hdegree'
    simpa [hno] using hQ
  · simp only [hzero, if_false]
    have hdiff := firstSector_difference β γ δ ε hβ hdegree
    by_cases heq : δ = γ + 1
    · simp only [heq, if_true] at hdiff ⊢
      omega
    · simp only [heq, if_false] at hdiff ⊢
      omega

/--
The second-sector equality is the bijection `x ↦ β-x`. It is valid for arbitrary
integer endpoints, so all empty-interval boundary cases are included.
-/
theorem secondSector_reflection (β u : ℤ) :
    intervalCount 0 β (u + 1) (β - u) =
      intervalCount 0 β u (β - u - 1) := by
  unfold intervalCount
  refine Finset.card_bij (fun x _ => β - x) ?_ ?_ ?_
  · intro x hx
    simp only [Finset.mem_inter, Finset.mem_Icc] at hx ⊢
    omega
  · intro x hx y hy hxy
    omega
  · intro y hy
    refine ⟨β - y, ?_, ?_⟩
    · simp only [Finset.mem_inter, Finset.mem_Icc] at hy ⊢
      omega
    · omega

/--
The raw `Z` and `P` counts agree in the second sector. In the Schur expansion
both terms are present only when `γ≥1`; the identity of interval counts itself
needs no sign restriction on `γ`.
-/
theorem secondSector_counts_cancel (β γ δ ε : ℤ)
    (hdegree : ε = β + 2 * γ - 3 - 2 * δ) :
    intervalCount (γ - 2) (β + γ - 2) δ (δ + ε) =
      intervalCount (γ - 1) (β + γ - 1) δ (δ + ε) := by
  have hZ : intervalCount (γ - 2) (β + γ - 2) δ (δ + ε) =
      intervalCount 0 β ((δ - γ + 1) + 1) (β - (δ - γ + 1)) := by
    calc
      _ = intervalCount ((γ - 2) - (γ - 2)) ((β + γ - 2) - (γ - 2))
          (δ - (γ - 2)) ((δ + ε) - (γ - 2)) := intervalCount_shift _ _ _ _ _
      _ = _ := by congr 1 <;> omega
  have hP : intervalCount (γ - 1) (β + γ - 1) δ (δ + ε) =
      intervalCount 0 β (δ - γ + 1) (β - (δ - γ + 1) - 1) := by
    calc
      _ = intervalCount ((γ - 1) - (γ - 1)) ((β + γ - 1) - (γ - 1))
          (δ - (γ - 1)) ((δ + ε) - (γ - 1)) := intervalCount_shift _ _ _ _ _
      _ = _ := by congr 1 <;> omega
  rw [hZ, hP]
  exact secondSector_reflection β (δ - γ + 1)

/-- The surviving second-sector count when the target has no three-box rows. -/
theorem secondSector_zero_threes (β δ ε : ℤ)
    (hδ : 0 ≤ δ) (hε : 0 ≤ ε)
    (hdegree : ε = β - 3 - 2 * δ) :
    (intervalCount (-2) (β - 2) δ (δ + ε) : ℤ) = ε + 1 := by
  rw [intervalCount_formula]
  simp only [min_def, max_def]
  split_ifs <;> omega

/-- The complete second-sector coefficient, including the absence of `P` at `γ=0`. -/
theorem secondSector_coefficient (β γ δ ε : ℤ)
    (hδ : 0 ≤ δ) (hε : 0 ≤ ε)
    (hdegree : ε = β + 2 * γ - 3 - 2 * δ) :
    (intervalCount (γ - 2) (β + γ - 2) δ (δ + ε) : ℤ) -
        (if γ = 0 then 0 else
          (intervalCount (γ - 1) (β + γ - 1) δ (δ + ε) : ℤ)) =
      if γ = 0 then ε + 1 else 0 := by
  by_cases hzero : γ = 0
  · subst γ
    have hdegree' : ε = β - 3 - 2 * δ := by omega
    simpa using secondSector_zero_threes β δ ε hδ hε hdegree'
  · simp only [hzero, if_false]
    rw [secondSector_counts_cancel β γ δ ε hdegree]
    omega

/-- First-sector row-upgrade bounds already imply the original source range. -/
theorem firstSector_source_bounds (α β γ k j : ℤ)
    (hα : 0 ≤ α) (hγ : 0 ≤ γ)
    (hsector : α + β + γ = k)
    (hj : γ ≤ j ∧ j ≤ β + γ) : 0 ≤ j ∧ j ≤ k := by
  omega

/-- The `Z` intersection in the second sector enforces `0≤j≤k-1`. -/
theorem secondSector_Z_source_bounds (α β γ δ k j : ℤ)
    (hα : 0 ≤ α) (hδ : 0 ≤ δ)
    (hsector : α + β + γ = k + 1)
    (hlo : δ ≤ j) (hhi : j ≤ β + γ - 2) : 0 ≤ j ∧ j ≤ k - 1 := by
  omega

/-- The `P` intersection in the second sector enforces `0≤j≤k`. -/
theorem secondSector_P_source_bounds (α β γ δ k j : ℤ)
    (hα : 0 ≤ α) (hδ : 0 ≤ δ)
    (hsector : α + β + γ = k + 1)
    (hlo : δ ≤ j) (hhi : j ≤ β + γ - 1) : 0 ≤ j ∧ j ≤ k := by
  omega

end CoefficientOne
