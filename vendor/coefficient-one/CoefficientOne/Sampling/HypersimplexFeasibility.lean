import CoefficientOne.Sampling.Model
import Mathlib

/-!
# Feasibility of prescribed fixed-cardinality marginals

The proof follows Appendix E.2: perturb two fractional coordinates in opposite
directions until one reaches a boundary, and induct on their number.
-/

open scoped BigOperators
open EffectiveResistance

namespace CoefficientOne.Sampling

noncomputable section

variable {ι : Type*} [Fintype ι] [DecidableEq ι] {k : ℕ}

/-- The marginal map on real mass vectors, before imposing probability axioms. -/
def massMeanLinear : (RankSubset ι k → ℝ) →ₗ[ℝ] (ι → ℝ) where
  toFun p i := ∑ S, p S * indicator i S.1
  map_add' p q := by ext i; simp [add_mul, Finset.sum_add_distrib]
  map_smul' a p := by ext i; simp [Finset.mul_sum, mul_assoc]

@[simp] theorem massMeanLinear_apply (p : RankSubset ι k → ℝ) (i : ι) :
    massMeanLinear p i = ∑ S, p S * indicator i S.1 := rfl

/-- The finite-dimensional compact fiber of laws with prescribed marginals. -/
def marginalFiber (x : ι → ℝ) : Set (RankSubset ι k → ℝ) :=
  {p | p ∈ stdSimplex ℝ (RankSubset ι k) ∧ massMeanLinear p = x}

theorem marginalFiber_isCompact (x : ι → ℝ) : IsCompact (marginalFiber (k := k) x) := by
  apply (isCompact_stdSimplex ℝ (RankSubset ι k)).inter_right
  exact isClosed_eq (massMeanLinear (ι := ι) (k := k)).continuous_of_finiteDimensional
    continuous_const

theorem marginalFiber_convex (x : ι → ℝ) : Convex ℝ (marginalFiber (k := k) x) := by
  intro p hp q hq a b ha hb hab
  refine ⟨(convex_stdSimplex ℝ (RankSubset ι k)) hp.1 hq.1 ha hb hab, ?_⟩
  simp only [map_add, map_smul, hp.2, hq.2, ← add_smul, hab, one_smul]

def fractionalCoordinates (x : ι → ℝ) : Finset ι :=
  Finset.univ.filter (fun i => 0 < x i ∧ x i < 1)

@[simp] theorem mem_fractionalCoordinates (x : ι → ℝ) (i : ι) :
    i ∈ fractionalCoordinates x ↔ 0 < x i ∧ x i < 1 := by
  simp [fractionalCoordinates]

theorem coordinate_boundary_of_not_fractional (x : ι → ℝ)
    (hx : ∀ i, 0 ≤ x i ∧ x i ≤ 1) (i : ι)
    (hi : i ∉ fractionalCoordinates x) : x i = 0 ∨ x i = 1 := by
  simp only [mem_fractionalCoordinates, not_and, not_lt] at hi
  have := hx i
  by_cases h : 0 < x i
  · exact Or.inr (le_antisymm this.2 (hi h))
  · exact Or.inl (le_antisymm (le_of_not_gt h) this.1)

theorem exists_second_fractional (x : ι → ℝ)
    (hx : ∀ i, 0 ≤ x i ∧ x i ≤ 1) (hs : ∑ i, x i = (k : ℝ))
    (i : ι) (hi : i ∈ fractionalCoordinates x) :
    ∃ j, j ≠ i ∧ j ∈ fractionalCoordinates x := by
  classical
  by_contra hn
  push_neg at hn
  let ones := Finset.univ.filter (fun j => x j = 1)
  have hi1 : x i ≠ 1 := ne_of_lt (mem_fractionalCoordinates x i |>.mp hi).2
  have hform (j : ι) : x j = (if j = i then x i else 0) +
      (if j ∈ ones then (1 : ℝ) else 0) := by
    by_cases hji : j = i
    · subst j; simp [ones, hi1]
    · rcases coordinate_boundary_of_not_fractional x hx j (hn j hji) with hj | hj
      · simp [hji, ones, hj]
      · simp [hji, ones, hj]
  have hsum : (k : ℝ) = x i + (ones.card : ℝ) := by
    rw [← hs]
    calc
      _ = ∑ j, ((if j = i then x i else 0) +
          (if j ∈ ones then (1 : ℝ) else 0)) := Finset.sum_congr rfl (fun j _ => hform j)
      _ = _ := by simp [Finset.sum_add_distrib]
  have hfrac := (mem_fractionalCoordinates x i).mp hi
  have hlo : (ones.card : ℝ) < k := by linarith
  have hhi : (k : ℝ) < (ones.card + 1 : ℕ) := by push_cast; linarith
  have hlo' : ones.card < k := by exact_mod_cast hlo
  have hhi' : k < ones.card + 1 := by exact_mod_cast hhi
  omega

/-- Transfer mass between two coordinates without changing their total. -/
def coordinateTransfer (x : ι → ℝ) (i j : ι) (t : ℝ) : ι → ℝ :=
  fun l => x l + if l = i then t else if l = j then -t else 0

theorem coordinateTransfer_sum (x : ι → ℝ) (i j : ι) (hij : i ≠ j) (t : ℝ) :
    ∑ l, coordinateTransfer x i j t l = ∑ l, x l := by
  classical
  have heq : (fun l : ι => if l = i then t else if l = j then -t else 0) =
      (fun l => (if l = i then t else 0) - (if l = j then t else 0)) := by
    funext l; split_ifs <;> simp_all
  simp only [coordinateTransfer, Finset.sum_add_distrib, heq, Finset.sum_sub_distrib]
  simp

theorem coordinateTransfer_bounded (x : ι → ℝ)
    (hx : ∀ l, 0 ≤ x l ∧ x l ≤ 1) (i j : ι) (hij : i ≠ j) (t : ℝ)
    (hi : 0 ≤ x i + t ∧ x i + t ≤ 1)
    (hj : 0 ≤ x j - t ∧ x j - t ≤ 1) :
    ∀ l, 0 ≤ coordinateTransfer x i j t l ∧ coordinateTransfer x i j t l ≤ 1 := by
  intro l
  by_cases hli : l = i
  · subst l; simpa [coordinateTransfer] using hi
  by_cases hlj : l = j
  · subst l; simpa [coordinateTransfer, Ne.symm hij, sub_eq_add_neg] using hj
  simpa [coordinateTransfer, hli, hlj] using hx l

theorem fractionalCoordinates_transfer_subset (x : ι → ℝ) (i j : ι)
    (hi : i ∈ fractionalCoordinates x) (hj : j ∈ fractionalCoordinates x) (t : ℝ) :
    fractionalCoordinates (coordinateTransfer x i j t) ⊆ fractionalCoordinates x := by
  intro l hl
  by_cases hli : l = i
  · simpa [hli] using hi
  by_cases hlj : l = j
  · simpa [hlj] using hj
  simpa [coordinateTransfer, hli, hlj] using hl

theorem fractionalCoordinates_transfer_card_lt (x : ι → ℝ) (i j : ι)
    (hi : i ∈ fractionalCoordinates x) (hj : j ∈ fractionalCoordinates x) (t : ℝ)
    (r : ι) (hr : r ∈ fractionalCoordinates x)
    (hboundary : coordinateTransfer x i j t r = 0 ∨
      coordinateTransfer x i j t r = 1) :
    (fractionalCoordinates (coordinateTransfer x i j t)).card <
      (fractionalCoordinates x).card := by
  apply Finset.card_lt_card
  refine Finset.ssubset_iff_subset_ne.mpr
    ⟨fractionalCoordinates_transfer_subset x i j hi hj t, ?_⟩
  intro heq
  have hmem : r ∈ fractionalCoordinates (coordinateTransfer x i j t) := heq.symm ▸ hr
  have hfrac := (mem_fractionalCoordinates _ r).mp hmem
  rcases hboundary with h | h <;> simp_all

/-- The two boundary-reaching perturbations used in the fractional induction. -/
theorem fractional_split (x : ι → ℝ)
    (hx : ∀ i, 0 ≤ x i ∧ x i ≤ 1) (hs : ∑ i, x i = (k : ℝ))
    (i j : ι) (hij : i ≠ j)
    (hi : i ∈ fractionalCoordinates x) (hj : j ∈ fractionalCoordinates x) :
    ∃ (y z : ι → ℝ) (a b : ℝ),
      (∀ l, 0 ≤ y l ∧ y l ≤ 1) ∧ (∑ l, y l = (k : ℝ)) ∧
      (∀ l, 0 ≤ z l ∧ z l ≤ 1) ∧ (∑ l, z l = (k : ℝ)) ∧
      (fractionalCoordinates y).card < (fractionalCoordinates x).card ∧
      (fractionalCoordinates z).card < (fractionalCoordinates x).card ∧
      0 ≤ a ∧ 0 ≤ b ∧ a + b = 1 ∧ x = a • y + b • z := by
  let s := min (1 - x i) (x j)
  let t := min (x i) (1 - x j)
  have hi' := (mem_fractionalCoordinates x i).mp hi
  have hj' := (mem_fractionalCoordinates x j).mp hj
  have hspos : 0 < s := lt_min (by linarith) hj'.1
  have htpos : 0 < t := lt_min hi'.1 (by linarith)
  have hs1 : s ≤ 1 - x i := min_le_left _ _
  have hs2 : s ≤ x j := min_le_right _ _
  have ht1 : t ≤ x i := min_le_left _ _
  have ht2 : t ≤ 1 - x j := min_le_right _ _
  have hy := coordinateTransfer_bounded x hx i j hij s
    (by constructor <;> linarith) (by constructor <;> linarith)
  have hz := coordinateTransfer_bounded x hx i j hij (-t)
    (by constructor <;> linarith) (by constructor <;> linarith)
  have hycard : (fractionalCoordinates (coordinateTransfer x i j s)).card <
      (fractionalCoordinates x).card := by
    rcases le_total (1 - x i) (x j) with h | h
    · apply fractionalCoordinates_transfer_card_lt x i j hi hj s i hi
      right
      simp [coordinateTransfer, s, min_eq_left h]
    · apply fractionalCoordinates_transfer_card_lt x i j hi hj s j hj
      left
      simp [coordinateTransfer, Ne.symm hij, s, min_eq_right h]
  have hzcard : (fractionalCoordinates (coordinateTransfer x i j (-t))).card <
      (fractionalCoordinates x).card := by
    rcases le_total (x i) (1 - x j) with h | h
    · apply fractionalCoordinates_transfer_card_lt x i j hi hj (-t) i hi
      left
      simp [coordinateTransfer, t, min_eq_left h]
    · apply fractionalCoordinates_transfer_card_lt x i j hi hj (-t) j hj
      right
      simp [coordinateTransfer, Ne.symm hij, t, min_eq_right h]
  have hst : s + t ≠ 0 := ne_of_gt (add_pos hspos htpos)
  refine ⟨coordinateTransfer x i j s, coordinateTransfer x i j (-t),
    t / (s + t), s / (s + t), hy, ?_, hz, ?_, hycard, hzcard,
    div_nonneg htpos.le (add_pos hspos htpos).le,
    div_nonneg hspos.le (add_pos hspos htpos).le, ?_, ?_⟩
  · exact (coordinateTransfer_sum x i j hij s).trans hs
  · exact (coordinateTransfer_sum x i j hij (-t)).trans hs
  · field_simp; ring
  · ext l
    simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, coordinateTransfer]
    split_ifs <;> field_simp <;> ring

theorem boundary_vector_mem_mean_image (x : ι → ℝ)
    (hx : ∀ i, x i = 0 ∨ x i = 1) (hs : ∑ i, x i = (k : ℝ)) :
    x ∈ massMeanLinear (ι := ι) (k := k) '' stdSimplex ℝ (RankSubset ι k) := by
  classical
  let S := Finset.univ.filter (fun i => x i = 1)
  have hi (i : ι) : indicator i S = x i := by
    rcases hx i with h | h <;> simp [indicator, S, h]
  have hcard : S.card = k := by
    have heq : (S.card : ℝ) = (k : ℝ) := by
      calc
        _ = ∑ i, indicator i S := by simp [indicator]
        _ = ∑ i, x i := Finset.sum_congr rfl (fun i _ => hi i)
        _ = _ := hs
    exact_mod_cast heq
  let T : RankSubset ι k := ⟨S, hcard⟩
  refine ⟨Pi.single T 1, single_mem_stdSimplex ℝ T, ?_⟩
  ext i
  simpa [massMeanLinear, T, Pi.single_apply] using hi i

/-- Every admissible marginal vector is the mean of an actual finite law. -/
theorem marginalFiber_nonempty (x : ι → ℝ)
    (hx : ∀ i, 0 ≤ x i ∧ x i ≤ 1) (hs : ∑ i, x i = (k : ℝ)) :
    (marginalFiber (k := k) x).Nonempty := by
  classical
  let P := massMeanLinear (ι := ι) (k := k) '' stdSimplex ℝ (RankSubset ι k)
  have hP : Convex ℝ P := (convex_stdSimplex ℝ (RankSubset ι k)).linear_image _
  have aux : ∀ m (x : ι → ℝ), (fractionalCoordinates x).card = m →
      (∀ i, 0 ≤ x i ∧ x i ≤ 1) → (∑ i, x i = (k : ℝ)) → x ∈ P := by
    intro m
    induction m using Nat.strong_induction_on with
    | h m ih =>
      intro x hm hx hs
      by_cases hzero : fractionalCoordinates x = ∅
      · apply boundary_vector_mem_mean_image x _ hs
        intro i
        apply coordinate_boundary_of_not_fractional x hx i
        simp [hzero]
      · obtain ⟨i, hi⟩ := Finset.nonempty_iff_ne_empty.mpr hzero
        obtain ⟨j, hji, hj⟩ := exists_second_fractional x hx hs i hi
        obtain ⟨y, z, a, b, hy, hys, hz, hzs, hyc, hzc, ha, hb, hab, hcomb⟩ :=
          fractional_split x hx hs i j (Ne.symm hji) hi hj
        have hyp := ih _ (by omega) y rfl hy hys
        have hzp := ih _ (by omega) z rfl hz hzs
        rw [hcomb]
        exact hP hyp hzp ha hb hab
  obtain ⟨p, hp, hpx⟩ := aux _ x rfl hx hs
  exact ⟨p, hp, hpx⟩

theorem marginalFiber_nonempty_of_mem_hypersimplex (x : ι → ℝ)
    (hx : x ∈ hypersimplex ι k) : (marginalFiber (k := k) x).Nonempty :=
  marginalFiber_nonempty x hx.1 hx.2

end
end CoefficientOne.Sampling
