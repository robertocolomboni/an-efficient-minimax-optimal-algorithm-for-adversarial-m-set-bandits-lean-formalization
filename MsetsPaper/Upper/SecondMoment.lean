import MsetsLower.Core.HistoryStats
import Mathlib.LinearAlgebra.Matrix.PosDef
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Linarith

/-!
# Actual second moments of full-support fixed-cardinality laws

This module establishes the nonsingular-moment part of manuscript Lemma 2.
The matrix is the actual finite second moment on `MSetAction`, not an abstract
matrix supplied together with a positive-definiteness certificate.  Positive
definiteness is proved from full support and the exchange of two items.
The covariance-pseudoinverse comparison is not asserted in this module.
-/

noncomputable section

open scoped BigOperators
open Matrix MsetsLower MsetsLower.History

namespace MsetsPaper.Upper

abbrev Action (d m : ℕ) := MSetAction d m

variable {d m : ℕ}

/-- Actual marginal inclusion probabilities (or masses before normalization). -/
def marginal (p : Action d m → ℝ) (i : Fin d) : ℝ :=
  ∑ a, p a * selectedIndicator i a

/-- Actual uncentered second-moment matrix of the action indicators. -/
def secondMoment (p : Action d m → ℝ) : Matrix (Fin d) (Fin d) ℝ :=
  fun i j => ∑ a, p a * selectedIndicator i a * selectedIndicator j a

@[simp] theorem sum_selectedIndicator (a : Action d m) :
    ∑ i : Fin d, selectedIndicator i a = (m : ℝ) := by
  classical
  simp [selectedIndicator, a.property]

theorem dot_indicator_eq_actionLoss (a : Action d m) (x : Fin d → ℝ) :
    x ⬝ᵥ (fun i => selectedIndicator i a) = actionLoss a x := by
  classical
  simp [dotProduct, selectedIndicator, actionLoss]

theorem sum_marginal (p : Action d m → ℝ) (hp : ∑ a, p a = 1) :
    ∑ i, marginal p i = (m : ℝ) := by
  classical
  unfold marginal
  rw [Finset.sum_comm]
  simp_rw [← Finset.mul_sum, sum_selectedIndicator]
  rw [← Finset.sum_mul, hp, one_mul]

theorem secondMoment_isSymm (p : Action d m → ℝ) :
    (secondMoment p).IsSymm := by
  apply Matrix.IsSymm.ext
  intro i j
  unfold secondMoment
  apply Finset.sum_congr rfl
  intro a _
  ring

/-- Fixed cardinality gives the row-sum identity, with no probabilistic premise. -/
theorem secondMoment_mulVec_one (p : Action d m → ℝ) :
    secondMoment p *ᵥ (fun _ => 1) = (m : ℝ) • marginal p := by
  classical
  ext i
  simp only [Matrix.mulVec, dotProduct, secondMoment, mul_one, Pi.smul_apply,
    smul_eq_mul]
  rw [Finset.sum_comm]
  simp_rw [← Finset.mul_sum, sum_selectedIndicator]
  rw [← Finset.sum_mul]
  change marginal p i * (m : ℝ) = (m : ℝ) * marginal p i
  ring

/-- The quadratic form is exactly the finite average of squared action sums. -/
theorem secondMoment_quadratic (p : Action d m → ℝ) (x : Fin d → ℝ) :
    x ⬝ᵥ (secondMoment p *ᵥ x) =
      ∑ a, p a * (actionLoss a x) ^ 2 := by
  classical
  simp only [dotProduct, Matrix.mulVec, secondMoment, Finset.mul_sum, Finset.sum_mul]
  calc
    (∑ i, ∑ j, ∑ a, x i * (p a * selectedIndicator i a * selectedIndicator j a * x j)) =
        ∑ i, ∑ a, ∑ j,
          x i * (p a * selectedIndicator i a * selectedIndicator j a * x j) := by
      apply Finset.sum_congr rfl
      intro i _
      rw [Finset.sum_comm]
    _ = ∑ a, ∑ i, ∑ j,
          x i * (p a * selectedIndicator i a * selectedIndicator j a * x j) := by
      rw [Finset.sum_comm]
    _ = ∑ a, ∑ i, ∑ j,
          p a * ((x i * selectedIndicator i a) * (x j * selectedIndicator j a)) := by
      apply Finset.sum_congr rfl
      intro a _
      apply Finset.sum_congr rfl
      intro i _
      apply Finset.sum_congr rfl
      intro j _
      ring
    _ = ∑ a, p a * (actionLoss a x) ^ 2 := by
      apply Finset.sum_congr rfl
      intro a _
      rw [← dot_indicator_eq_actionLoss]
      simp only [dotProduct, pow_two, Finset.mul_sum, Finset.sum_mul]
      apply Finset.sum_congr rfl
      intro i _
      apply Finset.sum_congr rfl
      intro j _
      ring

/-- The indicator vectors of nontrivial fixed-size actions span all coordinates.
The proof compares two actions differing by exactly one exchanged item. -/
theorem eq_zero_of_actionLoss_eq_zero (hmpos : 1 ≤ m) (hmtop : m ≤ d - 1)
    (x : Fin d → ℝ) (hx : ∀ a : Action d m, actionLoss a x = 0) : x = 0 := by
  classical
  have hconst : ∀ i j : Fin d, x i = x j := by
    intro i j
    by_cases hij : i = j
    · simp [hij]
    let R : Finset (Fin d) := (Finset.univ.erase i).erase j
    have hj : j ∈ (Finset.univ : Finset (Fin d)).erase i := by simp [Ne.symm hij]
    have hR : R.card = d - 2 := by
      simp only [R, Finset.card_erase_of_mem hj,
        Finset.card_erase_of_mem (Finset.mem_univ i), Finset.card_univ,
        Fintype.card_fin]
      omega
    obtain ⟨A, hAR, hAc⟩ := Finset.exists_subset_card_eq
      (show m - 1 ≤ R.card by rw [hR]; omega)
    have hiA : i ∉ A := by
      intro hi
      have hh := hAR hi
      simp [R] at hh
    have hjA : j ∉ A := by
      intro hj'
      have hh := hAR hj'
      simp [R] at hh
    let ai : Action d m := ⟨insert i A, by rw [Finset.card_insert_of_notMem hiA, hAc]; omega⟩
    let aj : Action d m := ⟨insert j A, by rw [Finset.card_insert_of_notMem hjA, hAc]; omega⟩
    have hxi : x i + ∑ k ∈ A, x k = 0 := by
      simpa [actionLoss_eq_finset_sum, ai, hiA] using hx ai
    have hxj : x j + ∑ k ∈ A, x k = 0 := by
      simpa [actionLoss_eq_finset_sum, aj, hjA] using hx aj
    linarith
  let i₀ : Fin d := ⟨0, by omega⟩
  obtain ⟨a⟩ := nonempty_MSetAction (show m ≤ d by omega)
  have ha : actionLoss a x = (m : ℝ) * x i₀ := by
    rw [actionLoss_eq_finset_sum]
    calc
      ∑ i ∈ a.val, x i = ∑ i ∈ a.val, x i₀ := by
        apply Finset.sum_congr rfl
        intro i _
        exact hconst i i₀
      _ = _ := by simp [a.property]
  have hm : (m : ℝ) ≠ 0 := by exact_mod_cast (show m ≠ 0 by omega)
  have hzero : x i₀ = 0 := (mul_eq_zero.mp (ha.symm.trans (hx a))).resolve_left hm
  ext i
  exact (hconst i i₀).trans hzero

/-- Full support, not a positive-definiteness assumption, makes M positive definite. -/
theorem secondMoment_posDef (p : Action d m → ℝ) (hp : ∀ a, 0 < p a)
    (hmpos : 1 ≤ m) (hmtop : m ≤ d - 1) : (secondMoment p).PosDef := by
  classical
  apply Matrix.posDef_iff_dotProduct_mulVec.mpr
  refine ⟨Matrix.isHermitian_iff_isSymm.mpr (secondMoment_isSymm p), ?_⟩
  intro x hx
  simp only [star_trivial]
  rw [secondMoment_quadratic]
  have ha : ∃ a : Action d m, actionLoss a x ≠ 0 := by
    by_contra h
    push Not at h
    exact hx (eq_zero_of_actionLoss_eq_zero hmpos hmtop x h)
  obtain ⟨a, ha⟩ := ha
  apply Finset.sum_pos'
  · intro b _
    exact mul_nonneg (hp b).le (sq_nonneg _)
  · exact ⟨a, Finset.mem_univ _, mul_pos (hp a) (sq_pos_of_ne_zero ha)⟩

/-- The inverse is itself positive definite; no inverse witness is assumed. -/
theorem secondMoment_inv_posDef (p : Action d m → ℝ) (hp : ∀ a, 0 < p a)
    (hmpos : 1 ≤ m) (hmtop : m ≤ d - 1) : (secondMoment p)⁻¹.PosDef :=
  (secondMoment_posDef p hp hmpos hmtop).inv

/-- The exact identity M^{-1} mu = (1/m) 1 used by Lemma 2 and Theorem 1. -/
theorem secondMoment_inv_mulVec_marginal (p : Action d m → ℝ) (hp : ∀ a, 0 < p a)
    (hmpos : 1 ≤ m) (hmtop : m ≤ d - 1) :
    (secondMoment p)⁻¹ *ᵥ marginal p = fun _ => (m : ℝ)⁻¹ := by
  classical
  letI := (secondMoment_posDef p hp hmpos hmtop).isUnit.invertible
  apply Matrix.inv_mulVec_eq_vec
  have hm : (m : ℝ) ≠ 0 := by exact_mod_cast (show m ≠ 0 by omega)
  symm
  calc
    secondMoment p *ᵥ (fun _ => (m : ℝ)⁻¹) =
        (m : ℝ)⁻¹ • (secondMoment p *ᵥ (fun _ => 1)) := by
      rw [← Matrix.mulVec_smul]
      congr 1
      ext i
      simp
    _ = marginal p := by
      rw [secondMoment_mulVec_one, smul_smul, inv_mul_cancel₀ hm, one_smul]

end MsetsPaper.Upper
