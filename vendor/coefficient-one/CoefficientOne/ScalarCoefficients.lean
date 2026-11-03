import CoefficientOne.ScalarExpansion

/-!
# Exact coefficients and positivity in the scalar Schur expansion

This is the coefficient calculation in the manuscript's `eq:coeff`. The
coefficients are the actual finite strip and strip-pair cardinalities from
`ScalarExpansion.rawCoefficient`; no Schur coefficient formula is assumed.
-/

noncomputable section

namespace CoefficientOne.ScalarCoefficients

open Finset ScalarExpansion ScalarPieriShapes InitialPieriCount SignedLoad

variable {N : ℕ}
attribute [local instance] Classical.propDecidable

/-- A source family with no rowwise strip has no admissible source index. -/
theorem pieriSourceIndices_empty (source : ℤ → Fin N → ℕ) (nu : Fin N → ℕ)
    (t : ℕ) (lo hi : ℤ) (h : ∀ j ∈ Icc lo hi, ¬ RowStrip (source j) nu) :
    pieriSourceIndices source nu t lo hi = ∅ := by
  apply Finset.eq_empty_iff_forall_notMem.mpr
  intro j hj
  obtain ⟨hj, S, hS, _⟩ := Finset.mem_filter.mp hj
  exact h j hj (rowStrip_of_pieriSubset (source j) nu t S hS)

/-- Two strips from the three-square rectangle preserve the number of long rows. -/
theorem doubleSubset_heightCount (k : ℕ) (nu : Fin N → ℕ) (t s : ℕ)
    (hN : (k : ℤ) ≤ N) (p : Finset (Fin N) × Finset (Fin N))
    (hp : p ∈ doubleSubsets k nu t s) : heightCount nu 2 = k := by
  apply heightCount_eq_of_row_iff nu 2 k (by omega) hN
  intro i
  have h := row_bounds_of_doubleSubset k nu t s p hp i
  unfold baseShape at h
  split_ifs at h <;> omega

theorem doubleSubsets_empty_of_sector (k : ℕ) (nu : Fin N → ℕ) (t s : ℕ)
    (hN : (k : ℤ) ≤ N) (hne : heightCount nu 2 ≠ k) : doubleSubsets k nu t s = ∅ := by
  apply Finset.eq_empty_iff_forall_notMem.mpr
  intro p hp
  exact hne (doubleSubset_heightCount k nu t s hN p hp)

/-- The first-sector coefficient includes the exact double-Pieri difference,
the Q/P interval counts, and the absence of Z. -/
theorem rawCoefficient_firstSector (k : ℕ) (α β γ δ ε : ℤ)
    (hα : 0 ≤ α) (hβ : 0 ≤ β) (hγ : 0 ≤ γ) (hδ : 0 ≤ δ) (hε : 0 ≤ ε)
    (hN : 2 * (k : ℤ) + 3 ≤ N) (hfit : α + β + γ + δ + ε ≤ N)
    (hsector : α + β + γ = k) (hdegree : ε = β + 2 * γ + 2 - 2 * δ) :
    rawCoefficient k (targetShape (N := N) α β γ δ ε) =
      if δ = 0 then β + 1 else 0 := by
  have hi := initial_doublePieri_pair_count (N := N) k α β γ δ ε
    hα hβ hγ hδ hε hsector (by omega) (by omega)
  rw [show ((k : ℤ) + 1).toNat = k + 1 by omega,
    show ((k : ℤ) + 2).toNat = k + 2 by omega, Int.toNat_natCast] at hi
  have hq := q_firstSector_count (N := N) k α β γ δ ε
    hα hβ hγ hδ hε hN hfit hsector hdegree
  have hp := p_firstSector_count (N := N) k α β γ δ ε
    hα hβ hγ hδ hε hN hfit hsector hdegree
  simp only [Int.toNat_natCast] at hq hp
  have hz : pieriSourceIndices (zShape k) (targetShape (N := N) α β γ δ ε)
      k 0 ((k : ℤ) - 1) = ∅ := by
    apply pieriSourceIndices_empty
    intro j hj
    exact zShape_not_firstSector k j α β γ δ ε hα hβ hγ
      (Finset.mem_Icc.mp hj).1 (Finset.mem_Icc.mp hj).2 hN hsector
  unfold rawCoefficient
  rw [hi, hq, hp, hz, Finset.card_empty, Nat.cast_zero, add_zero]
  push_cast
  exact firstSector_coefficient β γ δ ε hβ hγ hδ hdegree

/-- The second sector has only the actual Z/P strips, which cancel unless γ=0. -/
theorem rawCoefficient_secondSector (k : ℕ) (α β γ δ ε : ℤ)
    (hα : 0 ≤ α) (hβ : 0 ≤ β) (hγ : 0 ≤ γ) (hδ : 0 ≤ δ) (hε : 0 ≤ ε)
    (hN : 2 * (k : ℤ) + 3 ≤ N) (hfit : α + β + γ + δ + ε ≤ N)
    (hsector : α + β + γ = (k : ℤ) + 1) (hdegree : ε = β + 2 * γ - 3 - 2 * δ) :
    rawCoefficient k (targetShape (N := N) α β γ δ ε) =
      if γ = 0 then ε + 1 else 0 := by
  have hd₁ := doubleSubsets_secondSector_empty (N := N) k α β γ δ ε
    (by omega) (by omega) hsector (k + 1) (k + 1)
  have hd₂ := doubleSubsets_secondSector_empty (N := N) k α β γ δ ε
    (by omega) (by omega) hsector k (k + 2)
  have hq : pieriSourceIndices (qShape k) (targetShape (N := N) α β γ δ ε) k 0 k = ∅ := by
    apply pieriSourceIndices_empty
    intro j hj
    exact qShape_not_secondSector k j α β γ δ ε hα hβ hγ
      (Finset.mem_Icc.mp hj).1 (Finset.mem_Icc.mp hj).2 hN hsector
  have hcount := secondSector_signedCount (N := N) k α β γ δ ε
    hα hβ hγ hδ hε hN hfit hsector hdegree
  simp only [Int.toNat_natCast] at hcount
  unfold rawCoefficient
  simp only [hd₁, hd₂, hq, Finset.card_empty, Nat.cast_zero]
  linarith

/-- Every actual source contribution vanishes outside the two possible sectors. -/
theorem rawCoefficient_otherSector (k : ℕ) (nu : Fin N → ℕ)
    (hN : 2 * (k : ℤ) + 3 ≤ N)
    (h₀ : heightCount nu 2 ≠ k) (h₁ : heightCount nu 2 ≠ (k : ℤ) + 1) :
    rawCoefficient k nu = 0 := by
  have hd₁ := doubleSubsets_empty_of_sector k nu (k + 1) (k + 1) (by omega) h₀
  have hd₂ := doubleSubsets_empty_of_sector k nu k (k + 2) (by omega) h₀
  have hq : pieriSourceIndices (qShape k) nu k 0 k = ∅ := by
    apply pieriSourceIndices_empty
    intro j hj hs
    have hc := (q_reachable_classification k j nu (Finset.mem_Icc.mp hj).1
      (Finset.mem_Icc.mp hj).2 hN hs).2
    exact h₀ hc
  have hp : pieriSourceIndices (pShape k) nu k 0 k = ∅ := by
    apply pieriSourceIndices_empty
    intro j hj hs
    have hc := (p_reachable_classification k j nu (Finset.mem_Icc.mp hj).1
      (Finset.mem_Icc.mp hj).2 hN hs).2
    exact hc.elim h₀ h₁
  have hz : pieriSourceIndices (zShape k) nu k 0 ((k : ℤ) - 1) = ∅ := by
    apply pieriSourceIndices_empty
    intro j hj hs
    have hc := (z_reachable_classification k j nu (Finset.mem_Icc.mp hj).1
      (Finset.mem_Icc.mp hj).2 hN hs).2
    exact h₁ hc
  simp [rawCoefficient, hd₁, hd₂, hq, hp, hz]

/-- The displayed coefficient formula, now for the actual regrouped finite sum. -/
theorem rawCoefficient_formula (k : ℕ) (α β γ δ ε : ℤ)
    (hα : 0 ≤ α) (hβ : 0 ≤ β) (hγ : 0 ≤ γ) (hδ : 0 ≤ δ) (hε : 0 ≤ ε)
    (hN : 2 * (k : ℤ) + 3 ≤ N) (hfit : α + β + γ + δ + ε ≤ N)
    (hdegree : shapeDegree (targetShape (N := N) α β γ δ ε) = 5 * (k : ℤ) + 2) :
    rawCoefficient k (targetShape (N := N) α β γ δ ε) =
      if α + β + γ = k ∧ δ = 0 then β + 1
      else if α + β + γ = (k : ℤ) + 1 ∧ γ = 0 then ε + 1 else 0 := by
  by_cases hs₀ : α + β + γ = k
  · have hs₁ : α + β + γ ≠ (k : ℤ) + 1 := by omega
    rw [rawCoefficient_firstSector k α β γ δ ε hα hβ hγ hδ hε hN hfit hs₀
      (firstSector_degree_relation k α β γ δ ε hα hβ hγ hδ hε hfit hs₀ hdegree)]
    split_ifs <;> omega
  · by_cases hs₁ : α + β + γ = (k : ℤ) + 1
    · rw [rawCoefficient_secondSector k α β γ δ ε hα hβ hγ hδ hε hN hfit hs₁
        (secondSector_degree_relation k α β γ δ ε hα hβ hγ hδ hε hfit hs₁ hdegree)]
      split_ifs <;> omega
    · have hc := (targetShape_heightCounts α β γ δ ε hα hβ hγ hδ hε hfit).2.2.1
      rw [rawCoefficient_otherSector k _ hN (by omega) (by omega)]
      simp only [hs₀, hs₁, false_and, if_false]

/-- Every coefficient occurring in the exact finite Schur sum is nonnegative. -/
theorem rawCoefficient_nonneg (k : ℕ) (hN : 2 * (k : ℤ) + 3 ≤ N)
    (nu : Fin N → ℕ) (hnu : nu ∈ targets (5 * (k : ℤ) + 2)) :
    0 ≤ rawCoefficient k nu := by
  obtain ⟨hmax, hpart, hdegree⟩ := (mem_targets _ nu).mp hnu
  obtain ⟨α, β, γ, δ, ε, ⟨hα, hβ, hγ, hδ, hε, hfit⟩, heq, hsector⟩ :=
    exists_target_parameters nu hpart hmax
  rw [heq] at hdegree ⊢
  rw [rawCoefficient_formula k α β γ δ ε hα hβ hγ hδ hε hN hfit hdegree]
  split_ifs <;> omega

/-- The lower-bound term `(5^k,1,1)` has coefficient exactly one. -/
theorem rawCoefficient_distinguished (k : ℕ) (hN : 2 * (k : ℤ) + 3 ≤ N) :
    rawCoefficient k (targetShape (N := N) k 0 0 0 2) = 1 := by
  have h := rawCoefficient_firstSector (N := N) k k 0 0 0 2
    (by omega) (by omega) (by omega) (by omega) (by omega) hN (by omega) (by omega) (by omega)
  simpa using h

end CoefficientOne.ScalarCoefficients