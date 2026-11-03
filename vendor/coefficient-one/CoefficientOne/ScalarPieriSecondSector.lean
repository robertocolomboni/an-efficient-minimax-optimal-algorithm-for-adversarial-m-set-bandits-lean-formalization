import CoefficientOne.ScalarPieriShapes

/-!
# The second sector of the scalar Pieri expansion

The exact Z/P vertical-strip conditions in Step 4 of the manuscript, followed
by their integer source counts. All cardinalities refer to actual subsets of
rows, and all row shapes and degrees come from the verified load expansion.
-/

namespace CoefficientOne.ScalarPieriShapes

open Finset SignedLoad AlternantCancellation

variable {N : ℕ}

set_option maxHeartbeats 1200000 in
/-- Z's four/three blocks and its one-box block give the two stated intervals. -/
theorem zPart_secondSector_iff (k j α β γ δ ε M : ℤ)
    (hα : 0 ≤ α) (hβ : 0 ≤ β) (hγ : 0 ≤ γ) (hδ : 0 ≤ δ) (hε : 0 ≤ ε)
    (hj : 0 ≤ j) (hjk : j ≤ k - 1) (hN : 2 * k + 3 ≤ M)
    (hsector : α + β + γ = k + 1) :
    (∀ r : ℤ, 1 ≤ r → r ≤ M →
      zPart k j r ≤ targetPart α β γ δ ε r ∧
      targetPart α β γ δ ε r ≤ zPart k j r + 1) ↔
      γ - 2 ≤ j ∧ j ≤ β + γ - 2 ∧ δ ≤ j ∧ j ≤ δ + ε := by
  constructor
  · intro h
    refine ⟨?_, ?_, ?_, ?_⟩
    · by_contra hn
      have ht := h (k - j - 1) (by omega) (by omega)
      unfold zPart targetPart at ht
      split_ifs at ht <;> omega
    · by_contra hn
      have ht := h (k - j) (by omega) (by omega)
      unfold zPart targetPart at ht
      split_ifs at ht <;> omega
    · by_contra hn
      have ht := h (k + j + 2) (by omega) (by omega)
      unfold zPart targetPart at ht
      split_ifs at ht <;> omega
    · by_contra hn
      have ht := h (k + j + 1) (by omega) (by omega)
      unfold zPart targetPart at ht
      split_ifs at ht <;> omega
  · rintro ⟨h₁, h₂, h₃, h₄⟩ r hr hrN
    unfold zPart targetPart
    split_ifs <;> omega

set_option maxHeartbeats 1200000 in
/-- P's distinguished row becomes three, forcing γ≥1. -/
theorem pPart_secondSector_iff (k j α β γ δ ε M : ℤ)
    (hα : 0 ≤ α) (hβ : 0 ≤ β) (hγ : 0 ≤ γ) (hδ : 0 ≤ δ) (hε : 0 ≤ ε)
    (hj : 0 ≤ j) (hjk : j ≤ k) (hN : 2 * k + 3 ≤ M)
    (hsector : α + β + γ = k + 1) :
    (∀ r : ℤ, 1 ≤ r → r ≤ M →
      pPart k j r ≤ targetPart α β γ δ ε r ∧
      targetPart α β γ δ ε r ≤ pPart k j r + 1) ↔
      1 ≤ γ ∧ γ - 1 ≤ j ∧ j ≤ β + γ - 1 ∧ δ ≤ j ∧ j ≤ δ + ε := by
  constructor
  · intro h
    refine ⟨?_, ?_, ?_, ?_, ?_⟩
    · by_contra hn
      have ht := h (k + 1) (by omega) (by omega)
      unfold pPart targetPart at ht
      split_ifs at ht <;> omega
    · by_contra hn
      have ht := h (k - j) (by omega) (by omega)
      unfold pPart targetPart at ht
      split_ifs at ht <;> omega
    · by_contra hn
      have ht := h (k - j + 1) (by omega) (by omega)
      unfold pPart targetPart at ht
      split_ifs at ht <;> omega
    · by_contra hn
      have ht := h (k + j + 2) (by omega) (by omega)
      unfold pPart targetPart at ht
      split_ifs at ht <;> omega
    · by_contra hn
      have ht := h (k + j + 1) (by omega) (by omega)
      unfold pPart targetPart at ht
      split_ifs at ht <;> omega
  · rintro ⟨h₀, h₁, h₂, h₃, h₄⟩ r hr hrN
    unfold pPart targetPart
    split_ifs <;> omega

theorem zShape_secondSector_iff (k j α β γ δ ε : ℤ)
    (hα : 0 ≤ α) (hβ : 0 ≤ β) (hγ : 0 ≤ γ) (hδ : 0 ≤ δ) (hε : 0 ≤ ε)
    (hj : 0 ≤ j) (hjk : j ≤ k - 1) (hN : 2 * k + 3 ≤ N)
    (hsector : α + β + γ = k + 1) :
    RowStrip (zShape k j) (targetShape (N := N) α β γ δ ε) ↔
      γ - 2 ≤ j ∧ j ≤ β + γ - 2 ∧ δ ≤ j ∧ j ≤ δ + ε := by
  unfold zShape targetShape
  rw [rowStrip_toNat_iff]
  · exact zPart_secondSector_iff k j α β γ δ ε N hα hβ hγ hδ hε hj hjk hN hsector
  · intro r; unfold zPart; split_ifs <;> omega
  · exact targetPart_nonneg α β γ δ ε

theorem pShape_secondSector_iff (k j α β γ δ ε : ℤ)
    (hα : 0 ≤ α) (hβ : 0 ≤ β) (hγ : 0 ≤ γ) (hδ : 0 ≤ δ) (hε : 0 ≤ ε)
    (hj : 0 ≤ j) (hjk : j ≤ k) (hN : 2 * k + 3 ≤ N)
    (hsector : α + β + γ = k + 1) :
    RowStrip (pShape k j) (targetShape (N := N) α β γ δ ε) ↔
      1 ≤ γ ∧ γ - 1 ≤ j ∧ j ≤ β + γ - 1 ∧ δ ≤ j ∧ j ≤ δ + ε := by
  unfold pShape targetShape
  rw [rowStrip_toNat_iff]
  · exact pPart_secondSector_iff k j α β γ δ ε N hα hβ hγ hδ hε hj hjk hN hsector
  · intro r; unfold pPart; split_ifs <;> omega
  · exact targetPart_nonneg α β γ δ ε

theorem zShape_degree (k j : ℤ) (hj : 0 ≤ j) (hjk : j ≤ k - 1)
    (hN : 2 * k + 3 ≤ N) : shapeDegree (zShape (N := N) k j) = 4 * k + 2 := by
  have hp (i : Fin N) : ((zShape k j i : ℕ) : ℤ) =
      (if rowIndex i ≤ k - j - 1 then 1 else 0) +
      2 * (if rowIndex i ≤ k + 1 then 1 else 0) +
      (if rowIndex i ≤ k + j + 1 then 1 else 0) := by
    unfold zShape zPart
    split_ifs <;> omega
  unfold shapeDegree
  simp_rw [hp, Finset.sum_add_distrib, ← Finset.mul_sum]
  rw [prefix_sum (k - j - 1) (by omega) (by omega),
    prefix_sum (k + 1) (by omega) (by omega),
    prefix_sum (k + j + 1) (by omega) (by omega)]
  omega

/-- Each admissible Z index contributes exactly one k-box strip. -/
theorem zShape_secondSector_pieri (k j α β γ δ ε : ℤ)
    (hα : 0 ≤ α) (hβ : 0 ≤ β) (hγ : 0 ≤ γ) (hδ : 0 ≤ δ) (hε : 0 ≤ ε)
    (hj : 0 ≤ j) (hjk : j ≤ k - 1) (hN : 2 * k + 3 ≤ N)
    (hfit : α + β + γ + δ + ε ≤ N)
    (hsector : α + β + γ = k + 1) (hdegree : ε = β + 2 * γ - 3 - 2 * δ) :
    (∃! S : Finset (Fin N), IsPieriSubset (zShape k j)
      (targetShape α β γ δ ε) k.toNat S) ↔
      γ - 2 ≤ j ∧ j ≤ β + γ - 2 ∧ δ ≤ j ∧ j ≤ δ + ε := by
  rw [existsUnique_pieriSubset_iff]
  · exact zShape_secondSector_iff k j α β γ δ ε hα hβ hγ hδ hε hj hjk hN hsector
  · rw [targetShape_degree α β γ δ ε hα hβ hγ hδ hε hfit,
      zShape_degree k j hj hjk hN]
    omega

/-- Each admissible P index contributes exactly one k-box strip in sector two. -/
theorem pShape_secondSector_pieri (k j α β γ δ ε : ℤ)
    (hα : 0 ≤ α) (hβ : 0 ≤ β) (hγ : 0 ≤ γ) (hδ : 0 ≤ δ) (hε : 0 ≤ ε)
    (hj : 0 ≤ j) (hjk : j ≤ k) (hN : 2 * k + 3 ≤ N)
    (hfit : α + β + γ + δ + ε ≤ N)
    (hsector : α + β + γ = k + 1) (hdegree : ε = β + 2 * γ - 3 - 2 * δ) :
    (∃! S : Finset (Fin N), IsPieriSubset (pShape k j)
      (targetShape α β γ δ ε) k.toNat S) ↔
      1 ≤ γ ∧ γ - 1 ≤ j ∧ j ≤ β + γ - 1 ∧ δ ≤ j ∧ j ≤ δ + ε := by
  rw [existsUnique_pieriSubset_iff]
  · exact pShape_secondSector_iff k j α β γ δ ε hα hβ hγ hδ hε hj hjk hN hsector
  · rw [targetShape_degree α β γ δ ε hα hβ hγ hδ hε hfit,
      pShape_degree k j hj hjk hN]
    omega


attribute [local instance] Classical.propDecidable

/-- The Z count really counts source indices and their unique Pieri strips. -/
theorem z_secondSector_sourceIndices (k α β γ δ ε : ℤ)
    (hα : 0 ≤ α) (hβ : 0 ≤ β) (hγ : 0 ≤ γ) (hδ : 0 ≤ δ) (hε : 0 ≤ ε)
    (hN : 2 * k + 3 ≤ N) (hfit : α + β + γ + δ + ε ≤ N)
    (hsector : α + β + γ = k + 1) (hdegree : ε = β + 2 * γ - 3 - 2 * δ) :
    pieriSourceIndices (zShape k) (targetShape (N := N) α β γ δ ε) k.toNat 0 (k - 1) =
      Icc (γ - 2) (β + γ - 2) ∩ Icc δ (δ + ε) := by
  ext j
  simp only [pieriSourceIndices, Finset.mem_filter, Finset.mem_Icc, Finset.mem_inter]
  constructor
  · rintro ⟨⟨hj, hjk⟩, h⟩
    have hh := (zShape_secondSector_pieri k j α β γ δ ε hα hβ hγ hδ hε
      hj hjk hN hfit hsector hdegree).mp h
    omega
  · intro hh
    have hj : 0 ≤ j := by omega
    have hjk : j ≤ k - 1 := by omega
    refine ⟨⟨hj, hjk⟩, ?_⟩
    exact (zShape_secondSector_pieri k j α β γ δ ε hα hβ hγ hδ hε
      hj hjk hN hfit hsector hdegree).mpr (by omega)

theorem z_secondSector_count (k α β γ δ ε : ℤ)
    (hα : 0 ≤ α) (hβ : 0 ≤ β) (hγ : 0 ≤ γ) (hδ : 0 ≤ δ) (hε : 0 ≤ ε)
    (hN : 2 * k + 3 ≤ N) (hfit : α + β + γ + δ + ε ≤ N)
    (hsector : α + β + γ = k + 1) (hdegree : ε = β + 2 * γ - 3 - 2 * δ) :
    (pieriSourceIndices (zShape k) (targetShape (N := N) α β γ δ ε) k.toNat 0 (k - 1)).card =
      intervalCount (γ - 2) (β + γ - 2) δ (δ + ε) := by
  rw [z_secondSector_sourceIndices k α β γ δ ε hα hβ hγ hδ hε hN hfit hsector hdegree]
  rfl

/-- P has no second-sector strip when γ=0, as well as the stated interval otherwise. -/
theorem p_secondSector_sourceIndices (k α β γ δ ε : ℤ)
    (hα : 0 ≤ α) (hβ : 0 ≤ β) (hγ : 0 ≤ γ) (hδ : 0 ≤ δ) (hε : 0 ≤ ε)
    (hN : 2 * k + 3 ≤ N) (hfit : α + β + γ + δ + ε ≤ N)
    (hsector : α + β + γ = k + 1) (hdegree : ε = β + 2 * γ - 3 - 2 * δ) :
    pieriSourceIndices (pShape k) (targetShape (N := N) α β γ δ ε) k.toNat 0 k =
      if γ = 0 then ∅ else Icc (γ - 1) (β + γ - 1) ∩ Icc δ (δ + ε) := by
  ext j
  simp only [pieriSourceIndices, Finset.mem_filter, Finset.mem_Icc]
  by_cases hd : γ = 0
  · rw [if_pos hd]
    simp only [Finset.notMem_empty, iff_false, not_and]
    intro hj
    rw [pShape_secondSector_pieri k j α β γ δ ε hα hβ hγ hδ hε
      hj.1 hj.2 hN hfit hsector hdegree]
    omega
  · rw [if_neg hd]
    simp only [Finset.mem_inter, Finset.mem_Icc]
    constructor
    · rintro ⟨⟨hj, hjk⟩, h⟩
      have hh := (pShape_secondSector_pieri k j α β γ δ ε hα hβ hγ hδ hε
        hj hjk hN hfit hsector hdegree).mp h
      omega
    · intro hh
      have hj : 0 ≤ j := by omega
      have hjk : j ≤ k := by omega
      refine ⟨⟨hj, hjk⟩, ?_⟩
      exact (pShape_secondSector_pieri k j α β γ δ ε hα hβ hγ hδ hε
        hj hjk hN hfit hsector hdegree).mpr (by omega)

theorem p_secondSector_count (k α β γ δ ε : ℤ)
    (hα : 0 ≤ α) (hβ : 0 ≤ β) (hγ : 0 ≤ γ) (hδ : 0 ≤ δ) (hε : 0 ≤ ε)
    (hN : 2 * k + 3 ≤ N) (hfit : α + β + γ + δ + ε ≤ N)
    (hsector : α + β + γ = k + 1) (hdegree : ε = β + 2 * γ - 3 - 2 * δ) :
    (pieriSourceIndices (pShape k) (targetShape (N := N) α β γ δ ε) k.toNat 0 k).card =
      if γ = 0 then 0 else intervalCount (γ - 1) (β + γ - 1) δ (δ + ε) := by
  rw [p_secondSector_sourceIndices k α β γ δ ε hα hβ hγ hδ hε hN hfit hsector hdegree]
  split_ifs <;> rfl




/-- Q cannot create an additional row of length at least three. -/
theorem qShape_not_secondSector (k j α β γ δ ε : ℤ)
    (hα : 0 ≤ α) (hβ : 0 ≤ β) (hγ : 0 ≤ γ)
    (hj : 0 ≤ j) (hjk : j ≤ k) (hN : 2 * k + 3 ≤ N)
    (hsector : α + β + γ = k + 1) :
    ¬ RowStrip (qShape k j) (targetShape (N := N) α β γ δ ε) := by
  intro h
  let i : Fin N := ⟨k.toNat, by omega⟩
  have hh := h i
  change (qPart k j (k.toNat + 1)).toNat ≤
    (targetPart α β γ δ ε (k.toNat + 1)).toNat ∧
    (targetPart α β γ δ ε (k.toNat + 1)).toNat ≤
      (qPart k j (k.toNat + 1)).toNat + 1 at hh
  unfold qPart targetPart at hh
  split_ifs at hh <;> omega

/-- Z already has k+1 long rows, so it cannot reach a first-sector target. -/
theorem zShape_not_firstSector (k j α β γ δ ε : ℤ)
    (hα : 0 ≤ α) (hβ : 0 ≤ β) (hγ : 0 ≤ γ)
    (hj : 0 ≤ j) (hjk : j ≤ k - 1) (hN : 2 * k + 3 ≤ N)
    (hsector : α + β + γ = k) :
    ¬ RowStrip (zShape k j) (targetShape (N := N) α β γ δ ε) := by
  intro h
  let i : Fin N := ⟨k.toNat, by omega⟩
  have hh := h i
  change (zPart k j (k.toNat + 1)).toNat ≤
    (targetPart α β γ δ ε (k.toNat + 1)).toNat ∧
    (targetPart α β γ δ ε (k.toNat + 1)).toNat ≤
      (zPart k j (k.toNat + 1)).toNat + 1 at hh
  unfold zPart targetPart at hh
  split_ifs at hh <;> omega

/-- The second-sector signed number of actual strips has the manuscript's
nonnegative coefficient, including γ=0 and every empty-interval case. -/
theorem secondSector_signedCount (k α β γ δ ε : ℤ)
    (hα : 0 ≤ α) (hβ : 0 ≤ β) (hγ : 0 ≤ γ) (hδ : 0 ≤ δ) (hε : 0 ≤ ε)
    (hN : 2 * k + 3 ≤ N) (hfit : α + β + γ + δ + ε ≤ N)
    (hsector : α + β + γ = k + 1) (hdegree : ε = β + 2 * γ - 3 - 2 * δ) :
    ((pieriSourceIndices (zShape k) (targetShape (N := N) α β γ δ ε)
      k.toNat 0 (k - 1)).card : ℤ) -
    ((pieriSourceIndices (pShape k) (targetShape (N := N) α β γ δ ε)
      k.toNat 0 k).card : ℤ) = if γ = 0 then ε + 1 else 0 := by
  rw [z_secondSector_count k α β γ δ ε hα hβ hγ hδ hε hN hfit hsector hdegree,
    p_secondSector_count k α β γ δ ε hα hβ hγ hδ hε hN hfit hsector hdegree]
  push_cast
  exact secondSector_coefficient β γ δ ε hδ hε hdegree

end CoefficientOne.ScalarPieriShapes