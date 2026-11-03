import CoefficientOne.VerticalPieri
import CoefficientOne.SignedLoad
import CoefficientOne.PieriCounts

/-!
# Exact vertical-strip conditions for the scalar coefficient lemma

The target rows are `(5^α,4^β,3^γ,2^δ,1^ε)`. We prove the rowwise
conditions and uniqueness of the subset underlying Pieri before counting any
source indices. This is the manuscript's Step 3, not an assumption of its
coefficient formulas. Vertical Pieri itself is proved in `VerticalPieri.lean`.
-/

namespace CoefficientOne.ScalarPieriShapes

open Finset SignedLoad AlternantCancellation

variable {N : ℕ}

/-- The target partition, in one-based integer row coordinates. -/
def targetPart (α β γ δ ε r : ℤ) : ℤ :=
  if r ≤ α then 5 else if r ≤ α + β then 4
  else if r ≤ α + β + γ then 3 else if r ≤ α + β + γ + δ then 2
  else if r ≤ α + β + γ + δ + ε then 1 else 0

def targetShape (α β γ δ ε : ℤ) (i : Fin N) : ℕ :=
  (targetPart α β γ δ ε (rowIndex i)).toNat

theorem targetShape_isPartition (α β γ δ ε : ℤ)
    (_hβ : 0 ≤ β) (_hγ : 0 ≤ γ) (_hδ : 0 ≤ δ) (_hε : 0 ≤ ε) :
    AlgebraicCombinatorics.IsNPartition (targetShape (N := N) α β γ δ ε) := by
  intro i z hiz
  unfold targetShape targetPart rowIndex
  split_ifs <;> omega

/-- Rowwise containment with at most one added box in each row. -/
def RowStrip (mu nu : Fin N → ℕ) : Prop := ∀ i, mu i ≤ nu i ∧ nu i ≤ mu i + 1

theorem exists_subset_iff_rowStrip (mu nu : Fin N → ℕ) :
    (∃ S : Finset (Fin N), mu + subsetIndicator S = nu) ↔ RowStrip mu nu := by
  classical
  constructor
  · rintro ⟨S, rfl⟩ i
    simp only [Pi.add_apply, subsetIndicator]
    split_ifs <;> omega
  · intro h
    refine ⟨univ.filter (fun i => mu i < nu i), ?_⟩
    funext i
    have hi := h i
    simp only [Pi.add_apply, subsetIndicator, Finset.mem_filter, Finset.mem_univ, true_and]
    split_ifs <;> omega

theorem subset_unique (mu nu : Fin N → ℕ) (S T : Finset (Fin N))
    (hS : mu + subsetIndicator S = nu) (hT : mu + subsetIndicator T = nu) : S = T := by
  ext i
  have hs := congrFun hS i
  have ht := congrFun hT i
  simp only [Pi.add_apply, subsetIndicator] at hs ht
  split_ifs at hs ht <;> simp_all

/-- A fixed source and target determine at most one vertical strip. -/
theorem existsUnique_subset_iff_rowStrip (mu nu : Fin N → ℕ) :
    (∃! S : Finset (Fin N), mu + subsetIndicator S = nu) ↔ RowStrip mu nu := by
  constructor
  · intro h
    exact (exists_subset_iff_rowStrip mu nu).mp h.exists
  · intro h
    obtain ⟨S, hS⟩ := (exists_subset_iff_rowStrip mu nu).mpr h
    exact ⟨S, hS, fun T hT => subset_unique mu nu T S hT hS⟩

/-- In the first sector, the Q row inequalities are exactly the two
integer intervals in the manuscript. All padded rows are included. -/
theorem qPart_firstSector_iff (k j α β γ δ ε M : ℤ)
    (hα : 0 ≤ α) (hβ : 0 ≤ β) (hγ : 0 ≤ γ) (_hδ : 0 ≤ δ) (hε : 0 ≤ ε)
    (hj : 0 ≤ j) (hjk : j ≤ k) (hN : 2 * k + 3 ≤ M)
    (hsector : α + β + γ = k) :
    (∀ r : ℤ, 1 ≤ r → r ≤ M →
      qPart k j r ≤ targetPart α β γ δ ε r ∧
      targetPart α β γ δ ε r ≤ qPart k j r + 1) ↔
      γ ≤ j ∧ j ≤ β + γ ∧ δ - 2 ≤ j ∧ j ≤ δ + ε - 2 := by
  constructor
  · intro h
    refine ⟨?_, ?_, ?_, ?_⟩
    · by_contra hn
      have ht := h (k - j) (by omega) (by omega)
      unfold qPart targetPart at ht
      split_ifs at ht <;> omega
    · by_contra hn
      have ht := h (k - j + 1) (by omega) (by omega)
      unfold qPart targetPart at ht
      split_ifs at ht <;> omega
    · by_contra hn
      have ht := h (k + j + 3) (by omega) (by omega)
      unfold qPart targetPart at ht
      split_ifs at ht <;> omega
    · by_contra hn
      have ht := h (k + j + 2) (by omega) (by omega)
      unfold qPart targetPart at ht
      split_ifs at ht <;> omega
  · rintro ⟨h₁, h₂, h₃, h₄⟩ r hr hrN
    unfold qPart targetPart
    split_ifs <;> omega


set_option maxHeartbeats 1200000 in
/-- The distinguished two-box row must remain two in the first sector. -/
theorem pPart_firstSector_iff (k j α β γ δ ε M : ℤ)
    (hα : 0 ≤ α) (hβ : 0 ≤ β) (hγ : 0 ≤ γ) (hδ : 0 ≤ δ) (hε : 0 ≤ ε)
    (hj : 0 ≤ j) (hjk : j ≤ k) (hN : 2 * k + 3 ≤ M)
    (hsector : α + β + γ = k) :
    (∀ r : ℤ, 1 ≤ r → r ≤ M →
      pPart k j r ≤ targetPart α β γ δ ε r ∧
      targetPart α β γ δ ε r ≤ pPart k j r + 1) ↔
      1 ≤ δ ∧ γ ≤ j ∧ j ≤ β + γ ∧ δ - 1 ≤ j ∧ j ≤ δ + ε - 1 := by
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

/-- Passing between finite padded rows and one-based integer coordinates loses
no row: the map `rowIndex` enumerates exactly `[1,N]`. -/
theorem rowStrip_toNat_iff (f g : ℤ → ℤ) (hf : ∀ r, 0 ≤ f r) (hg : ∀ r, 0 ≤ g r) :
    RowStrip (fun i : Fin N => (f (rowIndex i)).toNat)
      (fun i => (g (rowIndex i)).toNat) ↔
      ∀ r : ℤ, 1 ≤ r → r ≤ N → f r ≤ g r ∧ g r ≤ f r + 1 := by
  constructor
  · intro h r hr hN
    let i : Fin N := ⟨(r - 1).toNat, by omega⟩
    have hi : rowIndex i = r := by simp only [rowIndex, i]; omega
    have hh := h i
    change (f (rowIndex i)).toNat ≤ (g (rowIndex i)).toNat ∧ (g (rowIndex i)).toNat ≤ (f (rowIndex i)).toNat + 1 at hh
    rw [hi] at hh
    have := hf r
    have := hg r
    omega
  · intro h i
    change (f (rowIndex i)).toNat ≤ (g (rowIndex i)).toNat ∧ (g (rowIndex i)).toNat ≤ (f (rowIndex i)).toNat + 1
    have hi := Finset.mem_Icc.mp (rowIndex_mem i)
    have hh := h (rowIndex i) hi.1 hi.2
    have := hf (rowIndex i)
    have := hg (rowIndex i)
    omega

theorem targetPart_nonneg (α β γ δ ε r : ℤ) : 0 ≤ targetPart α β γ δ ε r := by
  unfold targetPart
  split_ifs <;> omega

theorem qShape_firstSector_iff (k j α β γ δ ε : ℤ)
    (hα : 0 ≤ α) (hβ : 0 ≤ β) (hγ : 0 ≤ γ) (hδ : 0 ≤ δ) (hε : 0 ≤ ε)
    (hj : 0 ≤ j) (hjk : j ≤ k) (hN : 2 * k + 3 ≤ N)
    (hsector : α + β + γ = k) :
    RowStrip (qShape k j) (targetShape (N := N) α β γ δ ε) ↔
      γ ≤ j ∧ j ≤ β + γ ∧ δ - 2 ≤ j ∧ j ≤ δ + ε - 2 := by
  unfold qShape targetShape
  rw [rowStrip_toNat_iff]
  · exact qPart_firstSector_iff k j α β γ δ ε N hα hβ hγ hδ hε hj hjk hN hsector
  · intro r; unfold qPart; split_ifs <;> omega
  · exact targetPart_nonneg α β γ δ ε

theorem pShape_firstSector_iff (k j α β γ δ ε : ℤ)
    (hα : 0 ≤ α) (hβ : 0 ≤ β) (hγ : 0 ≤ γ) (hδ : 0 ≤ δ) (hε : 0 ≤ ε)
    (hj : 0 ≤ j) (hjk : j ≤ k) (hN : 2 * k + 3 ≤ N)
    (hsector : α + β + γ = k) :
    RowStrip (pShape k j) (targetShape (N := N) α β γ δ ε) ↔
      1 ≤ δ ∧ γ ≤ j ∧ j ≤ β + γ ∧ δ - 1 ≤ j ∧ j ≤ δ + ε - 1 := by
  unfold pShape targetShape
  rw [rowStrip_toNat_iff]
  · exact pPart_firstSector_iff k j α β γ δ ε N hα hβ hγ hδ hε hj hjk hN hsector
  · intro r; unfold pPart; split_ifs <;> omega
  · exact targetPart_nonneg α β γ δ ε

/-- Exact existence and uniqueness for each Q source index. -/
theorem qShape_firstSector_unique (k j α β γ δ ε : ℤ)
    (hα : 0 ≤ α) (hβ : 0 ≤ β) (hγ : 0 ≤ γ) (hδ : 0 ≤ δ) (hε : 0 ≤ ε)
    (hj : 0 ≤ j) (hjk : j ≤ k) (hN : 2 * k + 3 ≤ N)
    (hsector : α + β + γ = k) :
    (∃! S : Finset (Fin N), qShape k j + subsetIndicator S =
      targetShape α β γ δ ε) ↔
      γ ≤ j ∧ j ≤ β + γ ∧ δ - 2 ≤ j ∧ j ≤ δ + ε - 2 := by
  rw [existsUnique_subset_iff_rowStrip]
  exact qShape_firstSector_iff k j α β γ δ ε hα hβ hγ hδ hε hj hjk hN hsector

/-- Exact existence and uniqueness for each P source index, including δ=0. -/
theorem pShape_firstSector_unique (k j α β γ δ ε : ℤ)
    (hα : 0 ≤ α) (hβ : 0 ≤ β) (hγ : 0 ≤ γ) (hδ : 0 ≤ δ) (hε : 0 ≤ ε)
    (hj : 0 ≤ j) (hjk : j ≤ k) (hN : 2 * k + 3 ≤ N)
    (hsector : α + β + γ = k) :
    (∃! S : Finset (Fin N), pShape k j + subsetIndicator S =
      targetShape α β γ δ ε) ↔
      1 ≤ δ ∧ γ ≤ j ∧ j ≤ β + γ ∧ δ - 1 ≤ j ∧ j ≤ δ + ε - 1 := by
  rw [existsUnique_subset_iff_rowStrip]
  exact pShape_firstSector_iff k j α β γ δ ε hα hβ hγ hδ hε hj hjk hN hsector


/-- The degree of the actual finite padded shape; no discarded rows are counted. -/
def shapeDegree (mu : Fin N → ℕ) : ℤ := ∑ i, (mu i : ℤ)

theorem shapeDegree_add_indicator (mu : Fin N → ℕ) (S : Finset (Fin N)) :
    shapeDegree (mu + subsetIndicator S) = shapeDegree mu + (S.card : ℤ) := by
  simp [shapeDegree, Pi.add_apply, Nat.cast_add, Finset.sum_add_distrib, subsetIndicator]

/-- The usual degree argument proves the cardinality of the unique strip. -/
theorem strip_card_of_degree (mu nu : Fin N → ℕ) (S : Finset (Fin N)) (k : ℕ)
    (hS : mu + subsetIndicator S = nu)
    (hdegree : shapeDegree nu = shapeDegree mu + k) : S.card = k := by
  have hh := shapeDegree_add_indicator mu S
  rw [hS, hdegree] at hh
  omega

theorem prefix_sum (t : ℤ) (ht : 0 ≤ t) (hN : t ≤ N) :
    (∑ i : Fin N, if rowIndex i ≤ t then (1 : ℤ) else 0) = t := by
  rw [Finset.sum_boole]
  have hc : (univ.filter (fun i : Fin N => rowIndex i ≤ t)).card = (Icc 1 t).card := by
    refine Finset.card_bij (fun i _ => rowIndex i) ?_ ?_ ?_
    · intro i hi
      have hir := Finset.mem_Icc.mp (rowIndex_mem i)
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hi
      exact Finset.mem_Icc.mpr ⟨hir.1, hi⟩
    · intro i hi z hz heq
      apply Fin.ext
      unfold rowIndex at heq
      omega
    · intro r hr
      have hr' := Finset.mem_Icc.mp hr
      let i : Fin N := ⟨(r - 1).toNat, by omega⟩
      have hi : rowIndex i = r := by simp only [rowIndex, i]; omega
      refine ⟨i, ?_, hi⟩
      simp only [Finset.mem_filter, Finset.mem_univ, true_and, hi]
      exact hr'.2
  rw [hc, Int.card_Icc]
  omega

theorem targetShape_degree (α β γ δ ε : ℤ)
    (hα : 0 ≤ α) (hβ : 0 ≤ β) (hγ : 0 ≤ γ) (hδ : 0 ≤ δ) (hε : 0 ≤ ε)
    (hN : α + β + γ + δ + ε ≤ N) :
    shapeDegree (targetShape (N := N) α β γ δ ε) =
      5 * α + 4 * β + 3 * γ + 2 * δ + ε := by
  have hp (i : Fin N) : ((targetShape α β γ δ ε i : ℕ) : ℤ) =
      (if rowIndex i ≤ α then 1 else 0) +
      (if rowIndex i ≤ α + β then 1 else 0) +
      (if rowIndex i ≤ α + β + γ then 1 else 0) +
      (if rowIndex i ≤ α + β + γ + δ then 1 else 0) +
      (if rowIndex i ≤ α + β + γ + δ + ε then 1 else 0) := by
    unfold targetShape targetPart
    split_ifs <;> omega
  unfold shapeDegree
  simp_rw [hp, Finset.sum_add_distrib]
  rw [prefix_sum α hα (by omega), prefix_sum (α + β) (by omega) (by omega),
    prefix_sum (α + β + γ) (by omega) (by omega),
    prefix_sum (α + β + γ + δ) (by omega) (by omega),
    prefix_sum (α + β + γ + δ + ε) (by omega) hN]
  omega

theorem qShape_degree (k j : ℤ) (hj : 0 ≤ j) (hjk : j ≤ k)
    (hN : 2 * k + 3 ≤ N) : shapeDegree (qShape (N := N) k j) = 4 * k + 2 := by
  have hp (i : Fin N) : ((qShape k j i : ℕ) : ℤ) =
      (if rowIndex i ≤ k - j then 1 else 0) +
      2 * (if rowIndex i ≤ k then 1 else 0) +
      (if rowIndex i ≤ k + j + 2 then 1 else 0) := by
    unfold qShape qPart
    split_ifs <;> omega
  unfold shapeDegree
  simp_rw [hp, Finset.sum_add_distrib, ← Finset.mul_sum]
  rw [prefix_sum (k - j) (by omega) (by omega),
    prefix_sum k (by omega) (by omega),
    prefix_sum (k + j + 2) (by omega) (by omega)]
  omega

theorem pShape_degree (k j : ℤ) (hj : 0 ≤ j) (hjk : j ≤ k)
    (hN : 2 * k + 3 ≤ N) : shapeDegree (pShape (N := N) k j) = 4 * k + 2 := by
  have hp (i : Fin N) : ((pShape k j i : ℕ) : ℤ) =
      (if rowIndex i ≤ k - j then 1 else 0) +
      (if rowIndex i ≤ k then 1 else 0) +
      (if rowIndex i ≤ k + 1 then 1 else 0) +
      (if rowIndex i ≤ k + j + 1 then 1 else 0) := by
    unfold pShape pPart
    split_ifs <;> omega
  unfold shapeDegree
  simp_rw [hp, Finset.sum_add_distrib]
  rw [prefix_sum (k - j) (by omega) (by omega),
    prefix_sum k (by omega) (by omega),
    prefix_sum (k + 1) (by omega) (by omega),
    prefix_sum (k + j + 1) (by omega) (by omega)]
  omega


/-- The exact Pieri-index predicate, including the strip's cardinality. -/
def IsPieriSubset (mu nu : Fin N → ℕ) (k : ℕ) (S : Finset (Fin N)) : Prop :=
  S ∈ (univ : Finset (Fin N)).powersetCard k ∧ mu + subsetIndicator S = nu

theorem existsUnique_pieriSubset_iff (mu nu : Fin N → ℕ) (k : ℕ)
    (hdegree : shapeDegree nu = shapeDegree mu + k) :
    (∃! S : Finset (Fin N), IsPieriSubset mu nu k S) ↔ RowStrip mu nu := by
  constructor
  · rintro ⟨S, hS, huniq⟩
    exact (exists_subset_iff_rowStrip mu nu).mp ⟨S, hS.2⟩
  · intro h
    obtain ⟨S, hS⟩ := (exists_subset_iff_rowStrip mu nu).mpr h
    refine ⟨S, ⟨?_, hS⟩, ?_⟩
    · simp only [Finset.mem_powersetCard, Finset.subset_univ, true_and]
      exact strip_card_of_degree mu nu S k hS hdegree
    · intro T hT
      exact subset_unique mu nu T S hT.2 hS

theorem exists_pieriSubset_iff (mu nu : Fin N → ℕ) (k : ℕ)
    (hdegree : shapeDegree nu = shapeDegree mu + k) :
    (∃ S : Finset (Fin N), IsPieriSubset mu nu k S) ↔ RowStrip mu nu := by
  constructor
  · rintro ⟨S, hS⟩
    exact (exists_subset_iff_rowStrip mu nu).mp ⟨S, hS.2⟩
  · intro h
    exact ((existsUnique_pieriSubset_iff mu nu k hdegree).mpr h).exists

/-- Each admissible Q index contributes one actual k-box vertical strip. -/
theorem qShape_firstSector_pieri (k j α β γ δ ε : ℤ)
    (hα : 0 ≤ α) (hβ : 0 ≤ β) (hγ : 0 ≤ γ) (hδ : 0 ≤ δ) (hε : 0 ≤ ε)
    (hj : 0 ≤ j) (hjk : j ≤ k) (hN : 2 * k + 3 ≤ N)
    (hfit : α + β + γ + δ + ε ≤ N)
    (hsector : α + β + γ = k) (hdegree : ε = β + 2 * γ + 2 - 2 * δ) :
    (∃! S : Finset (Fin N), IsPieriSubset (qShape k j)
      (targetShape α β γ δ ε) k.toNat S) ↔
      γ ≤ j ∧ j ≤ β + γ ∧ δ - 2 ≤ j ∧ j ≤ δ + ε - 2 := by
  rw [existsUnique_pieriSubset_iff]
  · exact qShape_firstSector_iff k j α β γ δ ε hα hβ hγ hδ hε hj hjk hN hsector
  · rw [targetShape_degree α β γ δ ε hα hβ hγ hδ hε hfit,
      qShape_degree k j hj hjk hN]
    omega

/-- Each admissible P index contributes one actual k-box vertical strip. -/
theorem pShape_firstSector_pieri (k j α β γ δ ε : ℤ)
    (hα : 0 ≤ α) (hβ : 0 ≤ β) (hγ : 0 ≤ γ) (hδ : 0 ≤ δ) (hε : 0 ≤ ε)
    (hj : 0 ≤ j) (hjk : j ≤ k) (hN : 2 * k + 3 ≤ N)
    (hfit : α + β + γ + δ + ε ≤ N)
    (hsector : α + β + γ = k) (hdegree : ε = β + 2 * γ + 2 - 2 * δ) :
    (∃! S : Finset (Fin N), IsPieriSubset (pShape k j)
      (targetShape α β γ δ ε) k.toNat S) ↔
      1 ≤ δ ∧ γ ≤ j ∧ j ≤ β + γ ∧ δ - 1 ≤ j ∧ j ≤ δ + ε - 1 := by
  rw [existsUnique_pieriSubset_iff]
  · exact pShape_firstSector_iff k j α β γ δ ε hα hβ hγ hδ hε hj hjk hN hsector
  · rw [targetShape_degree α β γ δ ε hα hβ hγ hδ hε hfit,
      pShape_degree k j hj hjk hN]
    omega

attribute [local instance] Classical.propDecidable

/-- Source indices with a vertical strip reaching this exact finite target. -/
noncomputable def pieriSourceIndices (source : ℤ → Fin N → ℕ) (nu : Fin N → ℕ)
    (k : ℕ) (lo hi : ℤ) : Finset ℤ :=
  (Icc lo hi).filter (fun j => ∃! S : Finset (Fin N), IsPieriSubset (source j) nu k S)

/-- The Q count really counts source indices and their unique Pieri strips. -/
theorem q_firstSector_sourceIndices (k α β γ δ ε : ℤ)
    (hα : 0 ≤ α) (hβ : 0 ≤ β) (hγ : 0 ≤ γ) (hδ : 0 ≤ δ) (hε : 0 ≤ ε)
    (hN : 2 * k + 3 ≤ N) (hfit : α + β + γ + δ + ε ≤ N)
    (hsector : α + β + γ = k) (hdegree : ε = β + 2 * γ + 2 - 2 * δ) :
    pieriSourceIndices (qShape k) (targetShape (N := N) α β γ δ ε) k.toNat 0 k =
      Icc γ (β + γ) ∩ Icc (δ - 2) (δ + ε - 2) := by
  ext j
  simp only [pieriSourceIndices, Finset.mem_filter, Finset.mem_Icc, Finset.mem_inter]
  constructor
  · rintro ⟨⟨hj, hjk⟩, h⟩
    have hh := (qShape_firstSector_pieri k j α β γ δ ε hα hβ hγ hδ hε
      hj hjk hN hfit hsector hdegree).mp h
    omega
  · intro hh
    have hj : 0 ≤ j := by omega
    have hjk : j ≤ k := by omega
    refine ⟨⟨hj, hjk⟩, ?_⟩
    exact (qShape_firstSector_pieri k j α β γ δ ε hα hβ hγ hδ hε
      hj hjk hN hfit hsector hdegree).mpr (by omega)

/-- P has no first-sector strip when δ=0, as well as the stated interval otherwise. -/
theorem p_firstSector_sourceIndices (k α β γ δ ε : ℤ)
    (hα : 0 ≤ α) (hβ : 0 ≤ β) (hγ : 0 ≤ γ) (hδ : 0 ≤ δ) (hε : 0 ≤ ε)
    (hN : 2 * k + 3 ≤ N) (hfit : α + β + γ + δ + ε ≤ N)
    (hsector : α + β + γ = k) (hdegree : ε = β + 2 * γ + 2 - 2 * δ) :
    pieriSourceIndices (pShape k) (targetShape (N := N) α β γ δ ε) k.toNat 0 k =
      if δ = 0 then ∅ else Icc γ (β + γ) ∩ Icc (δ - 1) (δ + ε - 1) := by
  ext j
  simp only [pieriSourceIndices, Finset.mem_filter, Finset.mem_Icc]
  by_cases hd : δ = 0
  · rw [if_pos hd]
    simp only [Finset.notMem_empty, iff_false, not_and]
    intro hj
    rw [pShape_firstSector_pieri k j α β γ δ ε hα hβ hγ hδ hε
      hj.1 hj.2 hN hfit hsector hdegree]
    omega
  · rw [if_neg hd]
    simp only [Finset.mem_inter, Finset.mem_Icc]
    constructor
    · rintro ⟨⟨hj, hjk⟩, h⟩
      have hh := (pShape_firstSector_pieri k j α β γ δ ε hα hβ hγ hδ hε
        hj hjk hN hfit hsector hdegree).mp h
      omega
    · intro hh
      have hj : 0 ≤ j := by omega
      have hjk : j ≤ k := by omega
      refine ⟨⟨hj, hjk⟩, ?_⟩
      exact (pShape_firstSector_pieri k j α β γ δ ε hα hβ hγ hδ hε
        hj hjk hN hfit hsector hdegree).mpr (by omega)

theorem q_firstSector_count (k α β γ δ ε : ℤ)
    (hα : 0 ≤ α) (hβ : 0 ≤ β) (hγ : 0 ≤ γ) (hδ : 0 ≤ δ) (hε : 0 ≤ ε)
    (hN : 2 * k + 3 ≤ N) (hfit : α + β + γ + δ + ε ≤ N)
    (hsector : α + β + γ = k) (hdegree : ε = β + 2 * γ + 2 - 2 * δ) :
    (pieriSourceIndices (qShape k) (targetShape (N := N) α β γ δ ε) k.toNat 0 k).card =
      intervalCount γ (β + γ) (δ - 2) (δ + ε - 2) := by
  rw [q_firstSector_sourceIndices k α β γ δ ε hα hβ hγ hδ hε hN hfit hsector hdegree]
  rfl

theorem p_firstSector_count (k α β γ δ ε : ℤ)
    (hα : 0 ≤ α) (hβ : 0 ≤ β) (hγ : 0 ≤ γ) (hδ : 0 ≤ δ) (hε : 0 ≤ ε)
    (hN : 2 * k + 3 ≤ N) (hfit : α + β + γ + δ + ε ≤ N)
    (hsector : α + β + γ = k) (hdegree : ε = β + 2 * γ + 2 - 2 * δ) :
    (pieriSourceIndices (pShape k) (targetShape (N := N) α β γ δ ε) k.toNat 0 k).card =
      if δ = 0 then 0 else intervalCount γ (β + γ) (δ - 1) (δ + ε - 1) := by
  rw [p_firstSector_sourceIndices k α β γ δ ε hα hβ hγ hδ hε hN hfit hsector hdegree]
  split_ifs <;> rfl

end CoefficientOne.ScalarPieriShapes