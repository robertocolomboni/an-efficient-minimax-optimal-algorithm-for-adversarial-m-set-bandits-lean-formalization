import CoefficientOne.ScalarPieriShapes

/-!
# The initial double-Pieri count

This is Step 2 of the scalar coefficient proof, equation `eq:initial-count`
in `paper/main.tex`.
Intermediate partitions are reconstructed from their two initial segments.
We count actual subsets of rows, using the proved vertical-Pieri interface.
-/

noncomputable section

namespace CoefficientOne.InitialPieriCount

open Finset ScalarPieriShapes SignedLoad AlgebraicCombinatorics

variable {N : ℕ}

def baseShape (k : ℤ) (i : Fin N) : ℕ := if rowIndex i ≤ k then 3 else 0

/-- Here `a` is the number of four-box rows and `b` the total number of rows. -/
def middlePart (k a b r : ℤ) : ℤ :=
  if r ≤ a then 4 else if r ≤ k then 3 else if r ≤ b then 1 else 0

def middleShape (k a b : ℤ) (i : Fin N) : ℕ := (middlePart k a b (rowIndex i)).toNat

def cutoff (mu : Fin N → ℕ) (c : ℕ) : ℤ :=
  ((univ.filter (fun i => c < mu i)).card : ℤ)

theorem cutoff_nonneg (mu : Fin N → ℕ) (c : ℕ) : 0 ≤ cutoff mu c := by
  unfold cutoff
  positivity

theorem cutoff_le (mu : Fin N → ℕ) (c : ℕ) : cutoff mu c ≤ N := by
  have h := Finset.card_le_card (Finset.filter_subset (fun i => c < mu i) univ)
  simp only [Finset.card_univ, Fintype.card_fin] at h
  unfold cutoff
  exact_mod_cast h

theorem rowIndex_le_cutoff_iff (mu : Fin N → ℕ) (hmu : AlgebraicCombinatorics.IsNPartition mu)
    (c : ℕ) (i : Fin N) : rowIndex i ≤ cutoff mu c ↔ c < mu i := by
  have h := Tuple.lt_card_gt_iff_apply_gt_of_antitone (j := i) (a := c) hmu
  simp only [rowIndex, cutoff]
  exact (show (i.val : ℤ) + 1 ≤ ((univ.filter (fun i => c < mu i)).card : ℤ) ↔
    i.val < (univ.filter (fun i => c < mu i)).card by omega).trans h

/-- The two first-strip row choices are initial segments, not arbitrary subsets. -/
theorem middleShape_eq_of_first_strip (k : ℤ) (mu : Fin N → ℕ)
    (hmu : AlgebraicCombinatorics.IsNPartition mu) (hstrip : RowStrip (baseShape k) mu) :
    mu = middleShape k (cutoff mu 3) (cutoff mu 0) := by
  funext i
  have h := hstrip i
  have h4 := rowIndex_le_cutoff_iff mu hmu 3 i
  have h1 := rowIndex_le_cutoff_iff mu hmu 0 i
  unfold baseShape at h
  unfold middleShape middlePart
  split_ifs at h ⊢ <;> omega

theorem four_cutoff_le_k (k : ℤ) (hk : 0 ≤ k) (mu : Fin N → ℕ)
    (hmu : AlgebraicCombinatorics.IsNPartition mu) (hstrip : RowStrip (baseShape k) mu) : cutoff mu 3 ≤ k := by
  by_contra hn
  have hc := cutoff_le mu 3
  let i : Fin N := ⟨k.toNat, by omega⟩
  have hi : rowIndex i = k + 1 := by simp only [rowIndex, i]; omega
  have h4 := (rowIndex_le_cutoff_iff mu hmu 3 i).mp (by rw [hi]; omega)
  have h := hstrip i
  unfold baseShape at h
  rw [hi, if_neg (by omega)] at h
  omega

theorem k_le_positive_cutoff (k : ℤ) (hN : k ≤ (N : ℤ)) (mu : Fin N → ℕ)
    (hmu : AlgebraicCombinatorics.IsNPartition mu) (hstrip : RowStrip (baseShape k) mu) : k ≤ cutoff mu 0 := by
  by_contra hn
  have hc := cutoff_nonneg mu 0
  let i : Fin N := ⟨(cutoff mu 0).toNat, by omega⟩
  have hi : rowIndex i = cutoff mu 0 + 1 := by simp only [rowIndex, i]; omega
  have h1 := rowIndex_le_cutoff_iff mu hmu 0 i
  have h := hstrip i
  unfold baseShape at h
  rw [hi, if_pos (by omega)] at h
  rw [hi] at h1
  omega

theorem middleShape_isPartition (k a b : ℤ) :
    AlgebraicCombinatorics.IsNPartition (middleShape (N := N) k a b) := by
  intro i j hij
  unfold middleShape middlePart rowIndex
  split_ifs <;> omega

theorem baseShape_isPartition (k : ℤ) : AlgebraicCombinatorics.IsNPartition (baseShape (N := N) k) := by
  intro i j hij
  unfold baseShape rowIndex
  split_ifs <;> omega

theorem base_middle_rowStrip (k a b : ℤ) (ha : a ≤ k) (hb : k ≤ b) :
    RowStrip (baseShape (N := N) k) (middleShape k a b) := by
  intro i
  unfold baseShape middleShape middlePart
  split_ifs <;> omega

set_option maxHeartbeats 1200000 in
theorem middle_target_part_iff (k a b α β γ δ ε M : ℤ)
    (ha0 : 0 ≤ a) (hak : a ≤ k) (hkb : k ≤ b) (hbM : b ≤ M)
    (hα : 0 ≤ α) (hβ : 0 ≤ β) (hγ : 0 ≤ γ) (hδ : 0 ≤ δ) (hε : 0 ≤ ε)
    (hsector : α + β + γ = k) (hfit : k + δ + ε ≤ M) :
    (∀ r : ℤ, 1 ≤ r → r ≤ M →
      middlePart k a b r ≤ targetPart α β γ δ ε r ∧
      targetPart α β γ δ ε r ≤ middlePart k a b r + 1) ↔
      α ≤ a ∧ a ≤ α + β ∧ k + δ ≤ b ∧ b ≤ k + δ + ε := by
  constructor
  · intro h
    refine ⟨?_, ?_, ?_, ?_⟩
    · by_contra hn
      have hh := h (a + 1) (by omega) (by omega)
      unfold middlePart targetPart at hh
      split_ifs at hh <;> omega
    · by_contra hn
      have hh := h a (by omega) (by omega)
      unfold middlePart targetPart at hh
      split_ifs at hh <;> omega
    · by_contra hn
      have hh := h (b + 1) (by omega) (by omega)
      unfold middlePart targetPart at hh
      split_ifs at hh <;> omega
    · by_contra hn
      have hh := h b (by omega) (by omega)
      unfold middlePart targetPart at hh
      split_ifs at hh <;> omega
  · rintro ⟨h₁, h₂, h₃, h₄⟩ r hr hrM
    unfold middlePart targetPart
    split_ifs <;> omega

theorem middle_target_iff (k a b α β γ δ ε : ℤ)
    (ha0 : 0 ≤ a) (hak : a ≤ k) (hkb : k ≤ b) (hbN : b ≤ N)
    (hα : 0 ≤ α) (hβ : 0 ≤ β) (hγ : 0 ≤ γ) (hδ : 0 ≤ δ) (hε : 0 ≤ ε)
    (hsector : α + β + γ = k) (hfit : k + δ + ε ≤ N) :
    RowStrip (middleShape k a b) (targetShape (N := N) α β γ δ ε) ↔
      α ≤ a ∧ a ≤ α + β ∧ k + δ ≤ b ∧ b ≤ k + δ + ε := by
  unfold middleShape targetShape
  rw [rowStrip_toNat_iff]
  · exact middle_target_part_iff k a b α β γ δ ε N ha0 hak hkb hbN
      hα hβ hγ hδ hε hsector hfit
  · intro r; unfold middlePart; split_ifs <;> omega
  · exact targetPart_nonneg α β γ δ ε

/-- Every admissible intermediate partition has unique parameters `x,y` in
the two boxes of the manuscript's convolution count. -/
theorem exists_middle_parameters (k α β γ δ ε : ℤ)
    (hα : 0 ≤ α) (hβ : 0 ≤ β) (hγ : 0 ≤ γ) (hδ : 0 ≤ δ) (hε : 0 ≤ ε)
    (hsector : α + β + γ = k) (hfit : k + δ + ε ≤ N)
    (mu : Fin N → ℕ) (hmu : AlgebraicCombinatorics.IsNPartition mu)
    (hfirst : RowStrip (baseShape k) mu)
    (hsecond : RowStrip mu (targetShape α β γ δ ε)) :
    ∃ x y : ℤ, 0 ≤ x ∧ x ≤ β ∧ 0 ≤ y ∧ y ≤ ε ∧
      mu = middleShape k (α + x) (k + δ + y) := by
  have hke : 0 ≤ k := by omega
  have ha := four_cutoff_le_k k hke mu hmu hfirst
  have hb := k_le_positive_cutoff k (by omega) mu hmu hfirst
  have heq := middleShape_eq_of_first_strip k mu hmu hfirst
  have hbounds := (middle_target_iff k (cutoff mu 3) (cutoff mu 0) α β γ δ ε
    (cutoff_nonneg mu 3) ha hb (cutoff_le mu 0)
    hα hβ hγ hδ hε hsector hfit).mp (by rw [← heq]; exact hsecond)
  refine ⟨cutoff mu 3 - α, cutoff mu 0 - k - δ, by omega, by omega,
    by omega, by omega, ?_⟩
  convert heq using 1 <;> congr 1 <;> omega


theorem middleShape_degree (k a b : ℤ)
    (ha0 : 0 ≤ a) (hak : a ≤ k) (hkb : k ≤ b) (hbN : b ≤ N) :
    shapeDegree (middleShape (N := N) k a b) = a + 2 * k + b := by
  have hp (i : Fin N) : ((middleShape k a b i : ℕ) : ℤ) =
      (if rowIndex i ≤ a then 1 else 0) +
      2 * (if rowIndex i ≤ k then 1 else 0) +
      (if rowIndex i ≤ b then 1 else 0) := by
    unfold middleShape middlePart
    split_ifs <;> omega
  unfold shapeDegree
  simp_rw [hp, Finset.sum_add_distrib, ← Finset.mul_sum]
  rw [prefix_sum a ha0 (by omega), prefix_sum k (by omega) (by omega),
    prefix_sum b (by omega) hbN]

theorem baseShape_degree (k : ℤ) (hk : 0 ≤ k) (hN : k ≤ N) :
    shapeDegree (baseShape (N := N) k) = 3 * k := by
  have hp (i : Fin N) : ((baseShape k i : ℕ) : ℤ) =
      3 * (if rowIndex i ≤ k then 1 else 0) := by
    unfold baseShape
    split_ifs <;> norm_num
  unfold shapeDegree
  simp_rw [hp, ← Finset.mul_sum]
  rw [prefix_sum k hk hN]

theorem cutoff_middle_four (k a b : ℤ)
    (ha0 : 0 ≤ a) (haN : a ≤ N) : cutoff (middleShape (N := N) k a b) 3 = a := by
  have heq : (univ.filter (fun i : Fin N => 3 < middleShape k a b i)) =
      univ.filter (fun i => rowIndex i ≤ a) := by
    ext i
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    unfold middleShape middlePart
    split_ifs <;> omega
  unfold cutoff
  rw [heq, ← Finset.sum_boole, prefix_sum a ha0 haN]

theorem cutoff_middle_positive (k a b : ℤ)
    (hak : a ≤ k) (hkb : k ≤ b) (hb0 : 0 ≤ b) (hbN : b ≤ N) :
    cutoff (middleShape (N := N) k a b) 0 = b := by
  have heq : (univ.filter (fun i : Fin N => 0 < middleShape k a b i)) =
      univ.filter (fun i => rowIndex i ≤ b) := by
    ext i
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    unfold middleShape middlePart
    split_ifs <;> omega
  unfold cutoff
  rw [heq, ← Finset.sum_boole, prefix_sum b hb0 hbN]

/-- The actual rows occupied by the first strip of the given intermediate shape. -/
def middleRows (k a b : ℤ) : Finset (Fin N) :=
  univ.filter (fun i => baseShape k i < middleShape k a b i)

theorem add_middleRows (k a b : ℤ) (hak : a ≤ k) (hkb : k ≤ b) :
    baseShape (N := N) k + subsetIndicator (middleRows k a b) = middleShape k a b := by
  funext i
  have h := base_middle_rowStrip (N := N) k a b hak hkb i
  simp only [Pi.add_apply, subsetIndicator, middleRows, Finset.mem_filter,
    Finset.mem_univ, true_and]
  split_ifs <;> omega

theorem middleRows_card (k a b : ℤ)
    (ha0 : 0 ≤ a) (hak : a ≤ k) (hkb : k ≤ b) (hbN : b ≤ N) :
    ((middleRows (N := N) k a b).card : ℤ) = a + b - k := by
  have h := shapeDegree_add_indicator (baseShape (N := N) k) (middleRows k a b)
  rw [add_middleRows k a b hak hkb, middleShape_degree k a b ha0 hak hkb hbN,
    baseShape_degree k (by omega) (by omega)] at h
  omega

theorem middleRows_injective (k a b c d : ℤ)
    (ha0 : 0 ≤ a) (hak : a ≤ k) (hkb : k ≤ b) (hbN : b ≤ N)
    (hc0 : 0 ≤ c) (hck : c ≤ k) (hkd : k ≤ d) (hdN : d ≤ N)
    (heq : middleRows (N := N) k a b = middleRows k c d) : a = c ∧ b = d := by
  have hm : middleShape (N := N) k a b = middleShape k c d := by
    rw [← add_middleRows k a b hak hkb, ← add_middleRows k c d hck hkd, heq]
  have h4 := congrArg (fun mu : Fin N → ℕ => cutoff mu 3) hm
  have h1 := congrArg (fun mu : Fin N → ℕ => cutoff mu 0) hm
  rw [cutoff_middle_four k a b ha0 (by omega),
    cutoff_middle_four k c d hc0 (by omega)] at h4
  rw [cutoff_middle_positive k a b hak hkb (by omega) hbN,
    cutoff_middle_positive k c d hck hkd (by omega) hdN] at h1
  exact ⟨h4, h1⟩

/-- A first strip of size t, with a partition intermediate shape and an actual
second vertical strip to the fixed target. The second size follows from degree. -/
def firstSubsets (k : ℤ) (nu : Fin N → ℕ) (t : ℕ) : Finset (Finset (Fin N)) := by
  classical
  exact (univ.powersetCard t).filter (fun S =>
    AlgebraicCombinatorics.IsNPartition (baseShape k + subsetIndicator S) ∧
      RowStrip (baseShape k + subsetIndicator S) nu)

theorem mem_firstSubsets (k : ℤ) (nu : Fin N → ℕ) (t : ℕ) (S : Finset (Fin N)) :
    S ∈ firstSubsets k nu t ↔ S.card = t ∧
      AlgebraicCombinatorics.IsNPartition (baseShape k + subsetIndicator S) ∧
      RowStrip (baseShape k + subsetIndicator S) nu := by
  classical
  simp only [firstSubsets, Finset.mem_filter, Finset.mem_powersetCard,
    Finset.subset_univ, true_and]

/-- The actual first-strip subsets are in bijection with the bounded pairs
`(x,y)` described in the manuscript. In particular, no multiplicity is assumed. -/
theorem firstSubsets_card (k α β γ δ ε : ℤ)
    (hα : 0 ≤ α) (hβ : 0 ≤ β) (hγ : 0 ≤ γ) (hδ : 0 ≤ δ) (hε : 0 ≤ ε)
    (hsector : α + β + γ = k) (hfit : k + δ + ε ≤ N) (t : ℕ) :
    (firstSubsets k (targetShape (N := N) α β γ δ ε) t).card =
      convolutionCount β ε ((t : ℤ) - α - δ) := by
  classical
  unfold convolutionCount
  symm
  refine Finset.card_bij (fun p _ => middleRows k (α + p.1) (k + δ + p.2)) ?_ ?_ ?_
  · intro p hp
    have hp' : 0 ≤ p.1 ∧ p.1 ≤ β ∧ 0 ≤ p.2 ∧ p.2 ≤ ε ∧
        p.1 + p.2 = (t : ℤ) - α - δ := by
      simpa only [convolutionPairs, Finset.mem_filter, Finset.product_eq_sprod,
        Finset.mem_product, Finset.mem_Icc, and_assoc] using hp
    rw [mem_firstSubsets, add_middleRows k (α + p.1) (k + δ + p.2) (by omega) (by omega)]
    refine ⟨?_, middleShape_isPartition _ _ _, ?_⟩
    · have h := middleRows_card (N := N) k (α + p.1) (k + δ + p.2)
        (by omega) (by omega) (by omega) (by omega)
      omega
    · exact (middle_target_iff k (α + p.1) (k + δ + p.2) α β γ δ ε
        (by omega) (by omega) (by omega) (by omega)
        hα hβ hγ hδ hε hsector hfit).mpr ⟨by omega, by omega, by omega, by omega⟩
  · intro p hp q hq heq
    have hp' : 0 ≤ p.1 ∧ p.1 ≤ β ∧ 0 ≤ p.2 ∧ p.2 ≤ ε ∧
        p.1 + p.2 = (t : ℤ) - α - δ := by
      simpa only [convolutionPairs, Finset.mem_filter, Finset.product_eq_sprod,
        Finset.mem_product, Finset.mem_Icc, and_assoc] using hp
    have hq' : 0 ≤ q.1 ∧ q.1 ≤ β ∧ 0 ≤ q.2 ∧ q.2 ≤ ε ∧
        q.1 + q.2 = (t : ℤ) - α - δ := by
      simpa only [convolutionPairs, Finset.mem_filter, Finset.product_eq_sprod,
        Finset.mem_product, Finset.mem_Icc, and_assoc] using hq
    have hh := middleRows_injective k (α + p.1) (k + δ + p.2) (α + q.1) (k + δ + q.2)
      (by omega) (by omega) (by omega) (by omega)
      (by omega) (by omega) (by omega) (by omega) heq
    exact Prod.ext (by omega) (by omega)
  · intro S hS
    obtain ⟨hcard, hpart, hsecond⟩ := (mem_firstSubsets k _ t S).mp hS
    have hfirst : RowStrip (baseShape k) (baseShape k + subsetIndicator S) :=
      (exists_subset_iff_rowStrip _ _).mp ⟨S, rfl⟩
    obtain ⟨x, y, hx0, hxβ, hy0, hyε, hmid⟩ := exists_middle_parameters
      k α β γ δ ε hα hβ hγ hδ hε hsector hfit _ hpart hfirst hsecond
    have heq : middleRows (N := N) k (α + x) (k + δ + y) = S :=
      subset_unique (baseShape k) _ _ _
        (add_middleRows k (α + x) (k + δ + y) (by omega) (by omega)) hmid
    have hc := middleRows_card (N := N) k (α + x) (k + δ + y)
      (by omega) (by omega) (by omega) (by omega)
    rw [heq, hcard] at hc
    refine ⟨(x, y), ?_, heq⟩
    simp only [convolutionPairs, Finset.mem_filter, Finset.product_eq_sprod,
      Finset.mem_product, Finset.mem_Icc]
    exact ⟨⟨⟨hx0, hxβ⟩, ⟨hy0, hyε⟩⟩, by omega⟩

theorem initial_doublePieri_count (k α β γ δ ε : ℤ)
    (hα : 0 ≤ α) (hβ : 0 ≤ β) (hγ : 0 ≤ γ) (hδ : 0 ≤ δ) (hε : 0 ≤ ε)
    (hsector : α + β + γ = k) (hfit : k + δ + ε ≤ N)
    (hdegree : ε = β + 2 * γ + 2 - 2 * δ) :
    ((firstSubsets k (targetShape (N := N) α β γ δ ε) (k + 1).toNat).card : ℤ) -
      ((firstSubsets k (targetShape (N := N) α β γ δ ε) k.toNat).card : ℤ) =
        if δ = γ + 1 then 1 else 0 := by
  rw [firstSubsets_card k α β γ δ ε hα hβ hγ hδ hε hsector hfit,
    firstSubsets_card k α β γ δ ε hα hβ hγ hδ hε hsector hfit]
  have hk : 0 ≤ k := by omega
  rw [Int.toNat_of_nonneg (show 0 ≤ k + 1 by omega), Int.toNat_of_nonneg hk]
  exact initialProduct_count k α β γ δ ε hβ hε hsector hdegree



/-- Actual ordered pairs of row subsets in the two successive Pieri sums. -/
def doubleSubsets (k : ℤ) (nu : Fin N → ℕ) (t s : ℕ) :
    Finset (Finset (Fin N) × Finset (Fin N)) := by
  classical
  exact ((univ.powersetCard t).product (univ.powersetCard s)).filter (fun p =>
    AlgebraicCombinatorics.IsNPartition (baseShape k + subsetIndicator p.1) ∧
      baseShape k + subsetIndicator p.1 + subsetIndicator p.2 = nu)

theorem mem_doubleSubsets (k : ℤ) (nu : Fin N → ℕ) (t s : ℕ)
    (p : Finset (Fin N) × Finset (Fin N)) :
    p ∈ doubleSubsets k nu t s ↔ p.1.card = t ∧ p.2.card = s ∧
      AlgebraicCombinatorics.IsNPartition (baseShape k + subsetIndicator p.1) ∧
      baseShape k + subsetIndicator p.1 + subsetIndicator p.2 = nu := by
  classical
  simp only [doubleSubsets, Finset.mem_filter, Finset.product_eq_sprod,
    Finset.mem_product, Finset.mem_powersetCard, Finset.subset_univ, true_and, and_assoc]

theorem firstSubset_second_unique (k : ℤ) (nu : Fin N → ℕ) (t s : ℕ)
    (hdegree : shapeDegree nu = shapeDegree (baseShape (N := N) k) + t + s)
    (S : Finset (Fin N)) (hS : S ∈ firstSubsets k nu t) :
    ∃! T : Finset (Fin N), IsPieriSubset (baseShape k + subsetIndicator S) nu s T := by
  obtain ⟨hcard, hpart, hstrip⟩ := (mem_firstSubsets k nu t S).mp hS
  apply (existsUnique_pieriSubset_iff _ _ s ?_).mpr hstrip
  rw [shapeDegree_add_indicator, hcard]
  exact hdegree

/-- Projection to the first strip is a bijection because the second strip's
row set and its size are both determined, including empty-strip cases. -/
theorem doubleSubsets_card_eq_first (k : ℤ) (nu : Fin N → ℕ) (t s : ℕ)
    (hdegree : shapeDegree nu = shapeDegree (baseShape (N := N) k) + t + s) :
    (doubleSubsets k nu t s).card = (firstSubsets k nu t).card := by
  classical
  refine Finset.card_bij (fun p _ => p.1) ?_ ?_ ?_
  · intro p hp
    obtain ⟨ht, hs, hpart, heq⟩ := (mem_doubleSubsets k nu t s p).mp hp
    rw [mem_firstSubsets]
    exact ⟨ht, hpart, (exists_subset_iff_rowStrip _ _).mp ⟨p.2, heq⟩⟩
  · intro p hp q hq heq
    obtain ⟨htp, hsp, hpartp, heqp⟩ := (mem_doubleSubsets k nu t s p).mp hp
    obtain ⟨htq, hsq, hpartq, heqq⟩ := (mem_doubleSubsets k nu t s q).mp hq
    apply Prod.ext heq
    rw [heq] at heqp
    exact subset_unique (baseShape k + subsetIndicator q.1) nu p.2 q.2 heqp heqq
  · intro S hS
    obtain ⟨T, hT, huniq⟩ := firstSubset_second_unique k nu t s hdegree S hS
    obtain ⟨hcard, hpart, hstrip⟩ := (mem_firstSubsets k nu t S).mp hS
    refine ⟨(S, T), ?_, rfl⟩
    rw [mem_doubleSubsets]
    exact ⟨hcard, (Finset.mem_powersetCard.mp hT.1).2, hpart, hT.2⟩

theorem doubleSubsets_card (k α β γ δ ε : ℤ)
    (hα : 0 ≤ α) (hβ : 0 ≤ β) (hγ : 0 ≤ γ) (hδ : 0 ≤ δ) (hε : 0 ≤ ε)
    (hsector : α + β + γ = k) (hfit : k + δ + ε ≤ N) (t s : ℕ)
    (hdegree : 5 * α + 4 * β + 3 * γ + 2 * δ + ε = 3 * k + t + s) :
    (doubleSubsets k (targetShape (N := N) α β γ δ ε) t s).card =
      convolutionCount β ε ((t : ℤ) - α - δ) := by
  rw [doubleSubsets_card_eq_first k _ t s ?_]
  · exact firstSubsets_card k α β γ δ ε hα hβ hγ hδ hε hsector hfit t
  · rw [targetShape_degree α β γ δ ε hα hβ hγ hδ hε (by omega),
      baseShape_degree k (by omega) (by omega)]
    exact hdegree

/-- The coefficient difference in the actual two-Pieri expansion, with both
strip sizes checked, is the manuscript's Kronecker condition. -/
theorem initial_doublePieri_pair_count (k α β γ δ ε : ℤ)
    (hα : 0 ≤ α) (hβ : 0 ≤ β) (hγ : 0 ≤ γ) (hδ : 0 ≤ δ) (hε : 0 ≤ ε)
    (hsector : α + β + γ = k) (hfit : k + δ + ε ≤ N)
    (hdegree : 5 * α + 4 * β + 3 * γ + 2 * δ + ε = 5 * k + 2) :
    ((doubleSubsets k (targetShape (N := N) α β γ δ ε)
      (k + 1).toNat (k + 1).toNat).card : ℤ) -
      ((doubleSubsets k (targetShape (N := N) α β γ δ ε)
        k.toNat (k + 2).toNat).card : ℤ) =
        if δ = γ + 1 then 1 else 0 := by
  have hk : 0 ≤ k := by omega
  rw [doubleSubsets_card k α β γ δ ε hα hβ hγ hδ hε hsector hfit _ _ (by omega),
    doubleSubsets_card k α β γ δ ε hα hβ hγ hδ hε hsector hfit _ _ (by omega)]
  rw [Int.toNat_of_nonneg (show 0 ≤ k + 1 by omega), Int.toNat_of_nonneg hk]
  exact initialProduct_count k α β γ δ ε hβ hε hsector (by omega)



theorem row_bounds_of_doubleSubset (k : ℤ) (nu : Fin N → ℕ) (t s : ℕ)
    (p : Finset (Fin N) × Finset (Fin N)) (hp : p ∈ doubleSubsets k nu t s)
    (i : Fin N) : baseShape k i ≤ nu i ∧ nu i ≤ baseShape k i + 2 := by
  obtain ⟨ht, hs, hpart, heq⟩ := (mem_doubleSubsets k nu t s p).mp hp
  have h := congrFun heq i
  simp only [Pi.add_apply, subsetIndicator] at h
  split_ifs at h <;> omega

/-- Two strips cannot create a new row of length three. Thus the initial
product has no contribution in the manuscript's second sector. -/
theorem doubleSubsets_secondSector_empty (k α β γ δ ε : ℤ)
    (hk : 0 ≤ k) (hN : k + 1 ≤ (N : ℤ))
    (hsector : α + β + γ = k + 1) (t s : ℕ) :
    doubleSubsets k (targetShape (N := N) α β γ δ ε) t s = ∅ := by
  apply Finset.eq_empty_iff_forall_notMem.mpr
  intro p hp
  let i : Fin N := ⟨k.toNat, by omega⟩
  have hi : rowIndex i = k + 1 := by simp only [rowIndex, i]; omega
  have h := row_bounds_of_doubleSubset k _ t s p hp i
  unfold baseShape targetShape targetPart at h
  rw [hi] at h
  split_ifs at h <;> omega


end CoefficientOne.InitialPieriCount

end
