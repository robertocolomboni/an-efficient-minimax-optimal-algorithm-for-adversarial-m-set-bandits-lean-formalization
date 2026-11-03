import CoefficientOne.ScalarPieriSecondSector

/-!
# Classification of all scalar Pieri targets

A bounded partition is reconstructed from the initial-segment cardinalities
of its rows. This supplies the target parametrization used in Step 2 of the
scalar coefficient proof, without assuming that the displayed shapes exhaust
the expansion. The uniqueness statement explicitly rules out truncated targets.
-/

namespace CoefficientOne.ScalarPieriShapes

open Finset SignedLoad AlternantCancellation

variable {N : ℕ}

/-- Number of rows strictly above a specified height. -/
def heightCount (mu : Fin N → ℕ) (c : ℕ) : ℤ :=
  ((univ.filter (fun i => c < mu i)).card : ℤ)

theorem heightCount_nonneg (mu : Fin N → ℕ) (c : ℕ) : 0 ≤ heightCount mu c := by
  unfold heightCount
  positivity

theorem heightCount_le (mu : Fin N → ℕ) (c : ℕ) : heightCount mu c ≤ N := by
  have h := Finset.card_le_card (Finset.filter_subset (fun i => c < mu i) univ)
  simp only [Finset.card_univ, Fintype.card_fin] at h
  unfold heightCount
  exact_mod_cast h

theorem heightCount_antitone (mu : Fin N → ℕ) : Antitone (heightCount mu) := by
  intro a b hab
  apply Int.ofNat_le.mpr
  apply Finset.card_le_card
  intro i hi
  simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hi ⊢
  omega

theorem rowIndex_le_heightCount_iff (mu : Fin N → ℕ)
    (hmu : AlgebraicCombinatorics.IsNPartition mu) (c : ℕ) (i : Fin N) :
    rowIndex i ≤ heightCount mu c ↔ c < mu i := by
  have h := Tuple.lt_card_gt_iff_apply_gt_of_antitone (j := i) (a := c) hmu
  simp only [rowIndex, heightCount]
  exact (show (i.val : ℤ) + 1 ≤ ((univ.filter (fun i => c < mu i)).card : ℤ) ↔
    i.val < (univ.filter (fun i => c < mu i)).card by omega).trans h

/-- Every partition whose rows are at most five has the displayed five-block form. -/
theorem bounded_partition_eq_target (mu : Fin N → ℕ)
    (hmu : AlgebraicCombinatorics.IsNPartition mu) (hmax : ∀ i, mu i ≤ 5) :
    mu = targetShape (heightCount mu 4) (heightCount mu 3 - heightCount mu 4)
      (heightCount mu 2 - heightCount mu 3) (heightCount mu 1 - heightCount mu 2)
      (heightCount mu 0 - heightCount mu 1) := by
  funext i
  have h₅ := rowIndex_le_heightCount_iff mu hmu 4 i
  have h₄ := rowIndex_le_heightCount_iff mu hmu 3 i
  have h₃ := rowIndex_le_heightCount_iff mu hmu 2 i
  have h₂ := rowIndex_le_heightCount_iff mu hmu 1 i
  have h₁ := rowIndex_le_heightCount_iff mu hmu 0 i
  have hh := hmax i
  unfold targetShape targetPart
  split_ifs <;> omega

/-- The five multiplicities are nonnegative and the shape fits the alphabet. -/
theorem bounded_partition_target_parameters (mu : Fin N → ℕ) :
    0 ≤ heightCount mu 4 ∧
    0 ≤ heightCount mu 3 - heightCount mu 4 ∧
    0 ≤ heightCount mu 2 - heightCount mu 3 ∧
    0 ≤ heightCount mu 1 - heightCount mu 2 ∧
    0 ≤ heightCount mu 0 - heightCount mu 1 ∧
    heightCount mu 4 + (heightCount mu 3 - heightCount mu 4) +
      (heightCount mu 2 - heightCount mu 3) + (heightCount mu 1 - heightCount mu 2) +
      (heightCount mu 0 - heightCount mu 1) ≤ N := by
  have h₅ := heightCount_nonneg mu 4
  have h₄ := heightCount_antitone mu (show 3 ≤ 4 by omega)
  have h₃ := heightCount_antitone mu (show 2 ≤ 3 by omega)
  have h₂ := heightCount_antitone mu (show 1 ≤ 2 by omega)
  have h₁ := heightCount_antitone mu (show 0 ≤ 1 by omega)
  have hb := heightCount_le mu 0
  omega

theorem heightCount_eq_of_row_iff (mu : Fin N → ℕ) (c : ℕ) (t : ℤ)
    (ht : 0 ≤ t) (hN : t ≤ N)
    (h : ∀ i, c < mu i ↔ rowIndex i ≤ t) : heightCount mu c = t := by
  unfold heightCount
  rw [← Finset.sum_boole]
  simp_rw [h]
  exact prefix_sum t ht hN

set_option maxHeartbeats 1000000 in
/-- Exact cumulative counts of a five-block target; no row may be truncated. -/
theorem targetShape_heightCounts (α β γ δ ε : ℤ)
    (hα : 0 ≤ α) (hβ : 0 ≤ β) (hγ : 0 ≤ γ) (hδ : 0 ≤ δ) (hε : 0 ≤ ε)
    (hN : α + β + γ + δ + ε ≤ N) :
    heightCount (targetShape (N := N) α β γ δ ε) 4 = α ∧
    heightCount (targetShape (N := N) α β γ δ ε) 3 = α + β ∧
    heightCount (targetShape (N := N) α β γ δ ε) 2 = α + β + γ ∧
    heightCount (targetShape (N := N) α β γ δ ε) 1 = α + β + γ + δ ∧
    heightCount (targetShape (N := N) α β γ δ ε) 0 = α + β + γ + δ + ε := by
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  all_goals apply heightCount_eq_of_row_iff <;> try omega
  all_goals
    intro i
    have hi := Finset.mem_Icc.mp (rowIndex_mem i)
    unfold targetShape targetPart
    split_ifs <;> omega

/-- Thus the five multiplicities of a finite target are unique. -/
theorem targetShape_injective (α β γ δ ε a b c d e : ℤ)
    (hα : 0 ≤ α) (hβ : 0 ≤ β) (hγ : 0 ≤ γ) (hδ : 0 ≤ δ) (hε : 0 ≤ ε)
    (ha : 0 ≤ a) (hb : 0 ≤ b) (hc : 0 ≤ c) (hd : 0 ≤ d) (he : 0 ≤ e)
    (hN : α + β + γ + δ + ε ≤ N) (hN' : a + b + c + d + e ≤ N)
    (heq : targetShape (N := N) α β γ δ ε = targetShape a b c d e) :
    α = a ∧ β = b ∧ γ = c ∧ δ = d ∧ ε = e := by
  have h := targetShape_heightCounts α β γ δ ε hα hβ hγ hδ hε hN
  have h' := targetShape_heightCounts a b c d e ha hb hc hd he hN'
  rw [heq] at h
  omega


/-- A rowwise upper inclusion bounds the number of tall rows. -/
theorem heightCount_le_of_row_bound (mu : Fin N → ℕ) (c : ℕ) (t : ℤ)
    (ht : 0 ≤ t) (hN : t ≤ N)
    (h : ∀ i, c < mu i → rowIndex i ≤ t) : heightCount mu c ≤ t := by
  have hc : ((univ.filter (fun i : Fin N => rowIndex i ≤ t)).card : ℤ) = t := by
    rw [← Finset.sum_boole]
    exact prefix_sum t ht hN
  rw [← hc]
  apply Int.ofNat_le.mpr
  apply Finset.card_le_card
  intro i hi
  simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hi ⊢
  exact h i hi

/-- A rowwise lower inclusion bounds the number of tall rows from below. -/
theorem le_heightCount_of_row_bound (mu : Fin N → ℕ) (c : ℕ) (t : ℤ)
    (ht : 0 ≤ t) (hN : t ≤ N)
    (h : ∀ i, rowIndex i ≤ t → c < mu i) : t ≤ heightCount mu c := by
  have hc : ((univ.filter (fun i : Fin N => rowIndex i ≤ t)).card : ℤ) = t := by
    rw [← Finset.sum_boole]
    exact prefix_sum t ht hN
  rw [← hc]
  apply Int.ofNat_le.mpr
  apply Finset.card_le_card
  intro i hi
  simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hi ⊢
  exact h i hi

/-- A Q strip produces only the first sector and no row longer than five. -/
theorem q_reachable_classification (k j : ℤ) (mu : Fin N → ℕ)
    (hj : 0 ≤ j) (hjk : j ≤ k) (hN : 2 * k + 3 ≤ N)
    (hstrip : RowStrip (qShape k j) mu) :
    (∀ i, mu i ≤ 5) ∧ heightCount mu 2 = k := by
  constructor
  · intro i
    have h := hstrip i
    unfold qShape qPart at h
    split_ifs at h <;> omega
  · apply heightCount_eq_of_row_iff mu 2 k (by omega) (by omega)
    intro i
    have h := hstrip i
    unfold qShape qPart at h
    split_ifs at h <;> omega

/-- A Z strip produces only the second sector and no row longer than five. -/
theorem z_reachable_classification (k j : ℤ) (mu : Fin N → ℕ)
    (hj : 0 ≤ j) (hjk : j ≤ k - 1) (hN : 2 * k + 3 ≤ N)
    (hstrip : RowStrip (zShape k j) mu) :
    (∀ i, mu i ≤ 5) ∧ heightCount mu 2 = k + 1 := by
  constructor
  · intro i
    have h := hstrip i
    unfold zShape zPart at h
    split_ifs at h <;> omega
  · apply heightCount_eq_of_row_iff mu 2 (k + 1) (by omega) (by omega)
    intro i
    have h := hstrip i
    unfold zShape zPart at h
    split_ifs at h <;> omega

/-- The single two-box row in P can stay two or become three, giving exactly
these two sectors and no other one. -/
theorem p_reachable_classification (k j : ℤ) (mu : Fin N → ℕ)
    (hj : 0 ≤ j) (hjk : j ≤ k) (hN : 2 * k + 3 ≤ N)
    (hstrip : RowStrip (pShape k j) mu) :
    (∀ i, mu i ≤ 5) ∧ (heightCount mu 2 = k ∨ heightCount mu 2 = k + 1) := by
  constructor
  · intro i
    have h := hstrip i
    unfold pShape pPart at h
    split_ifs at h <;> omega
  · have hlo : k ≤ heightCount mu 2 := by
      apply le_heightCount_of_row_bound mu 2 k (by omega) (by omega)
      intro i hi
      have h := hstrip i
      unfold pShape pPart at h
      split_ifs at h <;> omega
    have hhi : heightCount mu 2 ≤ k + 1 := by
      apply heightCount_le_of_row_bound mu 2 (k + 1) (by omega) (by omega)
      intro i hi
      have h := hstrip i
      unfold pShape pPart at h
      split_ifs at h <;> omega
    omega

/-- Cardinality in Pieri transfers to the exact degree of the target. -/
theorem degree_of_pieriSubset (source mu : Fin N → ℕ) (k : ℕ)
    (S : Finset (Fin N)) (hS : IsPieriSubset source mu k S) :
    shapeDegree mu = shapeDegree source + k := by
  have hc : S.card = k := (Finset.mem_powersetCard.mp hS.1).2
  rw [← hS.2, shapeDegree_add_indicator, hc]

theorem rowStrip_of_pieriSubset (source mu : Fin N → ℕ) (k : ℕ)
    (S : Finset (Fin N)) (hS : IsPieriSubset source mu k S) : RowStrip source mu :=
  (exists_subset_iff_rowStrip source mu).mp ⟨S, hS.2⟩

/-- A degree bound bounds each multiplicity, supplying a finite global
parameter range for regrouping the scalar expansion. -/
theorem target_parameters_bounded_by_degree (α β γ δ ε D : ℤ)
    (hα : 0 ≤ α) (hβ : 0 ≤ β) (hγ : 0 ≤ γ) (hδ : 0 ≤ δ) (hε : 0 ≤ ε)
    (hN : α + β + γ + δ + ε ≤ N)
    (hdegree : shapeDegree (targetShape (N := N) α β γ δ ε) ≤ D) :
    α ≤ D ∧ β ≤ D ∧ γ ≤ D ∧ δ ≤ D ∧ ε ≤ D := by
  rw [targetShape_degree α β γ δ ε hα hβ hγ hδ hε hN] at hdegree
  omega

/-- The first-sector degree relation is forced by the actual homogeneous degree. -/
theorem firstSector_degree_relation (k α β γ δ ε : ℤ)
    (hα : 0 ≤ α) (hβ : 0 ≤ β) (hγ : 0 ≤ γ) (hδ : 0 ≤ δ) (hε : 0 ≤ ε)
    (hN : α + β + γ + δ + ε ≤ N)
    (hsector : α + β + γ = k)
    (hdegree : shapeDegree (targetShape (N := N) α β γ δ ε) = 5 * k + 2) :
    ε = β + 2 * γ + 2 - 2 * δ := by
  rw [targetShape_degree α β γ δ ε hα hβ hγ hδ hε hN] at hdegree
  omega

/-- The second-sector degree relation is likewise a consequence, not an assumption. -/
theorem secondSector_degree_relation (k α β γ δ ε : ℤ)
    (hα : 0 ≤ α) (hβ : 0 ≤ β) (hγ : 0 ≤ γ) (hδ : 0 ≤ δ) (hε : 0 ≤ ε)
    (hN : α + β + γ + δ + ε ≤ N)
    (hsector : α + β + γ = k + 1)
    (hdegree : shapeDegree (targetShape (N := N) α β γ δ ε) = 5 * k + 2) :
    ε = β + 2 * γ - 3 - 2 * δ := by
  rw [targetShape_degree α β γ δ ε hα hβ hγ hδ hε hN] at hdegree
  omega


/-- Existential interface for regrouping a finite sum by its target shape. -/
theorem exists_target_parameters (mu : Fin N → ℕ)
    (hmu : AlgebraicCombinatorics.IsNPartition mu) (hmax : ∀ i, mu i ≤ 5) :
    ∃ α β γ δ ε : ℤ,
      (0 ≤ α ∧ 0 ≤ β ∧ 0 ≤ γ ∧ 0 ≤ δ ∧ 0 ≤ ε ∧ α + β + γ + δ + ε ≤ N) ∧
      mu = targetShape α β γ δ ε ∧ α + β + γ = heightCount mu 2 := by
  refine ⟨heightCount mu 4, heightCount mu 3 - heightCount mu 4,
    heightCount mu 2 - heightCount mu 3, heightCount mu 1 - heightCount mu 2,
    heightCount mu 0 - heightCount mu 1, bounded_partition_target_parameters mu,
    bounded_partition_eq_target mu hmu hmax, ?_⟩
  omega

/-- A fixed degree supplies an actual finite global box of possible integer
multiplicity tuples. This does not depend on the alphabet size. -/
noncomputable def targetParameterBox (D : ℤ) : Finset (Fin 5 → ℤ) :=
  Fintype.piFinset (fun _ => Icc 0 D)

theorem mem_targetParameterBox (D : ℤ) (p : Fin 5 → ℤ) :
    p ∈ targetParameterBox D ↔ ∀ i, 0 ≤ p i ∧ p i ≤ D := by
  simp only [targetParameterBox, Fintype.mem_piFinset, Finset.mem_Icc]

/-- Every displayed target of bounded degree occurs in that finite box. -/
theorem target_parameters_mem_box (α β γ δ ε D : ℤ)
    (hα : 0 ≤ α) (hβ : 0 ≤ β) (hγ : 0 ≤ γ) (hδ : 0 ≤ δ) (hε : 0 ≤ ε)
    (hN : α + β + γ + δ + ε ≤ N)
    (hdegree : shapeDegree (targetShape (N := N) α β γ δ ε) ≤ D) :
    ![α, β, γ, δ, ε] ∈ targetParameterBox D := by
  have hh := target_parameters_bounded_by_degree α β γ δ ε D hα hβ hγ hδ hε hN hdegree
  rw [mem_targetParameterBox]
  intro i
  fin_cases i <;> dsimp <;> omega

end CoefficientOne.ScalarPieriShapes