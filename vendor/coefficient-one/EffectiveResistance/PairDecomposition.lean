import EffectiveResistance.FiniteLaw
import Mathlib.Data.Finset.Card
import Mathlib.Data.Finset.Image

/-!
# Decomposition of a fixed-rank subset at two endpoints

For distinct endpoints `i,j`, a rank-`q+2` subset is split into the four
states `11`, `10`, `01`, and `00`.  The remaining background subset has rank
`q`, `q+1`, `q+1`, or `q+2`, respectively.
-/

open scoped BigOperators

namespace EffectiveResistance

noncomputable section

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

abbrev PairComplement (i j : ι) :=
  {k : ι // k ≠ i ∧ k ≠ j}

theorem card_pairComplement (i j : ι) (hij : i ≠ j) :
    Fintype.card (PairComplement i j) = Fintype.card ι - 2 := by
  let e : PairComplement i j ≃ {k : ι // ¬ (k = i ∨ k = j)} :=
    { toFun := fun k => ⟨k.1, by
        intro h
        exact h.elim k.2.1 k.2.2⟩
      invFun := fun k => ⟨k.1, by
        constructor
        · intro h
          exact k.2 (Or.inl h)
        · intro h
          exact k.2 (Or.inr h)⟩
      left_inv := fun k => Subtype.ext rfl
      right_inv := fun k => Subtype.ext rfl }
  calc
    Fintype.card (PairComplement i j) =
        Fintype.card {k : ι // ¬ (k = i ∨ k = j)} :=
      Fintype.card_congr e
    _ = Fintype.card ι - Fintype.card {k : ι // k = i ∨ k = j} :=
      Fintype.card_subtype_compl (fun k : ι => k = i ∨ k = j)
    _ = Fintype.card ι - 2 := by
      rw [Fintype.card_subtype_eq_or_eq_of_ne hij]

def pairRestrictedWeight (w : ι → ℝ) (i j : ι) :
    PairComplement i j → ℝ :=
  fun k => w k.1

def pairBackground (i j : ι) (S : Finset ι) :
    Finset (PairComplement i j) :=
  S.subtype (fun k => k ≠ i ∧ k ≠ j)

def liftPairBackground (i j : ι) (A : Finset (PairComplement i j)) :
    Finset ι :=
  A.map (Function.Embedding.subtype _)

@[simp] theorem mem_liftPairBackground
    (i j : ι) (A : Finset (PairComplement i j))
    (k : PairComplement i j) :
    k.1 ∈ liftPairBackground i j A ↔ k ∈ A := by
  simpa [liftPairBackground, k.2]

theorem left_not_mem_liftPairBackground
    (i j : ι) (A : Finset (PairComplement i j)) :
    i ∉ liftPairBackground i j A := by
  intro hi
  simp only [liftPairBackground, Finset.mem_map] at hi
  obtain ⟨k, -, hk⟩ := hi
  exact k.2.1 hk

theorem right_not_mem_liftPairBackground
    (i j : ι) (A : Finset (PairComplement i j)) :
    j ∉ liftPairBackground i j A := by
  intro hj
  simp only [liftPairBackground, Finset.mem_map] at hj
  obtain ⟨k, -, hk⟩ := hj
  exact k.2.2 hk

@[simp] theorem card_liftPairBackground
    (i j : ι) (A : Finset (PairComplement i j)) :
    (liftPairBackground i j A).card = A.card := by
  simp [liftPairBackground]

theorem lift_pairBackground_eq_filter
    (i j : ι) (S : Finset ι) :
    liftPairBackground i j (pairBackground i j S) =
      S.filter (fun k => k ≠ i ∧ k ≠ j) := by
  exact Finset.subtype_map _

theorem pairBackground_card_11
    {i j : ι} (hij : i ≠ j) (S : Finset ι)
    (hi : i ∈ S) (hj : j ∈ S) :
    (pairBackground i j S).card = S.card - 2 := by
  rw [pairBackground, Finset.card_subtype]
  have hfilter :
      S.filter (fun k => k ≠ i ∧ k ≠ j) = (S.erase i).erase j := by
    ext k
    by_cases hki : k = i <;> by_cases hkj : k = j <;>
      simp [hki, hkj, hij, Ne.symm hij]
  rw [hfilter]
  have hj' : j ∈ S.erase i := by simp [hj, Ne.symm hij]
  rw [Finset.card_erase_of_mem hj', Finset.card_erase_of_mem hi]
  omega

theorem pairBackground_card_10
    {i j : ι} (S : Finset ι) (hi : i ∈ S) (hj : j ∉ S) :
    (pairBackground i j S).card = S.card - 1 := by
  rw [pairBackground, Finset.card_subtype]
  have hfilter :
      S.filter (fun k => k ≠ i ∧ k ≠ j) = S.erase i := by
    ext k
    by_cases hki : k = i <;> by_cases hkj : k = j <;> simp [hki, hkj, hj]
  rw [hfilter, Finset.card_erase_of_mem hi]

theorem pairBackground_card_01
    {i j : ι} (S : Finset ι) (hi : i ∉ S) (hj : j ∈ S) :
    (pairBackground i j S).card = S.card - 1 := by
  rw [pairBackground, Finset.card_subtype]
  have hfilter :
      S.filter (fun k => k ≠ i ∧ k ≠ j) = S.erase j := by
    ext k
    by_cases hki : k = i <;> by_cases hkj : k = j <;> simp [hki, hkj, hi]
  rw [hfilter, Finset.card_erase_of_mem hj]

theorem pairBackground_card_00
    {i j : ι} (S : Finset ι) (hi : i ∉ S) (hj : j ∉ S) :
    (pairBackground i j S).card = S.card := by
  rw [pairBackground, Finset.card_subtype]
  have hfilter :
      S.filter (fun k => k ≠ i ∧ k ≠ j) = S := by
    ext k
    by_cases hki : k = i <;> by_cases hkj : k = j <;> simp [hki, hkj, hi, hj]
  rw [hfilter]

def liftPair00 (i j : ι) (A : RankSubset (PairComplement i j) (q + 2)) :
    RankSubset ι (q + 2) :=
  ⟨liftPairBackground i j A.1, by simpa using A.2⟩

def liftPair10 (i j : ι) (A : RankSubset (PairComplement i j) (q + 1)) :
    RankSubset ι (q + 2) :=
  ⟨insert i (liftPairBackground i j A.1), by
    rw [Finset.card_insert_of_notMem (left_not_mem_liftPairBackground i j A.1)]
    simp [A.2]⟩

def liftPair01 (i j : ι) (A : RankSubset (PairComplement i j) (q + 1)) :
    RankSubset ι (q + 2) :=
  ⟨insert j (liftPairBackground i j A.1), by
    rw [Finset.card_insert_of_notMem (right_not_mem_liftPairBackground i j A.1)]
    simp [A.2]⟩

def liftPair11 (i j : ι) (hij : i ≠ j)
    (A : RankSubset (PairComplement i j) q) : RankSubset ι (q + 2) :=
  ⟨insert i (insert j (liftPairBackground i j A.1)), by
    have hji : j ≠ i := Ne.symm hij
    have hj : j ∉ liftPairBackground i j A.1 :=
      right_not_mem_liftPairBackground i j A.1
    have hi : i ∉ insert j (liftPairBackground i j A.1) := by
      simp [hij, left_not_mem_liftPairBackground i j A.1]
    rw [Finset.card_insert_of_notMem hi, Finset.card_insert_of_notMem hj]
    simp [A.2]⟩

theorem subsetWeight_liftPairBackground
    (w : ι → ℝ) (i j : ι) (A : Finset (PairComplement i j)) :
    subsetWeight w (liftPairBackground i j A) =
      subsetWeight (pairRestrictedWeight w i j) A := by
  simp [subsetWeight, liftPairBackground, pairRestrictedWeight]

theorem subsetWeight_liftPair00
    (w : ι → ℝ) (i j : ι)
    (A : RankSubset (PairComplement i j) (q + 2)) :
    subsetWeight w (liftPair00 i j A).1 =
      subsetWeight (pairRestrictedWeight w i j) A.1 := by
  exact subsetWeight_liftPairBackground w i j A.1

theorem subsetWeight_liftPair10
    (w : ι → ℝ) (i j : ι)
    (A : RankSubset (PairComplement i j) (q + 1)) :
    subsetWeight w (liftPair10 i j A).1 =
      w i * subsetWeight (pairRestrictedWeight w i j) A.1 := by
  unfold liftPair10
  rw [subsetWeight, Finset.prod_insert
    (left_not_mem_liftPairBackground i j A.1)]
  change w i * subsetWeight w (liftPairBackground i j A.1) = _
  rw [subsetWeight_liftPairBackground]

theorem subsetWeight_liftPair01
    (w : ι → ℝ) (i j : ι)
    (A : RankSubset (PairComplement i j) (q + 1)) :
    subsetWeight w (liftPair01 i j A).1 =
      w j * subsetWeight (pairRestrictedWeight w i j) A.1 := by
  unfold liftPair01
  rw [subsetWeight, Finset.prod_insert
    (right_not_mem_liftPairBackground i j A.1)]
  change w j * subsetWeight w (liftPairBackground i j A.1) = _
  rw [subsetWeight_liftPairBackground]

theorem subsetWeight_liftPair11
    (w : ι → ℝ) (i j : ι) (hij : i ≠ j)
    (A : RankSubset (PairComplement i j) q) :
    subsetWeight w (liftPair11 i j hij A).1 =
      w i * w j * subsetWeight (pairRestrictedWeight w i j) A.1 := by
  unfold liftPair11
  have hj : j ∉ liftPairBackground i j A.1 :=
    right_not_mem_liftPairBackground i j A.1
  have hi : i ∉ insert j (liftPairBackground i j A.1) := by
    simp [hij, left_not_mem_liftPairBackground i j A.1]
  rw [subsetWeight, Finset.prod_insert hi, Finset.prod_insert hj]
  change w i * (w j * subsetWeight w (liftPairBackground i j A.1)) = _
  rw [subsetWeight_liftPairBackground]
  ring

@[simp] theorem left_mem_liftPair10
    (i j : ι) (A : RankSubset (PairComplement i j) (q + 1)) :
    i ∈ (liftPair10 i j A).1 := by
  simp [liftPair10]

@[simp] theorem right_not_mem_liftPair10
    (i j : ι) (hij : i ≠ j)
    (A : RankSubset (PairComplement i j) (q + 1)) :
    j ∉ (liftPair10 i j A).1 := by
  simp [liftPair10, right_not_mem_liftPairBackground, Ne.symm hij]

@[simp] theorem left_not_mem_liftPair01
    (i j : ι) (hij : i ≠ j)
    (A : RankSubset (PairComplement i j) (q + 1)) :
    i ∉ (liftPair01 i j A).1 := by
  simp [liftPair01, left_not_mem_liftPairBackground, hij]

@[simp] theorem right_mem_liftPair01
    (i j : ι) (A : RankSubset (PairComplement i j) (q + 1)) :
    j ∈ (liftPair01 i j A).1 := by
  simp [liftPair01]

@[simp] theorem left_not_mem_liftPair00
    (i j : ι) (A : RankSubset (PairComplement i j) (q + 2)) :
    i ∉ (liftPair00 i j A).1 :=
  left_not_mem_liftPairBackground i j A.1

@[simp] theorem right_not_mem_liftPair00
    (i j : ι) (A : RankSubset (PairComplement i j) (q + 2)) :
    j ∉ (liftPair00 i j A).1 :=
  right_not_mem_liftPairBackground i j A.1

@[simp] theorem left_mem_liftPair11
    (i j : ι) (hij : i ≠ j)
    (A : RankSubset (PairComplement i j) q) :
    i ∈ (liftPair11 i j hij A).1 := by
  simp [liftPair11]

@[simp] theorem right_mem_liftPair11
    (i j : ι) (hij : i ≠ j)
    (A : RankSubset (PairComplement i j) q) :
    j ∈ (liftPair11 i j hij A).1 := by
  simp [liftPair11]

theorem pairBackground_liftPairBackground
    (i j : ι) (A : Finset (PairComplement i j)) :
    pairBackground i j (liftPairBackground i j A) = A := by
  ext k
  simp [pairBackground, mem_liftPairBackground]

@[simp] theorem pairBackground_liftPair00
    (i j : ι) (A : RankSubset (PairComplement i j) (q + 2)) :
    pairBackground i j (liftPair00 i j A).1 = A.1 := by
  exact pairBackground_liftPairBackground i j A.1

@[simp] theorem pairBackground_liftPair10
    (i j : ι) (A : RankSubset (PairComplement i j) (q + 1)) :
    pairBackground i j (liftPair10 i j A).1 = A.1 := by
  ext k
  simp [pairBackground, liftPair10, mem_liftPairBackground, k.2]

@[simp] theorem pairBackground_liftPair01
    (i j : ι) (A : RankSubset (PairComplement i j) (q + 1)) :
    pairBackground i j (liftPair01 i j A).1 = A.1 := by
  ext k
  simp [pairBackground, liftPair01, mem_liftPairBackground, k.2]

@[simp] theorem pairBackground_liftPair11
    (i j : ι) (hij : i ≠ j)
    (A : RankSubset (PairComplement i j) q) :
    pairBackground i j (liftPair11 i j hij A).1 = A.1 := by
  ext k
  simp [pairBackground, liftPair11, mem_liftPairBackground, k.2]

theorem liftPair00_pairBackground
    {i j : ι} (S : RankSubset ι (q + 2))
    (hi : i ∉ S.1) (hj : j ∉ S.1) :
    liftPair00 i j
      ⟨pairBackground i j S.1, by
        rw [pairBackground_card_00 S.1 hi hj, S.2]⟩ = S := by
  apply Subtype.ext
  unfold liftPair00
  change liftPairBackground i j (pairBackground i j S.1) = S.1
  rw [lift_pairBackground_eq_filter]
  ext k
  by_cases hki : k = i <;> by_cases hkj : k = j <;>
    simp [hki, hkj, hi, hj]

theorem liftPair10_pairBackground
    {i j : ι} (S : RankSubset ι (q + 2))
    (hi : i ∈ S.1) (hj : j ∉ S.1) :
    liftPair10 i j
      ⟨pairBackground i j S.1, by
        rw [pairBackground_card_10 S.1 hi hj, S.2]
        omega⟩ = S := by
  have hij : i ≠ j := by
    intro h
    subst j
    exact hj hi
  apply Subtype.ext
  unfold liftPair10
  change insert i (liftPairBackground i j (pairBackground i j S.1)) = S.1
  rw [lift_pairBackground_eq_filter]
  ext k
  by_cases hki : k = i <;> by_cases hkj : k = j <;>
    simp [hki, hkj, hi, hj, hij, Ne.symm hij]

theorem liftPair01_pairBackground
    {i j : ι} (S : RankSubset ι (q + 2))
    (hi : i ∉ S.1) (hj : j ∈ S.1) :
    liftPair01 i j
      ⟨pairBackground i j S.1, by
        rw [pairBackground_card_01 S.1 hi hj, S.2]
        omega⟩ = S := by
  have hij : i ≠ j := by
    intro h
    subst j
    exact hi hj
  apply Subtype.ext
  unfold liftPair01
  change insert j (liftPairBackground i j (pairBackground i j S.1)) = S.1
  rw [lift_pairBackground_eq_filter]
  ext k
  by_cases hki : k = i <;> by_cases hkj : k = j <;>
    simp [hki, hkj, hi, hj, hij, Ne.symm hij]

theorem liftPair11_pairBackground
    {i j : ι} (hij : i ≠ j) (S : RankSubset ι (q + 2))
    (hi : i ∈ S.1) (hj : j ∈ S.1) :
    liftPair11 i j hij
      ⟨pairBackground i j S.1, by
        rw [pairBackground_card_11 hij S.1 hi hj, S.2]
        omega⟩ = S := by
  apply Subtype.ext
  unfold liftPair11
  change insert i (insert j
    (liftPairBackground i j (pairBackground i j S.1))) = S.1
  rw [lift_pairBackground_eq_filter]
  ext k
  by_cases hki : k = i <;> by_cases hkj : k = j <;>
    simp [hki, hkj, hi, hj, hij, Ne.symm hij]

abbrev PairSlices (i j : ι) (q : ℕ) :=
  RankSubset (PairComplement i j) q ⊕
    (RankSubset (PairComplement i j) (q + 1) ⊕
      (RankSubset (PairComplement i j) (q + 1) ⊕
        RankSubset (PairComplement i j) (q + 2)))

def splitPair (i j : ι) (hij : i ≠ j)
    (S : RankSubset ι (q + 2)) : PairSlices i j q :=
  if hi : i ∈ S.1 then
    if hj : j ∈ S.1 then
      Sum.inl ⟨pairBackground i j S.1, by
        rw [pairBackground_card_11 hij S.1 hi hj, S.2]
        omega⟩
    else
      Sum.inr (Sum.inl ⟨pairBackground i j S.1, by
        rw [pairBackground_card_10 S.1 hi hj, S.2]
        omega⟩)
  else
    if hj : j ∈ S.1 then
      Sum.inr (Sum.inr (Sum.inl ⟨pairBackground i j S.1, by
        rw [pairBackground_card_01 S.1 hi hj, S.2]
        omega⟩))
    else
      Sum.inr (Sum.inr (Sum.inr ⟨pairBackground i j S.1, by
        rw [pairBackground_card_00 S.1 hi hj, S.2]⟩))

def unsplitPair (i j : ι) (hij : i ≠ j) :
    PairSlices i j q → RankSubset ι (q + 2)
  | Sum.inl A => liftPair11 i j hij A
  | Sum.inr (Sum.inl A) => liftPair10 i j A
  | Sum.inr (Sum.inr (Sum.inl A)) => liftPair01 i j A
  | Sum.inr (Sum.inr (Sum.inr A)) => liftPair00 i j A

theorem unsplitPair_splitPair
    (i j : ι) (hij : i ≠ j) (S : RankSubset ι (q + 2)) :
    unsplitPair i j hij (splitPair i j hij S) = S := by
  unfold splitPair
  by_cases hi : i ∈ S.1 <;> by_cases hj : j ∈ S.1 <;>
    simp [hi, hj, unsplitPair,
      liftPair11_pairBackground, liftPair10_pairBackground,
      liftPair01_pairBackground, liftPair00_pairBackground, hij]

theorem splitPair_unsplitPair
    (i j : ι) (hij : i ≠ j) (T : PairSlices i j q) :
    splitPair i j hij (unsplitPair i j hij T) = T := by
  rcases T with A | ⟨A | ⟨A | A⟩⟩
  · simp [splitPair, unsplitPair, pairBackground_liftPair11]
  · simp [splitPair, unsplitPair, pairBackground_liftPair10,
      right_not_mem_liftPair10 i j hij A]
  · simp [splitPair, unsplitPair, pairBackground_liftPair01,
      left_not_mem_liftPair01 i j hij A]
  · simp [splitPair, unsplitPair, pairBackground_liftPair00]

def pairDecompositionEquiv (i j : ι) (hij : i ≠ j) (q : ℕ) :
    RankSubset ι (q + 2) ≃ PairSlices i j q where
  toFun := splitPair i j hij
  invFun := unsplitPair i j hij
  left_inv := unsplitPair_splitPair i j hij
  right_inv := splitPair_unsplitPair i j hij

/-- Splitting a sum over rank-`q+2` subsets according to the four endpoint
states `11`, `10`, `01`, and `00`. -/
theorem sum_rankSubset_pairDecomposition
    (i j : ι) (hij : i ≠ j) (q : ℕ)
    (F : RankSubset ι (q + 2) → ℝ) :
    (∑ S : RankSubset ι (q + 2), F S) =
      (∑ A : RankSubset (PairComplement i j) q,
        F (liftPair11 i j hij A)) +
      (∑ A : RankSubset (PairComplement i j) (q + 1),
        F (liftPair10 i j A)) +
      (∑ A : RankSubset (PairComplement i j) (q + 1),
        F (liftPair01 i j A)) +
      (∑ A : RankSubset (PairComplement i j) (q + 2),
        F (liftPair00 i j A)) := by
  rw [← (pairDecompositionEquiv i j hij q).symm.sum_comp]
  simp only [Fintype.sum_sum_type]
  simp [pairDecompositionEquiv, unsplitPair, add_assoc]

/-- Four-cell decomposition of the elementary symmetric sum. -/
theorem elementarySum_pairDecomposition
    (w : ι → ℝ) (i j : ι) (hij : i ≠ j) (q : ℕ) :
    elementarySum w (q + 2) =
      w i * w j * elementarySum (pairRestrictedWeight w i j) q +
      w i * elementarySum (pairRestrictedWeight w i j) (q + 1) +
      w j * elementarySum (pairRestrictedWeight w i j) (q + 1) +
      elementarySum (pairRestrictedWeight w i j) (q + 2) := by
  unfold elementarySum
  rw [sum_rankSubset_pairDecomposition i j hij q]
  simp_rw [subsetWeight_liftPair11, subsetWeight_liftPair10,
    subsetWeight_liftPair01, subsetWeight_liftPair00]
  simp only [Finset.mul_sum]

end

end EffectiveResistance
