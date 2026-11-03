import CoefficientOne.InitialPieriCount
import CoefficientOne.ScalarTargetClassification
import CoefficientOne.ScalarReciprocity
import CoefficientOne.ScalarPadding
import CoefficientOne.RectangleContinuity

/-!
# Reassembly of the scalar Schur expansion

Provenance: the expanded manuscript, `lem:scalar` and `eq:coeff`.
Every multiplicity below is a cardinality of actual vertical-Pieri row subsets.
-/

noncomputable section

namespace CoefficientOne.ScalarExpansion

open Finset ScalarPieriShapes InitialPieriCount SignedLoad
open ScalarLoad ScalarReciprocity SchurStability RectangleDeterminants

variable {N M : ℕ}
attribute [local instance] Classical.propDecidable

def targets (d : ℤ) : Finset (Fin N → ℕ) := by
  classical
  exact (Fintype.piFinset (fun _ : Fin N => Finset.range 6)).filter
    (fun mu => AlgebraicCombinatorics.IsNPartition mu ∧ shapeDegree mu = d)

theorem mem_targets (d : ℤ) (mu : Fin N → ℕ) :
    mu ∈ targets d ↔ (∀ i, mu i ≤ 5) ∧
      AlgebraicCombinatorics.IsNPartition mu ∧ shapeDegree mu = d := by
  classical
  simp only [targets, Finset.mem_filter, Fintype.mem_piFinset, Finset.mem_range]
  constructor
  · rintro ⟨hb, hp, hd⟩
    exact ⟨fun i => by have h := hb i; omega, hp, hd⟩
  · rintro ⟨hb, hp, hd⟩
    exact ⟨fun i => by have h := hb i; omega, hp, hd⟩

theorem sum_regroup {ι τ : Type*} [DecidableEq τ] (s : Finset ι) (T : Finset τ)
    (g : ι → τ) (f : τ → ℝ) (h : ∀ i ∈ s, g i ∈ T) :
    (∑ i ∈ s, f (g i)) = ∑ nu ∈ T, ((s.filter (fun i => g i = nu)).card : ℝ) * f nu := by
  simpa only [Finset.sum_const, nsmul_eq_mul] using
    (Finset.sum_fiberwise_of_maps_to' h f).symm

def stripFiber (mu nu : Fin N → ℕ) (t : ℕ) : Finset (Finset (Fin N)) := by
  classical
  exact (univ.powersetCard t).filter (fun S => mu + subsetIndicator S = nu)

theorem mem_stripFiber (mu nu : Fin N → ℕ) (t : ℕ) (S : Finset (Fin N)) :
    S ∈ stripFiber mu nu t ↔ IsPieriSubset mu nu t S := by
  classical
  simp only [stripFiber, Finset.mem_filter, IsPieriSubset]

theorem stripFiber_card (mu nu : Fin N → ℕ) (t : ℕ) :
    (stripFiber mu nu t).card = if ∃! S, IsPieriSubset mu nu t S then 1 else 0 := by
  classical
  by_cases h : ∃! S, IsPieriSubset mu nu t S
  · rw [if_pos h]
    obtain ⟨T, hT, huniq⟩ := h
    apply Finset.card_eq_one.mpr
    refine ⟨T, ?_⟩
    ext S
    rw [mem_stripFiber, Finset.mem_singleton]
    exact ⟨fun hS => huniq S hS, fun heq => heq.symm ▸ hT⟩
  · rw [if_neg h]
    apply Finset.card_eq_zero.mpr
    apply Finset.eq_empty_iff_forall_notMem.mpr
    intro S hS
    have hs := (mem_stripFiber mu nu t S).mp hS
    exact h ⟨S, hs, fun T hT => subset_unique mu nu T S hT.2 hs.2⟩

def validStrips (mu : Fin N → ℕ) (t : ℕ) : Finset (Finset (Fin N)) := by
  classical
  exact (univ.powersetCard t).filter
    (fun S => AlgebraicCombinatorics.IsNPartition (mu + subsetIndicator S))

theorem mem_validStrips (mu : Fin N → ℕ) (t : ℕ) (S : Finset (Fin N)) :
    S ∈ validStrips mu t ↔ S ∈ (univ : Finset (Fin N)).powersetCard t ∧
      AlgebraicCombinatorics.IsNPartition (mu + subsetIndicator S) := by
  classical
  simp only [validStrips, Finset.mem_filter]

theorem validStrip_target (mu : Fin N → ℕ) (t : ℕ) (d : ℤ)
    (hbound : ∀ i, mu i ≤ 4) (hdegree : shapeDegree mu + t = d)
    (S : Finset (Fin N)) (hS : S ∈ validStrips mu t) :
    mu + subsetIndicator S ∈ targets d := by
  obtain ⟨hcard, hpart⟩ := (mem_validStrips mu t S).mp hS
  apply (mem_targets d _).mpr
  refine ⟨?_, hpart, ?_⟩
  · intro i
    have h := hbound i
    simp only [Pi.add_apply, subsetIndicator]
    split_ifs <;> omega
  · rw [shapeDegree_add_indicator, (Finset.mem_powersetCard.mp hcard).2]
    exact hdegree

theorem validStrips_fiber (mu nu : Fin N → ℕ) (t : ℕ)
    (hnu : AlgebraicCombinatorics.IsNPartition nu) :
    (validStrips mu t).filter (fun S => mu + subsetIndicator S = nu) = stripFiber mu nu t := by
  classical
  ext S
  rw [Finset.mem_filter, mem_validStrips, mem_stripFiber]
  unfold IsPieriSubset
  constructor
  · rintro ⟨⟨hS, hp⟩, heq⟩
    exact ⟨hS, heq⟩
  · rintro ⟨hS, heq⟩
    exact ⟨⟨hS, heq.symm ▸ hnu⟩, heq⟩

/-- One actual vertical-Pieri expansion grouped by its final partition. -/
theorem singlePieri_reindex (a : Fin N → ℝ) (mu : Fin N → ℕ)
    (hmu : AlgebraicCombinatorics.IsNPartition mu) (t : ℕ) (d : ℤ)
    (hbound : ∀ i, mu i ≤ 4) (hdegree : shapeDegree mu + t = d) :
    elementaryInt a t * schurValue mu a =
      ∑ nu ∈ targets d, if ∃! S, IsPieriSubset mu nu t S then schurValue nu a else 0 := by
  classical
  rw [elementaryInt_nat, verticalPieri_value mu hmu t a]
  rw [← Finset.sum_filter]
  change (∑ S ∈ validStrips mu t, schurValue (mu + subsetIndicator S) a) = _
  rw [sum_regroup (validStrips mu t) (targets d) (fun S => mu + subsetIndicator S)
    (fun nu => schurValue nu a) (validStrip_target mu t d hbound hdegree)]
  apply Finset.sum_congr rfl
  intro nu hnu
  rw [validStrips_fiber mu nu t ((mem_targets d nu).mp hnu).2.1, stripFiber_card]
  split_ifs <;> simp

/-- Summing a source family counts its unique strips, as required by the
manuscript's Q/P/Z source-index cardinalities. -/
theorem familyPieri_reindex (a : Fin N → ℝ) (source : ℤ → Fin N → ℕ)
    (lo hi : ℤ) (t : ℕ) (d : ℤ)
    (hpart : ∀ j ∈ Icc lo hi, AlgebraicCombinatorics.IsNPartition (source j))
    (hbound : ∀ j ∈ Icc lo hi, ∀ i, source j i ≤ 4)
    (hdegree : ∀ j ∈ Icc lo hi, shapeDegree (source j) + t = d) :
    elementaryInt a t * (∑ j ∈ Icc lo hi, schurValue (source j) a) =
      ∑ nu ∈ targets d,
        ((pieriSourceIndices source nu t lo hi).card : ℝ) * schurValue nu a := by
  classical
  rw [Finset.mul_sum]
  calc
    _ = ∑ j ∈ Icc lo hi, ∑ nu ∈ targets d,
        if ∃! S, IsPieriSubset (source j) nu t S then schurValue nu a else 0 := by
      apply Finset.sum_congr rfl
      intro j hj
      exact singlePieri_reindex a (source j) (hpart j hj) t d (hbound j hj) (hdegree j hj)
    _ = ∑ nu ∈ targets d, ∑ j ∈ Icc lo hi,
        if ∃! S, IsPieriSubset (source j) nu t S then schurValue nu a else 0 :=
      Finset.sum_comm
    _ = _ := by
      apply Finset.sum_congr rfl
      intro nu hnu
      rw [← Finset.sum_filter]
      change (∑ j ∈ pieriSourceIndices source nu t lo hi, schurValue nu a) = _
      simp


theorem singlePieri_valid (a : Fin N → ℝ) (mu : Fin N → ℕ)
    (hmu : AlgebraicCombinatorics.IsNPartition mu) (t : ℕ) :
    elementaryInt a t * schurValue mu a =
      ∑ S ∈ validStrips mu t, schurValue (mu + subsetIndicator S) a := by
  classical
  rw [elementaryInt_nat, verticalPieri_value mu hmu t a, ← Finset.sum_filter]
  rfl

theorem second_valid_filter (k : ℤ) (nu : Fin N → ℕ) (t s : ℕ)
    (hdegree : shapeDegree nu = shapeDegree (baseShape (N := N) k) + t + s) :
    (validStrips (baseShape k) t).filter
      (fun S => ∃! T, IsPieriSubset (baseShape k + subsetIndicator S) nu s T) =
        firstSubsets k nu t := by
  classical
  ext S
  rw [Finset.mem_filter, mem_validStrips, mem_firstSubsets]
  simp only [Finset.mem_powersetCard, Finset.subset_univ, true_and]
  by_cases ht : S.card = t
  · simp only [ht, true_and]
    rw [existsUnique_pieriSubset_iff _ _ s (by
      rw [shapeDegree_add_indicator, ht]
      exact hdegree)]
  · simp only [ht, false_and]

/-- Two successive actual Pieri expansions, grouped by their true pair counts. -/
theorem doublePieri_reindex (a : Fin N → ℝ) (k : ℤ) (hk : 0 ≤ k) (hkN : k ≤ N)
    (t s : ℕ) (d : ℤ) (hdegree : 3 * k + t + s = d) :
    elementaryInt a s * (elementaryInt a t * schurValue (baseShape k) a) =
      ∑ nu ∈ targets d, ((doubleSubsets k nu t s).card : ℝ) * schurValue nu a := by
  classical
  rw [singlePieri_valid a (baseShape k) (baseShape_isPartition k) t, Finset.mul_sum]
  calc
    _ = ∑ S ∈ validStrips (baseShape k) t, ∑ nu ∈ targets d,
        if ∃! T, IsPieriSubset (baseShape k + subsetIndicator S) nu s T
          then schurValue nu a else 0 := by
      apply Finset.sum_congr rfl
      intro S hS
      obtain ⟨hcard, hpart⟩ := (mem_validStrips _ t S).mp hS
      apply singlePieri_reindex a _ hpart s d
      · intro i
        simp only [Pi.add_apply, baseShape, subsetIndicator]
        split_ifs <;> omega
      · rw [shapeDegree_add_indicator, (Finset.mem_powersetCard.mp hcard).2,
          baseShape_degree k hk hkN]
        exact hdegree
    _ = ∑ nu ∈ targets d, ∑ S ∈ validStrips (baseShape k) t,
        if ∃! T, IsPieriSubset (baseShape k + subsetIndicator S) nu s T
          then schurValue nu a else 0 := Finset.sum_comm
    _ = _ := by
      apply Finset.sum_congr rfl
      intro nu hnu
      have hn : shapeDegree nu = shapeDegree (baseShape (N := N) k) + t + s := by
        rw [((mem_targets d nu).mp hnu).2.2, baseShape_degree k hk hkN]
        exact hdegree.symm
      rw [← Finset.sum_filter, second_valid_filter k nu t s hn,
        doubleSubsets_card_eq_first k nu t s hn]
      simp


def rawCoefficient (k : ℕ) (nu : Fin N → ℕ) : ℤ :=
  ((doubleSubsets k nu (k + 1) (k + 1)).card : ℤ) -
    ((doubleSubsets k nu k (k + 2)).card : ℤ) +
    ((pieriSourceIndices (qShape k) nu k 0 k).card : ℤ) -
    ((pieriSourceIndices (pShape k) nu k 0 k).card : ℤ) +
    ((pieriSourceIndices (zShape k) nu k 0 ((k : ℤ) - 1)).card : ℤ)

theorem globalBase_eq_baseShape (a : Fin N → ℝ) (k : ℕ) (hk : k ≤ N) :
    globalSchurValue (rectanglePartition 3 k) a = schurValue (baseShape k) a := by
  rw [globalRectangle_eq_rectangleSchur a 3 k hk]
  change schurValue (rectangleShape N 3 k) a = _
  apply congrArg (fun lam : Fin N → ℕ => schurValue lam a)
  funext i
  unfold rectangleShape baseShape rowIndex
  split_ifs <;> omega

theorem globalQ_eq_shape (a : Fin N → ℝ) (k j : ℤ) (hj : 0 ≤ j) (hjk : j ≤ k)
    (hN : 2 * k + 3 ≤ N) : globalSchurValue (qPartition k j) a = schurValue (qShape k j) a := by
  rw [globalSchurValue_eq_of_fits _ _ (qPartition_zero k j hj hjk hN)]
  rfl

theorem globalP_eq_shape (a : Fin N → ℝ) (k j : ℤ) (hj : 0 ≤ j) (hjk : j ≤ k)
    (hN : 2 * k + 3 ≤ N) : globalSchurValue (pPartition k j) a = schurValue (pShape k j) a := by
  rw [globalSchurValue_eq_of_fits _ _ (pPartition_zero k j hj hjk hN)]
  rfl

theorem globalZ_eq_shape (a : Fin N → ℝ) (k j : ℤ) (hj : 0 ≤ j) (hjk : j ≤ k - 1)
    (hN : 2 * k + 3 ≤ N) : globalSchurValue (zPartition k j) a = schurValue (zShape k j) a := by
  rw [globalSchurValue_eq_of_fits _ _ (zPartition_zero k j hj hjk hN)]
  rfl

theorem globalRectangle_two (a : Fin N → ℝ) (ha : ∀ i, 0 ≤ a i)
    (k : ℕ) (hk : k + 1 ≤ N) :
    globalSchurValue (rectanglePartition 2 (k + 1)) a =
      elementaryInt a (k + 1 : ℕ) ^ 2 -
        elementaryInt a k * elementaryInt a (k + 2 : ℕ) := by
  rw [globalRectangle_eq_rectangleSchur a 2 (k + 1) hk,
    RectangleContinuity.rectangleSchur_eq_elementaryDet_of_nonneg a ha 2 (k + 1) hk]
  unfold elementaryDet
  rw [Matrix.det_fin_two]
  simp only [toeplitz, Fin.val_zero, Fin.val_one, Nat.cast_add, Nat.cast_one, Nat.cast_zero, Nat.cast_ofNat,
    sub_zero, add_zero, add_sub_cancel_right]
  have heq : (k : ℤ) + 1 + 1 = k + 2 := by omega
  rw [heq]
  ring

theorem scalarB_expanded (a : Fin N → ℝ) (ha : ∀ i, 0 ≤ a i)
    (k : ℕ) (hN : 2 * (k : ℤ) + 3 ≤ N) :
    scalarB a k =
      elementaryInt a (k + 1 : ℕ) *
        (elementaryInt a (k + 1 : ℕ) * schurValue (baseShape k) a) -
      elementaryInt a (k + 2 : ℕ) * (elementaryInt a k * schurValue (baseShape k) a) +
      elementaryInt a k * (∑ j ∈ Icc 0 (k : ℤ), schurValue (qShape k j) a) -
      elementaryInt a k * (∑ j ∈ Icc 0 (k : ℤ), schurValue (pShape k j) a) +
      elementaryInt a k * (∑ j ∈ Icc 0 ((k : ℤ) - 1), schurValue (zShape k j) a) := by
  have hpq : (∑ j ∈ Icc 0 (k : ℤ),
      (globalSchurValue (pPartition k j) a - globalSchurValue (qPartition k j) a)) =
      (∑ j ∈ Icc 0 (k : ℤ), schurValue (pShape k j) a) -
        ∑ j ∈ Icc 0 (k : ℤ), schurValue (qShape k j) a := by
    rw [← Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl
    intro j hj
    obtain ⟨hj0, hjk⟩ := Finset.mem_Icc.mp hj
    rw [globalP_eq_shape a k j hj0 hjk hN, globalQ_eq_shape a k j hj0 hjk hN]
  have hz : (∑ j ∈ Icc 0 ((k : ℤ) - 1), globalSchurValue (zPartition k j) a) =
      ∑ j ∈ Icc 0 ((k : ℤ) - 1), schurValue (zShape k j) a := by
    apply Finset.sum_congr rfl
    intro j hj
    obtain ⟨hj0, hjk⟩ := Finset.mem_Icc.mp hj
    rw [globalZ_eq_shape a k j hj0 hjk hN]
  unfold scalarB
  rw [globalBase_eq_baseShape a k (by omega), globalRectangle_two a ha k (by omega),
    load_eq_signed_schur, hpq, hz]
  ring

/-- The scalar expression is the sum of its actual, signed strip-pair counts. -/
theorem scalarB_eq_raw_sum (a : Fin N → ℝ) (ha : ∀ i, 0 ≤ a i)
    (k : ℕ) (hN : 2 * (k : ℤ) + 3 ≤ N) :
    scalarB a k = ∑ nu ∈ targets (5 * (k : ℤ) + 2),
      (rawCoefficient k nu : ℝ) * schurValue nu a := by
  have hpp := doublePieri_reindex a k (by omega) (by omega) (k + 1) (k + 1)
    (5 * (k : ℤ) + 2) (by omega)
  have hkm := doublePieri_reindex a k (by omega) (by omega) k (k + 2)
    (5 * (k : ℤ) + 2) (by omega)
  have hq := familyPieri_reindex a (qShape k) 0 k k (5 * (k : ℤ) + 2)
    (fun j hj => qShape_isPartition k j (Finset.mem_Icc.mp hj).1)
    (fun j hj i => by unfold qShape AlternantCancellation.qPart; split_ifs <;> omega)
    (fun j hj => by
      rw [qShape_degree k j (Finset.mem_Icc.mp hj).1 (Finset.mem_Icc.mp hj).2 hN]
      omega)
  have hp := familyPieri_reindex a (pShape k) 0 k k (5 * (k : ℤ) + 2)
    (fun j hj => pShape_isPartition k j (Finset.mem_Icc.mp hj).1)
    (fun j hj i => by unfold pShape AlternantCancellation.pPart; split_ifs <;> omega)
    (fun j hj => by
      rw [pShape_degree k j (Finset.mem_Icc.mp hj).1 (Finset.mem_Icc.mp hj).2 hN]
      omega)
  have hz := familyPieri_reindex a (zShape k) 0 ((k : ℤ) - 1) k (5 * (k : ℤ) + 2)
    (fun j hj => zShape_isPartition k j (Finset.mem_Icc.mp hj).1)
    (fun j hj i => by unfold zShape AlternantCancellation.zPart; split_ifs <;> omega)
    (fun j hj => by
      rw [zShape_degree k j (Finset.mem_Icc.mp hj).1 (Finset.mem_Icc.mp hj).2 hN]
      omega)
  rw [scalarB_expanded a ha k hN, hpp, hkm, hq, hp, hz,
    ← Finset.sum_sub_distrib, ← Finset.sum_add_distrib,
    ← Finset.sum_sub_distrib, ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro nu hnu
  unfold rawCoefficient
  push_cast
  ring


end CoefficientOne.ScalarExpansion

end
