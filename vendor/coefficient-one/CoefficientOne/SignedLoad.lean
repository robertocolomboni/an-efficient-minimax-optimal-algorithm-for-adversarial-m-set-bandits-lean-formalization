import CoefficientOne.AlternantCancellation
import CoefficientOne.AlternantIdentities
import CoefficientOne.SchurFoundations

/-!
# Assembly of the signed-load Schur expansion

The alphabet-size hypothesis in this module is `2*k+3 ≤ N`. It ensures that every
tail source and every row of the displayed partitions is actually present.
`ScalarPadding` extends the identity to smaller alphabets by zero padding.

This is Step 1 of the scalar coefficient proof, equations `eq:load` and
`eq:load-power-sums` in `paper/main.tex`. The bialternant theorem is Macdonald,
Chapter I, (3.1), through `AlgebraicCombinatorics.schurPoly_eq_alternant_div`.

The proof uses the manuscript's exponent cancellation, with an actual
determinant for the decreasing enumeration of each finite exponent set.
This enumeration is specified by uniqueness, using classical choice; its
determinant is identified with explicit row vectors by proved image equalities.
-/

noncomputable section

namespace CoefficientOne.SignedLoad

open Finset AlternantCancellation AlternantIdentities

variable {N : ℕ} {R : Type*} [CommRing R]

/-- The alternant of the uniquely determined decreasing enumeration of a set. -/
def orderedSetAlternant (x : Fin N → R) (s : Finset ℕ) : R := by
  classical
  exact if h : ∃ e : Fin N → ℕ, StrictAnti e ∧ univ.image e = s then
    detAlternant x h.choose
  else 0

theorem orderedSetAlternant_eq (x : Fin N → R) (s : Finset ℕ)
    (e : Fin N → ℕ) (he : StrictAnti e) (hs : univ.image e = s) :
    orderedSetAlternant x s = detAlternant x e := by
  unfold orderedSetAlternant
  split_ifs with h
  · congr 1
    exact eq_of_strictAnti_image_eq h.choose e h.choose_spec.1 he
      (h.choose_spec.2.trans hs.symm)
  · exact (h ⟨e, he, hs⟩).elim

theorem detAlternant_raise_eq_signed_set (x : Fin N → R)
    (e : Fin N → ℕ) (he : StrictAnti e) (b : Fin N) (t : ℕ)
    (hcollision : ∀ i, i ≠ b → e i ≠ e b + t) :
    detAlternant x (raiseExponent e b t) =
      (-1 : R) ^ (crossingRows e b t).card *
        orderedSetAlternant x (univ.image (raiseExponent e b t)) := by
  obtain ⟨a, hab, hbefore, hafter⟩ := exists_insertionPosition e he b t hcollision
  have hs := raiseExponent_moveUp_strictAnti e he a b t hab hbefore hafter
  rw [orderedSetAlternant_eq x _ _ hs (image_comp_perm _ (moveUp a b))]
  exact detAlternant_raise_eq_signed_sort x e he a b t hab hbefore hafter

/-- Translate integer exponents by N before using them as actual powers. -/
def shiftSet (s : Finset ℤ) : Finset ℕ := s.image (fun z : ℤ => (z + (N : ℤ)).toNat)

def exponentSetAlternant (x : Fin N → R) (s : Finset ℤ) : R :=
  orderedSetAlternant x (shiftSet (N := N) s)

theorem image_shiftedExponent (c : Fin N → ℤ) :
    univ.image (shiftedExponent c N) = shiftSet (N := N) (univ.image c) := by
  simp only [shiftSet, Finset.image_image]
  rfl

theorem exponentSetAlternant_eq (x : Fin N → R) (s : Finset ℤ)
    (c : Fin N → ℤ) (hc : StrictAnti c) (hpos : ∀ i, 0 ≤ c i + N)
    (hs : univ.image c = s) :
    exponentSetAlternant x s = detAlternant x (shiftedExponent c N) := by
  apply orderedSetAlternant_eq x _ _ (shiftedExponent_strictAnti c hc N hpos)
  rw [image_shiftedExponent, hs]

theorem image_update_of_injective {α : Type*} [DecidableEq α] (c : Fin N → α)
    (hc : Function.Injective c) (b : Fin N) (z : α) :
    univ.image (Function.update c b z) = insert z ((univ.image c).erase (c b)) := by
  have hrest : (univ.erase b).image (Function.update c b z) = (univ.erase b).image c := by
    apply Finset.image_congr
    intro i hi
    exact Function.update_of_ne (Finset.mem_erase.mp hi).1 z c
  calc
    univ.image (Function.update c b z) =
        (insert b (univ.erase b)).image (Function.update c b z) := by
      rw [Finset.insert_erase (Finset.mem_univ b)]
    _ = insert z ((univ.erase b).image c) := by
      rw [Finset.image_insert, Function.update_self, hrest]
    _ = insert z ((univ.image c).erase (c b)) := by
      rw [Finset.image_erase hc univ b]

theorem detAlternant_raise_shifted_eq_signed_set (x : Fin N → R)
    (c : Fin N → ℤ) (hc : StrictAnti c) (hpos : ∀ i, 0 ≤ c i + N)
    (b : Fin N) (t : ℕ) (hcollision : ∀ i, i ≠ b → c i ≠ c b + t) :
    detAlternant x (raiseExponent (shiftedExponent c N) b t) =
      (-1 : R) ^ (crossingExponents c b t).card *
        exponentSetAlternant x (insert (c b + t) ((univ.image c).erase (c b))) := by
  have he := shiftedExponent_strictAnti c hc N hpos
  have hn : ∀ i, i ≠ b → shiftedExponent c N i ≠ shiftedExponent c N b + t := by
    intro i hi
    have hb := hpos b
    have hii := hpos i
    have hne := hcollision i hi
    simp only [shiftedExponent]
    omega
  rw [detAlternant_raise_eq_signed_set x _ he b t hn,
    crossingRows_shifted_card c hc.injective N hpos b t]
  congr 1
  change orderedSetAlternant x _ = orderedSetAlternant x _
  congr 1
  rw [shiftedExponent_raise c N b t (hpos b), image_shiftedExponent,
    image_update_of_injective c hc.injective b (c b + t)]

/-- One-based row indices for the integer combinatorial description. -/
def rowIndex (i : Fin N) : ℤ := i.val + 1

def initialC (k j : ℤ) (i : Fin N) : ℤ := initialExponent k j (rowIndex i)

def initialShape (k j : ℤ) (i : Fin N) : ℕ := (initialPart k j (rowIndex i)).toNat

def tailC (k j d : ℤ) (i : Fin N) : ℤ := tailExponent k j d (rowIndex i)

def tailShape (k j d : ℤ) (i : Fin N) : ℕ := (tailPart k j d (rowIndex i)).toNat

def pShape (k j : ℤ) (i : Fin N) : ℕ := (pPart k j (rowIndex i)).toNat

def qShape (k j : ℤ) (i : Fin N) : ℕ := (qPart k j (rowIndex i)).toNat

def zShape (k j : ℤ) (i : Fin N) : ℕ := (zPart k j (rowIndex i)).toNat

theorem rowIndex_mem (i : Fin N) : rowIndex i ∈ Icc 1 (N : ℤ) := by
  have hi := i.isLt
  simp only [rowIndex, Finset.mem_Icc]
  omega

theorem image_rowIndex : univ.image (rowIndex (N := N)) = Icc 1 (N : ℤ) := by
  ext r
  simp only [Finset.mem_image, Finset.mem_univ, true_and, Finset.mem_Icc]
  constructor
  · rintro ⟨i, rfl⟩
    exact Finset.mem_Icc.mp (rowIndex_mem i)
  · intro hr
    refine ⟨⟨(r - 1).toNat, by omega⟩, ?_⟩
    simp only [rowIndex]
    omega

theorem initialC_image (k j : ℤ) (hj : 0 ≤ j) (hjk : j ≤ k) (hN : k ≤ N) :
    univ.image (initialC (N := N) k j) = occupied k N j := by
  calc
    univ.image (initialC k j) =
        (univ.image (rowIndex (N := N))).image (initialExponent k j) := by
      rw [Finset.image_image]
      rfl
    _ = occupied k N j := by
      rw [image_rowIndex, initial_exponents_eq_occupied k N j hj hjk hN]

theorem initialC_strictAnti (k j : ℤ) (hj : 0 ≤ j) :
    StrictAnti (initialC (N := N) k j) := by
  intro i z hiz
  apply initialExponent_strict k j _ _ hj
  simp only [rowIndex]
  omega

theorem initialC_offset_nonneg (k j : ℤ) (i : Fin N) :
    0 ≤ initialC k j i + N := by
  have hi := i.isLt
  unfold initialC initialExponent initialPart rowIndex
  split_ifs <;> omega

theorem initialShape_isPartition (k j : ℤ) (hj : 0 ≤ j) :
    AlgebraicCombinatorics.IsNPartition (initialShape (N := N) k j) := by
  intro i z hiz
  unfold initialShape initialPart rowIndex
  split_ifs <;> omega

theorem initialShape_add_rho (k j : ℤ) :
    initialShape (N := N) k j + AlgebraicCombinatorics.rho N =
      shiftedExponent (initialC k j) N := by
  funext i
  have hi := i.isLt
  simp only [Pi.add_apply, initialShape, AlgebraicCombinatorics.rho, shiftedExponent,
    initialC, initialExponent, initialPart, rowIndex]
  split_ifs <;> omega

theorem tailC_strictAnti (k j d : ℤ) (hj : 0 ≤ j) (hd : 0 ≤ d)
    (hd2 : d ≤ 2) (hjd : d - 1 ≤ j) :
    StrictAnti (tailC (N := N) k j d) := by
  intro i z hiz
  apply tailExponent_strict k j d _ _ hj hd hd2 hjd
  simp only [rowIndex]
  omega

theorem tailC_offset_nonneg (k j d : ℤ) (hd : 0 ≤ d) (i : Fin N) :
    0 ≤ tailC k j d i + N := by
  have hi := i.isLt
  have hp := tailPart_nonneg k j d (rowIndex i) hd
  unfold tailC tailExponent rowIndex at *
  omega

theorem tailShape_isPartition (k j d : ℤ) (hj : 0 ≤ j) (hd : 0 ≤ d)
    (hd2 : d ≤ 2) (hjd : d - 1 ≤ j) :
    AlgebraicCombinatorics.IsNPartition (tailShape (N := N) k j d) := by
  intro i z hiz
  unfold tailShape tailPart rowIndex
  split_ifs <;> omega

theorem tailShape_add_rho (k j d : ℤ) (hd : 0 ≤ d) :
    tailShape (N := N) k j d + AlgebraicCombinatorics.rho N =
      shiftedExponent (tailC k j d) N := by
  funext i
  have hi := i.isLt
  simp only [Pi.add_apply, tailShape, AlgebraicCombinatorics.rho, shiftedExponent,
    tailC, tailExponent, tailPart, rowIndex]
  split_ifs <;> omega

theorem tailC_image (k j d : ℤ) (hj : 0 ≤ j) (hjk : j ≤ k)
    (hN : 2 * k + 3 ≤ N) (hd : 0 ≤ d) (hd2 : d ≤ 2) (hjd : d - 1 ≤ j) :
    univ.image (tailC (N := N) k j d) = raised k N j (tailSource k j d) := by
  calc
    univ.image (tailC k j d) =
        (univ.image (rowIndex (N := N))).image (tailExponent k j d) := by
      rw [Finset.image_image]
      rfl
    _ = raised k N j (tailSource k j d) := by
      rw [image_rowIndex, tail_exponents_eq_raised k N j d hj hjk hN hd hd2 hjd]

theorem tailShape_zero_eq_qShape (k j : ℤ) (hj : 0 ≤ j) :
    tailShape (N := N) k j 0 = qShape k j := by
  funext i
  simp only [tailShape, qShape, tailPart_zero_eq_qPart k j hj]

theorem tailShape_one_eq_pShape (k j : ℤ) :
    tailShape (N := N) k j 1 = pShape k j := by
  funext i
  simp only [tailShape, pShape, tailPart_one_eq_pPart]

theorem tailShape_two_eq_zShape (k j : ℤ) (hj : 1 ≤ j) :
    tailShape (N := N) k j 2 = zShape k (j - 1) := by
  funext i
  simp only [tailShape, zShape, tailPart_two_eq_zPart k j hj]


/-- The determinant contribution of one source, with collisions explicitly discarded. -/
def raisedContribution (x : Fin N → R) (k j q : ℤ) : R :=
  if destination j q ∈ occupied k N j then 0 else
    (-1 : R) ^ (crossed k N j q).card * exponentSetAlternant x (raised k N j q)

theorem initialC_mem (k j : ℤ) (hj : 0 ≤ j) (hjk : j ≤ k) (hN : k ≤ N)
    (b : Fin N) : initialC k j b ∈ occupied k N j := by
  rw [← initialC_image k j hj hjk hN]
  exact Finset.mem_image.mpr ⟨b, Finset.mem_univ _, rfl⟩

theorem detAlternant_raise_initial_eq_contribution (x : Fin N → R) (k j : ℤ)
    (hj : 0 ≤ j) (hjk : j ≤ k) (hN : k ≤ N) (b : Fin N) :
    detAlternant x (raiseExponent (shiftedExponent (initialC k j) N) b (j + 2).toNat) =
      raisedContribution x k j (initialC k j b) := by
  have hpos := initialC_offset_nonneg (N := N) k j
  have ht : ((j + 2).toNat : ℤ) = j + 2 := by omega
  unfold raisedContribution
  split_ifs with hd
  · have hm : destination j (initialC k j b) ∈ univ.image (initialC (N := N) k j) := by
      rwa [initialC_image k j hj hjk hN]
    obtain ⟨r, _, hr⟩ := Finset.mem_image.mp hm
    have hbr : b ≠ r := by
      intro h
      subst r
      unfold destination at hr
      omega
    apply detAlternant_raise_eq_zero_of_collision x _ b r (j + 2).toNat hbr
    have hb := hpos b
    have hrp := hpos r
    unfold destination at hr
    simp only [shiftedExponent]
    omega
  · have hcollision : ∀ i : Fin N, i ≠ b → initialC k j i ≠ initialC k j b + (j + 2).toNat := by
      intro i hi heq
      apply hd
      have him := initialC_mem k j hj hjk hN i
      have heq' : initialC k j i = destination j (initialC k j b) := by
        unfold destination
        omega
      rwa [heq'] at him
    rw [detAlternant_raise_shifted_eq_signed_set x _ (initialC_strictAnti k j hj) hpos
      b (j + 2).toNat hcollision]
    have hcross : crossingExponents (initialC (N := N) k j) b (j + 2).toNat =
        crossed k N j (initialC k j b) := by
      ext z
      unfold crossingExponents crossed
      rw [Finset.mem_filter, Finset.mem_filter]
      simp only [initialC_image k j hj hjk hN, destination]
      rw [ht]
      simp only [add_assoc]
    rw [hcross]
    congr 2
    simp only [raised, initialC_image k j hj hjk hN, destination]
    congr 1
    omega

/-- Reindex the determinant source sum by the actual occupied integer exponents. -/
theorem powerSum_initial_det_eq_sources (x : Fin N → R) (k j : ℤ)
    (hj : 0 ≤ j) (hjk : j ≤ k) (hN : k ≤ N) :
    powerSum x (j + 2).toNat *
        detAlternant x (initialShape k j + AlgebraicCombinatorics.rho N) =
      ∑ q ∈ occupied k N j, raisedContribution x k j q := by
  rw [initialShape_add_rho, powerSum_mul_detAlternant]
  refine Finset.sum_bij (fun b _ => initialC k j b) ?_ ?_ ?_ ?_
  · intro b hb
    exact initialC_mem k j hj hjk hN b
  · intro b hb r hr hbr
    exact (initialC_strictAnti k j hj).injective hbr
  · intro q hq
    rw [← initialC_image k j hj hjk hN] at hq
    obtain ⟨b, hb, heq⟩ := Finset.mem_image.mp hq
    exact ⟨b, hb, heq⟩
  · intro b hb
    exact detAlternant_raise_initial_eq_contribution x k j hj hjk hN b

/-- Include the alternating prefactor from the rectangular deletion expansion. -/
def signedContribution (x : Fin N → R) (k j q : ℤ) : R :=
  if destination j q ∈ occupied k N j then 0 else
    (exponentSign (j + ((crossed k N j q).card : ℤ)) : R) *
      exponentSetAlternant x (raised k N j q)

theorem exponentSign_cast_add_card (j : ℤ) (hj : 0 ≤ j) (m : ℕ) :
    (exponentSign (j + (m : ℤ)) : R) = (-1 : R) ^ (j.toNat + m) := by
  have h : j + (m : ℤ) = ((j.toNat + m : ℕ) : ℤ) := by omega
  rw [h, exponentSign_nat]
  simp

theorem prefactor_mul_raisedContribution (x : Fin N → R) (k j q : ℤ) (hj : 0 ≤ j) :
    (-1 : R) ^ j.toNat * raisedContribution x k j q = signedContribution x k j q := by
  unfold raisedContribution signedContribution
  split_ifs
  · simp
  · rw [exponentSign_cast_add_card j hj, ← mul_assoc, ← pow_add]

theorem signed_powerSum_initial_det_eq_sources (x : Fin N → R) (k j : ℤ)
    (hj : 0 ≤ j) (hjk : j ≤ k) (hN : k ≤ N) :
    (-1 : R) ^ j.toNat * powerSum x (j + 2).toNat *
        detAlternant x (initialShape k j + AlgebraicCombinatorics.rho N) =
      ∑ q ∈ occupied k N j, signedContribution x k j q := by
  rw [mul_assoc, powerSum_initial_det_eq_sources x k j hj hjk hN, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro q hq
  exact prefactor_mul_raisedContribution x k j q hj

theorem upper_disjoint_tail (k N j : ℤ) : Disjoint (upper k j) (tail k N) := by
  apply Finset.disjoint_left.mpr
  intro q hq ht
  simp only [upper, tail, Finset.mem_erase, Finset.mem_Icc] at hq ht
  omega

theorem sum_upper_eq_indexed (k j : ℤ) (f : ℤ → R) :
    (∑ q ∈ upper k j, f q) = ∑ l ∈ Icc 0 k, if l ≠ j then f (gap k l) else 0 := by
  rw [← Finset.sum_filter]
  symm
  refine Finset.sum_bij (fun l _ => gap k l) ?_ ?_ ?_ ?_
  · intro l hl
    simp only [Finset.mem_filter, Finset.mem_Icc] at hl
    exact (gap_mem_upper_iff k j l).mpr ⟨hl.1.1, hl.1.2, hl.2⟩
  · intro l hl m hm h
    unfold gap at h
    omega
  · intro q hq
    simp only [upper, Finset.mem_erase, Finset.mem_Icc, gap] at hq
    refine ⟨q - 3 + k, ?_, ?_⟩
    · simp only [Finset.mem_filter, Finset.mem_Icc]
      omega
    · unfold gap
      omega
  · intro l hl
    rfl

theorem upper_signedContribution_indexed (x : Fin N → R) (k j l : ℤ)
    (hj : 0 ≤ j) (hjk : j ≤ k) (hl : 0 ≤ l) (hlk : l ≤ k) :
    (if l ≠ j then signedContribution x k j (gap k l) else 0) =
      if j ≠ l ∧ 3 < destination j (gap k l) then
        (exponentSign (upperSignExponent k j l) : R) *
          exponentSetAlternant x (raised k N j (gap k l)) else 0 := by
  by_cases hne : j = l
  · subst l
    simp
  · have hne' : l ≠ j := Ne.symm hne
    simp only [if_pos hne']
    unfold signedContribution
    by_cases hd : 3 < destination j (gap k l)
    · have hn := (upper_survives_iff k N j l hj hl).mpr hd
      rw [if_neg hn, if_pos (And.intro hne hd),
        ← upperSignExponent_eq_crossed k N j l hj hjk hl hlk hd]
    · have hm : destination j (gap k l) ∈ occupied k N j := by
        by_contra hn
        exact hd ((upper_survives_iff k N j l hj hl).mp hn)
      rw [if_pos hm, if_neg (fun h => hd h.2)]

/-- The actual determinant contributions from all upper sources cancel. -/
theorem sum_upper_signedContribution_eq_zero (x : Fin N → R) (k : ℤ) :
    (∑ j ∈ Icc 0 k, ∑ q ∈ upper k j, signedContribution x k j q) = 0 := by
  have h := upper_sum_eq_zero k (N : ℤ)
    (fun s => exponentSetAlternant x s)
  have hindexed :
      (∑ j ∈ Icc 0 k, ∑ q ∈ upper k j, signedContribution x k j q) =
        ∑ j ∈ Icc 0 k, ∑ l ∈ Icc 0 k,
          if j ≠ l ∧ 3 < destination j (gap k l) then
            (exponentSign (upperSignExponent k j l) : R) *
              exponentSetAlternant x (raised k N j (gap k l)) else 0 := by
    apply Finset.sum_congr rfl
    intro j hj
    rw [sum_upper_eq_indexed]
    apply Finset.sum_congr rfl
    intro l hl
    exact upper_signedContribution_indexed x k j l
      (Finset.mem_Icc.mp hj).1 (Finset.mem_Icc.mp hj).2
      (Finset.mem_Icc.mp hl).1 (Finset.mem_Icc.mp hl).2
  rw [hindexed]
  simpa only [upperPairs, Finset.sum_filter, Finset.product_eq_sprod, Finset.sum_product,
    zsmul_eq_mul] using h



def allowedTail (j : ℤ) : Finset ℤ := (Icc 0 2).filter (fun d => d - 1 ≤ j)

theorem tailSource_no_collision (k j d : ℤ) (hj : 0 ≤ j) (hjk : j ≤ k)
    (hN : 2 * k + 3 ≤ N) (hd : 0 ≤ d) (hd2 : d ≤ 2) (hjd : d - 1 ≤ j) :
    destination j (tailSource k j d) ∉ occupied k N j := by
  have hq := (tailSource_mem_iff k N j d hj hjk hN hd hd2).mpr hjd
  exact (tail_survives_iff k N j _ hj hjk hq).mpr ⟨d, hd, hd2, rfl⟩

theorem signedContribution_tailSource (x : Fin N → R) (k j d : ℤ)
    (hj : 0 ≤ j) (hjk : j ≤ k) (hN : 2 * k + 3 ≤ N)
    (hd : 0 ≤ d) (hd2 : d ≤ 2) (hjd : d - 1 ≤ j) :
    signedContribution x k j (tailSource k j d) =
      (exponentSign (1 - d) : R) *
        detAlternant x (tailShape k j d + AlgebraicCombinatorics.rho N) := by
  rw [signedContribution, if_neg (tailSource_no_collision k j d hj hjk hN hd hd2 hjd),
    tail_crossed_card k N j d hj hjk hN hd hd2 hjd, tail_sign]
  rw [exponentSetAlternant_eq x _ (tailC k j d)
    (tailC_strictAnti k j d hj hd hd2 hjd) (tailC_offset_nonneg k j d hd)
    (tailC_image k j d hj hjk hN hd hd2 hjd), tailShape_add_rho k j d hd]

theorem sum_tail_eq_allowed (x : Fin N → R) (k j : ℤ)
    (hj : 0 ≤ j) (hjk : j ≤ k) (hN : 2 * k + 3 ≤ N) :
    (∑ q ∈ tail k N, signedContribution x k j q) =
      ∑ d ∈ allowedTail j, signedContribution x k j (tailSource k j d) := by
  have hfilter : (∑ q ∈ tail k N, signedContribution x k j q) =
      ∑ q ∈ (tail k N).filter (fun q => destination j q ∉ occupied k N j),
        signedContribution x k j q := by
    rw [Finset.sum_filter]
    apply Finset.sum_congr rfl
    intro q hq
    by_cases h : destination j q ∈ occupied k N j
    · simp [signedContribution, h]
    · simp [h]
  rw [hfilter]
  symm
  refine Finset.sum_bij (fun d _ => tailSource k j d) ?_ ?_ ?_ ?_
  · intro d hd
    simp only [allowedTail, Finset.mem_filter, Finset.mem_Icc] at hd
    apply Finset.mem_filter.mpr
    exact ⟨(tailSource_mem_iff k N j d hj hjk hN hd.1.1 hd.1.2).mpr hd.2,
      tailSource_no_collision k j d hj hjk hN hd.1.1 hd.1.2 hd.2⟩
  · intro d hd e he h
    unfold tailSource at h
    omega
  · intro q hq
    obtain ⟨hqt, hqn⟩ := Finset.mem_filter.mp hq
    obtain ⟨d, hd, hd2, hqeq⟩ := (tail_survives_iff k N j q hj hjk hqt).mp hqn
    have hjd : d - 1 ≤ j := by
      apply (tailSource_mem_iff k N j d hj hjk hN hd hd2).mp
      rwa [← hqeq]
    refine ⟨d, ?_, hqeq.symm⟩
    simp only [allowedTail, Finset.mem_filter, Finset.mem_Icc]
    exact ⟨⟨hd, hd2⟩, hjd⟩
  · intro d hd
    rfl

theorem allowedTail_zero : allowedTail 0 = {0, 1} := by
  ext d
  simp only [allowedTail, Finset.mem_filter, Finset.mem_Icc, Finset.mem_insert,
    Finset.mem_singleton]
  omega

theorem allowedTail_of_pos (j : ℤ) (hj : 1 ≤ j) : allowedTail j = {0, 1, 2} := by
  ext d
  simp only [allowedTail, Finset.mem_filter, Finset.mem_Icc, Finset.mem_insert,
    Finset.mem_singleton]
  omega

theorem signedContribution_tail_zero (x : Fin N → R) (k j : ℤ)
    (hj : 0 ≤ j) (hjk : j ≤ k) (hN : 2 * k + 3 ≤ N) :
    signedContribution x k j (tailSource k j 0) =
      -detAlternant x (qShape k j + AlgebraicCombinatorics.rho N) := by
  rw [signedContribution_tailSource x k j 0 hj hjk hN (by omega) (by omega) (by omega),
    tailShape_zero_eq_qShape k j hj]
  norm_num [exponentSign]

theorem signedContribution_tail_one (x : Fin N → R) (k j : ℤ)
    (hj : 0 ≤ j) (hjk : j ≤ k) (hN : 2 * k + 3 ≤ N) :
    signedContribution x k j (tailSource k j 1) =
      detAlternant x (pShape k j + AlgebraicCombinatorics.rho N) := by
  rw [signedContribution_tailSource x k j 1 hj hjk hN (by omega) (by omega) (by omega),
    tailShape_one_eq_pShape]
  norm_num [exponentSign]

theorem signedContribution_tail_two (x : Fin N → R) (k j : ℤ)
    (hj : 1 ≤ j) (hjk : j ≤ k) (hN : 2 * k + 3 ≤ N) :
    signedContribution x k j (tailSource k j 2) =
      -detAlternant x (zShape k (j - 1) + AlgebraicCombinatorics.rho N) := by
  rw [signedContribution_tailSource x k j 2 (by omega) hjk hN
    (by omega) (by omega) (by omega), tailShape_two_eq_zShape k j hj]
  norm_num [exponentSign]

/-- All three tail types with the absent `Z` term at `j=0` handled explicitly. -/
theorem sum_tail_signedContribution (x : Fin N → R) (k j : ℤ)
    (hj : 0 ≤ j) (hjk : j ≤ k) (hN : 2 * k + 3 ≤ N) :
    (∑ q ∈ tail k N, signedContribution x k j q) =
      detAlternant x (pShape k j + AlgebraicCombinatorics.rho N) -
        detAlternant x (qShape k j + AlgebraicCombinatorics.rho N) -
          if j = 0 then 0 else detAlternant x (zShape k (j - 1) + AlgebraicCombinatorics.rho N) := by
  rw [sum_tail_eq_allowed x k j hj hjk hN]
  by_cases hj0 : j = 0
  · subst j
    rw [allowedTail_zero, Finset.sum_pair (by decide),
      signedContribution_tail_zero x k 0 (by omega) hjk hN,
      signedContribution_tail_one x k 0 (by omega) hjk hN]
    simp
    ring
  · have hj1 : 1 ≤ j := by omega
    rw [allowedTail_of_pos j hj1, Finset.sum_insert (by decide), Finset.sum_pair (by decide),
      signedContribution_tail_zero x k j hj hjk hN,
      signedContribution_tail_one x k j hj hjk hN,
      signedContribution_tail_two x k j hj1 hjk hN, if_neg hj0]
    ring



theorem sum_shift_nonzero (k : ℤ) (f : ℤ → R) :
    (∑ j ∈ Icc 0 k, if j = 0 then 0 else f (j - 1)) =
      ∑ i ∈ Icc 0 (k - 1), f i := by
  have hfilter : (∑ j ∈ Icc 0 k, if j = 0 then 0 else f (j - 1)) =
      ∑ j ∈ (Icc 0 k).filter (fun j => j ≠ 0), f (j - 1) := by
    rw [Finset.sum_filter]
    apply Finset.sum_congr rfl
    intro j hj
    by_cases h : j = 0 <;> simp [h]
  rw [hfilter]
  refine Finset.sum_bij (fun j _ => j - 1) ?_ ?_ ?_ ?_
  · intro j hj
    simp only [Finset.mem_filter, Finset.mem_Icc] at hj
    simp only [Finset.mem_Icc]
    omega
  · intro j hj l hl heq
    omega
  · intro i hi
    simp only [Finset.mem_Icc] at hi
    refine ⟨i + 1, ?_, by omega⟩
    simp only [Finset.mem_filter, Finset.mem_Icc]
    omega
  · intro j hj
    rfl

/-- The entire signed-load expansion at the level of actual alternant determinants. -/
theorem signed_load_determinants (x : Fin N → R) (k : ℤ)
    (hk : 0 ≤ k) (hN : 2 * k + 3 ≤ N) :
    (∑ j ∈ Icc 0 k, (-1 : R) ^ j.toNat * powerSum x (j + 2).toNat *
      detAlternant x (initialShape k j + AlgebraicCombinatorics.rho N)) =
      (∑ j ∈ Icc 0 k,
        (detAlternant x (pShape k j + AlgebraicCombinatorics.rho N) -
          detAlternant x (qShape k j + AlgebraicCombinatorics.rho N))) -
      ∑ j ∈ Icc 0 (k - 1), detAlternant x (zShape k j + AlgebraicCombinatorics.rho N) := by
  have hkN : k ≤ N := by omega
  calc
    _ = ∑ j ∈ Icc 0 k, ∑ q ∈ occupied k N j, signedContribution x k j q := by
      apply Finset.sum_congr rfl
      intro j hj
      exact signed_powerSum_initial_det_eq_sources x k j
        (Finset.mem_Icc.mp hj).1 (Finset.mem_Icc.mp hj).2 hkN
    _ = ∑ j ∈ Icc 0 k,
        ((∑ q ∈ upper k j, signedContribution x k j q) +
          ∑ q ∈ tail k N, signedContribution x k j q) := by
      apply Finset.sum_congr rfl
      intro j hj
      exact Finset.sum_union (upper_disjoint_tail k N j)
    _ = (∑ j ∈ Icc 0 k, ∑ q ∈ upper k j, signedContribution x k j q) +
        ∑ j ∈ Icc 0 k, ∑ q ∈ tail k N, signedContribution x k j q :=
      Finset.sum_add_distrib
    _ = ∑ j ∈ Icc 0 k, ∑ q ∈ tail k N, signedContribution x k j q := by
      rw [sum_upper_signedContribution_eq_zero, zero_add]
    _ = ∑ j ∈ Icc 0 k,
        (detAlternant x (pShape k j + AlgebraicCombinatorics.rho N) -
          detAlternant x (qShape k j + AlgebraicCombinatorics.rho N) -
          if j = 0 then 0 else detAlternant x (zShape k (j - 1) + AlgebraicCombinatorics.rho N)) := by
      apply Finset.sum_congr rfl
      intro j hj
      exact sum_tail_signedContribution x k j
        (Finset.mem_Icc.mp hj).1 (Finset.mem_Icc.mp hj).2 hN
    _ = _ := by
      rw [Finset.sum_sub_distrib, sum_shift_nonzero k (fun j => detAlternant x (zShape k j + AlgebraicCombinatorics.rho N))]

theorem pShape_isPartition (k j : ℤ) (hj : 0 ≤ j) :
    AlgebraicCombinatorics.IsNPartition (pShape (N := N) k j) := by
  rw [← tailShape_one_eq_pShape]
  exact tailShape_isPartition k j 1 hj (by omega) (by omega) (by omega)

theorem qShape_isPartition (k j : ℤ) (hj : 0 ≤ j) :
    AlgebraicCombinatorics.IsNPartition (qShape (N := N) k j) := by
  rw [← tailShape_zero_eq_qShape k j hj]
  exact tailShape_isPartition k j 0 hj (by omega) (by omega) (by omega)

theorem zShape_isPartition (k j : ℤ) (hj : 0 ≤ j) :
    AlgebraicCombinatorics.IsNPartition (zShape (N := N) k j) := by
  have h : tailShape (N := N) k (j + 1) 2 = zShape k j := by
    simpa only [add_sub_cancel_right] using tailShape_two_eq_zShape (N := N) k (j + 1) (by omega)
  rw [← h]
  exact tailShape_isPartition k (j + 1) 2 (by omega) (by omega) (by omega) (by omega)

theorem det_shape_add_rho (lam : Fin N → ℕ) (hlam : AlgebraicCombinatorics.IsNPartition lam) :
    detAlternant (MvPolynomial.X : Fin N → MvPolynomial (Fin N) R)
        (lam + AlgebraicCombinatorics.rho N) =
      AlgebraicCombinatorics.alternant (AlgebraicCombinatorics.rho N) *
        AlgebraicCombinatorics.schurPoly lam := by
  rw [← alternant_eq_detAlternant]
  exact AlgebraicCombinatorics.schurPoly_eq_alternant_div lam hlam

/--
The signed Schur expansion before substituting the rectangular deletion sum.
The alphabet-size hypothesis is explicit and covers every displayed row.
-/
theorem signed_load_schur [IsDomain R] (k : ℤ) (hk : 0 ≤ k) (hN : 2 * k + 3 ≤ N) :
    (∑ j ∈ Icc 0 k,
      (-1 : MvPolynomial (Fin N) R) ^ j.toNat *
        powerSum MvPolynomial.X (j + 2).toNat *
          AlgebraicCombinatorics.schurPoly (initialShape k j)) =
      (∑ j ∈ Icc 0 k,
        (AlgebraicCombinatorics.schurPoly (pShape k j) -
          AlgebraicCombinatorics.schurPoly (qShape k j))) -
        ∑ j ∈ Icc 0 (k - 1), AlgebraicCombinatorics.schurPoly (zShape k j) := by
  let v : MvPolynomial (Fin N) R :=
    AlgebraicCombinatorics.alternant (AlgebraicCombinatorics.rho N)
  have hdet := signed_load_determinants
    (MvPolynomial.X : Fin N → MvPolynomial (Fin N) R) k hk hN
  have hleft :
      (∑ j ∈ Icc 0 k,
        (-1 : MvPolynomial (Fin N) R) ^ j.toNat * powerSum MvPolynomial.X (j + 2).toNat *
          detAlternant MvPolynomial.X (initialShape k j + AlgebraicCombinatorics.rho N)) =
        v * ∑ j ∈ Icc 0 k,
          (-1 : MvPolynomial (Fin N) R) ^ j.toNat * powerSum MvPolynomial.X (j + 2).toNat *
            AlgebraicCombinatorics.schurPoly (initialShape k j) := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro j hj
    rw [det_shape_add_rho (initialShape k j) (initialShape_isPartition k j (Finset.mem_Icc.mp hj).1)]
    dsimp only [v]
    ring
  have hpq :
      (∑ j ∈ Icc 0 k,
        (detAlternant MvPolynomial.X (pShape k j + AlgebraicCombinatorics.rho N) -
          detAlternant MvPolynomial.X (qShape k j + AlgebraicCombinatorics.rho N))) =
        v * ∑ j ∈ Icc 0 k,
          (AlgebraicCombinatorics.schurPoly (pShape k j) -
            AlgebraicCombinatorics.schurPoly (qShape k j)) := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro j hj
    rw [det_shape_add_rho (pShape k j) (pShape_isPartition k j (Finset.mem_Icc.mp hj).1),
      det_shape_add_rho (qShape k j) (qShape_isPartition k j (Finset.mem_Icc.mp hj).1)]
    dsimp only [v]
    ring
  have hz :
      (∑ j ∈ Icc 0 (k - 1), detAlternant MvPolynomial.X
        (zShape k j + AlgebraicCombinatorics.rho N)) =
        v * ∑ j ∈ Icc 0 (k - 1), AlgebraicCombinatorics.schurPoly (zShape k j) := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro j hj
    exact det_shape_add_rho (zShape k j) (zShape_isPartition k j (Finset.mem_Icc.mp hj).1)
  rw [hleft, hpq, hz, ← mul_sub] at hdet
  exact (AlgebraicCombinatorics.alternant_rho_isRegular (R := R) (N := N)).left hdet



theorem eval_powerSum (a : Fin N → R) (t : ℕ) :
    MvPolynomial.eval a (powerSum MvPolynomial.X t : MvPolynomial (Fin N) R) =
      powerSum a t := by
  simp [powerSum]

/-- The identity holds at all real letters, including coinciding or zero letters. -/
theorem signed_load_value (a : Fin N → ℝ) (k : ℤ) (hk : 0 ≤ k) (hN : 2 * k + 3 ≤ N) :
    (∑ j ∈ Icc 0 k, (-1 : ℝ) ^ j.toNat * powerSum a (j + 2).toNat *
        CoefficientOne.schurValue (initialShape k j) a) =
      (∑ j ∈ Icc 0 k,
        (CoefficientOne.schurValue (pShape k j) a - CoefficientOne.schurValue (qShape k j) a)) -
      ∑ j ∈ Icc 0 (k - 1), CoefficientOne.schurValue (zShape k j) a := by
  have h := congrArg (MvPolynomial.eval a) (signed_load_schur (R := ℝ) (N := N) k hk hN)
  simpa only [CoefficientOne.schurValue, map_sum, map_sub, map_mul, map_pow,
    map_neg, map_one, eval_powerSum] using h


end CoefficientOne.SignedLoad

end
