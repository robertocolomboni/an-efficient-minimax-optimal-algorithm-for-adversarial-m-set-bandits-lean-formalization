import Mathlib

/-!
# Exponent cancellation in the signed-load identity

This module proves the finite combinatorics of Step 1 of the scalar lemma in
`paper/main.tex`, from the occupied exponent set through the three-row tail
table. The argument uses finite-set cardinalities and a sign-reversing
involution.

All row and exponent indices are integers. Row functions are interpreted on
`Icc 1 N`. Using integers avoids truncated subtraction in the exponents and
retains the cases `j = 0`, `j = k`, and the absent `d = 2, j = 0` source.

`AlternantIdentities` proves the power-sum action, collision vanishing and
sorting signs for determinants. `SignedLoad` combines these results with the
finite sets and row functions below to obtain equations `eq:load` and
`eq:load-power-sums` of the manuscript.
-/

namespace CoefficientOne.AlternantCancellation

noncomputable section

open Finset

/-- The moving hole in the upper occupied block. -/
def gap (k j : ℤ) : ℤ := 3 - k + j

/-- The occupied upper exponents, with the moving hole removed. -/
def upper (k j : ℤ) : Finset ℤ := (Icc (3 - k) 3).erase (gap k j)

/-- The occupied zero-part tail, including the last padded row. -/
def tail (k N : ℤ) : Finset ℤ := Icc (-N) (-k - 1)

def occupied (k N j : ℤ) : Finset ℤ := upper k j ∪ tail k N

/-- Raising source exponent `q` in the `j`th power-sum summand. -/
def destination (j q : ℤ) : ℤ := q + j + 2

def raised (k N j q : ℤ) : Finset ℤ :=
  insert (destination j q) ((occupied k N j).erase q)

/-- The actual occupied exponents crossed by a raised row. -/
def crossed (k N j q : ℤ) : Finset ℤ :=
  (occupied k N j).filter (fun x => q < x ∧ x < destination j q)

/-- Integer parity sign, also convenient for the manuscript's negative sign exponents. -/
def exponentSign (z : ℤ) : ℤ := if z % 2 = 0 then 1 else -1

theorem exponentSign_nat (n : ℕ) : exponentSign n = (-1 : ℤ) ^ n := by
  rw [neg_one_pow_eq_pow_mod_two]
  have hn : n % 2 = 0 ∨ n % 2 = 1 := by omega
  rcases hn with hn | hn
  · have hz : (n : ℤ) % 2 = 0 := by omega
    simp [exponentSign, hn, hz]
  · have hz : (n : ℤ) % 2 = 1 := by omega
    simp [exponentSign, hn, hz]

/-- The padded partition `(4^(k-j), 3^j)`, as a one-based row function. -/
def initialPart (k j r : ℤ) : ℤ :=
  if r ≤ k - j then 4 else if r ≤ k then 3 else 0

/-- Subtract the one-based row index, as in the shifted alternant convention. -/
def initialExponent (k j r : ℤ) : ℤ := initialPart k j r - r

theorem initial_exponents_eq_occupied (k N j : ℤ)
    (hj : 0 ≤ j) (hjk : j ≤ k) (hN : k ≤ N) :
    (Icc 1 N).image (initialExponent k j) = occupied k N j := by
  ext x
  simp only [Finset.mem_image, Finset.mem_Icc]
  constructor
  · rintro ⟨r, hr, rfl⟩
    simp only [occupied, upper, tail, Finset.mem_union, Finset.mem_erase,
      Finset.mem_Icc, initialExponent, initialPart, gap]
    split_ifs <;> omega
  · intro hx
    simp only [occupied, upper, tail, Finset.mem_union, Finset.mem_erase,
      Finset.mem_Icc, gap] at hx
    rcases hx with hx | hx
    · by_cases h : 3 - k + j < x
      · refine ⟨4 - x, by omega, ?_⟩
        simp only [initialExponent, initialPart]
        split_ifs <;> omega
      · refine ⟨3 - x, by omega, ?_⟩
        simp only [initialExponent, initialPart]
        split_ifs <;> omega
    · refine ⟨-x, by omega, ?_⟩
      simp only [initialExponent, initialPart]
      split_ifs <;> omega

theorem initialExponent_strict (k j r s : ℤ)
    (hj : 0 ≤ j) (hrs : r < s) :
    initialExponent k j s < initialExponent k j r := by
  unfold initialExponent initialPart
  split_ifs <;> omega

theorem gap_mem_upper_iff (k j l : ℤ) :
    gap k l ∈ upper k j ↔ 0 ≤ l ∧ l ≤ k ∧ l ≠ j := by
  simp only [upper, gap, Finset.mem_erase, Finset.mem_Icc]
  omega

/-- The destinations agree after exchanging summand and source indices. -/
theorem upper_destination_swap (k j l : ℤ) :
    destination j (gap k l) = destination l (gap k j) := by
  unfold destination gap
  omega

theorem upper_destination_formula (k j l : ℤ) :
    destination j (gap k l) = 5 - k + j + l := by
  unfold destination gap
  omega

/-- An upper source cannot land in its own summand's moving hole. -/
theorem upper_destination_ne_gap (k j l : ℤ) (hl : 0 ≤ l) :
    destination j (gap k l) ≠ gap k j := by
  unfold destination gap
  omega

/-- Exactly the upper sources that jump above three avoid a collision. -/
theorem upper_survives_iff (k N j l : ℤ)
    (hj : 0 ≤ j) (hl : 0 ≤ l) :
    destination j (gap k l) ∉ occupied k N j ↔
      3 < destination j (gap k l) := by
  simp only [occupied, upper, tail, destination, gap, Finset.mem_union,
    Finset.mem_erase, Finset.mem_Icc]
  omega

/-- Exchanging the indices gives exactly the same final exponent set. -/
theorem upper_raised_swap (k N j l : ℤ) (hj : 0 ≤ j) (hl : 0 ≤ l) :
    raised k N j (gap k l) = raised k N l (gap k j) := by
  ext x
  simp only [raised, occupied, upper, tail, destination, gap,
    Finset.mem_insert, Finset.mem_union, Finset.mem_erase, Finset.mem_Icc]
  omega

/-- Crossing an upper source counts the remaining occupied exponents above it. -/
theorem upper_crossed_eq (k N j l : ℤ) (hj : 0 ≤ j) (hl : 0 ≤ l)
    (hd : 3 < destination j (gap k l)) :
    crossed k N j (gap k l) = (Icc (gap k l + 1) 3).erase (gap k j) := by
  ext x
  unfold crossed
  rw [Finset.mem_filter]
  simp only [occupied, upper, tail, destination, gap,
    Finset.mem_filter, Finset.mem_union, Finset.mem_erase, Finset.mem_Icc] at *
  omega

/-- The cardinality formula counts actual crossings, including the moving hole. -/
theorem upper_crossed_card (k N j l : ℤ)
    (hj : 0 ≤ j) (hjk : j ≤ k) (hl : 0 ≤ l) (hlk : l ≤ k)
    (hd : 3 < destination j (gap k l)) :
    ((crossed k N j (gap k l)).card : ℤ) = k - l - if l < j then 1 else 0 := by
  rw [upper_crossed_eq k N j l hj hl hd]
  have hcard : ((Icc (gap k l + 1) 3).card : ℤ) = k - l := by
    rw [Int.card_Icc_of_le (a := gap k l + 1) (b := 3) (by unfold gap; omega)]
    unfold gap
    omega
  by_cases h : l < j
  · have hmem : gap k j ∈ Icc (gap k l + 1) 3 := by
      simp only [Finset.mem_Icc, gap]
      omega
    rw [Finset.cast_card_erase_of_mem hmem, hcard, if_pos h]
  · have hmem : gap k j ∉ Icc (gap k l + 1) 3 := by
      simp only [Finset.mem_Icc, gap]
      omega
    rw [Finset.erase_eq_of_notMem hmem, hcard, if_neg h]
    omega

def upperSignExponent (k j l : ℤ) : ℤ :=
  j + k - l - if l < j then 1 else 0

theorem upperSignExponent_eq_crossed (k N j l : ℤ)
    (hj : 0 ≤ j) (hjk : j ≤ k) (hl : 0 ≤ l) (hlk : l ≤ k)
    (hd : 3 < destination j (gap k l)) :
    upperSignExponent k j l = j + ((crossed k N j (gap k l)).card : ℤ) := by
  rw [upper_crossed_card k N j l hj hjk hl hlk hd]
  unfold upperSignExponent
  omega

/-- The prefactor and row-sorting signs reverse under the upper-source swap. -/
theorem upper_sign_swap (k j l : ℤ) (hne : j ≠ l) :
    exponentSign (upperSignExponent k j l) =
      -exponentSign (upperSignExponent k l j) := by
  unfold exponentSign upperSignExponent
  split_ifs <;> omega

/-- All surviving upper sources, indexed by `(summand, source)`. -/
def upperPairs (k : ℤ) : Finset (ℤ × ℤ) :=
  ((Icc 0 k).product (Icc 0 k)).filter
    (fun p => p.1 ≠ p.2 ∧ 3 < destination p.1 (gap k p.2))

theorem mem_upperPairs (k : ℤ) (p : ℤ × ℤ) :
    p ∈ upperPairs k ↔
      (0 ≤ p.1 ∧ p.1 ≤ k) ∧ (0 ≤ p.2 ∧ p.2 ≤ k) ∧
      p.1 ≠ p.2 ∧ 3 < destination p.1 (gap k p.2) := by
  rcases p with ⟨j, l⟩
  simp only [upperPairs, Finset.mem_filter, Finset.product_eq_sprod, Finset.mem_product, Finset.mem_Icc]
  tauto

theorem swap_mem_upperPairs (k : ℤ) (p : ℤ × ℤ) (hp : p ∈ upperPairs k) :
    p.swap ∈ upperPairs k := by
  simp only [mem_upperPairs, Prod.fst_swap, Prod.snd_swap,
    destination, gap] at hp ⊢
  omega

theorem swap_ne_self (k : ℤ) (p : ℤ × ℤ) (hp : p ∈ upperPairs k) :
    p.swap ≠ p := by
  have hne := (mem_upperPairs k p).mp hp
  intro h
  have hfst := congrArg Prod.fst h
  simp only [Prod.fst_swap] at hfst
  exact hne.2.2.1 hfst.symm

/--
The upper sources cancel for every interpretation of an ordered exponent set
in an additive commutative group. In the determinant application `f` is the
alternant of the decreasing enumeration of this finite set.
-/
theorem upper_sum_eq_zero {A : Type*} [AddCommGroup A] (k N : ℤ)
    (f : Finset ℤ → A) :
    ∑ p ∈ upperPairs k,
      exponentSign (upperSignExponent k p.1 p.2) •
        f (raised k N p.1 (gap k p.2)) = 0 := by
  classical
  apply Finset.sum_involution (fun p _ => p.swap)
  · intro p hp
    have hr := (mem_upperPairs k p).mp hp
    dsimp only [Prod.fst_swap, Prod.snd_swap]
    rw [upper_raised_swap k N p.1 p.2 hr.1.1 hr.2.1.1,
      upper_sign_swap k p.1 p.2 hr.2.2.1]
    simp
  · intro p hp _
    exact swap_ne_self k p hp
  · intro p hp
    exact Prod.swap_swap p
  · intro p hp
    exact swap_mem_upperPairs k p hp

/-- The source that lands at the fixed gap `-k+d` in summand `j`. -/
def tailSource (k j d : ℤ) : ℤ := -k + d - j - 2

theorem tail_destination (k j d : ℤ) :
    destination j (tailSource k j d) = -k + d := by
  unfold destination tailSource
  omega

/-- The chosen padded alternant contains precisely the allowed tail sources. -/
theorem tailSource_mem_iff (k N j d : ℤ)
    (hj : 0 ≤ j) (hjk : j ≤ k) (hN : 2 * k + 3 ≤ N)
    (hd : 0 ≤ d) (hd2 : d ≤ 2) :
    tailSource k j d ∈ tail k N ↔ d - 1 ≤ j := by
  simp only [tail, tailSource, Finset.mem_Icc]
  omega

/-- Tail sources cannot land at the moving upper-block hole. -/
theorem tail_destination_ne_gap (k N j q : ℤ) (hq : q ∈ tail k N) :
    destination j q ≠ gap k j := by
  simp only [tail, Finset.mem_Icc] at hq
  unfold destination gap
  omega

/-- Every surviving tail source, and only such a source, lands at a fixed gap. -/
theorem tail_survives_iff (k N j q : ℤ)
    (hj : 0 ≤ j) (hjk : j ≤ k) (hq : q ∈ tail k N) :
    destination j q ∉ occupied k N j ↔
      ∃ d : ℤ, 0 ≤ d ∧ d ≤ 2 ∧ q = tailSource k j d := by
  simp only [tail, Finset.mem_Icc] at hq
  simp only [occupied, upper, tail, destination, gap, tailSource,
    Finset.mem_union, Finset.mem_erase, Finset.mem_Icc]
  constructor
  · intro h
    refine ⟨q + j + 2 + k, ?_, ?_, ?_⟩ <;> omega
  · rintro ⟨d, hd, hd2, hq'⟩
    omega

theorem tail_crossed_eq (k N j d : ℤ)
    (hj : 0 ≤ j) (hjk : j ≤ k) (hN : 2 * k + 3 ≤ N)
    (hd : 0 ≤ d) (hd2 : d ≤ 2) (hjd : d - 1 ≤ j) :
    crossed k N j (tailSource k j d) =
      Icc (tailSource k j d + 1) (-k - 1) := by
  ext x
  unfold crossed
  rw [Finset.mem_filter]
  simp only [occupied, upper, tail, destination, gap, tailSource,
    Finset.mem_filter, Finset.mem_union, Finset.mem_erase, Finset.mem_Icc]
  omega

/-- This counts exactly the crossed occupied tail exponents. -/
theorem tail_crossed_card (k N j d : ℤ)
    (hj : 0 ≤ j) (hjk : j ≤ k) (hN : 2 * k + 3 ≤ N)
    (hd : 0 ≤ d) (hd2 : d ≤ 2) (hjd : d - 1 ≤ j) :
    ((crossed k N j (tailSource k j d)).card : ℤ) = j + 1 - d := by
  rw [tail_crossed_eq k N j d hj hjk hN hd hd2 hjd,
    Int.card_Icc_of_le (a := tailSource k j d + 1) (b := -k - 1)
      (by unfold tailSource; omega)]
  unfold tailSource
  omega

/-- The summand prefactor times the sorting sign is independent of `j`. -/
theorem tail_sign (j d : ℤ) :
    exponentSign (j + (j + 1 - d)) = exponentSign (1 - d) := by
  unfold exponentSign
  split_ifs <;> omega

theorem tail_sign_zero (j : ℤ) : exponentSign (j + (j + 1 - 0)) = -1 := by
  rw [tail_sign]
  norm_num [exponentSign]

theorem tail_sign_one (j : ℤ) : exponentSign (j + (j + 1 - 1)) = 1 := by
  rw [tail_sign]
  norm_num [exponentSign]

theorem tail_sign_two (j : ℤ) : exponentSign (j + (j + 1 - 2)) = -1 := by
  rw [tail_sign]
  norm_num [exponentSign]

/--
The resulting padded row function: the old first `k` parts, the inserted
`d+1` part, and then the displaced tail rows, which acquire part one.
-/
def tailPart (k j d r : ℤ) : ℤ :=
  if r ≤ k - j then 4 else if r ≤ k then 3
  else if r = k + 1 then d + 1 else if r ≤ k + j + 2 - d then 1 else 0

def tailExponent (k j d r : ℤ) : ℤ := tailPart k j d r - r

theorem tailPart_nonneg (k j d r : ℤ) (hd : 0 ≤ d) :
    0 ≤ tailPart k j d r := by
  unfold tailPart
  split_ifs <;> omega

/-- The reconstructed exponent vector is already strictly decreasing. -/
theorem tailExponent_strict (k j d r s : ℤ)
    (hj : 0 ≤ j) (hd : 0 ≤ d) (hd2 : d ≤ 2) (hjd : d - 1 ≤ j)
    (hrs : r < s) :
    tailExponent k j d s < tailExponent k j d r := by
  unfold tailExponent tailPart
  split_ifs <;> omega

/--
The reconstructed row vector has exactly the raised exponent set. Together
with strict decrease this determines the sorted vector, not just its support.
-/
theorem tail_exponents_eq_raised (k N j d : ℤ)
    (hj : 0 ≤ j) (hjk : j ≤ k) (hN : 2 * k + 3 ≤ N)
    (hd : 0 ≤ d) (hd2 : d ≤ 2) (hjd : d - 1 ≤ j) :
    (Icc 1 N).image (tailExponent k j d) = raised k N j (tailSource k j d) := by
  ext x
  simp only [Finset.mem_image, Finset.mem_Icc]
  constructor
  · rintro ⟨r, hr, rfl⟩
    simp only [raised, occupied, upper, tail, destination, gap, tailSource,
      Finset.mem_insert, Finset.mem_union, Finset.mem_erase, Finset.mem_Icc,
      tailExponent, tailPart]
    split_ifs <;> omega
  · intro hx
    simp only [raised, occupied, upper, tail, destination, gap, tailSource,
      Finset.mem_insert, Finset.mem_union, Finset.mem_erase, Finset.mem_Icc] at hx
    rcases hx with hx | ⟨hne, hx | hx⟩
    · refine ⟨k + 1, by omega, ?_⟩
      simp only [tailExponent, tailPart]
      split_ifs <;> omega
    · by_cases h : 3 - k + j < x
      · refine ⟨4 - x, by omega, ?_⟩
        simp only [tailExponent, tailPart]
        split_ifs <;> omega
      · refine ⟨3 - x, by omega, ?_⟩
        simp only [tailExponent, tailPart]
        split_ifs <;> omega
    · by_cases h : -k + d - j - 2 < x
      · refine ⟨1 - x, by omega, ?_⟩
        simp only [tailExponent, tailPart]
        split_ifs <;> omega
      · refine ⟨-x, by omega, ?_⟩
        simp only [tailExponent, tailPart]
        split_ifs <;> omega

/-- The padded rows of `Q_j = (4^(k-j), 3^j, 1^(j+2))`. -/
def qPart (k j r : ℤ) : ℤ :=
  if r ≤ k - j then 4 else if r ≤ k then 3
  else if r ≤ k + j + 2 then 1 else 0

/-- The padded rows of `P_j = (4^(k-j), 3^j, 2, 1^j)`. -/
def pPart (k j r : ℤ) : ℤ :=
  if r ≤ k - j then 4 else if r ≤ k then 3
  else if r = k + 1 then 2 else if r ≤ k + j + 1 then 1 else 0

/-- The padded rows of `Z_i = (4^(k-i-1), 3^(i+2), 1^i)`. -/
def zPart (k i r : ℤ) : ℤ :=
  if r ≤ k - i - 1 then 4 else if r ≤ k + 1 then 3
  else if r ≤ k + i + 1 then 1 else 0

theorem tailPart_zero_eq_qPart (k j : ℤ) (hj : 0 ≤ j) :
    tailPart k j 0 = qPart k j := by
  funext r
  unfold tailPart qPart
  split_ifs <;> omega

theorem tailPart_one_eq_pPart (k j : ℤ) : tailPart k j 1 = pPart k j := by
  funext r
  unfold tailPart pPart
  split_ifs <;> omega

theorem tailPart_two_eq_zPart (k j : ℤ) (hj : 1 ≤ j) :
    tailPart k j 2 = zPart k (j - 1) := by
  funext r
  unfold tailPart zPart
  split_ifs <;> omega

/-- The exact index ranges in the manuscript's tail table, including all endpoints. -/
theorem allowed_tail_cases (j d : ℤ) (hj : 0 ≤ j) :
    (0 ≤ d ∧ d ≤ 2 ∧ d - 1 ≤ j) ↔
      d = 0 ∨ d = 1 ∨ (d = 2 ∧ 1 ≤ j) := by
  omega

end

end CoefficientOne.AlternantCancellation
