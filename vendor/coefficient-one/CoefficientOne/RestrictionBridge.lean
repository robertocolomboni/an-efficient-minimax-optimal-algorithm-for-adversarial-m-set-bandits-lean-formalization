import CoefficientOne.AlphabetDeterminants

/-!
# Restricting an alphabet versus replacing omitted letters by zero

This bridge identifies the original finite-law pair-complement alphabet with
the zero-padded alphabet used in the determinant identities. It follows the
actual finite-multiset elementary sums, with no positivity assumptions and no
exception at degree zero or at negative integer degrees.
-/

noncomputable section

namespace CoefficientOne.RestrictionBridge

open Finset EffectiveResistance ElementaryDeletion AlphabetDeterminants

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

omit [Fintype ι] in
/-- Zeroing a letter outside the chosen finite subalphabet is the same as
omitting it from every elementary symmetric function. -/
theorem esymm_zero_outside (a : ι → ℝ) (P : ι → Prop) [DecidablePred P]
    (s : Finset ι) (n : ℕ) :
    (s.val.map (fun i => if P i then a i else 0)).esymm n =
      ((s.filter P).val.map a).esymm n := by
  induction s using Finset.induction_on generalizing n with
  | empty => simp
  | @insert i s hi ih =>
    rw [Finset.insert_val_of_notMem hi, Multiset.map_cons]
    by_cases hPi : P i
    · have hif : i ∉ s.filter P := fun h => hi (Finset.mem_filter.mp h).1
      rw [if_pos hPi, Finset.filter_insert, if_pos hPi,
        Finset.insert_val_of_notMem hif, Multiset.map_cons]
      cases n with
      | zero => simp [Multiset.esymm]
      | succ n => rw [multiset_esymm_cons_succ, multiset_esymm_cons_succ, ih, ih]
    · rw [if_neg hPi, multiset_esymm_cons_zero, Finset.filter_insert, if_neg hPi]
      exact ih n

/-- The actual subtype alphabet enumerates the same multiset of letters as
the ambient alphabet filtered by its defining predicate. -/
theorem elementarySum_subtype (a : ι → ℝ) (P : ι → Prop) [DecidablePred P]
    (n : ℕ) : elementarySum (fun i : {i // P i} => a i.val) n =
      (((univ : Finset ι).filter P).val.map a).esymm n := by
  rw [elementarySum_eq_multiset]
  have hs : (univ : Finset {i // P i}).map (Function.Embedding.subtype P) =
      (univ : Finset ι).filter P := by
    ext i
    simp
  rw [← hs, Finset.map_val, Multiset.map_map]
  rfl

/-- General restriction/zero-padding identity for the original elementary sums. -/
theorem elementarySum_subtype_eq_zero_outside (a : ι → ℝ)
    (P : ι → Prop) [DecidablePred P] (n : ℕ) :
    elementarySum (fun i : {i // P i} => a i.val) n =
      elementarySum (fun i => if P i then a i else 0) n := by
  rw [elementarySum_subtype, elementarySum_eq_multiset, esymm_zero_outside]

theorem elementaryInt_subtype_eq_zero_outside (a : ι → ℝ)
    (P : ι → Prop) [DecidablePred P] (d : ℤ) :
    elementaryInt (fun i : {i // P i} => a i.val) d =
      elementaryInt (fun i => if P i then a i else 0) d := by
  unfold elementaryInt
  split_ifs
  · exact elementarySum_subtype_eq_zero_outside a P d.toNat
  · rfl

omit [Fintype ι] in
theorem zeroPair_eq_zero_outside (a : ι → ℝ) (i l : ι) :
    zeroPair a i l = fun j => if j ≠ i ∧ j ≠ l then a j else 0 := by
  funext j
  by_cases hji : j = i <;> by_cases hjl : j = l <;>
    simp_all [zeroPair, zeroLetter, Function.update]

/-- Exact bridge used by the kernel matrix: valid even if the two indices agree. -/
theorem elementaryInt_pairRestricted_eq_zeroPair (a : ι → ℝ) (i l : ι) (d : ℤ) :
    elementaryInt (pairRestrictedWeight a i l) d = elementaryInt (zeroPair a i l) d := by
  rw [zeroPair_eq_zero_outside]
  exact elementaryInt_subtype_eq_zero_outside a (fun j => j ≠ i ∧ j ≠ l) d

theorem elementarySum_pairRestricted_eq_zeroPair (a : ι → ℝ) (i l : ι) (n : ℕ) :
    elementarySum (pairRestrictedWeight a i l) n = elementarySum (zeroPair a i l) n := by
  rw [zeroPair_eq_zero_outside]
  exact elementarySum_subtype_eq_zero_outside a (fun j => j ≠ i ∧ j ≠ l) n

/-- Consequently the two-square kernel is identical in the two representations. -/
theorem kernelK_pairRestricted_eq_zeroPair (a : ι → ℝ) (i l : ι) (d : ℤ) :
    kernelK (pairRestrictedWeight a i l) d = kernelK (zeroPair a i l) d := by
  simp only [kernelK, elementaryInt_pairRestricted_eq_zeroPair]

/-- One-letter version, useful for the diagonal and load of the certificate. -/
theorem elementaryInt_subtype_ne_eq_zeroLetter (a : ι → ℝ) (i : ι) (d : ℤ) :
    elementaryInt (fun j : {j // j ≠ i} => a j.val) d = elementaryInt (zeroLetter a i) d := by
  have heq : zeroLetter a i = fun j => if j ≠ i then a j else 0 := by
    funext j
    by_cases h : j = i <;> simp_all [zeroLetter, Function.update]
  rw [heq]
  exact elementaryInt_subtype_eq_zero_outside a (fun j => j ≠ i) d

end CoefficientOne.RestrictionBridge