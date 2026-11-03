import CoefficientOne.RectangleDeterminants

/-!
# Deleting one letter from a complete symmetric function

We prove the elementary generating-function recurrence directly from the
definition of h_n as the sum of monomials indexed by multisets of size n.
Multisets containing a fixed letter are in explicit bijection with multisets
of size n-1; setting that letter to zero removes precisely those summands.
No generating-function or deletion identity is assumed.
-/

noncomputable section

namespace CoefficientOne.CompleteDeletion

open Finset MvPolynomial

variable {ι R : Type*} [Fintype ι] [DecidableEq ι] [CommRing R]

def symWeight (a : ι → R) {n : ℕ} (s : Sym ι n) : R := (s.val.map a).prod

theorem eval_hsymm_eq_sum (a : ι → R) (n : ℕ) :
    MvPolynomial.eval a (MvPolynomial.hsymm ι R n) = ∑ s : Sym ι n, symWeight a s := by
  simp [MvPolynomial.hsymm, symWeight, map_multiset_prod, Multiset.map_map,
    Function.comp_def]

theorem symWeight_cons (a : ι → R) (i : ι) {n : ℕ} (s : Sym ι n) :
    symWeight a (i ::ₛ s) = a i * symWeight a s := by
  simp [symWeight, Sym.coe_cons]

theorem symWeight_update_of_mem (a : ι → R) (i : ι) {n : ℕ} (s : Sym ι n)
    (hi : i ∈ s) : symWeight (Function.update a i 0) s = 0 := by
  apply Multiset.prod_eq_zero
  apply Multiset.mem_map.mpr
  exact ⟨i, hi, by simp⟩

theorem symWeight_update_of_notMem (a : ι → R) (i : ι) {n : ℕ} (s : Sym ι n)
    (hi : i ∉ s) : symWeight (Function.update a i 0) s = symWeight a s := by
  apply congrArg Multiset.prod
  apply Multiset.map_congr rfl
  intro j hj
  have hji : j ≠ i := by rintro rfl; exact hi hj
  simp [Function.update, hji]

/-- Add one copy of i, with erase as its inverse. Repeated copies of i cause
no multiplicity factor, since h_n indexes multisets rather than sequences. -/
def consContainingEquiv (i : ι) (n : ℕ) :
    Sym ι n ≃ {s : Sym ι (n + 1) // i ∈ s} where
  toFun s := ⟨i ::ₛ s, Sym.mem_cons_self i s⟩
  invFun s := s.1.erase i s.2
  left_inv s := by simp
  right_inv s := by
    apply Subtype.ext
    exact Sym.cons_erase s.2

theorem sum_containing (a : ι → R) (i : ι) (n : ℕ) :
    (∑ s : {s : Sym ι (n + 1) // i ∈ s}, symWeight a s.1) =
      a i * ∑ s : Sym ι n, symWeight a s := by
  rw [Finset.mul_sum]
  symm
  apply Fintype.sum_equiv (consContainingEquiv i n)
  intro s
  exact (symWeight_cons a i s).symm

theorem eval_hsymm_update_zero_succ (a : ι → R) (i : ι) (n : ℕ) :
    MvPolynomial.eval (Function.update a i 0) (MvPolynomial.hsymm ι R (n + 1)) =
      MvPolynomial.eval a (MvPolynomial.hsymm ι R (n + 1)) -
        a i * MvPolynomial.eval a (MvPolynomial.hsymm ι R n) := by
  simp only [eval_hsymm_eq_sum]
  have hu := Fintype.sum_subtype_add_sum_subtype
    (fun s : Sym ι (n + 1) => i ∈ s) (symWeight (Function.update a i 0))
  have ha := Fintype.sum_subtype_add_sum_subtype
    (fun s : Sym ι (n + 1) => i ∈ s) (symWeight a)
  have hz : (∑ s : {s : Sym ι (n + 1) // i ∈ s},
      symWeight (Function.update a i 0) s.1) = 0 := by
    apply Finset.sum_eq_zero
    intro s _
    exact symWeight_update_of_mem a i s.1 s.2
  have he : (∑ s : {s : Sym ι (n + 1) // i ∉ s},
      symWeight (Function.update a i 0) s.1) =
      ∑ s : {s : Sym ι (n + 1) // i ∉ s}, symWeight a s.1 := by
    apply Finset.sum_congr rfl
    intro s _
    exact symWeight_update_of_notMem a i s.1 s.2
  rw [hz, zero_add, he] at hu
  rw [sum_containing a i n] at ha
  rw [← hu, ← ha]
  ring

/-- The complete-symmetric deletion identity, with all integer boundary cases.
Putting a letter to zero retains the alphabet indexing for later matrix steps. -/
theorem completeInt_update_zero {N : ℕ} (a : Fin N → ℝ) (i : Fin N) (d : ℤ) :
    RectangleDeterminants.completeInt (Function.update a i 0) d =
      RectangleDeterminants.completeInt a d -
        a i * RectangleDeterminants.completeInt a (d - 1) := by
  by_cases hd : d < 0
  · rw [RectangleDeterminants.completeInt_of_neg _ _ hd,
      RectangleDeterminants.completeInt_of_neg _ _ hd,
      RectangleDeterminants.completeInt_of_neg _ _ (by omega)]
    ring
  by_cases hd0 : d = 0
  · subst d
    rw [RectangleDeterminants.completeInt_zero,
      RectangleDeterminants.completeInt_zero,
      RectangleDeterminants.completeInt_of_neg _ _ (by omega)]
    ring
  have hdpos : 0 < d := by omega
  obtain ⟨n, hn⟩ := Int.eq_ofNat_of_zero_le (le_of_lt hdpos)
  have hnpos : 0 < n := by omega
  obtain ⟨r, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.ne_of_gt hnpos)
  subst d
  have hr0 : (0 : ℤ) ≤ (r : ℤ) + 1 := by omega
  simpa [RectangleDeterminants.completeInt, SymmetricFunctions.hsymmExt, hr0] using
    eval_hsymm_update_zero_succ a i r

end CoefficientOne.CompleteDeletion
