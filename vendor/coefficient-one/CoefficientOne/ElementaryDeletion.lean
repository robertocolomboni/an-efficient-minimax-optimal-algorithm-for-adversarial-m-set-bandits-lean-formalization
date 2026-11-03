import CoefficientOne.ElementaryBridge
import CoefficientOne.CovarianceBridge
import CoefficientOne.DeterminantIdentities
import CoefficientOne.RectangleContinuity

/-!
# Actual one- and two-letter elementary identities

The recurrence is proved from the finite-subset definition of e_n. The standard
powerset-cardinality recurrence separates subsets containing the added letter
from those avoiding it. The integer-index convention includes zero and negative
indices explicitly. We then identify the covariance kernel K with its concrete
two-square determinant and with the width-two tableau Schur value.
-/

noncomputable section

namespace CoefficientOne.ElementaryDeletion

open Finset EffectiveResistance RectangleDeterminants

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

theorem multiset_esymm_cons_succ {R : Type*} [CommSemiring R]
    (s : Multiset R) (x : R) (n : ℕ) :
    (x ::ₘ s).esymm (n + 1) = s.esymm (n + 1) + x * s.esymm n := by
  simp [Multiset.esymm, Multiset.powersetCard_cons, Multiset.map_map,
    Function.comp_def, Multiset.sum_map_mul_left]

theorem multiset_esymm_cons_zero {R : Type*} [CommSemiring R]
    (s : Multiset R) (n : ℕ) : (0 ::ₘ s).esymm n = s.esymm n := by
  cases n with
  | zero => simp [Multiset.esymm]
  | succ n => rw [multiset_esymm_cons_succ]; simp

theorem elementarySum_eq_multiset (a : ι → ℝ) (n : ℕ) :
    elementarySum a n = ((Finset.univ : Finset ι).val.map a).esymm n := by
  rw [elementarySum_eq_powersetCard, Finset.esymm_map_val]

theorem elementarySum_eq_cons (a : ι → ℝ) (i : ι) (n : ℕ) :
    elementarySum a n =
      (a i ::ₘ (((Finset.univ : Finset ι).erase i).val.map a)).esymm n := by
  rw [elementarySum_eq_multiset]
  have hv : (Finset.univ : Finset ι).val =
      i ::ₘ ((Finset.univ : Finset ι).erase i).val := by
    simpa only [Finset.erase_val] using
      (Multiset.cons_erase (show i ∈ (Finset.univ : Finset ι).val from Finset.mem_univ i)).symm
  rw [hv, Multiset.map_cons]

theorem elementarySum_update_zero_eq (a : ι → ℝ) (i : ι) (n : ℕ) :
    elementarySum (Function.update a i 0) n =
      (((Finset.univ : Finset ι).erase i).val.map a).esymm n := by
  rw [elementarySum_eq_cons]
  have hmap : (((Finset.univ : Finset ι).erase i).val.map (Function.update a i 0)) =
      (((Finset.univ : Finset ι).erase i).val.map a) := by
    apply Multiset.map_congr rfl
    intro j hj
    have hji : j ≠ i := (Finset.mem_erase.mp hj).1
    simp [Function.update, hji]
  rw [hmap]
  simp [multiset_esymm_cons_zero]

theorem elementarySum_one_deletion_succ (a : ι → ℝ) (i : ι) (n : ℕ) :
    elementarySum a (n + 1) = elementarySum (Function.update a i 0) (n + 1) +
      a i * elementarySum (Function.update a i 0) n := by
  rw [elementarySum_eq_cons a i, elementarySum_update_zero_eq,
    elementarySum_update_zero_eq, multiset_esymm_cons_succ]

/-- One-letter deletion at every integer degree. -/
theorem elementaryInt_one_deletion (a : ι → ℝ) (i : ι) (d : ℤ) :
    elementaryInt a d = elementaryInt (Function.update a i 0) d +
      a i * elementaryInt (Function.update a i 0) (d - 1) := by
  by_cases hd : d < 0
  · rw [elementaryInt_of_neg _ _ hd, elementaryInt_of_neg _ _ hd,
      elementaryInt_of_neg _ _ (by omega)]
    ring
  by_cases hd0 : d = 0
  · subst d
    rw [elementaryInt_zero, elementaryInt_zero,
      elementaryInt_of_neg _ _ (by omega)]
    ring
  obtain ⟨n, hn⟩ := Int.eq_ofNat_of_zero_le (show 0 ≤ d by omega)
  have hnpos : 0 < n := by omega
  obtain ⟨r, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.ne_of_gt hnpos)
  subst d
  have hm : ((r + 1 : ℕ) : ℤ) - 1 = r := by omega
  rw [hm, elementaryInt_nat, elementaryInt_nat, elementaryInt_nat]
  exact elementarySum_one_deletion_succ a i r

/-- Two-letter deletion, derived by applying the actual one-letter identity twice. -/
theorem elementaryInt_two_deletions (a : ι → ℝ) (i l : ι) (hil : i ≠ l) (d : ℤ) :
    elementaryInt a d =
      elementaryInt (Function.update (Function.update a i 0) l 0) d +
        (a i + a l) * elementaryInt (Function.update (Function.update a i 0) l 0) (d - 1) +
        a i * a l * elementaryInt (Function.update (Function.update a i 0) l 0) (d - 2) := by
  rw [elementaryInt_one_deletion a i d,
    elementaryInt_one_deletion (Function.update a i 0) l d,
    elementaryInt_one_deletion (Function.update a i 0) l (d - 1)]
  have hl : Function.update a i 0 l = a l := by simp [Function.update, Ne.symm hil]
  rw [hl, show d - 1 - 1 = d - 2 by ring]
  ring

theorem kernelK_eq_rectangleTwo (a : ι → ℝ) (d : ℤ) :
    kernelK a d = rectangleTwo (elementaryInt a (d - 1))
      (elementaryInt a d) (elementaryInt a (d + 1)) := rfl

theorem kernelK_eq_detTwo (a : ι → ℝ) (d : ℤ) :
    kernelK a d = detTwo (elementaryInt a d) (elementaryInt a (d + 1))
      (elementaryInt a (d - 1)) (elementaryInt a d) := by
  unfold kernelK detTwo
  ring

theorem kernelK_eq_elementaryDet {N : ℕ} (a : Fin N → ℝ) (k : ℕ) :
    kernelK a k = elementaryDet a 2 k := by
  simp only [kernelK, elementaryDet, Matrix.det_fin_two, toeplitz,
    Fin.val_zero, Fin.val_one, Nat.cast_zero, Nat.cast_one, sub_zero, add_zero,
    sub_add_cancel]
  ring

theorem kernelK_eq_rectangleSchur {N : ℕ} (a : Fin N → ℝ) (ha : ∀ i, 0 ≤ a i)
    (k : ℕ) (hk : k ≤ N) : kernelK a k = rectangleSchur a 2 k := by
  rw [kernelK_eq_elementaryDet,
    RectangleContinuity.rectangleSchur_eq_elementaryDet_of_nonneg a ha 2 k hk]

theorem kernelK_nonneg {N : ℕ} (a : Fin N → ℝ) (ha : ∀ i, 0 ≤ a i)
    (k : ℕ) (hk : k ≤ N) : 0 ≤ kernelK a k := by
  rw [kernelK_eq_rectangleSchur a ha k hk]
  exact schurValue_nonneg _ a ha

end CoefficientOne.ElementaryDeletion
