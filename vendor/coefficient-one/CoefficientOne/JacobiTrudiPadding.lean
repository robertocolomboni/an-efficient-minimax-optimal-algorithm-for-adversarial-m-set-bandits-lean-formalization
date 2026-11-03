import CoefficientOne.JacobiTrudi

/-!
# Removing padded rows from ordinary Jacobi–Trudi

This is a direct last-row expansion. A zero part in the final row gives zero
entries before the diagonal, whose entry is one. Thus zero parts can be removed
without changing either the determinant or the alphabet. Ordinary Jacobi–Trudi
is the identity cited as Macdonald, Chapter I, (3.4), p. 41 in the manuscript.
-/

noncomputable section

namespace CoefficientOne.JacobiTrudiPadding

open Finset Matrix

variable {R : Type*} [CommRing R] {N : ℕ}

def rowIndexMatrix (f : ℤ → R) (lam : ℕ → ℤ) (n : ℕ) :
    Matrix (Fin n) (Fin n) R :=
  fun i j => f (lam i.val - (i.val : ℤ) + (j.val : ℤ))

theorem rowIndexMatrix_det_succ (f : ℤ → R) (hf0 : f 0 = 1)
    (hfneg : ∀ z < 0, f z = 0) (lam : ℕ → ℤ) (n : ℕ) (hlam : lam n = 0) :
    (rowIndexMatrix f lam (n + 1)).det = (rowIndexMatrix f lam n).det := by
  rw [Matrix.det_succ_row _ (Fin.last n), Finset.sum_eq_single (Fin.last n)]
  · have hsub : (rowIndexMatrix f lam (n + 1)).submatrix
        (Fin.last n).succAbove (Fin.last n).succAbove = rowIndexMatrix f lam n := by
      ext i j
      simp only [rowIndexMatrix, submatrix_apply, Fin.succAbove_last, Fin.val_castSucc]
    have hpow : (-1 : R) ^ (n + n) = 1 := by
      rw [← two_mul, pow_mul]
      simp
    simp only [Fin.val_last, rowIndexMatrix, hlam,
      zero_sub, neg_add_cancel, hf0, hpow, one_mul, hsub]
  · intro j _ hj
    have hjn : j.val < n := by
      have hne : j.val ≠ n := fun h => hj (Fin.ext h)
      omega
    have hz : (0 : ℤ) - n + j.val < 0 := by omega
    simp only [rowIndexMatrix, Fin.val_last, hlam, hfneg _ hz, mul_zero, zero_mul]
  · simp

theorem rowIndexMatrix_det_truncate (f : ℤ → R) (hf0 : f 0 = 1)
    (hfneg : ∀ z < 0, f z = 0) (lam : ℕ → ℤ) (k n : ℕ) (hkn : k ≤ n)
    (hzero : ∀ i, k ≤ i → i < n → lam i = 0) :
    (rowIndexMatrix f lam n).det = (rowIndexMatrix f lam k).det := by
  obtain ⟨t, rfl⟩ := Nat.exists_eq_add_of_le hkn
  induction t with
  | zero => rfl
  | succ t ih =>
      rw [show k + (t + 1) = k + t + 1 by omega,
        rowIndexMatrix_det_succ f hf0 hfneg lam (k + t) (hzero _ (by omega) (by omega))]
      exact ih (by omega) (fun i hik hin => hzero i hik (by omega))

/-- Extend a finite partition by zero, without changing any part in its domain. -/
def extendParts (lam : Fin N → ℕ) (i : ℕ) : ℤ :=
  if hi : i < N then lam ⟨i, hi⟩ else 0

theorem extendParts_apply (lam : Fin N → ℕ) (i : Fin N) :
    extendParts lam i.val = lam i := by
  simp [extendParts, i.isLt]

/-- Jacobi–Trudi with determinant size k when all parts after k are zero.
This theorem changes the determinant size only; it does not specialize letters. -/
theorem schurValue_eq_det_of_zero_tail (a : Fin N → ℝ) (lam : Fin N → ℕ)
    (hlam : AlgebraicCombinatorics.IsNPartition lam) (k : ℕ) (hk : k ≤ N)
    (htail : ∀ i : Fin N, k ≤ i.val → lam i = 0) :
    schurValue lam a = Matrix.det (fun i j : Fin k => MvPolynomial.eval a
      (SymmetricFunctions.hsymmExt (R := ℝ)
        ((lam (Fin.castLE hk i) : ℤ) - (i.val : ℤ) + (j.val : ℤ)))) := by
  let f : ℤ → ℝ := fun j => MvPolynomial.eval a (SymmetricFunctions.hsymmExt (R := ℝ) j)
  have hf0 : f 0 = 1 := by simp [f, SymmetricFunctions.hsymmExt]
  have hfneg : ∀ z < 0, f z = 0 := by
    intro z hz
    simp [f, SymmetricFunctions.hsymmExt, not_le.mpr hz]
  have ht : ∀ i, k ≤ i → i < N → extendParts lam i = 0 := by
    intro i hik hiN
    rw [extendParts, dif_pos hiN, htail ⟨i, hiN⟩ hik]
    rfl
  have htop : (fun i j : Fin N => MvPolynomial.eval a
      (SymmetricFunctions.hsymmExt (R := ℝ)
        ((lam i : ℤ) - (i.val : ℤ) + (j.val : ℤ)))) =
      rowIndexMatrix f (extendParts lam) N := by
    ext i j
    simp only [rowIndexMatrix, extendParts_apply, f]
  have hsmall : rowIndexMatrix f (extendParts lam) k =
      (fun i j : Fin k => MvPolynomial.eval a
        (SymmetricFunctions.hsymmExt (R := ℝ)
          ((lam (Fin.castLE hk i) : ℤ) - (i.val : ℤ) + (j.val : ℤ)))) := by
    ext i j
    have he := extendParts_apply lam (Fin.castLE hk i)
    change extendParts lam i.val = (lam (Fin.castLE hk i) : ℤ) at he
    simp only [rowIndexMatrix, he, f]
  rw [JacobiTrudi.schurValue_eq_det lam hlam a, htop,
    rowIndexMatrix_det_truncate f hf0 hfneg _ k N hk ht, hsmall]

end CoefficientOne.JacobiTrudiPadding
