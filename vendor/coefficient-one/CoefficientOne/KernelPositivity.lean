import CoefficientOne.RestrictionBridge
import CoefficientOne.MatrixCertificate

/-!
# Positivity and symmetry of the actual kernel matrix

The two-square kernel is positive because it is the Schur function of a
two-column rectangle on the actual remaining alphabet. Equivalences of
finite alphabets preserve their multisets of letters, so no coordinate
restriction or positivity claim is assumed in passing to Fin indexing.
-/

noncomputable section

namespace CoefficientOne

open Matrix Finset EffectiveResistance ElementaryDeletion RectangleDeterminants

variable {ι κ : Type*} [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ]

theorem elementarySum_comp_equiv (a : κ → ℝ) (e : ι ≃ κ) (k : ℕ) :
    elementarySum (a ∘ e) k = elementarySum a k := by
  rw [elementarySum_eq_multiset, elementarySum_eq_multiset]
  have hset : (Finset.univ : Finset ι).map e.toEmbedding = Finset.univ := by
    ext i
    simp
  rw [← hset, Finset.map_val, Multiset.map_map]
  rfl

theorem elementaryInt_comp_equiv (a : κ → ℝ) (e : ι ≃ κ) (d : ℤ) :
    elementaryInt (a ∘ e) d = elementaryInt a d := by
  unfold elementaryInt
  split_ifs
  · exact elementarySum_comp_equiv a e d.toNat
  · rfl

theorem kernelK_comp_equiv (a : κ → ℝ) (e : ι ≃ κ) (d : ℤ) :
    kernelK (a ∘ e) d = kernelK a d := by
  simp only [kernelK, elementaryInt_comp_equiv]

theorem kernelK_pos (a : ι → ℝ) (ha : ∀ i, 0 < a i) (k : ℕ)
    (hk : k ≤ Fintype.card ι) : 0 < kernelK a k := by
  let e := Fintype.equivFin ι
  rw [← kernelK_comp_equiv a e.symm]
  have haFin : ∀ j : Fin (Fintype.card ι), 0 < (a ∘ e.symm) j := fun j => ha _
  rw [kernelK_eq_rectangleSchur (a ∘ e.symm) (fun j => (haFin j).le) k hk]
  exact rectangleSchur_pos (a ∘ e.symm) haFin 2 k

theorem kernelMatrix_offDiagonal_pos (a : ι → ℝ) (ha : ∀ i, 0 < a i)
    (k : ℕ) (hk : k ≤ Fintype.card ι - 2) (i j : ι) (hij : i ≠ j) :
    0 < kernelMatrix a k i j := by
  have hkp : k ≤ Fintype.card (PairComplement i j) := by
    rwa [card_pairComplement i j hij]
  simpa only [kernelMatrix, if_neg hij] using
    kernelK_pos (pairRestrictedWeight a i j) (fun l => ha l.val) k hkp

theorem kernelMatrix_nonneg (a : ι → ℝ) (ha : ∀ i, 0 < a i)
    (k : ℕ) (hk : k ≤ Fintype.card ι - 2) (i j : ι) :
    0 ≤ kernelMatrix a k i j := by
  by_cases hij : i = j
  · simp [kernelMatrix, hij]
  · exact (kernelMatrix_offDiagonal_pos a ha k hk i j hij).le

theorem kernelMatrix_isSymm (a : ι → ℝ) (d : ℤ) : (kernelMatrix a d).IsSymm := by
  ext i j
  change kernelMatrix a d j i = kernelMatrix a d i j
  by_cases hij : i = j
  · subst j
    rfl
  · simp only [kernelMatrix, if_neg hij, if_neg (Ne.symm hij),
      RestrictionBridge.kernelK_pairRestricted_eq_zeroPair,
      AlphabetDeterminants.zeroPair_comm a j i (Ne.symm hij)]

theorem kernelMatrix_positive_direction (a : ι → ℝ) (ha : ∀ i, 0 < a i)
    (k : ℕ) (hk : k ≤ Fintype.card ι - 2) (hcard : 2 ≤ Fintype.card ι) :
    0 < (fun _ => (1 : ℝ)) ⬝ᵥ (kernelMatrix a k *ᵥ (fun _ => 1)) := by
  haveI : Nonempty ι := Fintype.card_pos_iff.mp (by omega)
  simp only [dotProduct, Matrix.mulVec, one_mul, mul_one]
  apply Finset.sum_pos _ Finset.univ_nonempty
  intro i _
  obtain ⟨j, hji⟩ := Fintype.exists_ne_of_one_lt_card (by omega) i
  exact Finset.sum_pos' (fun l _ => kernelMatrix_nonneg a ha k hk i l)
    ⟨j, Finset.mem_univ _, kernelMatrix_offDiagonal_pos a ha k hk i j (Ne.symm hji)⟩

/-- The remaining input for exact inertia is precisely the certificate's
negative hyperplane; the positive direction is supplied by actual Schur positivity. -/
theorem kernelMatrix_inertia_of_negative_hyperplane
    (a : ι → ℝ) (ha : ∀ i, 0 < a i) (k : ℕ)
    (hk : k ≤ Fintype.card ι - 2) (hcard : 2 ≤ Fintype.card ι) (b : ι → ℝ)
    (hneg : ∀ z : ι → ℝ, z ≠ 0 → b ⬝ᵥ z = 0 → z ⬝ᵥ (kernelMatrix a k *ᵥ z) < 0) :
    ∃ i, 0 < (Matrix.isHermitian_iff_isSymm.mpr (kernelMatrix_isSymm a k)).eigenvalues i ∧
      ∀ j, j ≠ i →
        (Matrix.isHermitian_iff_isSymm.mpr (kernelMatrix_isSymm a k)).eigenvalues j < 0 := by
  exact unique_positive_eigenvalue_of_negative_hyperplane (kernelMatrix a k)
    (Matrix.isHermitian_iff_isSymm.mpr (kernelMatrix_isSymm a k)) b (fun _ => 1)
    hneg (kernelMatrix_positive_direction a ha k hk hcard)

end CoefficientOne
