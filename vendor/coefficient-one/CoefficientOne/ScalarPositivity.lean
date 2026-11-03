import CoefficientOne.ScalarCoefficients

/-!
# Positivity and the distinguished Schur lower bound

The distinguished partition keeps every row, so the arbitrary-alphabet
statements use the proved zero-padding convention of `SchurStability`.
-/

noncomputable section

namespace CoefficientOne.ScalarPositivity

open Finset ScalarExpansion ScalarPieriShapes ScalarReciprocity SchurStability

variable {N M : ℕ}

theorem distinguished_shape_eq (k : ℕ) :
    (fun i : Fin N => distinguishedPartition k i.val) = targetShape k 0 0 0 2 := by
  funext i
  unfold distinguishedPartition targetShape targetPart SignedLoad.rowIndex
  split_ifs <;> omega

theorem distinguished_mem_targets (k : ℕ) (hN : k + 2 ≤ N) :
    targetShape (N := N) k 0 0 0 2 ∈ targets (5 * (k : ℤ) + 2) := by
  apply (mem_targets _ _).mpr
  refine ⟨?_, targetShape_isPartition _ _ _ _ _ (by omega) (by omega) (by omega) (by omega), ?_⟩
  · intro i
    unfold targetShape targetPart
    split_ifs <;> omega
  · rw [targetShape_degree k 0 0 0 2 (by omega) (by omega) (by omega)
      (by omega) (by omega) (by omega)]
    ring

theorem globalDistinguished_eq_target (a : Fin N → ℝ) (k : ℕ) (hN : k + 2 ≤ N) :
    globalSchurValue (distinguishedPartition k) a = schurValue (targetShape k 0 0 0 2) a := by
  rw [globalSchurValue_eq_of_fits _ _ (by
    intro r hr
    unfold distinguishedPartition
    split_ifs <;> omega), distinguished_shape_eq]


/-- Regard a finite padded shape as its complete sequence of row lengths. -/
def completedShape (mu : Fin M → ℕ) (r : ℕ) : ℕ :=
  if hr : r < M then mu ⟨r, hr⟩ else 0

theorem completedShape_antitone (mu : Fin M → ℕ)
    (hmu : AlgebraicCombinatorics.IsNPartition mu) : Antitone (completedShape mu) := by
  intro r s hrs
  unfold completedShape
  split_ifs with hs hr hr
  · exact hmu _ _ hrs
  · omega
  · omega
  · exact le_rfl

theorem globalCompleted_eq_padded (h : N ≤ M) (a : Fin N → ℝ) (mu : Fin M → ℕ)
    (hmu : AlgebraicCombinatorics.IsNPartition mu) :
    globalSchurValue (completedShape mu) a = schurValue mu (paddedAlphabet a) := by
  have heq : (fun i : Fin M => completedShape mu i.val) = mu := by
    funext i
    simp only [completedShape, dif_pos i.isLt]
  have hh := schurValue_padded_eq_global h a (completedShape mu)
    (completedShape_antitone mu hmu) (by
      intro r hr
      simp only [completedShape, dif_neg (show ¬r < M by omega)])
  rw [heq] at hh
  exact hh.symm

/-- The complete scalar expansion on every nonnegative finite alphabet.
M is only a chosen finite realization of the full partitions; overlong
partitions specialize to zero by the proved tableau specialization theorem. -/
theorem scalarB_global_expansion (M : ℕ) (h : N ≤ M) (a : Fin N → ℝ)
    (ha : ∀ i, 0 ≤ a i) (k : ℕ) (hM : 2 * (k : ℤ) + 3 ≤ M) :
    scalarB a k = ∑ nu ∈ targets (N := M) (5 * (k : ℤ) + 2),
      (rawCoefficient k nu : ℝ) * globalSchurValue (completedShape nu) a := by
  have hb := scalarB_eq_raw_sum (paddedAlphabet (M := M) a)
    (paddedAlphabet_nonneg a ha) k hM
  rw [ScalarPadding.scalarB_padded h a k] at hb
  rw [hb]
  apply Finset.sum_congr rfl
  intro nu hnu
  rw [globalCompleted_eq_padded h a nu ((mem_targets _ nu).mp hnu).2.1]



/-- On a sufficiently large alphabet, retain the actual coefficient-one term. -/
theorem scalarB_ge_distinguished_large (a : Fin N → ℝ) (ha : ∀ i, 0 ≤ a i)
    (k : ℕ) (hN : 2 * (k : ℤ) + 3 ≤ N) :
    globalSchurValue (distinguishedPartition k) a ≤ scalarB a k := by
  rw [globalDistinguished_eq_target a k (by omega), scalarB_eq_raw_sum a ha k hN]
  calc
    schurValue (targetShape k 0 0 0 2) a =
        (rawCoefficient k (targetShape k 0 0 0 2) : ℝ) *
          schurValue (targetShape k 0 0 0 2) a := by
      rw [ScalarCoefficients.rawCoefficient_distinguished k hN]
      norm_num
    _ ≤ _ := by
      apply Finset.single_le_sum (s := targets (5 * (k : ℤ) + 2))
        (f := fun nu : Fin N → ℕ => (rawCoefficient k nu : ℝ) * schurValue nu a)
        (a := targetShape k 0 0 0 2)
      · intro nu hnu
        apply mul_nonneg
        · exact_mod_cast ScalarCoefficients.rawCoefficient_nonneg k hN nu hnu
        · exact schurValue_nonneg nu a ha
      · exact distinguished_mem_targets k (by omega)

/-- The coefficient-one Schur lower bound on every finite nonnegative alphabet.
This includes empty alphabets and all overlong distinguished partitions. -/
theorem scalarB_ge_distinguished (a : Fin N → ℝ) (ha : ∀ i, 0 ≤ a i) (k : ℕ) :
    globalSchurValue (distinguishedPartition k) a ≤ scalarB a k := by
  let M := N + 2 * k + 3
  have hNM : N ≤ M := by omega
  have hM : 2 * (k : ℤ) + 3 ≤ (M : ℤ) := by dsimp [M]; omega
  have hh := scalarB_ge_distinguished_large (paddedAlphabet (M := M) a)
    (paddedAlphabet_nonneg a ha) k hM
  rw [ScalarPadding.scalarB_padded hNM a k,
    globalSchurValue_padded hNM a _ (distinguishedPartition_antitone k)] at hh
  exact hh

theorem scalarB_nonneg (a : Fin N → ℝ) (ha : ∀ i, 0 ≤ a i) (k : ℕ) :
    0 ≤ scalarB a k :=
  (globalSchurValue_nonneg (distinguishedPartition k) a ha).trans
    (scalarB_ge_distinguished a ha k)

theorem scalarB_pos_of_fits (a : Fin N → ℝ) (ha : ∀ i, 0 < a i)
    (k : ℕ) (hN : k + 2 ≤ N) : 0 < scalarB a k := by
  have hpos : 0 < globalSchurValue (distinguishedPartition k) a := by
    apply globalSchurValue_pos_of_fits _ a ha
    intro r hr
    unfold distinguishedPartition
    split_ifs <;> omega
  exact hpos.trans_le (scalarB_ge_distinguished a (fun i => le_of_lt (ha i)) k)


end CoefficientOne.ScalarPositivity

end
