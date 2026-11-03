import MsetsLower.Lower.Sparse.Construction
import MsetsLower.Lower.TruncatedRegret

/-!
# Inactive suffix of the sparse construction

The manuscript runs the sparse environment for `T0` rounds and sets all
later item losses to zero.  This file connects that literal definition to the
generic pathwise and distributional truncation lemmas.
-/

namespace MsetsLower.Lower.Sparse

open MsetsLower Set

noncomputable section

theorem sparseLossProcess_zeroActionLossFrom
    {n k : Nat} (hk : 1 ≤ k) (eta : Real) (heta0 : 0 ≤ eta)
    (heta : eta ≤ (1 : Real) / 16) (n' q c0 T0 : Nat)
    (U : Nat → Fin n → Real) (hU : ∀ b i, |U b i| ≤ 1)
    (Z : Nat → Real) (hZ : ∀ t, Z t ∈ Icc (-1 : Real) 1) :
    ZeroActionLossFrom
      (sparseLossProcess hk eta heta0 heta n' q c0 T0 U hU Z hZ) T0 := by
  intro t ht h A
  change actionLoss A (sparseItemLoss eta n' q c0 T0 U Z t h) = 0
  rw [show sparseItemLoss eta n' q c0 T0 U Z t h = (fun _ => 0) by
    funext i
    exact sparseItemLoss_of_le eta n' q c0 T0 U Z ht h i]
  exact actionLoss_zero A

theorem sparse_pathRegret_add
    {n k : Nat} (hk : 1 ≤ k) (eta : Real) (heta0 : 0 ≤ eta)
    (heta : eta ≤ (1 : Real) / 16) (n' q c0 T0 : Nat)
    (U : Nat → Fin n → Real) (hU : ∀ b i, |U b i| ≤ 1)
    (Z : Nat → Real) (hZ : ∀ t, Z t ∈ Icc (-1 : Real) 1)
    (r : Nat) (h : History n k (T0 + r)) :
    pathRegret
        (sparseLossProcess hk eta heta0 heta n' q c0 T0 U hU Z hZ)
        (T0 + r) h =
      pathRegret
        (sparseLossProcess hk eta heta0 heta n' q c0 T0 U hU Z hZ)
        T0 (History.dropSuffix T0 r h) := by
  exact pathRegret_add_of_zeroFrom
    (sparseLossProcess_zeroActionLossFrom hk eta heta0 heta n' q c0 T0
      U hU Z hZ) h

theorem sparse_runLaw_add_regretTailProbability
    {n k : Nat} (hkn : k ≤ n) (P : Policy n k)
    (hk : 1 ≤ k) (eta : Real) (heta0 : 0 ≤ eta)
    (heta : eta ≤ (1 : Real) / 16) (n' q c0 T0 : Nat)
    (U : Nat → Fin n → Real) (hU : ∀ b i, |U b i| ≤ 1)
    (Z : Nat → Real) (hZ : ∀ t, Z t ∈ Icc (-1 : Real) 1)
    (r : Nat) (threshold : Real) :
    (runLaw P
      (sparseLossProcess hk eta heta0 heta n' q c0 T0 U hU Z hZ)
      (T0 + r)).real
        {h | threshold ≤ pathRegret
          (sparseLossProcess hk eta heta0 heta n' q c0 T0 U hU Z hZ)
          (T0 + r) h} =
      (runLaw P
        (sparseLossProcess hk eta heta0 heta n' q c0 T0 U hU Z hZ)
        T0).real
          {h | threshold ≤ pathRegret
            (sparseLossProcess hk eta heta0 heta n' q c0 T0 U hU Z hZ)
            T0 h} := by
  exact runLaw_add_regretTailProbability_of_zeroFrom hkn P _
    (sparseLossProcess_zeroActionLossFrom hk eta heta0 heta n' q c0 T0
      U hU Z hZ) threshold

#print axioms sparseLossProcess_zeroActionLossFrom
#print axioms sparse_pathRegret_add
#print axioms sparse_runLaw_add_regretTailProbability

end

end MsetsLower.Lower.Sparse
