import MsetsLower.Lower.Dense.Fixing
import MsetsLower.Lower.Sparse.FinalAction
import MsetsLower.Lower.Sparse.Parameters

/-!
# Assembly of the two action-count regimes

The only logical split in `cor:lower-action-count` is whether
`floor(n/k)` is at least `2^32`.  The dense side is already a closed
capstone; the sparse side is supplied by the closed full-table construction
in `Sparse.FinalAction`.
-/

namespace MsetsLower.Lower

open MsetsLower

noncomputable section

/-- The natural interface of the sparse capstone.  It isolates the exact
fact consumed by the dense/sparse case split and is instantiated below by
the unconditional sparse theorem. -/
def SparseActionCountCapstone : Prop :=
  ∀ {n k T : Nat} (hk : 1 ≤ k) (hkn : k ≤ n)
      (hr : 2 ^ 32 ≤ n / k)
      (horizon :
        64 * (n : Real) * (k : Real) * actionCountLog n k ≤ (T : Real)),
    ActionCountConclusion n k T hkn

theorem actionCountConclusion_case_split
    {n k T : Nat} (hk : 1 ≤ k) (hkHalf : k ≤ n / 2)
    (hDenseHorizon : n ^ 2 ≤ T)
    (hSparse : 2 ^ 32 ≤ n / k →
      ActionCountConclusion n k T (by omega : k ≤ n)) :
    ActionCountConclusion n k T (by omega : k ≤ n) := by
  by_cases hr : 2 ^ 32 ≤ n / k
  · exact hSparse hr
  · exact Dense.lower_dense_actionCountConclusion hk hkHalf
      (Nat.lt_of_not_ge hr) hDenseHorizon

/-- `cor:lower-action-count`, modulo precisely the sparse capstone interface.
The dense/sparse split and both horizon projections are discharged here. -/
theorem lower_actionCountConclusion_of_sparseCapstone
    (hSparse : SparseActionCountCapstone)
    {n k T : Nat} (hk : 1 ≤ k) (hkHalf : k ≤ n / 2)
    (hDenseHorizon : n ^ 2 ≤ T)
    (hSparseHorizon :
      64 * (n : Real) * (k : Real) * actionCountLog n k ≤ (T : Real)) :
    ActionCountConclusion n k T (by omega : k ≤ n) := by
  apply actionCountConclusion_case_split hk hkHalf hDenseHorizon
  intro hr
  simpa only [proof_irrel_heq] using
    hSparse hk (by omega : k ≤ n) hr hSparseHorizon

/-- The closed sparse-capstone interface, supplied by the full-table sparse
construction rather than by an assumption. -/
theorem lower_sparseActionCountCapstone : SparseActionCountCapstone := by
  intro n k T hk hkn hr hT
  exact Sparse.lower_sparse_actionCountConclusion hk hkn
    (by simpa only [Sparse.sparseRatio] using hr) hT

/-- Literal unconditional form of `cor:lower-action-count`. -/
theorem lower_actionCountConclusion
    {n k T : Nat} (hk : 1 ≤ k) (hkHalf : k ≤ n / 2)
    (hDenseHorizon : n ^ 2 ≤ T)
    (hSparseHorizon :
      64 * (n : Real) * (k : Real) * actionCountLog n k ≤ (T : Real)) :
    ActionCountConclusion n k T (by omega : k ≤ n) :=
  lower_actionCountConclusion_of_sparseCapstone
    lower_sparseActionCountCapstone hk hkHalf
      hDenseHorizon hSparseHorizon

#print axioms actionCountConclusion_case_split
#print axioms lower_actionCountConclusion_of_sparseCapstone
#print axioms lower_sparseActionCountCapstone
#print axioms lower_actionCountConclusion

end

end MsetsLower.Lower
