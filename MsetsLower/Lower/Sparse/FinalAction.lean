import MsetsLower.Lower.Sparse.ConcreteLikelihood
import MsetsLower.Lower.Sparse.ConcreteMean
import MsetsLower.Lower.Sparse.GammaTail

/-!
# Sparse action-count capstone

This module performs only the last deterministic specialization of the sparse
construction.  Its input is the concrete full-table mean estimate for
`sparseGamma`; the mean-to-tail theorem fixes the table, and the remaining
lemmas convert its threshold to the literal binomial action-count threshold.
-/

set_option linter.style.header false

namespace MsetsLower.Lower.Sparse

open MsetsLower MeasureTheory
open MsetsLower.Lower

noncomputable section

/-- A concrete full-table `Gamma` mean witness for a fixed policy yields the
literal sparse action-count tail, still with the stronger probability
`2^-10`. -/
theorem lower_sparse_two_neg_31_tail_of_concreteGammaMean
    {n k T : Nat} (P : Policy n k) (hk : 1 <= k) (hkn : k <= n)
    (hr : 2 ^ 32 <= sparseRatio n k)
    (hT : 64 * (n : Real) * (k : Real) * actionCountLog n k <= T)
    (hmean : exists sigma : Equiv.Perm (Fin (sparseSignalCount n k)),
      sparseA / 4 * (k : Real) * (sparseT0 n k T : Real) <=
        ∫ z,
          sparseGamma hk (sparseEta n k T) (sparseEta_nonneg n k T)
            ((sparseEta_bounds hk hr hT).1.trans
              (sparseEta_bounds hk hr hT).2.le)
            (sparseQ n k T) (sparseC0 n k T)
            (sparseSignalCount_le n k)
            (rfl : sparseSignalCount n k = k * sparseRatio n k)
            (lt_of_lt_of_le (by norm_num) hr) sigma (sparseT0 n k T) z
          ∂sparseConcreteJointLaw hk hr hT (sparseCenteredPolicy P)) :
    HasRegretLowerTail hkn P T
      ((1 / (2 : Real) ^ 31) *
        Real.sqrt ((n : Real) * (T : Real) *
          Real.log (n.choose k : Real)))
      (1 / (2 : Real) ^ 10) := by
  obtain ⟨sigma, hmean⟩ := hmean
  have hrpos : 0 < sparseRatio n k :=
    lt_of_lt_of_le (by norm_num) hr
  have hsignal : k <= sparseSignalCount n k := sparseSignalCount_ge hr
  have hT0pos : 0 < sparseT0 n k T := by
    have hcpos : 0 < sparseC0 n k T := by
      exact lt_of_lt_of_le (by positivity) (sparseC0_ge hk hr hT)
    have hellpos : 0 < sparseEll n k T := by
      simpa [sparseC0] using hcpos
    have hBpos : 0 < sparseBlockCount n k := sparseBlockCount_one_le hr
    simp only [sparseT0, sparseQ]
    positivity
  have hT0T : sparseT0 n k T <= T := (sparseT0_bounds hk hr hT).2
  have htail : HasRegretLowerTail
      ((sparseSignalCount_ge hr).trans (sparseSignalCount_le n k)) P T
      (sparseA * sparseEta n k T * (sparseT0 n k T : Real) / 8)
      (1 / (2 : Real) ^ 10) := by
    apply lower_sparse_gammaTail_fixed_at_larger_horizon
      P hk hsignal hT0pos hT0T (sparseEta n k T)
        (sparseEta_nonneg n k T)
        ((sparseEta_bounds hk hr hT).1.trans
          (sparseEta_bounds hk hr hT).2.le)
        (sparseQ n k T) (sparseC0 n k T)
        (sparseSignalCount_le n k)
        (rfl : sparseSignalCount n k = k * sparseRatio n k)
        hrpos sigma
    simpa [sparseConcreteJointLaw,
      sparseConcreteHiddenTableParameterFamily] using hmean
  have hthreshold :
      (1 / (2 : Real) ^ 31) *
          Real.sqrt ((n : Real) * (T : Real) *
            Real.log (n.choose k : Real)) <=
        sparseA * sparseEta n k T * (sparseT0 n k T : Real) / 8 := by
    have hetaT0 := sparseEta_mul_T0_ge_logChoose hk hkn hr hT
    have hconverted := sparse_eta_threshold_implies_two_neg_31 hetaT0
    simpa only [mul_assoc] using hconverted
  have htail' := htail.mono hthreshold le_rfl
  simpa only [Subsingleton.elim
    ((sparseSignalCount_ge hr).trans (sparseSignalCount_le n k)) hkn] using htail'

/-- The literal conclusion of `prop:lower-sparse-action`, with its stronger
threshold `2^-31` and probability `2^-10`.  The concrete full-table mean
witness is discharged internally, so this capstone has exactly the paper's
parameter assumptions and no analytic premise. -/
theorem lower_sparse_action
    {n k T : Nat} (hk : 1 <= k) (hkHalf : k <= n / 2)
    (hr : 2 ^ 32 <= sparseRatio n k)
    (hT : 64 * (n : Real) * (k : Real) * actionCountLog n k <= T) :
    forall P : Policy n k,
      HasRegretLowerTail (by omega : k <= n) P T
        ((1 / (2 : Real) ^ 31) *
          Real.sqrt ((n : Real) * (T : Real) *
            Real.log (n.choose k : Real)))
        (1 / (2 : Real) ^ 10) := by
  intro P
  exact lower_sparse_two_neg_31_tail_of_concreteGammaMean
    P hk (by omega : k <= n) hr hT
      (lower_sparse_concreteGammaMean hk hr hT P)

/-- If every policy has the concrete full-table mean witness, the sparse
branch of the common action-count conclusion follows.  No probabilistic or
event-to-regret premise remains besides that concrete mean estimate. -/
theorem lower_sparse_actionCountConclusion_of_concreteGammaMean
    {n k T : Nat} (hk : 1 <= k) (hkn : k <= n)
    (hr : 2 ^ 32 <= sparseRatio n k)
    (hT : 64 * (n : Real) * (k : Real) * actionCountLog n k <= T)
    (hmean : forall P : Policy n k,
      exists sigma : Equiv.Perm (Fin (sparseSignalCount n k)),
        sparseA / 4 * (k : Real) * (sparseT0 n k T : Real) <=
          ∫ z,
            sparseGamma hk (sparseEta n k T) (sparseEta_nonneg n k T)
              ((sparseEta_bounds hk hr hT).1.trans
                (sparseEta_bounds hk hr hT).2.le)
              (sparseQ n k T) (sparseC0 n k T)
              (sparseSignalCount_le n k)
              (rfl : sparseSignalCount n k = k * sparseRatio n k)
              (lt_of_lt_of_le (by norm_num) hr) sigma
              (sparseT0 n k T) z
            ∂sparseConcreteJointLaw hk hr hT (sparseCenteredPolicy P)) :
    ActionCountConclusion n k T hkn := by
  intro P
  apply sparse_tail_implies_actionCountTail hkn P
  exact lower_sparse_two_neg_31_tail_of_concreteGammaMean
    P hk hkn hr hT (hmean P)

/-- The unconditional sparse branch of `cor:lower-action-count`.  The genuine
full-table score-bias theorem supplies the concrete `Gamma` mean, so no
probabilistic premise remains in this capstone. -/
theorem lower_sparse_actionCountConclusion
    {n k T : Nat} (hk : 1 <= k) (hkn : k <= n)
    (hr : 2 ^ 32 <= sparseRatio n k)
    (hT : 64 * (n : Real) * (k : Real) * actionCountLog n k <= T) :
    ActionCountConclusion n k T hkn := by
  apply lower_sparse_actionCountConclusion_of_concreteGammaMean
    hk hkn hr hT
  intro P
  have hmean := lower_sparse_concreteGammaMean hk hr hT P
  simpa only [sparseConcreteGammaMean] using hmean

#print axioms lower_sparse_two_neg_31_tail_of_concreteGammaMean
#print axioms lower_sparse_action
#print axioms lower_sparse_actionCountConclusion_of_concreteGammaMean
#print axioms lower_sparse_actionCountConclusion

end

end MsetsLower.Lower.Sparse
