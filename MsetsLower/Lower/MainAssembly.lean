import MsetsLower.Lower.ActionCount
import MsetsLower.Lower.Confidence.Fixing
import MsetsLower.Lower.ThresholdArithmetic

/-!
# Assembly at the manuscript's sparse action size

This is the final theorem-independent glue: combine action-count and
confidence tails at `s=min(m,d-m)`, then transport through complementation to
the original exact-`m` action space.
-/

namespace MsetsLower.Lower

open MsetsLower

noncomputable section

theorem explicitLowerConclusion_of_actionCount_confidence
    {d m T : Nat} (hm : 1 ≤ m) (hmLt : m ≤ d - 1)
    {delta : Real} (hdelta : 0 < delta)
    (hdeltaSmall : delta ≤ 1 / (2 : Real) ^ 36)
    (haction : ActionCountConclusion d (sparseSize d m) T
      (sparseSize_le_dimension (by omega : m ≤ d)))
    (hconfidence : ConfidenceConclusion d (sparseSize d m) T
      (sparseSize_le_dimension (by omega : m ≤ d)) delta) :
    ExplicitLowerConclusion d m T (by omega) delta := by
  have hlocal := actionCount_confidence_final_assembly
    (sparseSize_le_dimension (by omega : m ≤ d)) hdelta hdeltaSmall
      haction hconfidence
  exact explicitLowerConclusion_of_sparseSize hm hmLt hlocal

/-- The literal explicit lower bound, with the only remaining input packaged
as the sparse action-count capstone.  All threshold splitting, the dense
branch, the confidence branch, and complementation are closed in this
declaration. -/
theorem lower_bound_explicit_of_sparseCapstone
    (hSparse : SparseActionCountCapstone)
    {d m T : Nat} (_hd : 2 ≤ d) (hm : 1 ≤ m) (hmLt : m ≤ d - 1)
    {delta : Real} (hdelta : 0 < delta)
    (hdeltaSmall : delta ≤ 1 / (2 : Real) ^ 36)
    (hT : explicitHorizonThreshold d (sparseSize d m) delta ≤ T) :
    ExplicitLowerConclusion d m T (by omega) delta := by
  have hmd : m ≤ d := by omega
  have hsBounds := sparseSize_bounds hm hmLt
  have hsd : sparseSize d m ≤ d := sparseSize_le_dimension hmd
  have hdeltaOne : delta ≤ 1 := hdeltaSmall.trans (by norm_num)
  obtain ⟨hDenseReal, hActionHorizon, hConfidenceHorizon⟩ :=
    explicit_threshold_splits hsBounds.1 hsd hdelta hdeltaOne hT
  have hDenseHorizon : d ^ 2 ≤ T := by
    exact_mod_cast hDenseReal
  have haction : ActionCountConclusion d (sparseSize d m) T hsd := by
    simpa only [proof_irrel_heq] using
      lower_actionCountConclusion_of_sparseCapstone hSparse
        hsBounds.1 hsBounds.2 hDenseHorizon hActionHorizon
  have hconfidence :
      ConfidenceConclusion d (sparseSize d m) T hsd delta := by
    simpa only [proof_irrel_heq] using
      Confidence.lower_confidence hsBounds.1 hsBounds.2 hdelta
        hdeltaSmall hConfidenceHorizon
  exact explicitLowerConclusion_of_actionCount_confidence
    hm hmLt hdelta hdeltaSmall haction hconfidence

/-- `thm:lower-bound-explicit`, with every action-count, confidence, and
finite-table premise discharged. -/
theorem lower_bound_explicit
    {d m T : Nat} (hd : 2 ≤ d) (hm : 1 ≤ m) (hmLt : m ≤ d - 1)
    {delta : Real} (hdelta : 0 < delta)
    (hdeltaSmall : delta ≤ 1 / (2 : Real) ^ 36)
    (hT : explicitHorizonThreshold d (sparseSize d m) delta ≤ T) :
    ExplicitLowerConclusion d m T (by omega) delta :=
  lower_bound_explicit_of_sparseCapstone lower_sparseActionCountCapstone
    hd hm hmLt hdelta hdeltaSmall hT

#print axioms explicitLowerConclusion_of_actionCount_confidence
#print axioms lower_bound_explicit_of_sparseCapstone
#print axioms lower_bound_explicit

end

end MsetsLower.Lower
