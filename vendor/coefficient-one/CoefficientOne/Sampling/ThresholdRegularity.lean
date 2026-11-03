import CoefficientOne.Sampling.QuotaMonotonicity

/-! # Smooth conditional thresholds on the positive-weight domain -/

open scoped BigOperators
open EffectiveResistance
namespace CoefficientOne.Sampling
noncomputable section
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

theorem subsetWeight_contDiff (S : Finset ι) :
    ContDiff ℝ ⊤ (fun w : ι → ℝ => subsetWeight w S) := by
  induction S using Finset.induction_on with
  | empty => simpa [subsetWeight] using (contDiff_const : ContDiff ℝ ⊤ (fun _ : ι → ℝ => (1 : ℝ)))
  | @insert i S hi ih =>
    simpa [subsetWeight, Finset.prod_insert hi] using (contDiff_apply ℝ (fun _ : ι => ℝ) i).mul ih

theorem restrictedElementary_contDiff (R : Finset ι) (r : ℕ) :
    ContDiff ℝ ⊤ (fun w : ι → ℝ => restrictedElementary w R r) := by
  exact ContDiff.sum (fun S _ => subsetWeight_contDiff S)

theorem sequentialThreshold_contDiffOn (R : Finset ι) (r : ℕ) (hr : r ≤ R.card) (i : ι) :
    ContDiffOn ℝ ⊤ (fun w : ι → ℝ => sequentialThreshold w R r i)
      {w | ∀ j, 0 < w j} := by
  exact ((contDiff_apply ℝ (fun _ : ι => ℝ) i).mul
    (restrictedElementary_contDiff (R.erase i) (r - 1))).contDiffOn.div
    (restrictedElementary_contDiff R r).contDiffOn
    (fun w hw => ne_of_gt (restrictedElementary_pos w hw R r hr))

theorem quotaThreshold_contDiffOn (R : Finset ι) (r : ℕ) (hr : r ≤ R.card) (i : ι) :
    ContDiffOn ℝ ⊤ (fun w : ι → ℝ => quotaThreshold w R r i)
      {w | ∀ j, 0 < w j} := by
  unfold quotaThreshold
  split_ifs
  · exact contDiffOn_const
  · exact contDiffOn_const
  · exact sequentialThreshold_contDiffOn R r hr i

end
end CoefficientOne.Sampling
